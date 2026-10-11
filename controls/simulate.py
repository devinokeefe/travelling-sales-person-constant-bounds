#!/usr/bin/env python3
"""Simulations of the rule recorded in a values file (illustration and control, not part of the proof).

blocks  Draw independent blocks.  For each, measure the path chosen by the rule and the shortest path
        through the block.  In every cell the rule takes, among the orders of least table cost, the first
        in the lexicographic order of (pi(1), ..., pi(k - 1)).  Divided by k h, the first mean estimates
        the true value of the rule, which the bound of the checkers must exceed; the second estimates the
        best value that any rule can reach for this k and h.  The cells of the sampled blocks are a sample
        of the cells, each drawn with its probability.  For each, the table entries along the chosen path
        are added, and so are the two brackets of bracket.py for these entries, on a mesh twice as fine.
        The mean of the first sum estimates the table cost of the rule, which the bound of the checkers
        exceeds by its rounding only; the means of the differences estimate how far the table cost lies
        above the two brackets of the true value of the rule.

tour    Draw a Poisson process of intensity 1 in a square of side W = (number of strips) * h and build the
        closed tour of the proof of the block bound: strips, an auxiliary first point in each strip, blocks
        completed by points to the right of the square, alternate strips reversed.  Points outside the
        square are then left out.  The walks through the blocks, before points are left out, have length
        k * blocks * (value of the rule) on average, and a strip holds (h W + (k + 1)/2)/k blocks on
        average, so that their length divided by W^2 exceeds the value of the rule by the factor
        1 + (k + 1)/(2 h W).  The closed tour differs from the walks by a bounded length for each strip.

shortest  No values file is needed.  Draw independent blocks with K gaps for the strip height H (a fraction
        such as 21/10) and measure the shortest path through each.  This estimates the best value that any
        rule can reach for these K and H.

Needs numpy and numba.

usage:  simulate.py SPEC blocks [SAMPLES] [SEED]
        simulate.py SPEC tour [STRIPS] [SEED]
        simulate.py shortest K H [SAMPLES] [SEED]
"""

import math
import os
import sys
import time
from fractions import Fraction

import numpy as np
from numba import njit, prange

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkers"))
from bracket import brackets, read_table  # noqa: E402
from check_bound import F, pairs, read_spec  # noqa: E402

PORTION = 1024  # blocks that a thread takes at a time


def rule_tables(par):
    """The table, the table row of every pair of points for every gap tuple, and the cell boundaries."""
    k, m = par["k"], par["m"]
    keys, table = read_table(par)
    row_of_key = {key: row for row, key in enumerate(keys)}
    pair_list = pairs(k)
    pair_index = np.zeros((k + 1, k + 1), dtype=np.int64)
    for index, (i, j) in enumerate(pair_list):
        pair_index[i, j] = pair_index[j, i] = index
    rows = np.zeros((m**k, len(pair_list)), dtype=np.int64)
    for g in range(m**k):
        digits = [g // m**t % m for t in range(k)]
        for index, (i, j) in enumerate(pair_list):
            rows[g, index] = row_of_key[tuple(digits[i:j].count(c) for c in range(m))]
    bounds = np.array(par["b"][1:], dtype=np.float64) / par["M"]
    return table, rows, pair_index, bounds


@njit(cache=True)
def choose(k, m, n, z, u, table, rows, pair_index, bounds, cost, rest, order):
    """Writes to order the order that the rule chooses for a block with gaps z and heights u, and
    returns the index of its gap tuple.

    rest[mask, v] is the least table cost of a path that starts at the interior point v + 1, visits the
    interior points outside mask (which contains v) and ends at point k.  The order is then built from
    its first point on, taking at each step the smallest point that a path of least cost can visit next.
    """
    g = 0
    power = 1
    for t in range(k):
        cell = 0
        for c in range(m - 1):
            if z[t] >= bounds[c]:
                cell = c + 1
        g += cell * power
        power *= m
    for i in range(k + 1):
        ai = min(int(n * u[i]), n - 1)
        for j in range(i + 1, k + 1):
            aj = min(int(n * u[j]), n - 1)
            cost[i, j] = cost[j, i] = table[rows[g, pair_index[i, j]], abs(ai - aj)]
    inner = k - 1
    full = (1 << inner) - 1
    for v in range(inner):
        rest[full, v] = cost[v + 1, k]
    for mask in range(full - 1, 0, -1):
        for v in range(inner):
            if not (mask >> v) & 1:
                continue
            best = -1
            for w in range(inner):
                if (mask >> w) & 1:
                    continue
                value = cost[v + 1, w + 1] + rest[mask | (1 << w), w]
                if best < 0 or value < best:
                    best = value
            rest[mask, v] = best
    order[0] = 0
    order[k] = k
    mask = 0
    here = 0
    for r in range(1, k):
        best = -1
        choice = -1
        for w in range(inner):
            if (mask >> w) & 1:
                continue
            value = cost[here, w + 1] + rest[mask | (1 << w), w]
            if best < 0 or value < best:
                best = value
                choice = w
        order[r] = choice + 1
        mask |= 1 << choice
        here = choice + 1
    return g


@njit(cache=True)
def distances(k, height, z, u, x, dist):
    """Writes to dist the distances between the points of a block with gaps z and heights u."""
    for t in range(k):
        x[t + 1] = x[t] + z[t]
    for i in range(k + 1):
        for j in range(i + 1, k + 1):
            d = math.sqrt((x[i] - x[j]) ** 2 + (height * (u[i] - u[j])) ** 2)
            dist[i, j] = dist[j, i] = d


@njit(cache=True)
def shortest(k, dist, dp):
    """The length of the shortest path from point 0 to point k through all interior points.

    dp[mask, v] is the length of the shortest path from point 0 through the interior points of mask that
    ends at the interior point v + 1.
    """
    inner = k - 1
    full = (1 << inner) - 1
    if inner == 0:
        return dist[0, k]
    dp[:, :] = 1e300
    for v in range(inner):
        dp[1 << v, v] = dist[0, v + 1]
    for mask in range(1, full + 1):
        for v in range(inner):
            here = dp[mask, v]
            if here >= 1e299:
                continue
            for w in range(inner):
                if (mask >> w) & 1:
                    continue
                value = here + dist[v + 1, w + 1]
                target = mask | (1 << w)
                dp[target, w] = min(dp[target, w], value)
    best = 1e300
    for v in range(inner):
        best = min(best, dp[full, v] + dist[v + 1, k])
    return best


@njit(parallel=True, cache=True)
def simulate_blocks(k, m, n, height, Z, U, table, rows, pair_index, bounds, low, high, scale):
    """For every sampled block: the lengths of the rule's path and of the shortest path, and for the
    rule's path in the cell of the block the table cost divided by scale and its excess over the sums
    of the brackets low and high."""
    samples = Z.shape[0]
    rule_length = np.zeros(samples)
    best_length = np.zeros(samples)
    table_cost = np.zeros(samples)
    over_low = np.zeros(samples)
    over_high = np.zeros(samples)
    inner = max(k - 1, 1)
    portions = (samples + PORTION - 1) // PORTION
    for portion in prange(portions):
        cost = np.zeros((k + 1, k + 1), dtype=np.int64)
        rest = np.zeros((1 << inner, inner), dtype=np.int64)
        order = np.zeros(k + 1, dtype=np.int64)
        dist = np.zeros((k + 1, k + 1))
        dp = np.zeros((1 << inner, inner))
        x = np.zeros(k + 1)
        for s in range(portion * PORTION, min(samples, (portion + 1) * PORTION)):
            distances(k, height, Z[s], U[s], x, dist)
            g = choose(k, m, n, Z[s], U[s], table, rows, pair_index, bounds, cost, rest, order)
            total = 0.0
            for r in range(k):
                total += dist[order[r], order[r + 1]]
            rule_length[s] = total
            best_length[s] = shortest(k, dist, dp)
            entries = 0
            sum_low = 0.0
            sum_high = 0.0
            for r in range(k):
                i, j = order[r], order[r + 1]
                row = rows[g, pair_index[i, j]]
                d = abs(min(int(n * U[s, i]), n - 1) - min(int(n * U[s, j]), n - 1))
                entries += table[row, d]
                sum_low += low[row, d]
                sum_high += high[row, d]
            table_cost[s] = entries / scale
            over_low[s] = entries / scale - sum_low
            over_high[s] = entries / scale - sum_high
    return rule_length, best_length, table_cost, over_low, over_high


@njit(cache=True)
def strip_sequence(k, m, n, h, xs, ys, table, rows, pair_index, bounds):
    """The visiting sequence of one strip: xs increasing with xs[0] = 0, len(xs) = 1 (mod k)."""
    count = xs.shape[0]
    sequence = np.zeros(count, dtype=np.int64)
    inner = max(k - 1, 1)
    cost = np.zeros((k + 1, k + 1), dtype=np.int64)
    rest = np.zeros((1 << inner, inner), dtype=np.int64)
    order = np.zeros(k + 1, dtype=np.int64)
    z = np.zeros(k)
    u = np.zeros(k + 1)
    for start in range(0, count - 1, k):
        for t in range(k):
            z[t] = h * (xs[start + t + 1] - xs[start + t])
        for t in range(k + 1):
            u[t] = ys[start + t] / h
        choose(k, m, n, z, u, table, rows, pair_index, bounds, cost, rest, order)
        for r in range(k):
            sequence[start + r] = start + order[r]
    sequence[count - 1] = count - 1
    return sequence


@njit(parallel=True, cache=True)
def shortest_paths(k, height, Z, U):
    """The length of the shortest path from P_0 to P_k through all interior points, for every block."""
    samples = Z.shape[0]
    out = np.zeros(samples)
    inner = max(k - 1, 1)
    portions = (samples + PORTION - 1) // PORTION
    for portion in prange(portions):
        dist = np.zeros((k + 1, k + 1))
        dp = np.zeros((1 << inner, inner))
        x = np.zeros(k + 1)
        for s in range(portion * PORTION, min(samples, (portion + 1) * PORTION)):
            distances(k, height, Z[s], U[s], x, dist)
            out[s] = shortest(k, dist, dp)
    return out


def run_shortest(k, h, samples, seed):
    rng = np.random.default_rng(seed)
    count = 0
    total = total2 = 0.0
    start = time.time()
    while count < samples:
        batch = min(100_000, samples - count)
        lengths = shortest_paths(k, h * h, rng.exponential(1.0, size=(batch, k)), rng.random((batch, k + 1)))
        total += float(lengths.sum())
        total2 += float((lengths**2).sum())
        count += batch
    mean = total / count
    se = math.sqrt((total2 / count - mean**2) / count)
    print(f"k {k}, h {h:.6f}, blocks {count}, seed {seed}, {time.time() - start:.0f} s")
    print(f"shortest path   {mean / (k * h):.6f} +/- {se / (k * h):.6f}")


def mean_and_error(total, squares, count):
    mean = total / count
    return mean, math.sqrt(max(squares / count - mean**2, 0.0) / count)


def run_blocks(par, samples, seed):
    k, m, n = par["k"], par["m"], par["n"]
    h = par["hn"] / par["hd"]
    tables = rule_tables(par)
    low, high, _ = brackets(par, read_table(par)[0], 2)
    rng = np.random.default_rng(seed)
    count = 0
    sums = np.zeros(6)
    squares = np.zeros(6)
    start = time.time()
    while count < samples:
        batch = min(500_000, samples - count)
        Z = rng.exponential(1.0, size=(batch, k))
        U = rng.random((batch, k + 1))
        rule, best, cost, over_low, over_high = simulate_blocks(
            k, m, n, h * h, Z, U, *tables, low, high, float(F)
        )
        for index, values in enumerate((rule, best, rule - best, cost, over_low, over_high)):
            sums[index] += values.sum()
            squares[index] += (values**2).sum()
        count += batch
    scale = 1.0 / (k * h)
    rows = [mean_and_error(sums[index], squares[index], count) for index in range(6)]
    print(f"blocks {count}, seed {seed}, {time.time() - start:.0f} s")
    print(f"rule            {rows[0][0] * scale:.6f} +/- {rows[0][1] * scale:.6f}")
    print(f"shortest path   {rows[1][0] * scale:.6f} +/- {rows[1][1] * scale:.6f}")
    print(f"difference      {rows[2][0] * scale:.6f} +/- {rows[2][1] * scale:.6f}")
    print(f"table cost      {rows[3][0] * scale:.6f} +/- {rows[3][1] * scale:.6f}")
    print(f"table - lower   {rows[4][0] * scale:.4e} +/- {rows[4][1] * scale:.1e}")
    print(f"table - upper   {rows[5][0] * scale:.4e} +/- {rows[5][1] * scale:.1e}")


def run_tour(par, strips, seed):
    k, m, n = par["k"], par["m"], par["n"]
    h = par["hn"] / par["hd"]
    side = strips * h
    tables = rule_tables(par)
    rng = np.random.default_rng(seed)
    walks = np.zeros(strips)  # the walk of the proof in each strip, through all points of its blocks
    blocks = np.zeros(strips)
    tour = 0.0  # the closed tour through the points in the square
    points = 0
    first = previous = None
    start = time.time()
    for j in range(strips):
        inside = rng.poisson(h * side)
        extra = k * (1 + inside // k) - inside
        xs = np.concatenate(
            ([0.0], np.sort(rng.random(inside)) * side, side + np.cumsum(rng.exponential(1 / h, extra)))
        )
        ys = rng.random(inside + extra + 1) * h
        sequence = strip_sequence(k, m, n, h, xs, ys, *tables)
        px, py = xs[sequence], ys[sequence] + j * h
        walks[j] = np.hypot(np.diff(px), np.diff(py)).sum()
        blocks[j] = (inside + extra) // k
        real = (sequence >= 1) & (sequence <= inside)
        px, py = px[real], py[real]
        if j % 2 == 1:
            px, py = px[::-1], py[::-1]
        if len(px) == 0:
            continue
        tour += float(np.hypot(np.diff(px), np.diff(py)).sum())
        if previous is None:
            first = (px[0], py[0])
        else:
            tour += math.hypot(px[0] - previous[0], py[0] - previous[1])
        previous = (px[-1], py[-1])
        points += len(px)
    tour += math.hypot(first[0] - previous[0], first[1] - previous[1])
    value = walks.sum() / (k * blocks.sum())
    error = math.sqrt(((walks - value * k * blocks) ** 2).sum()) / (k * blocks.sum())
    used, seconds = int(blocks.sum()), time.time() - start
    print(f"strips {strips}, side {side:.1f}, points {points}, blocks {used}, seed {seed}, {seconds:.0f} s")
    print(f"walks of the proof: length / (k * blocks)       = {value:.6f} +/- {error:.6f}")
    print(f"walks of the proof: length / side^2             = {walks.sum() / side**2:.6f}")
    print(f"blocks * k / side^2                             = {k * blocks.sum() / side**2:.6f}")
    print(f"1 + (k + 1) / (2 h side)                        = {1 + (k + 1) / (2 * h * side):.6f}")
    print(f"closed tour through the points: length / side^2 = {tour / side**2:.6f}")
    print(f"closed tour: length / sqrt(points * area)       = {tour / (side * math.sqrt(points)):.6f}")


def main(argv):
    if len(argv) >= 3 and argv[0] == "shortest":
        samples = int(argv[3]) if len(argv) > 3 else 1_000_000
        run_shortest(
            int(argv[1]), float(Fraction(argv[2])), samples, int(argv[4]) if len(argv) > 4 else 20261009
        )
        return 0
    if len(argv) < 2 or argv[1] not in ("blocks", "tour"):
        raise SystemExit(__doc__)
    par = read_spec(argv[0])
    seed = int(argv[3]) if len(argv) > 3 else 20261009
    if argv[1] == "blocks":
        run_blocks(par, int(argv[2]) if len(argv) > 2 else 2_000_000, seed)
    else:
        run_tour(par, int(argv[2]) if len(argv) > 2 else 1000, seed)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
