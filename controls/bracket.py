#!/usr/bin/env python3
"""Two-sided floating-point control of the table of a values file (a check, not part of the proof).

On a mesh R times finer than that of the spec file, every conditional expected segment length is bracketed:

  lower:  Jensen's inequality, the mass of each sub-interval placed at its conditional mean
          (and the part of a gap of the last cell beyond the truncation point left out);
  upper:  the chord bound, the mass of each sub-interval split between its two ends, plus the tail term.

If the table is right, then  lower <= upper <= table  for every entry.

With --rule the rule defined by the table (in every cell, an order that minimises the table cost) is
evaluated over all cells with the table and with both brackets.  Its sums of table costs are integers and
must equal the cell sums of the values file.  Its true expected length lies between the two bracket sums:
the lower must not exceed the upper, nor the upper the table cost of the rule.  (That this cost does not
exceed the bound of the checkers is tested by tools/paper_numbers.py.)  With --log FILE the sums are
written to FILE as they are found, and an interrupted run is continued by repeating the command.

Rounding errors are not controlled.  Needs numpy, numba and, for long keys, scipy.

usage:  bracket.py SPEC R [--rule] [--log FILE]
"""

import hashlib
import math
import os
import sys
import time

import numpy as np
from numba import njit, prange

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkers"))
from check_bound import F, all_keys, pairs, read_spec, read_values, stored_table  # noqa: E402

PORTION = 256  # gap tuples evaluated between two entries in the log


def read_table(par):
    """The table of the values file, as an array with one row for each key."""
    table = stored_table(par)
    keys = list(table)
    if keys != all_keys(par["m"], par["k"]):
        raise SystemExit("the keys of the values file are not in the expected order")
    return keys, np.array([table[key] for key in keys], dtype=np.int64)


def gap_vectors(par, R):
    """For each gap cell: the Jensen masses, the chord masses and the true probability of the cell."""
    M, b, m, T = par["M"], par["b"], par["m"], par["T"]
    delta = 1.0 / (M * R)
    theta = 1.0 - delta / math.expm1(delta)  # conditional mean of a gap within a sub-interval
    lower, upper, mass = [], [], []
    for c in range(m):
        if c < m - 1:
            width = (b[c + 1] - b[c]) * R
            norm = -math.expm1(-width * delta)
            mass.append(math.exp(-b[c] / M) * norm)
        else:
            width = T * M * R
            norm = 1.0
            mass.append(math.exp(-b[c] / M))
        inside = np.exp(-np.arange(width) * delta) * (-math.expm1(-delta)) / norm
        lower.append(inside.copy())
        chord = np.zeros(width + 1)
        chord[:-1] += inside * (1 - theta / delta)
        chord[1:] += inside * theta / delta
        if c == m - 1:
            chord[-1] += math.exp(-T)  # the atom of the truncated gap
        upper.append(chord)
    return lower, upper, mass, delta, theta


def convolve(u, v):
    if len(u) * len(v) < 4_000_000:
        return np.convolve(u, v)
    from scipy.signal import fftconvolve  # noqa: PLC0415

    return np.maximum(fftconvolve(u, v), 0.0)


def key_vector(key, cache, single):
    if key not in cache:
        c = max(i for i, count in enumerate(key) if count)
        shorter = key[:c] + (key[c] - 1,) + key[c + 1 :]
        cache[key] = (
            single[c] if sum(shorter) == 0 else convolve(key_vector(shorter, cache, single), single[c])
        )
    return cache[key]


@njit(parallel=True, cache=True)
def mean_distance(points, delta, shift, weight, offset, n, cell_height):
    """E|(x, y)| for x = j delta + shift and y = d cell_height + offset[t] with weights weight[t]."""
    out = np.zeros((n, points))
    for j in prange(points):
        x2 = (j * delta + shift) ** 2
        for d in range(n):
            total = 0.0
            for t in range(weight.shape[0]):
                y = d * cell_height + offset[t]
                total += weight[t] * math.sqrt(x2 + y * y)
            out[d, j] = total
    return out


def brackets(par, keys, R):
    """Lower and upper brackets for every table entry, in units of the scaled length."""
    k, m, n, b = par["k"], par["m"], par["n"], par["b"]
    lower, upper, mass, delta, theta = gap_vectors(par, R)
    cell_height = (par["hn"] / par["hd"]) ** 2 / n
    parts = par["nu"] * R
    eta = cell_height / parts
    ends = np.ones(parts + 1)
    ends[0] = ends[-1] = 0.5
    ends /= parts
    weight_up = np.convolve(ends, ends[::-1])
    offset_up = (np.arange(len(weight_up)) - parts) * eta
    middles = np.ones(parts) / parts
    weight_lo = np.convolve(middles, middles[::-1])
    offset_lo = (np.arange(len(weight_lo)) - (parts - 1)) * eta
    points = k * R * (b[-1] + par["T"] * par["M"]) + 2
    g_up = mean_distance(points, delta, 0.0, weight_up, offset_up, n, cell_height)
    g_lo = [None] + [
        mean_distance(points, delta, r * theta, weight_lo, offset_lo, n, cell_height) for r in range(1, k + 1)
    ]
    cache_lo, cache_up = {}, {}
    low = np.zeros((len(keys), n))
    high = np.zeros((len(keys), n))
    for row, key in enumerate(keys):
        base = sum(count * b[c] * R for c, count in enumerate(key))
        v_up = key_vector(key, cache_up, upper)
        v_lo = key_vector(key, cache_lo, lower)
        high[row] = g_up[:, base : base + len(v_up)] @ v_up + key[m - 1] * math.exp(-par["T"])
        low[row] = g_lo[sum(key)][:, base : base + len(v_lo)] @ v_lo
    return low, high, mass


@njit(parallel=True, cache=True)
def rule_value(k, n, table, rows, pair_index, low, high, first, last):
    """For the gap tuples first, ..., last - 1: the sums over all height tuples of the table cost and of
    the two brackets along an order that minimises the table cost.

    dp[mask, v] is the least table cost of a path from point 0 through the inner points of mask that ends
    at the inner point v; sl and sh are the two brackets summed along one such path.  These depend only on
    the heights of point 0 and of the points of mask.  The heights of the points 0, ..., k - 1 are run
    through like the digits of a counter, the last one fastest, and after each step only the masks whose
    highest point has a changed height are computed again.  The height of point k is the innermost loop.
    """
    inner = k - 1
    full = (1 << inner) - 1
    out_table = np.zeros(last - first, dtype=np.int64)
    out_low = np.zeros(last - first)
    out_high = np.zeros(last - first)
    for index in prange(last - first):
        g = first + index
        big = 1 << 62
        tw = np.zeros((k + 1, k + 1, n), dtype=np.int64)
        tl = np.zeros((k + 1, k + 1, n))
        th = np.zeros((k + 1, k + 1, n))
        for i in range(k + 1):
            for j in range(i + 1, k + 1):
                row = rows[g, pair_index[i, j]]
                for d in range(n):
                    tw[i, j, d] = tw[j, i, d] = table[row, d]
                    tl[i, j, d] = tl[j, i, d] = low[row, d]
                    th[i, j, d] = th[j, i, d] = high[row, d]
        a = np.zeros(k, dtype=np.int64)
        dp = np.zeros((full + 1, inner), dtype=np.int64)
        sl = np.zeros((full + 1, inner))
        sh = np.zeros((full + 1, inner))
        acc_table = 0
        acc_low = 0.0
        acc_high = 0.0
        changed = 1  # the first inner point whose masks must be computed again
        for _ in range(n**k):
            for point in range(changed, k):
                for mask in range(1 << (point - 1), 1 << point):
                    for v in range(point):
                        if not (mask >> v) & 1:
                            continue
                        rest = mask ^ (1 << v)
                        if rest == 0:
                            d = abs(a[0] - a[v + 1])
                            dp[mask, v] = tw[0, v + 1, d]
                            sl[mask, v] = tl[0, v + 1, d]
                            sh[mask, v] = th[0, v + 1, d]
                            continue
                        best = big
                        best_low = 0.0
                        best_high = 0.0
                        for u in range(point):
                            if not (rest >> u) & 1:
                                continue
                            d = abs(a[u + 1] - a[v + 1])
                            value = dp[rest, u] + tw[u + 1, v + 1, d]
                            if value < best:
                                best = value
                                best_low = sl[rest, u] + tl[u + 1, v + 1, d]
                                best_high = sh[rest, u] + th[u + 1, v + 1, d]
                        dp[mask, v] = best
                        sl[mask, v] = best_low
                        sh[mask, v] = best_high
            for top in range(n):
                best = big
                best_low = 0.0
                best_high = 0.0
                for v in range(inner):
                    d = abs(a[v + 1] - top)
                    value = dp[full, v] + tw[v + 1, k, d]
                    if value < best:
                        best = value
                        best_low = sl[full, v] + tl[v + 1, k, d]
                        best_high = sh[full, v] + th[v + 1, k, d]
                acc_table += best
                acc_low += best_low
                acc_high += best_high
            position = k - 1
            while position >= 0:
                a[position] += 1
                if a[position] < n:
                    break
                a[position] = 0
                position -= 1
            changed = max(position, 1)
        out_table[index] = acc_table
        out_low[index] = acc_low
        out_high[index] = acc_high
    return out_table, out_low, out_high


def open_log(path, par, R):
    """The sums already in the log, and the log opened for more; a damaged last line is dropped."""
    with open(par["values"], "rb") as handle:
        head = f"rule {hashlib.sha256(handle.read()).hexdigest()} {R}"
    found = {}
    lines = [head]
    if os.path.exists(path):
        with open(path, encoding="ascii") as handle:
            lines = handle.read().split("\n")[:-1]
        if not lines or lines[0] != head:
            raise SystemExit("bracket: the log belongs to another computation")
        for line in lines[1:]:
            g, value, lower, upper = line.split()
            found[int(g)] = (int(value), float.fromhex(lower), float.fromhex(upper))
    with open(path, "w", encoding="ascii", newline="\n") as handle:
        handle.write("".join(line + "\n" for line in lines))
    return found, open(path, "a", encoding="ascii", newline="\n")  # noqa: SIM115


def rule_sums(par, R, keys, table, low, high, log_path):
    """The three sums of rule_value for every gap tuple, found in portions and kept in the log, if any."""
    k, m, n = par["k"], par["m"], par["n"]
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
    found, log = ({}, None) if log_path is None else open_log(log_path, par, R)
    for first in range(0, m**k, PORTION):
        last = min(first + PORTION, m**k)
        if all(g in found for g in range(first, last)):
            continue
        out_table, out_low, out_high = rule_value(k, n, table, rows, pair_index, low, high, first, last)
        for g in range(first, last):
            if g not in found:
                found[g] = (int(out_table[g - first]), float(out_low[g - first]), float(out_high[g - first]))
                if log is not None:
                    log.write(f"{g} {found[g][0]} {found[g][1].hex()} {found[g][2].hex()}\n")
        if log is not None:
            log.flush()
            os.fsync(log.fileno())
        print(f"  rule: {last} of {m**k} gap tuples", file=sys.stderr, flush=True)
    if log is not None:
        log.close()
    return [found[g] for g in range(m**k)]


def main(argv):
    argv = list(argv)
    log_path = None
    if "--log" in argv[:-1]:
        position = argv.index("--log")
        log_path = argv[position + 1]
        del argv[position : position + 2]
    arguments = [a for a in argv if not a.startswith("-")]
    if len(arguments) != 2 or any(a.startswith("-") and a != "--rule" for a in argv):
        raise SystemExit(__doc__)
    par = read_spec(arguments[0])
    R = int(arguments[1])
    k, m, n = par["k"], par["m"], par["n"]
    keys, table = read_table(par)
    start = time.time()
    low, high, mass = brackets(par, keys, R)
    scaled = table / F
    print(f"brackets on a mesh {R} times finer, {len(keys)} keys, {time.time() - start:.1f} s")
    # the counts and the verdict are written so that a number that is not a number fails the test
    print(f"entries with lower > upper : {int((~(low <= high)).sum())}")
    print(f"entries with upper > table : {int((~(high <= scaled)).sum())}")
    margin = (scaled - high) / scaled
    print(f"(table - upper)/table      : min {margin.min():.3e}, max {margin.max():.3e}")
    print(f"(upper - lower)/table      : max {((high - low) / scaled).max():.3e}")
    failed = not bool((low <= high).all() and (high <= scaled).all())
    if "--rule" in argv:
        stored = read_values(par["values"])["S"]
        if max(stored) >= 1 << 62:
            raise SystemExit("bracket: the cell sums are too large for 64-bit integers")
        start = time.time()
        sums = rule_sums(par, R, keys, table, low, high, log_path)
        different = sum(value != expected for (value, _, _), expected in zip(sums, stored, strict=True))
        prob = np.array([math.prod(mass[g // m**t % m] for t in range(k)) for g in range(m**k)])
        scale = par["hd"] / (n ** (k + 1) * k * par["hn"])
        value_table = float(prob @ np.array([value / F for value, _, _ in sums])) * scale
        value_low = float(prob @ np.array([lower for _, lower, _ in sums])) * scale
        value_high = float(prob @ np.array([upper for _, _, upper in sums])) * scale
        print(f"rule evaluated over all cells in {time.time() - start:.0f} s")
        print(f"cell sums that differ from the values file : {different}")
        print(f"table cost of the rule             : {value_table:.10f}")
        print(f"lower bracket of its true length   : {value_low:.10f}")
        print(f"upper bracket of its true length   : {value_high:.10f}")
        failed = failed or different > 0 or not value_low <= value_high <= value_table * (1 + 1e-12)
    print("FAILED" if failed else "PASSED")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
