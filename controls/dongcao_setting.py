#!/usr/bin/env python3
"""The setting of Dong and Cao (arXiv:2610.02809, Section 4.2), estimated by simulation (not a proof).

Their deterministic bound for blocks of six points (five gaps) is the average, over N_g^5 N_y^6 equally
likely cells, of min_pi B_pi(sigma) / 5, where B_pi adds the square roots of the conditional second moments
of the edge lengths (their equations (33) to (39)).  Since the cells are equally likely, drawing a block
and taking its cell draws a cell uniformly, so the average can be estimated without visiting all 1.6e13
cells.

For each sampled block this script computes
  (1) min_pi B_pi(sigma) / 5              their bound for the cell;
  (2) the length of the path of their rule (the order that minimises B_pi) / 5;
  (3) the length of the shortest path / 5.
The mean of (1) should reproduce their 0.8810, the mean of (2) is the true value of their rule, and the
mean of (3) is the best value any rule can reach with blocks of five gaps and strip height H.  The script
also prints the mean of (2) less (3) with its own standard error: the two come from the same blocks, so
their difference is known more exactly than either of them.

With the default seed the random numbers are those that "simulate.py SPEC blocks" draws with its default
seed for data/specs/k5.txt (k = 5, h = 2), in the same order and in batches of the same size.  The blocks
of this script are therefore the first blocks of that sample, reduced by the factor 2, and the two samples
are not independent: the blocks of runs/dongcao_setting.txt are the first of those of runs/blocks_k5.txt.

Needs numpy and numba.

usage:  dongcao_setting.py [SAMPLES] [SEED]
"""

import itertools
import math
import sys
import time

import numpy as np
from numba import njit, prange

K = 5
H = 2.0
N_G = 12
N_Y = 20


def gap_moments():
    """Boundaries q_a and the conditional first and second moments of a gap in each cell (their (33)-(35))."""
    q = [math.log(N_G / (N_G - a)) / H for a in range(N_G)]

    def phi(x):
        return x * x + 2 * x / H + 2 / H**2

    first, second = [], []
    for a in range(N_G - 1):
        first.append((N_G - a) * q[a] - (N_G - a - 1) * q[a + 1] + 1 / H)
        second.append((N_G - a) * phi(q[a]) - (N_G - a - 1) * phi(q[a + 1]))
    first.append(q[-1] + 1 / H)
    second.append(phi(q[-1]))
    return np.array(q), np.array(first), np.array(second)


@njit(parallel=True, cache=True)
def sample(gaps, heights, q, first, second, orders):
    count = gaps.shape[0]
    bound = np.zeros(count)
    rule = np.zeros(count)
    shortest = np.zeros(count)
    for s in prange(count):
        cell_g = np.zeros(K, dtype=np.int64)
        cell_y = np.zeros(K + 1, dtype=np.int64)
        x = np.zeros(K + 1)
        for i in range(K):
            x[i + 1] = x[i] + gaps[s, i]
            for a in range(N_G):
                if gaps[s, i] >= q[a]:
                    cell_g[i] = a
        for i in range(K + 1):
            cell_y[i] = min(int(N_Y * heights[s, i] / H), N_Y - 1)
        moment = np.zeros((K + 1, K + 1))
        dist = np.zeros((K + 1, K + 1))
        for r in range(K + 1):
            for t in range(r + 1, K + 1):
                total = 0.0
                for i in range(r, t):
                    total += second[cell_g[i]]
                    for j in range(i + 1, t):
                        total += 2 * first[cell_g[i]] * first[cell_g[j]]
                total += (H / N_Y) ** 2 * ((cell_y[t] - cell_y[r]) ** 2 + 1 / 6)
                moment[r, t] = moment[t, r] = math.sqrt(total)
                d = math.sqrt((x[r] - x[t]) ** 2 + (heights[s, r] - heights[s, t]) ** 2)
                dist[r, t] = dist[t, r] = d
        best_bound = 1e300
        best_true = 1e300
        chosen = 0.0
        for p in range(orders.shape[0]):
            b = 0.0
            d = 0.0
            for e in range(K):
                b += moment[orders[p, e], orders[p, e + 1]]
                d += dist[orders[p, e], orders[p, e + 1]]
            if b < best_bound:
                best_bound = b
                chosen = d
            best_true = min(best_true, d)
        bound[s] = best_bound / K
        rule[s] = chosen / K
        shortest[s] = best_true / K
    return bound, rule, shortest


def main(argv):
    samples = int(argv[0]) if argv else 4_000_000
    seed = int(argv[1]) if len(argv) > 1 else 20261009
    q, first, second = gap_moments()
    orders = np.array([(0, *p, K) for p in itertools.permutations(range(1, K))], dtype=np.int64)
    rng = np.random.default_rng(seed)
    sums = np.zeros(3)
    squares = np.zeros(3)
    loss_sum = loss_square = 0.0  # of the rule less the shortest path, block by block
    count = 0
    start = time.time()
    while count < samples:
        batch = min(500_000, samples - count)
        values = sample(
            rng.exponential(1 / H, size=(batch, K)), rng.random((batch, K + 1)) * H, q, first, second, orders
        )
        for i, value in enumerate(values):
            sums[i] += value.sum()
            squares[i] += (value**2).sum()
        loss = values[1] - values[2]
        loss_sum += loss.sum()
        loss_square += (loss**2).sum()
        count += batch
    mean = sums / count
    se = np.sqrt((squares / count - mean**2) / count)
    loss_mean = loss_sum / count
    loss_se = math.sqrt((loss_square / count - loss_mean**2) / count)
    seconds = time.time() - start
    print(
        f"blocks {count}, seed {seed}, {seconds:.0f} s  (k = 5, H = 2, {N_G} gap cells, {N_Y} height cells)"
    )
    print(f"mean of their cell bound       {mean[0]:.6f} +/- {se[0]:.6f}   (published: 0.8810)")
    print(f"true value of their rule       {mean[1]:.6f} +/- {se[1]:.6f}")
    print(f"shortest path                  {mean[2]:.6f} +/- {se[2]:.6f}   (their sample mean: 0.874256)")
    print(f"rule less shortest path        {loss_mean:.6f} +/- {loss_se:.6f}   (in the same blocks)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
