#!/usr/bin/env python3
"""Draws the figure of the paper.

fig_strip.pdf    Three consecutive blocks of a strip for the largest k that has a spec file
                 data/specs/kK.txt (K from 5 to 9), with the strip height of that file: the points in
                 the order of their first coordinates, and the path chosen by the rule of the file.
                 The file names its k and h in the field "Subject" of its metadata, which
                 tools/paper_numbers.py compares with the k and h of that spec file (the caption
                 in the paper takes them from the same file).

Needs numpy, numba and matplotlib.

usage:  make_figures.py          (from any folder; the file is written next to this script)
"""

import os
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.join(HERE, "..", "..")
sys.path.insert(0, os.path.join(REPO, "controls"))
sys.path.insert(0, os.path.join(REPO, "checkers"))
from check_bound import read_spec  # noqa: E402
from simulate import choose, rule_tables  # noqa: E402

plt.rcParams.update(
    {
        "font.family": "serif",
        "mathtext.fontset": "cm",
        "font.size": 9,
        "axes.linewidth": 0.6,
        "pdf.fonttype": 42,
    }
)
STRIP_SEED = 11
STRIP_BLOCKS = 3


def save(figure, name, subject):
    figure.savefig(
        os.path.join(HERE, name),
        bbox_inches="tight",
        pad_inches=0.02,
        metadata={"CreationDate": None, "Subject": subject},
    )
    plt.close(figure)
    print(f"wrote {name}")


def strip_figure():
    specs = [os.path.join(REPO, "data", "specs", f"k{k}.txt") for k in range(5, 10)]
    par = read_spec([spec for spec in specs if os.path.exists(spec)][-1])
    k, m, n = par["k"], par["m"], par["n"]
    h = par["hn"] / par["hd"]
    table, rows, pair_index, bounds = rule_tables(par)
    rng = np.random.default_rng(STRIP_SEED)
    count = k * STRIP_BLOCKS + 1
    xs = np.concatenate(([0.0], np.cumsum(rng.exponential(1 / h, count - 1))))
    ys = rng.random(count) * h
    cost = np.zeros((k + 1, k + 1), dtype=np.int64)
    rest = np.zeros((1 << (k - 1), k - 1), dtype=np.int64)
    order = np.zeros(k + 1, dtype=np.int64)

    figure, axis = plt.subplots(figsize=(6.2, 1.9))
    axis.plot(xs, ys, color="0.72", linewidth=0.8, linestyle=(0, (3, 2)), zorder=1)
    for block in range(STRIP_BLOCKS):
        first = block * k
        gaps = h * np.diff(xs[first : first + k + 1])
        heights = ys[first : first + k + 1] / h
        choose(k, m, n, gaps, heights, table, rows, pair_index, bounds, cost, rest, order)
        axis.plot(xs[first + order], ys[first + order], color="black", linewidth=1.0, zorder=2)
    ends = np.arange(0, count, k)
    inner = np.setdiff1d(np.arange(count), ends)
    axis.scatter(xs[inner], ys[inner], s=10, color="black", zorder=3, clip_on=False)
    axis.scatter(
        xs[ends], ys[ends], s=26, facecolor="white", edgecolor="black", linewidth=1.0, zorder=3, clip_on=False
    )
    margin = 0.25
    axis.set_xlim(-margin, xs[-1] + margin)
    axis.set_ylim(0, h)
    axis.set_aspect("equal")
    axis.set_xticks([])
    axis.set_yticks([0, h])
    axis.set_yticklabels(["$0$", "$h$"])
    for side in ("left", "right"):
        axis.spines[side].set_visible(False)
    axis.tick_params(length=0)
    save(figure, "fig_strip.pdf", f"k = {k}, h = {par['hn']}/{par['hd']}")


if __name__ == "__main__":
    strip_figure()
