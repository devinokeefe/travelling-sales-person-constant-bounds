#!/usr/bin/env python3
"""The conditional expected lengths of the segments by numerical integration (a control, not part of
the proof).

For a key kappa and a difference d of the height cells, Proposition 3.5 of the paper bounds

    E sqrt(X^2 + (c (d + U - U'))^2),

where X is the sum of the gaps of the segment, each of them an exponential variable conditioned on its
gap cell, c = h^2 / n is the height of a height cell in the scaled coordinates, U and U' are uniform on
[0, 1], and all of these are independent.  The gaps have the joint density exp(-(x_1 + ... + x_r)) / p on
the product of their cells, where p is the product of the probabilities of the cells.  So X has the density

    exp(-x) V(x) / p,

where V(x) is the volume of the part of that product in which the gaps add up to x.  V is the convolution
of the indicator functions of the cells, a piecewise polynomial, which the script finds in rational
arithmetic.  The mean over U and U' has a closed form, and the integral over x is taken by Gauss-Legendre
quadrature on each piece.

The script evaluates this integral for every table entry.  The entry Tab / F of the values file must not
be below it, and the two sides of the bracket of controls/bracket.py must enclose it.  The integral uses
none of the lemmas of Section 3 of the paper, so the comparison would show an inequality of that section
that had been taken in the wrong direction.

Two checks of the integration itself: the density of every key must have total mass 1, and for the keys
with one gap or two gaps the integral is evaluated a second time, as a double integral over x and
U - U' with mpmath, without the piecewise polynomials and without the closed form.

Rounding errors are not controlled.  Needs mpmath and what bracket.py needs.

usage:  segment_integral.py SPEC
"""

import bisect
import math
import os
import sys
import time
from fractions import Fraction

import mpmath as mp
import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkers"))
from bracket import brackets  # noqa: E402
from check_bound import F, all_keys, read_spec, stored_table  # noqa: E402

FINER = 2  # the bracket is taken on a mesh this many times finer, as in the records of bracket.py
NODES = 32  # nodes of the quadrature on each piece
TAIL = 64  # the integral over x ends this far beyond the last point at which V changes its form
HALVINGS = 40  # halvings of a piece that begins at x = 0, where the mean over the heights is not smooth
MASS_ERROR = 1e-12  # allowed error of the total mass of a density
AGREEMENT = 1e-12  # allowed relative difference between the two evaluations of an integral


# ------------------------------------------------------------------------- piecewise polynomials
# A piecewise polynomial is a pair (points, pieces): it vanishes to the left of points[0], is pieces[i]
# between points[i] and points[i + 1], and pieces[-1] to the right of points[-1].  The points are integers,
# gaps in units of 1/M; a polynomial is the list of its coefficients, lowest first, as fractions.
def value(poly, u):
    result = Fraction(0)
    for coefficient in reversed(poly):
        result = result * u + coefficient
    return result


def shifted(poly, a):
    """The polynomial u -> poly(u + a)."""
    out = [Fraction(0)] * len(poly)
    for j, coefficient in enumerate(poly):
        for i in range(j + 1):
            out[i] += coefficient * math.comb(j, i) * Fraction(a) ** (j - i)
    return out


def difference(p, q):
    size = max(len(p), len(q))
    p, q = p + [Fraction(0)] * (size - len(p)), q + [Fraction(0)] * (size - len(q))
    return [x - y for x, y in zip(p, q, strict=True)]


def piece_at(points, pieces, u):
    """The polynomial that is in force at u, which is not one of the points."""
    return pieces[bisect.bisect_right(points, u) - 1] if u > points[0] else []


def primitive(points, pieces):
    """The pieces of the integral, from the far left up to u, of a piecewise polynomial."""
    out, start = [], Fraction(0)
    for i, poly in enumerate(pieces):
        integral = [Fraction(0)] + [coefficient / (j + 1) for j, coefficient in enumerate(poly)]
        integral[0] = start - value(integral, points[i])
        out.append(integral)
        if i + 1 < len(points):
            start = value(integral, points[i + 1])
    return out


def cell_indicator(low, high):
    """The indicator function of a gap cell; high is None for the last cell, which has no upper end."""
    one = [Fraction(1)]
    return ([low], [one]) if high is None else ([low, high], [one, []])


def with_gap(points, pieces, low, high):
    """The convolution of a piecewise polynomial with the indicator function of a gap cell: its
    integral over [u - high, u - low]."""
    total = primitive(points, pieces)
    ends = [low] if high is None else [low, high]
    new_points = sorted({point + end for point in points for end in ends})
    new_pieces = []
    for i, left in enumerate(new_points):
        inside = Fraction(left + new_points[i + 1], 2) if i + 1 < len(new_points) else left + 1
        poly = shifted(piece_at(points, total, inside - low), -low)
        if high is not None:
            poly = difference(poly, shifted(piece_at(points, total, inside - high), -high))
        new_pieces.append(poly)
    return new_points, new_pieces


def volume(key, cells, cache):
    """V for a key, in the variable u = M x: the convolution of the indicators of its gap cells."""
    if key not in cache:
        c = max(i for i, count in enumerate(key) if count)
        shorter = key[:c] + (key[c] - 1,) + key[c + 1 :]
        cache[key] = (
            cell_indicator(*cells[c])
            if sum(shorter) == 0
            else with_gap(*volume(shorter, cells, cache), *cells[c])
        )
    return cache[key]


# ------------------------------------------------------------------------- the integral
def height_mean(x, d, c):
    """The mean of sqrt(x^2 + (c (d + U - U'))^2) over U and U', for an array of x > 0.

    With y = c (d + t) and the density 1 - |t| of t = U - U' this is the integral of
    sqrt(x^2 + y^2) (1 - |y / c - d|) / c over c (d - 1) < y < c (d + 1)."""

    def first(y):  # a primitive of sqrt(x^2 + y^2)
        return (y * np.hypot(x, y) + x * x * np.arcsinh(y / x)) / 2

    def second(y):  # a primitive of y sqrt(x^2 + y^2)
        return np.hypot(x, y) ** 3 / 3

    below, middle, above = c * (d - 1), c * d, c * (d + 1)
    rising = (1 - d) * (first(middle) - first(below)) + (second(middle) - second(below)) / c
    falling = (1 + d) * (first(above) - first(middle)) - (second(above) - second(middle)) / c
    return (rising + falling) / c


def quadrature(points, pieces, M):
    """Nodes u, with weights, and the values of the piecewise polynomial at them."""
    xi, omega = np.polynomial.legendre.leggauss(NODES)
    xi, omega = (xi + 1) / 2, omega / 2
    stretches = [(points[i], points[i + 1], pieces[i]) for i in range(len(points) - 1)]
    if any(pieces[-1]):
        stretches.append((points[-1], points[-1] + TAIL * M, pieces[-1]))
    nodes, weights, values = [], [], []
    for left, right, poly in stretches:
        parts = -(-(right - left) // M)
        cuts = [Fraction(left) + Fraction(right - left, parts) * j for j in range(parts + 1)]
        if left == 0:
            cuts[1:1] = [cuts[1] / 2**j for j in range(HALVINGS, 0, -1)]
        for start, end in zip(cuts[:-1], cuts[1:], strict=True):
            width = end - start
            local = [float(coefficient * width**j) for j, coefficient in enumerate(shifted(poly, start))]
            nodes.append(float(start) + float(width) * xi)
            weights.append(float(width) * omega)
            values.append(np.polynomial.polynomial.polyval(xi, local))
    return np.concatenate(nodes), np.concatenate(weights), np.concatenate(values)


def cell_mass(low, high, M):
    """The probability that a gap lies in a gap cell."""
    return math.exp(-low / M) * (1.0 if high is None else -math.expm1(-(high - low) / M))


def expected_lengths(key, cells, cache, par, c):
    """The total mass of the density of X, which is 1, and the integral for d = 0, ..., n - 1."""
    M = par["M"]
    nodes, weights, values = quadrature(*volume(key, cells, cache), M)
    mass = math.prod(cell_mass(*cells[i], M) ** count for i, count in enumerate(key))
    density = weights * np.exp(-nodes / M) * values / (M ** sum(key) * mass)
    return float(density.sum()), [float(density @ height_mean(nodes / M, d, c)) for d in range(par["n"])]


def double_integral(key, cells, d, par):
    """The same integral for a key with one gap or two gaps, as a double integral with mpmath."""
    M = par["M"]
    c = mp.mpf(par["hn"]) ** 2 / (mp.mpf(par["hd"]) ** 2 * par["n"])
    ends = [(mp.mpf(low) / M, mp.inf if high is None else mp.mpf(high) / M) for low, high in cells]
    of_key = [ends[i] for i, count in enumerate(key) for _ in range(count)]
    mass = math.prod(mp.exp(-low) - mp.exp(-high) for low, high in of_key)
    if len(of_key) == 1:
        points = list(of_key[0])

        def density(x):
            return mp.exp(-x) / mass
    else:
        (low1, high1), (low2, high2) = of_key
        points = sorted({low1 + low2, low1 + high2, high1 + low2, high1 + high2})

        def density(x):
            return mp.exp(-x) * max(min(high1, x - low2) - max(low1, x - high2), 0) / mass

    if points[-1] == mp.inf:
        points = [*points[:-1], *(points[-2] + step for step in (2, 8, 32)), mp.inf]

    def over_heights(x):
        return mp.quad(lambda t: (1 - abs(t)) * mp.sqrt(x * x + (c * (d + t)) ** 2), [-1, 0, 1])

    return mp.quad(lambda x: density(x) * over_heights(x), points)


def main(argv):
    if len(argv) != 1 or argv[0].startswith("-"):
        raise SystemExit(__doc__)
    mp.mp.dps = 20
    par = read_spec(argv[0])
    m, n, b = par["m"], par["n"], par["b"]
    c = (par["hn"] / par["hd"]) ** 2 / n
    table = stored_table(par)
    keys = all_keys(m, par["k"])
    low, high, _ = brackets(par, keys, FINER)
    cells = [(b[i], b[i + 1] if i + 1 < m else None) for i in range(m)]
    start = time.time()
    cache = {}
    integrals = np.zeros((len(keys), n))
    # every test below is written so that a number that is not a number fails it; the largest element
    # of an array of numpy is not a number if one of the elements is not
    masses = np.zeros(len(keys))
    for row, key in enumerate(keys):
        masses[row], integrals[row] = expected_lengths(key, cells, cache, par, c)
    mass_error = float(np.abs(masses - 1).max())
    print(
        f"integrals for {len(keys)} keys and {n} differences of the height cells, {time.time() - start:.0f} s"
    )
    print(f"total mass of a density, largest error  : {mass_error:.1e}")
    short = [(row, key) for row, key in enumerate(keys) if sum(key) <= 2]
    start = time.time()
    second = np.array([[float(double_integral(key, cells, d, par)) for d in range(n)] for _, key in short])
    disagreement = float(np.abs(integrals[[row for row, _ in short]] / second - 1).max())
    print(f"double integrals for the {len(short)} keys with one gap or two gaps, {time.time() - start:.0f} s")
    print(f"largest relative difference between them: {disagreement:.1e}")
    scaled = np.array([table[key] for key in keys]) / F
    margin = (scaled - integrals) / scaled
    below = int((~(integrals <= scaled)).sum())
    outside = int((~((low <= integrals) & (integrals <= high))).sum())
    print(f"entries below the integral              : {below}")
    print(f"(table - integral)/table                : min {margin.min():.3e}, max {margin.max():.3e}")
    print(f"integrals outside the bracket           : {outside}")
    failed = not (mass_error <= MASS_ERROR and disagreement <= AGREEMENT) or below > 0 or outside > 0
    print("FAILED" if failed else "PASSED")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
