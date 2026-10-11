#!/usr/bin/env python3
"""The strip bound of Beardwood, Halton and Hammersley by numerical integration (a control, not a proof).

For strips of height h the bound is the expected distance between consecutive points of a strip,

    2 * integral over x > 0 and 0 < y < h of  sqrt(x^2 + y^2) exp(-h x) (1 - y / h),

which is the case k = 1 of Theorem 2.2 of the paper.  The value for h = 26/15 is compared in the README.md
of this folder with the output of the checkers for data/specs/bhh.txt; the value for h = sqrt(3) is the
constant 0.92116... of the literature.  The last line printed gives the height at which the bound is least,
which is not sqrt(3), and the bound there.

Needs mpmath.

usage:  strip_integral.py
"""

import mpmath as mp


def strip_bound(h):
    def inner(x):
        return mp.quad(lambda y: mp.sqrt(x * x + y * y) * (1 - y / h), [0, h])

    return 2 * mp.quad(lambda x: mp.exp(-h * x) * inner(x), [0, 1, 4, 16, mp.inf])


def main():
    mp.mp.dps = 30
    for name, h in (("26/15", mp.mpf(26) / 15), ("sqrt(3)", mp.sqrt(3))):
        print(f"h = {name}: {mp.nstr(strip_bound(h), 12)}")
    mp.mp.dps = 20
    best = mp.findroot(lambda h: mp.diff(strip_bound, h), mp.mpf("1.734"))  # where the derivative vanishes
    print(f"least at h = {mp.nstr(best, 5)}: {mp.nstr(strip_bound(best), 12)}")


if __name__ == "__main__":
    main()
