#!/usr/bin/env python3
"""Tests of the parts of check_bound.py against slow, direct computations.

Each test compares a function of the checker with the definition it implements, evaluated with exact
rational arithmetic or with 60-digit decimals: the rounding must go upwards (downwards where a lower
bound is wanted) and must cost little.  The numpy routine for the cell sums and cell_sums, which between
them use the three identities of Section 7 of RECIPE.md, are compared on small blocks with a minimum over
all orders (with the real table) and with a routine that uses none of the identities (with random tables).
One test continues a run from its log of cell sums (--log).
The tests use small parameters and take a few seconds.

usage:  test_check_bound.py          (exit status 0 if all tests pass)
"""

import itertools
import math
import os
import random
import sys
import tempfile
from decimal import Decimal, getcontext
from fractions import Fraction

import check_bound as cb

getcontext().prec = 60
HERE = os.path.dirname(os.path.abspath(__file__))
TINY = os.path.join(HERE, "..", "data", "specs", "tiny.txt")
RELEASE = {"k": 7, "hn": 21, "hd": 10, "M": 128, "b": [0, 48, 112, 208], "n": 6, "nu": 64, "T": 16, "m": 4}
# coarse meshes, for which the bracket of exp(-1/M) is wide, and cells of one mesh interval
COARSE = [
    {"M": 2, "b": [0, 2, 6], "m": 3, "T": 4},
    {"M": 3, "b": [0, 1, 2, 4], "m": 4, "T": 4},
    {"M": 256, "b": [0, 1], "m": 2, "T": 1},
]


def exp_minus(i, M):
    """exp(-i / M) as a Decimal."""
    return (Decimal(-i) / Decimal(M)).exp()


def test_integer_helpers():
    rng = random.Random(1)
    for _ in range(2000):
        a, b = rng.randrange(10**40), rng.randrange(1, 10**20)
        q = cb.cdiv(a, b)
        assert (q - 1) * b < a <= q * b or (a == 0 and q == 0)
        u = cb.ceil_sqrt(a)
        assert u * u >= a and (u == 0 or (u - 1) * (u - 1) < a)
    assert [cb.ceil_sqrt(x) for x in (0, 1, 2, 4, 5, 9, 10)] == [0, 1, 2, 2, 3, 3, 4]
    assert (
        cb.decimal_up(1, 3, 4) == "0.3334"
        and cb.decimal_up(1, 4, 2) == "0.25"
        and cb.decimal_up(7, 2, 1) == "3.5"
    )


def test_exponential_bounds():
    for M in (2, 16, 128, 1024):
        rlo, rup = cb.exponential_bounds(M, 20 * M)
        # width of the bracket of exp(-1/M): the remainder of the series and a few units of rounding
        width = 3 + cb.Q // (M**12 * math.factorial(12))
        for i in range(0, 20 * M + 1, max(1, M // 8)):
            exact = Decimal(cb.Q) * exp_minus(i, M)
            assert rlo[i] <= exact <= rup[i]
            assert rup[i] - rlo[i] <= i * (width + 2)


def real_weights(par):
    """The weights w_c(i) of Lemmas 3.2 and 3.3 and the probabilities p_c, as Decimals."""
    M, b, m = par["M"], par["b"], par["m"]
    delta = Decimal(1) / M
    lam = 1 - (1 - exp_minus(1, M)) / delta
    mu = (1 - exp_minus(1, M)) / delta - exp_minus(1, M)

    def numerator(i, cells):
        return (lam * exp_minus(i, M) if i < cells else 0) + (mu * exp_minus(i - 1, M) if i >= 1 else 0)

    weights, masses = [], []
    for c in range(m - 1):
        cells = b[c + 1] - b[c]
        weights.append([numerator(i, cells) / (1 - exp_minus(cells, M)) for i in range(cells + 1)])
        masses.append(exp_minus(b[c], M) - exp_minus(b[c + 1], M))
    cells = par["T"] * M
    last = [numerator(i, cells) for i in range(cells + 1)]
    last[cells] += exp_minus(cells, M)
    weights.append(last)
    masses.append(exp_minus(b[-1], M))
    return weights, masses


def test_weights():
    """No weight and no mass is below its real value; for the meshes of the spec files they are close."""
    for par, slack in ((cb.read_spec(TINY), 4), (RELEASE, 4), *((par, 1024) for par in COARSE)):
        W, P, ET = cb.weights(par)
        weights, masses = real_weights(par)
        for c in range(par["m"]):
            assert abs(sum(weights[c]) - 1) < Decimal(10) ** -50  # the real weights sum to 1
            assert len(W[c]) == len(weights[c])
            for integer, real in zip(W[c], weights[c], strict=True):
                assert 0 <= integer - Decimal(cb.D) * real <= slack, (par, c, integer, real)
            assert 0 <= P[c] - Decimal(cb.D) * masses[c] <= slack
        assert 0 <= ET - Decimal(cb.F) * exp_minus(par["T"] * par["M"], par["M"]) <= 1


def test_keys_and_convolutions():
    for m, k in ((1, 2), (3, 3), (4, 5), (4, 7)):
        keys = cb.all_keys(m, k)
        assert len(keys) == math.comb(m + k, k) - 1 and keys == sorted(keys) and len(set(keys)) == len(keys)
    rng = random.Random(2)
    u = [rng.randrange(cb.D + 3) for _ in range(40)]
    v = [rng.randrange(cb.D + 3) for _ in range(17)]
    direct = [
        cb.cdiv(sum(u[i] * v[s - i] for i in range(len(u)) if 0 <= s - i < len(v)), cb.D)
        for s in range(len(u) + len(v) - 1)
    ]
    assert cb.convolve(u, v) == direct
    par = cb.read_spec(TINY)
    W, _, _ = cb.weights(par)
    V = cb.weight_vectors(par, W)
    weights, _ = real_weights(par)
    for key, vector in V.items():
        real = [Decimal(1)]
        for c, count in enumerate(key):
            for _ in range(count):
                real = [
                    sum(real[i] * weights[c][s - i] for i in range(len(real)) if 0 <= s - i < len(weights[c]))
                    for s in range(len(real) + len(weights[c]) - 1)
                ]
        assert len(vector) == len(real) == 1 + sum(n * (len(W[c]) - 1) for c, n in enumerate(key))
        for integer, value in zip(vector, real, strict=True):
            assert 0 <= integer - Decimal(cb.D) * value <= 64, (key, integer, value)


def test_table():
    """Every table entry is at least F times the real bound (3.2) of the paper, and close to it."""
    par = cb.read_spec(TINY)
    W, _, ET = cb.weights(par)
    table = cb.edge_table(par, cb.weight_vectors(par, W), ET)
    weights, _ = real_weights(par)
    M, n, nu = par["M"], par["n"], par["nu"]
    h2 = Fraction(par["hn"], par["hd"]) ** 2
    eta = [1 if s in (0, nu) else 2 for s in range(nu + 1)]
    for key in ((1, 0, 0), (0, 0, 1), (1, 1, 0), (0, 0, 2), (1, 1, 1), (0, 2, 1), (0, 0, 3)):
        real = [Decimal(1)]
        for c, count in enumerate(key):
            for _ in range(count):
                real = [
                    sum(real[i] * weights[c][s - i] for i in range(len(real)) if 0 <= s - i < len(weights[c]))
                    for s in range(len(real) + len(weights[c]) - 1)
                ]
        base = sum(count * par["b"][c] for c, count in enumerate(key))
        for d in range(n):
            value = Decimal(0)
            for s, weight in enumerate(real):
                x = Fraction(base + s, M)
                inner = Decimal(0)
                for i, j in itertools.product(range(nu + 1), repeat=2):
                    y = h2 * (d * nu + i - j) / (n * nu)
                    square = x * x + y * y
                    inner += (
                        eta[i] * eta[j] * (Decimal(square.numerator) / Decimal(square.denominator)).sqrt()
                    )
                value += weight * inner / (4 * nu * nu)
            value += key[-1] * exp_minus(par["T"] * M, M)
            excess = table[key][d] - Decimal(cb.F) * value
            assert 0 <= excess <= 64, (key, d, excess)  # the rounding of the weights adds up over s


def test_best_path():
    rng = random.Random(3)
    for k in range(2, 8):
        for _ in range(20):
            cost = {}
            for i, j in cb.pairs(k):
                cost[i, j] = cost[j, i] = rng.randrange(10**9)
            direct = min(
                sum(cost[a, b] for a, b in itertools.pairwise((0, *order, k)))
                for order in itertools.permutations(range(1, k))
            )
            assert cb.best_path(k, cost) == direct
    if cb.np is None:
        return
    for k in range(2, 8):  # the same with arrays of costs, as in cell_sums_numpy
        cost = {}
        for i, j in cb.pairs(k):
            cost[i, j] = cost[j, i] = cb.np.array(
                [rng.randrange(10**9) for _ in range(40)], dtype=cb.np.int64
            )
        direct = [
            min(
                sum(int(cost[a, b][t]) for a, b in itertools.pairwise((0, *order, k)))
                for order in itertools.permutations(range(1, k))
            )
            for t in range(40)
        ]
        assert cb.best_path(k, cost).tolist() == direct


def test_interior_paths():
    """The paths between interior points, and the cost of a block as a minimum over their two ends."""
    rng = random.Random(5)
    for k in range(2, 8):
        for _ in range(10):
            cost = {}
            for i, j in cb.pairs(k):
                cost[i, j] = cost[j, i] = rng.randrange(10**9)
            path = cb.interior_paths(k, cost)
            inner = range(1, k)
            assert set(path) == ({(1, 1)} if k == 2 else {(u, v) for u in inner for v in inner if u != v})
            for u, v in path:
                between = [i for i in inner if i not in (u, v)]
                direct = min(
                    sum(cost[a, b] for a, b in itertools.pairwise((u, *order, v) if k > 2 else (u,)))
                    for order in itertools.permutations(between)
                )
                assert path[u, v] == direct
            assert cb.best_path(k, cost) == min(cost[0, u] + path[u, v] + cost[v, k] for u, v in path)


def random_table(rng, k, m, n, top):
    """A table with random entries below top: no order and no triangle inequality, unlike the real one."""
    return {key: [rng.randrange(top) for _ in range(n)] for key in cb.all_keys(m, k)}


def gap_tuples(k, m):
    """The gap tuples in index order."""
    return [tuple(index // m**i % m for i in range(k)) for index in range(m**k)]


def backwards(index, k, m):
    """The index of the gap tuple read backwards."""
    return sum(c * m ** (k - 1 - i) for i, c in enumerate(gap_tuples(k, m)[index]))


def test_cell_sums_with_random_tables():
    """cell_sums_numpy and cell_sums agree with cell_sum_plain: k from 2 to 6, one and several gap cells,
    one height, even and odd numbers of heights, one and several heights looped over."""
    rng = random.Random(6)
    cases = [(2, 1, 1), (2, 3, 4), (2, 2, 5), (3, 1, 1), (3, 3, 2), (3, 2, 5), (4, 2, 1), (4, 1, 4)]
    cases += [(4, 2, 3), (4, 3, 2), (5, 1, 3), (5, 2, 2), (5, 2, 3), (6, 1, 2)]
    usual = cb.MAX_ARRAY
    for k, m, n in cases:
        par = {"k": k, "m": m, "n": n}
        table = random_table(rng, k, m, n, 1 << 40)
        tuples = gap_tuples(k, m)
        plain = {g: cb.cell_sum_plain(par, table, g) for g in tuples}
        # the identity Reversal in cell_sums, which needs no numpy
        assert cb.cell_sums(par, table, 1) == [plain[g] for g in tuples]
        if cb.np is None:
            continue
        groups = {}
        for g in tuples:
            groups.setdefault(g[1:-1], []).append(g)
        for limit in (usual, n * n, 1):  # with the smaller limits the heights of more points are looped over
            cb.MAX_ARRAY = limit
            for group in groups.values():
                rng.shuffle(group)
                assert cb.cell_sums_numpy(par, table, group) == [plain[g] for g in group]
                assert cb.cell_sums_numpy(par, table, group[:1]) == [plain[group[0]]]
        cb.MAX_ARRAY = usual


def test_cell_sums_near_the_bound():
    """Path costs just below 2^63 are added up without overflow; the bound of cell_sums stops larger ones."""
    rng = random.Random(7)
    for k, m, n in ((2, 1, 1), (2, 2, 2), (3, 1, 1), (3, 2, 3), (4, 1, 2)):
        par = {"k": k, "m": m, "n": n}
        top = ((1 << 63) - 1) // (k * n ** (k - 1))  # the largest entry that the bound allows
        table = random_table(rng, k, m, n, 1000)
        table = {key: [top - entry for entry in row] for key, row in table.items()}
        key = rng.choice(list(table))
        table[key][0] = top
        sums = cb.cell_sums(par, table, 1)
        assert n == 1 or max(sums) > 1 << 63  # a cell sum itself need not fit into 64 bits
        assert sums == [cb.cell_sum_plain(par, table, g) for g in gap_tuples(k, m)]
        table[key][0] = top + 1
        try:
            cb.cell_sums(par, table, 1)
        except cb.BadInputError:
            pass
        else:
            raise AssertionError("a table above the bound for 64-bit integers was accepted")


def test_cell_sums_for_longer_blocks():
    """The two ways of computing a cell sum agree with a direct minimum over all orders for k = 4 and 5."""
    for k in (4, 5):
        par = dict(cb.read_spec(TINY), k=k, n=2)
        W, _, ET = cb.weights(par)
        table = cb.edge_table(par, cb.weight_vectors(par, W), ET)
        rng = random.Random(4)
        for _ in range(6):
            g = tuple(rng.randrange(par["m"]) for _ in range(k))
            rows = cb.edge_rows(par, table, g)
            direct = 0
            for a in itertools.product(range(par["n"]), repeat=k + 1):
                direct += min(
                    sum(rows[i, j][abs(a[i] - a[j])] for i, j in itertools.pairwise((0, *order, k)))
                    for order in itertools.permutations(range(1, k))
                )
            assert cb.cell_sum_plain(par, table, g) == direct
            if cb.np is not None:
                assert cb.cell_sums_numpy(par, table, [g]) == [direct]


def test_cell_sums_and_total():
    par = cb.read_spec(TINY)
    W, P, ET = cb.weights(par)
    table = cb.edge_table(par, cb.weight_vectors(par, W), ET)
    k, m, n = par["k"], par["m"], par["n"]
    sums = []
    for index in range(m**k):
        g = tuple(index // m**i % m for i in range(k))
        rows = cb.edge_rows(par, table, g)
        direct = 0
        for a in itertools.product(range(n), repeat=k + 1):
            direct += min(
                sum(rows[i, j][abs(a[i] - a[j])] for i, j in itertools.pairwise((0, *order, k)))
                for order in itertools.permutations(range(1, k))
            )
        assert cb.cell_sum_plain(par, table, g) == direct
        if cb.np is not None:
            assert cb.cell_sums_numpy(par, table, [g]) == [direct]
        sums.append(direct)
    assert cb.cell_sums(par, table, 1) == sums
    total = cb.total_bound(par, P, sums)
    exact = sum(
        Fraction(math.prod(P[index // m**i % m] for i in range(k)), cb.D**k) * value
        for index, value in enumerate(sums)
    )
    assert 0 <= total - exact <= k + 1
    stored = cb.read_values(par["values"])
    assert stored["given"] == par["given"] and stored["S"] == sums and stored["total"] == total
    assert stored["P"] == P and cb.stored_table(par) == table and stored["ET"] == ET


def test_log_of_cell_sums():
    """A run continued from its log gives the same sums; the log of another computation is refused."""
    par = cb.read_spec(TINY)
    W, _, ET = cb.weights(par)
    table = cb.edge_table(par, cb.weight_vectors(par, W), ET)
    sums = cb.cell_sums(par, table, 1)
    with tempfile.TemporaryDirectory() as folder:
        path = os.path.join(folder, "sums.log")

        def read():
            with open(path, encoding="ascii", newline="") as handle:
                return handle.read()

        def write(text):
            with open(path, "w", encoding="ascii", newline="") as handle:
                handle.write(text)

        assert cb.cell_sums(par, table, 1, path) == sums
        complete = read()
        lines = complete.split("\n")
        head = next(number for number, line in enumerate(lines) if line.startswith("sum "))
        # the log holds the sums that were computed: for a gap tuple or for the tuple read backwards
        logged = [int(line.split()[1]) for line in lines[head:-1]]
        assert lines[head:-1] == [f"sum {index} {sums[index]}" for index in logged]
        both = [*logged, *(backwards(index, par["k"], par["m"]) for index in logged)]
        assert set(both) == set(range(len(sums))) and len(both) == len(sums) + par["m"] ** 2
        # an interrupted run: ten sums and the beginning of the next line
        write("\n".join(lines[: head + 10]) + "\n" + lines[head + 10][:-1])
        assert cb.cell_sums(par, table, 1, path) == sums and read() == complete
        # the sums in a log are not recomputed: a continued run is only as good as its log
        write("\n".join(lines[:head]) + f"\nsum 0 {sums[0] + 1}\n")
        assert cb.cell_sums(par, table, 1, path) == [sums[0] + 1, *sums[1:]]
        # and a sum in a log is also taken for the tuple read backwards, here (0, 0, 1) for (1, 0, 0)
        write("\n".join(lines[:head]) + f"\nsum 1 {sums[1] + 1}\n")
        changed = cb.cell_sums(par, table, 1, path)
        mirror = backwards(1, par["k"], par["m"])
        assert mirror != 1 and changed[1] == changed[mirror] == sums[1] + 1
        assert [value for index, value in enumerate(changed) if index not in (1, mirror)] == [
            value for index, value in enumerate(sums) if index not in (1, mirror)
        ]
        # two values for one sum, a sum that does not exist, another table, other parameters
        other_table = dict(table)
        key = next(iter(table))
        other_table[key] = [table[key][0] + 1, *table[key][1:]]
        for text, parameters, entries in (
            (complete + f"sum 3 {sums[3] + 1}\n", par, table),
            (complete + f"sum {len(sums)} 1\n", par, table),
            (complete, par, other_table),
            (complete, dict(par, T=par["T"] + 1), table),
        ):
            write(text)
            try:
                cb.cell_sums(parameters, entries, 1, path)
            except cb.BadInputError:
                pass
            else:
                raise AssertionError("a log that does not fit was continued")
        # a byte outside ASCII: malformed input, and the log is left as it is
        damaged = complete.encode("ascii") + b"sum \xc3\xa9 1\n"
        with open(path, "wb") as handle:
            handle.write(damaged)
        try:
            cb.cell_sums(par, table, 1, path)
        except cb.BadInputError:
            pass
        else:
            raise AssertionError("a log with a byte outside ASCII was continued")
        with open(path, "rb") as handle:
            assert handle.read() == damaged


def test_values_file_of_a_spec_file():
    """The values file is sought from the folder of the spec file as the given path names it.  The
    checker must not rewrite that path: after a symbolic link the system reads ".." otherwise than a
    rewriting of the text does."""
    spec = os.path.join(HERE, "..", "data", "specs", "..", "specs", "tiny.txt")
    assert cb.read_spec(spec)["values"] == os.path.join(os.path.dirname(spec), "..", "values", "tiny.txt")
    if os.name != "posix":
        return  # the rest needs the symbolic links of POSIX
    with open(TINY, encoding="ascii") as handle:
        lines = handle.read().split("\n")
    with tempfile.TemporaryDirectory() as folder:
        os.makedirs(os.path.join(folder, "real", "child"))
        try:
            os.symlink(os.path.join(folder, "real", "child"), os.path.join(folder, "link"))
        except OSError:
            print("no symbolic link could be made: the test of a spec path through a link was left out")
            return
        lines = ["values values.txt" if line.startswith("values ") else line for line in lines]
        with open(os.path.join(folder, "real", "spec.txt"), "w", encoding="ascii", newline="\n") as handle:
            handle.write("\n".join(lines))
        for place in ("real", "."):
            with open(os.path.join(folder, place, "values.txt"), "w", encoding="ascii") as handle:
                handle.write(place)
        # link/.. is the folder "real" for the system, and the top folder for a rewriting of the text
        par = cb.read_spec(os.path.join(folder, "link", "..", "spec.txt"))
        with open(par["values"], encoding="ascii") as handle:
            assert handle.read() == "real"


def main():
    tests = [value for name, value in sorted(globals().items()) if name.startswith("test_")]
    for test in tests:
        test()
        print(f"passed {test.__name__}")
    if cb.np is None:
        print("numpy was not found: the comparisons with the numpy routine were left out")
    print(f"all {len(tests)} tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
