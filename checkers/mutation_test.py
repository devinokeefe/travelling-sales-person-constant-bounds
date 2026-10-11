#!/usr/bin/env python3
"""Mutation tests: deliberately wrong versions of the Python checker must be detected.

Each mutant differs from check_bound.py in one place: a rounding goes the wrong way, a lower bound is
used where an upper bound is needed, a term of the bound is dropped, the final test is reversed, a
test of the input or of a log of cell sums is left out, a printed line is changed, or one of the three
identities for the cell sums (reversal, reflection, shared paths: Section 7 of RECIPE.md) is applied
wrongly.  For every mutant this script runs, in a temporary folder,

  tests    test_check_bound.py, which compares the parts of the checker with their definitions;
  tiny     the mutant on data/specs/tiny.txt: it must fail to reproduce the stored values, or print
           other lines than the unmodified checker does;
  rounding the same with data/specs/rounding.txt, parameters for which the last digits of the
           bounds for the exponentials reach the stored cell masses;
  table    the masses and the table of the mutant for the parameters of data/specs/k5.txt, compared
           with the stored values of k = 5 (no cell sums, a few seconds);
  inputs   the mutant on the test inputs of data/tests/ (make_tests.py), where every exit
           status must be the expected one.

A mutant is detected if at least one of the five fails.  The script prints one line for each mutant and
ends with status 0 if all mutants are detected.  The unmodified checker is run first and must pass all five.

One change of this kind is left out because no test of outputs can detect it: if the inner of the two
divisions for the weights of a bounded cell (Section 3 of RECIPE.md) is rounded down, no weight changes
for any parameters that we tried.  The recipe rounds it up because the proof needs an upper bound at
every step, not because the result depends on it.

usage:  mutation_test.py          (needs numpy and data/tests/; takes about twenty minutes)
"""

import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")
WORKERS = 4  # test inputs run at the same time
PRINTED = {}  # what the unmodified checker prints for tiny and rounding (set by the first call of detectors)

# (description, text in check_bound.py, replacement); the text must occur exactly once
MUTANTS = [
    (
        "series for exp(-1/M): both roundings reversed",
        "lo, up = Q - cdiv(up, M * j), Q - lo // (M * j)",
        "lo, up = Q - up // (M * j), Q - cdiv(lo, M * j)",
    ),
    ("series for exp(-1/M): upper and lower bound exchanged", "r1lo, r1up = lo, up", "r1lo, r1up = up, lo"),
    (
        "powers of exp(-1/M): upper bounds rounded down",
        "rup.append(cdiv(rup[-1] * r1up, Q))",
        "rup.append(rup[-1] * r1up // Q)",
    ),
    (
        "powers of exp(-1/M): lower bounds rounded up",
        "rlo.append(rlo[-1] * r1lo // Q)",
        "rlo.append(cdiv(rlo[-1] * r1lo, Q))",
    ),
    (
        "lambda from the lower bound of exp(-1/M)",
        "c_lambda = Q - M * (Q - rup[1])",
        "c_lambda = Q - M * (Q - rlo[1])",
    ),
    (
        "mu from the upper bound of exp(-1/M)",
        "c_mu = M * (Q - rlo[1]) - rlo[1]",
        "c_mu = M * (Q - rup[1]) - rup[1]",
    ),
    (
        "lambda and mu exchanged (mass moved to the wrong end of each mesh interval)",
        "return (rup[i] * c_lambda if i < cells else 0) + (rup[i - 1] * c_mu if i >= 1 else 0)",
        "return (rup[i] * c_mu if i < cells else 0) + (rup[i - 1] * c_lambda if i >= 1 else 0)",
    ),
    (
        "weights of a bounded cell: outer division rounded down",
        "W.append([cdiv(cdiv(numerator(i, cells), 1 << 14), qlo) for i in range(cells + 1)])",
        "W.append([cdiv(numerator(i, cells), 1 << 14) // qlo for i in range(cells + 1)])",
    ),
    (
        "weights of a bounded cell: divisor is an upper bound of the probability of the cell",
        "qlo = Q - rup[cells]",
        "qlo = Q - rlo[cells]",
    ),
    (
        "weights of the last cell rounded down",
        "last = [cdiv(numerator(i, n_tail), 1 << 76) for i in range(n_tail + 1)]",
        "last = [numerator(i, n_tail) >> 76 for i in range(n_tail + 1)]",
    ),
    (
        "the atom at the truncation point left out",
        "last[n_tail] += cdiv(rup[n_tail], 1 << 14)",
        "last[n_tail] += 0",
    ),
    (
        "masses of the bounded cells from the wrong bounds",
        "P = [cdiv(rup[b[c]] - rlo[b[c + 1]], 1 << 14) for c in range(m - 1)]",
        "P = [(rlo[b[c]] - rup[b[c + 1]]) >> 14 for c in range(m - 1)]",
    ),
    (
        "mass of the last cell rounded down",
        "P.append(cdiv(rup[b[-1]], 1 << 14))",
        "P.append(rlo[b[-1]] >> 14)",
    ),
    ("tail term rounded down", "ET = cdiv(rup[n_tail], 1 << 30)", "ET = rlo[n_tail] >> 30"),
    ("tail term left out of the table", "tail = key[-1] * ET", "tail = 0"),
    (
        "convolution rounded down",
        'return [cdiv(int.from_bytes(raw[16 * s : 16 * s + 16], "little"), D) for s in range(length)]',
        'return [int.from_bytes(raw[16 * s : 16 * s + 16], "little") // D for s in range(length)]',
    ),
    ("square root rounded down", "return u if u * u == a else u + 1", "return u"),
    (
        "distance rounded down",
        "dist = [cdiv(ceil_sqrt((aj2 + (gamma * tau) ** 2) * F * F), scale) for tau in range(n * nu + 1)]",
        "dist = [ceil_sqrt((aj2 + (gamma * tau) ** 2) * F * F) // scale for tau in range(n * nu + 1)]",
    ),
    (
        "height weights of the midpoint rule in place of the chord weights",
        "e = [1 if i in (0, nu) else 2 for i in range(nu + 1)]",
        "e = [0 if i in (0, nu) else 2 for i in range(nu + 1)]",
    ),
    (
        "average over the heights rounded down",
        "G[d][j] = cdiv(total, 4 * nu * nu)",
        "G[d][j] = total // (4 * nu * nu)",
    ),
    (
        "table rounded down",
        "cdiv(sum(x * y for x, y in zip(vector, G[d][base : base + len(vector)], strict=True)), D) + tail",
        "sum(x * y for x, y in zip(vector, G[d][base : base + len(vector)], strict=True)) // D + tail",
    ),
    (
        "offset of a key left out of the table",
        "base = sum(count * b[c] for c, count in enumerate(key))",
        "base = 0",
    ),
    ("shortest path: last segment left out", 'dp["end", v] = here + cost[v + 1, k]', 'dp["end", v] = here'),
    ("shortest path: maximum in place of minimum at the end", "    return min(ends)", "    return max(ends)"),
    (
        "shortest path: maximum in place of minimum at the end (numpy)",
        "        return np.minimum.reduce(ends)",
        "        return np.maximum.reduce(ends)",
    ),
    (
        "shortest path: maximum in place of minimum within the dynamic programme",
        "                dp[target] = min(dp[target], candidate)",
        "                dp[target] = max(dp[target], candidate)",
    ),
    (
        "shortest path: maximum in place of minimum within the dynamic programme (numpy)",
        "                    np.minimum(dp[target], candidate, out=dp[target])",
        "                    np.maximum(dp[target], candidate, out=dp[target])",
    ),
    # the numpy routine for the cell sums and the three identities of Section 7
    (
        "paths between interior points: the block from u does not end at v",
        "order = [u, *(i for i in inner if i not in (u, v)), v]",
        "order = [u, v, *(i for i in inner if i not in (u, v))]",
    ),
    (
        "paths between interior points: for three gaps the edge from 1 to 2 left out",
        "if k > 3 else cost[u, v]",
        "if k > 3 else 0 * cost[u, v]",
    ),
    (
        "cell sums: maximum in place of minimum over the ends of the interior path",
        "        np.minimum(best, other, out=best)",
        "        np.maximum(best, other, out=best)",
    ),
    (
        "cell sums: first edge left out",
        "least(start[u] + path[u, v] for u in inner if (u, v) in path)",
        "least(0 * start[u] + path[u, v] for u in inner if (u, v) in path)",
    ),
    (
        "cell sums: path between the interior points left out",
        "least(start[u] + path[u, v] for u in inner if (u, v) in path)",
        "least(start[u] + 0 * path[u, v] for u in inner if (u, v) in path)",
    ),
    (
        "cell sums: last edge left out",
        "before[v] + rows[g][v, k][np.abs(heights[v] - a_last)]",
        "before[v] + 0 * rows[g][v, k][np.abs(heights[v] - a_last)]",
    ),
    (
        "cell sums: a height of the second interior point left out when it is looped over",
        "*[range(n)] * (looped - 1)",
        "*[range(1, n)] * (looped - 1)",
    ),
    (
        "cell sums: the sums of the arrays added up with 64-bit integers",
        "weight * int(least(ends).sum())",
        "weight * least(ends).sum()",
    ),
    (
        "bound for the 64-bit integers: 2^64 in place of 2^63",
        "n ** (k - 1) >= 1 << 63:",
        "n ** (k - 1) >= 1 << 64:",
    ),
    (
        "bound for the 64-bit integers: the number of edges of a path left out",
        "if k * max(max(row) for row in table.values()) * n ** (k - 1) >= 1 << 63:",
        "if max(max(row) for row in table.values()) * n ** (k - 1) >= 1 << 63:",
    ),
    (
        "reflection: the two halves of the heights counted once",
        "weight = 1 if 2 * fixed[0] == n - 1 else 2",
        "weight = 1",
    ),
    (
        "reflection: the middle height counted twice when the number of heights is odd",
        "weight = 1 if 2 * fixed[0] == n - 1 else 2",
        "weight = 2",
    ),
    (
        "reflection: the middle height left out when the number of heights is odd",
        "range((n + 1) // 2)",
        "range(n // 2)",
    ),
    (
        "shared paths: the edges from point 0 taken from a gap tuple with another g_1",
        "rows[members[0]][0, u]",
        "rows[tuples[0]][0, u]",
    ),
    (
        "shared paths: the edges to point k taken from a gap tuple with another g_k",
        "rows[g][v, k]",
        "rows[members[0]][v, k]",
    ),
    (
        "shared paths: a job holds gap tuples that differ in g_2",
        "groups.setdefault(index // m % m ** (k - 2), [])",
        "groups.setdefault(index // m**2 % m ** (k - 2), [])",
    ),
    (
        "reversal: the gap tuple rotated, not read backwards",
        "enumerate(reversed(g))",
        "enumerate(g[1:] + g[:1])",
    ),
    (
        "reversal: the two end gaps exchanged, the gaps between them not reversed",
        "enumerate(reversed(g))",
        "enumerate([g[-1], *g[1:-1], g[0]])",
    ),
    (
        "reversal: the gap tuples that read the same backwards are not computed",
        "i % front <= backwards[i] % front",
        "i % front < backwards[i] % front",
    ),
    (
        "reversal: a sum in a log is not copied to the tuple read backwards",
        "        done.setdefault(backwards[index], value)",
        "        pass",
    ),
    (
        "total rounded down",
        "cdiv(sum(P[c] * level[i + c * (len(level) // m)] for c in range(m)), D)",
        "sum(P[c] * level[i + c * (len(level) // m)] for c in range(m)) // D",
    ),
    (
        "final test reversed",
        'accepted = numerator * par["theta_d"] <= par["theta_n"] * denominator',
        'accepted = numerator * par["theta_d"] >= par["theta_n"] * denominator',
    ),
    (
        "final test without the strip height",
        'numerator = result["total"] * par["hd"]',
        'numerator = result["total"]',
    ),
    (
        "final test with one height too few in the denominator",
        'denominator = n ** (k + 1) * F * k * par["hn"]',
        'denominator = n**k * F * k * par["hn"]',
    ),
    (
        "values file not compared: the entries of the table",
        "        if [*key, *row] != stored_row:",
        "        if [*key] != stored_row[: len(key)]:",
    ),
    ("values file not compared: the cell sums", "        if value != stored_value:", "        if False:"),
    (
        "values file not compared: the parameters",
        '    return stored["given"] == par["given"]',
        "    return True",
    ),
    (
        "values file: the numbers of masses, table lines and cell sums not checked",
        '        or len(stored["S"]) != m**k\n    ):',
        '        or len(stored["S"]) != m**k\n    ) and False:',
    ),
    (
        "text: a byte that is not allowed is taken for a blank",
        "    if data.translate(None, PRINTABLE):\n"
        '        raise BadInputError(f"{path}: a byte that is not allowed in a text file")',
        "    data = bytes(byte if byte in PRINTABLE else 32 for byte in data)",
    ),
    (
        "text: a number of 2^128 or more is accepted",
        'if not (field.isascii() and field.isdigit()) or len(digits) > 39 or int(digits or "0") >> 128:',
        "if not (field.isascii() and field.isdigit()) or len(digits) > 1000:",
    ),
    (
        "spec file: a path of the values file that is not relative is accepted",
        'if relative.startswith("/") or "\\\\" in relative or ":" in relative:',
        "if False:",
    ),
    (
        "spec file: the values file is sought from a rewritten path of the spec file",
        'par["values"] = os.path.join(os.path.dirname(path), *relative.split("/"))',
        'par["values"] = os.path.join(os.path.dirname(os.path.abspath(path)), *relative.split("/"))',
    ),
    (
        "log: the log of another computation is continued",
        "    if lines and lines[: len(head)] != head:",
        "    if lines and lines[: len(head)] != head and False:",
    ),
    (
        "log: a second, different value for a cell sum is accepted",
        '        if index >= par["m"] ** par["k"] or done.get(index, value) != value:',
        '        if index >= par["m"] ** par["k"]:',
    ),
    (
        "log: the incomplete last line of an interrupted run is kept",
        "                handle.truncate(complete)",
        "                complete = len(text)",
    ),
    (
        "log: a byte outside ASCII is not treated as malformed input",
        "        except UnicodeDecodeError as err:",
        "        except ZeroDivisionError as err:",
    ),
    (
        "output: the printed bound is not that of the total",
        'print(f"bound {decimal_up(numerator, denominator)} (rounded up)")',
        'print(f"bound {decimal_up(numerator, 2 * denominator)} (rounded up)")',
    ),
]

TABLE_CHECK = """
import sys
import check_bound as cb
par = cb.read_spec(sys.argv[1])
stored = cb.read_values(par["values"])
W, P, ET = cb.weights(par)
table = cb.edge_table(par, cb.weight_vectors(par, W), ET)
sys.exit(0 if (P, ET, table) == (stored["P"], stored["ET"], cb.stored_table(par)) else 1)
"""


def run(folder, *arguments, printed=False):
    """Exit status of a Python script run in the checkers folder of the temporary copy; with printed,
    the status and what the script wrote on standard output."""
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    done = subprocess.run(
        [sys.executable, "-B", *arguments], cwd=os.path.join(folder, "checkers"), env=environment,
        capture_output=True, text=True, check=False,
    )  # fmt: skip
    return (done.returncode, done.stdout) if printed else done.returncode


def detectors(folder):
    """Which of the five detectors fail for the checker in the folder."""
    failed = []
    if run(folder, "test_check_bound.py") != 0:
        failed.append("tests")
    for name in ("tiny", "rounding"):
        spec = os.path.join("..", "data", "specs", f"{name}.txt")
        status, lines = run(folder, "check_bound.py", spec, printed=True)
        if status != 0 or lines != PRINTED.setdefault(name, lines):
            failed.append(name)
    if run(folder, "-c", TABLE_CHECK, os.path.join("..", "data", "specs", "k5.txt")) != 0:
        failed.append("table")
    with open(os.path.join(folder, "data", "tests", "EXPECTED.txt"), encoding="ascii") as handle:
        expected = [line.split() for line in handle if line.strip()]
    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        statuses = pool.map(
            lambda name: run(folder, "check_bound.py", os.path.join("..", "data", "tests", f"{name}.txt")),
            [name for name, _ in expected],
        )
        if list(statuses) != [int(status) for _, status in expected]:
            failed.append("inputs")
    return failed


def main():
    if not os.path.exists(os.path.join(DATA, "tests", "EXPECTED.txt")):
        raise SystemExit("mutation_test: run make_tests.py first")
    if importlib.util.find_spec("numpy") is None:
        raise SystemExit("mutation_test: numpy is needed (many of the mutants change the numpy routine)")
    with open(os.path.join(HERE, "check_bound.py"), encoding="utf-8") as handle:
        source = handle.read()
    undetected = 0
    with tempfile.TemporaryDirectory() as folder:
        os.makedirs(os.path.join(folder, "checkers"))
        shutil.copy(os.path.join(HERE, "test_check_bound.py"), os.path.join(folder, "checkers"))
        for part in ("specs", "values", "tests"):
            shutil.copytree(os.path.join(DATA, part), os.path.join(folder, "data", part))
        target = os.path.join(folder, "checkers", "check_bound.py")

        def write(text):
            with open(target, "w", encoding="utf-8", newline="\n") as handle:
                handle.write(text)

        write(source)
        failed = detectors(folder)
        if failed or not all(lines.rstrip().endswith("\nACCEPTED") for lines in PRINTED.values()):
            raise SystemExit(f"mutation_test: the unmodified checker fails: {', '.join(failed)}")
        print("unmodified checker: passes tests, tiny, rounding, table and inputs")
        for number, (description, old, new) in enumerate(MUTANTS, start=1):
            if source.count(old) != 1:
                raise SystemExit(
                    f"mutation_test: mutant {number}: the text to replace occurs {source.count(old)} times"
                )
            write(source.replace(old, new))
            failed = detectors(folder)
            undetected += not failed
            verdict = "detected by " + ", ".join(failed) if failed else "NOT DETECTED"
            print(f"{number:2d}  {description}: {verdict}", flush=True)
    print(f"{len(MUTANTS) - undetected} of {len(MUTANTS)} mutants detected")
    return 1 if undetected else 0


if __name__ == "__main__":
    sys.exit(main())
