#!/usr/bin/env python3
"""Python checker for the block bound on the travelling salesman constant.

It follows RECIPE.md section by section with Python's unbounded integers, except in two places, each
behind a test of a bound that excludes overflow: the convolutions of Section 4 are done by one
multiplication of packed integers, and the cell sums of Section 7 use numpy (64-bit integers) for the
costs of paths and for their sums over the heights of the interior points.  The cell sums also use the
three identities of Section 7; in particular, of a gap tuple and the tuple read backwards only one is
computed.  Without numpy a slow pure-Python loop over all height tuples is used for the cell sums, which
is practical only for small parameters.

usage:  check_bound.py SPEC [-j PROCESSES] [--log FILE] [--write]

Without --write the values file named in SPEC is compared with the recomputed values.  With --write it
is created.  With --log the cell sums are appended to FILE as they are computed, and a run that was
interrupted is continued by repeating the command.  The sums already in FILE are then taken as they
stand, each for its gap tuple and for the tuple read backwards, and are not recomputed: a check that
is to rest on one run alone starts without FILE.
Exit status: 0 accepted, 1 rejected, 2 malformed input or a violated arithmetic bound.
"""

import hashlib
import itertools
import math
import os
import sys
import time
from multiprocessing import Pool

try:
    import numpy as np
except ImportError:  # the pure-Python loop is used instead
    np = None

Q = 1 << 62
D = 1 << 48
F = 1 << 32
TAYLOR_TERMS = 12
MAX_BOUNDARY = 1 << 20  # a limit of this program, not of the recipe (Section 9)
MAX_PROCESSES = 60  # a limit of this program: before Python 3.13 a Pool can wait for at most 61 under Windows
MAX_ARRAY = 50_000  # cell sums with numpy: more heights are looped over until no array has more entries
MAGIC = "tsp-block-values 1"
LOG_MAGIC = "tsp-block-log 1"
PARAMETER_NAMES = ("k", "h", "mesh", "gaps", "heights", "height_mesh", "tail")
PRINTABLE = bytes([9, 10, *range(32, 127)])  # the bytes of a text file: tab, line feed, 32 to 126


class BadInputError(Exception):
    """A malformed file or a violated arithmetic bound (exit status 2)."""


def cdiv(a, b):
    """ceil(a / b) for integers a >= 0 and b > 0."""
    return -(-a // b)


def ceil_sqrt(a):
    """The least integer u >= 0 with u * u >= a."""
    u = math.isqrt(a)
    return u if u * u == a else u + 1


# ---------------------------------------------------------------------------- files (Section 10)
def read_lines(path):
    """The lines of a text file as lists of fields, by the rules for text in Section 10."""
    try:
        with open(path, "rb") as handle:
            data = handle.read()
    except OSError as err:
        raise BadInputError(f"cannot read {path}: {err}") from err
    # A carriage return is allowed only directly before a line feed; one that is left over is
    # rejected with the other bytes that may not occur.
    data = data.replace(b"\r\n", b"\n")
    if data.translate(None, PRINTABLE):
        raise BadInputError(f"{path}: a byte that is not allowed in a text file")
    lines = data.decode("ascii").split("\n")
    if lines[-1] == "":
        lines.pop()  # the last line may or may not have its line end
    lines = [line.replace("\t", " ").split(" ") for line in lines]
    lines = [[field for field in line if field] for line in lines]
    if not all(lines):
        raise BadInputError(f"{path}: empty line")
    return lines


def number(field, where):
    """The value of a field that must be a number below 2^128; any number of leading zeros is allowed."""
    # 2^128 has 39 digits.  The length is tested first, so that int() is never given a long string.
    digits = field.lstrip("0")
    if not (field.isascii() and field.isdigit()) or len(digits) > 39 or int(digits or "0") >> 128:
        raise BadInputError(f"{where}: '{field[:50]}' is not a number below 2^128")
    return int(digits or "0")


def numbers(lines, name, count, where):
    """The next line: the name (if not empty), then count numbers, or any number of them if count is None."""
    fields = lines.pop(0) if lines else []
    if name:
        if not fields or fields[0] != name:
            raise BadInputError(f"{where}: expected a line '{name}'")
        fields = fields[1:]
    if count is not None and len(fields) != count:
        raise BadInputError(
            f"{where}: wrong number of numbers in a line '{name}'"
            if name
            else f"{where}: wrong number of numbers in a line"
        )
    return [number(field, where) for field in fields]


def counted_lines(lines, name, count, where):
    """The line 'name N' and the N lines of numbers that follow it (count numbers each, or any number)."""
    stated = numbers(lines, name, 1, where)[0]
    if stated > len(lines):
        raise BadInputError(f"{where}: fewer lines than the line '{name}' states")
    return [numbers(lines, "", count, where) for _ in range(stated)]


def parameter_numbers(lines, where):
    """The seven parameter lines shared by spec files and values files, as lists of numbers."""
    counts = {"k": 1, "h": 2, "mesh": 1, "gaps": None, "heights": 1, "height_mesh": 1, "tail": 1}
    return [numbers(lines, name, counts[name], where) for name in PARAMETER_NAMES]


def read_spec(path):
    """The parameters of a spec file, checked against the allowed ranges (Section 1)."""
    lines = read_lines(path)
    given = parameter_numbers(lines, path)
    par = {
        "k": given[0][0],
        "hn": given[1][0],
        "hd": given[1][1],
        "M": given[2][0],
        "b": [0, *given[3]],
        "n": given[4][0],
        "nu": given[5][0],
        "T": given[6][0],
    }
    par["m"] = len(par["b"])
    par["theta_n"], par["theta_d"] = numbers(lines, "threshold", 2, path)
    if len(lines) != 1 or len(lines[0]) != 2 or lines[0][0] != "values":
        raise BadInputError(f"{path}: expected a last line 'values PATH'")
    relative = lines[0][1]
    if relative.startswith("/") or "\\" in relative or ":" in relative:
        raise BadInputError(
            f"{path}: the path of the values file must be relative, with '/' between its parts"
        )
    increasing = all(x < y for x, y in itertools.pairwise(par["b"]))
    small = all(
        0 < x < 1 << 64 for x in (par["hn"], par["hd"], par["theta_n"], par["theta_d"], *par["b"][1:])
    )
    if not (
        2 <= par["k"] <= 9
        and small
        and math.gcd(par["hn"], par["hd"]) == 1
        and 2 <= par["M"] <= 1024
        and increasing
        and 1 <= par["m"] <= 8
        and 1 <= par["n"] <= 16
        and 1 <= par["nu"] <= 256
        and 1 <= par["T"] <= 40
    ):
        raise BadInputError(f"{path}: a parameter is outside the allowed range")
    par["given"] = given
    # The folder is that of the path as it was given: the system, not this program, resolves a "..".
    par["values"] = os.path.join(os.path.dirname(path), *relative.split("/"))
    return par


def parameter_lines(par):
    return [
        f"k {par['k']}",
        f"h {par['hn']} {par['hd']}",
        f"mesh {par['M']}",
        " ".join(["gaps", *(str(x) for x in par["b"][1:])]),
        f"heights {par['n']}",
        f"height_mesh {par['nu']}",
        f"tail {par['T']}",
    ]


def values_lines(par, result):
    lines = [MAGIC, *parameter_lines(par)]
    lines.append("masses " + " ".join(str(x) for x in result["P"]))
    lines.append(f"tail_term {result['ET']}")
    lines.append(f"table {len(result['table'])}")
    for key, row in result["table"].items():
        lines.append(" ".join(str(x) for x in (*key, *row)))
    lines.append(f"sums {len(result['S'])}")
    lines.extend(str(x) for x in result["S"])
    lines.append(f"total {result['total']}")
    return lines


def read_values(path):
    """The numbers of a values file.  Only the form of the file is checked here (step 2 of Section 10)."""
    lines = read_lines(path)
    if not lines or lines.pop(0) != MAGIC.split():
        raise BadInputError(f"{path}: the first line must be '{MAGIC}'")
    stored = {"given": parameter_numbers(lines, path)}
    stored["P"] = numbers(lines, "masses", None, path)
    stored["ET"] = numbers(lines, "tail_term", 1, path)[0]
    stored["rows"] = counted_lines(lines, "table", None, path)
    stored["S"] = [row[0] for row in counted_lines(lines, "sums", 1, path)]
    stored["total"] = numbers(lines, "total", 1, path)[0]
    if lines:
        raise BadInputError(f"{path}: lines after the total")
    return stored


def same_parameters(par, stored):
    """Whether the parameter lines of a values file give the numbers of the spec file (step 3)."""
    return stored["given"] == par["given"]


def check_counts(par, stored):
    """The numbers of masses, table lines, table entries and cell sums of a values file (step 4)."""
    k, m, n = par["k"], par["m"], par["n"]
    if (
        len(stored["P"]) != m
        or len(stored["rows"]) != math.comb(m + k, k) - 1
        or any(len(row) != m + n for row in stored["rows"])
        or len(stored["S"]) != m**k
    ):
        raise BadInputError(
            "the values file has the wrong number of masses, table lines, table entries or cell sums"
        )


def first_difference(result, stored):
    """What differs between the recomputed values and those of a values file, or None (step 5)."""
    if stored["P"] != result["P"]:
        return "the masses differ"
    if stored["ET"] != result["ET"]:
        return "the tail term differs"
    for (key, row), stored_row in zip(result["table"].items(), stored["rows"], strict=True):
        if [*key, *row] != stored_row:
            return "the table differs at the key " + " ".join(str(x) for x in key)
    for index, (value, stored_value) in enumerate(zip(result["S"], stored["S"], strict=True)):
        if value != stored_value:
            return f"the cell sum of gap tuple {index} differs"
    if stored["total"] != result["total"]:
        return "the total differs"
    return None


def stored_table(par):
    """The table of the values file of a spec, as a dictionary from keys to rows (used in controls/)."""
    stored = read_values(par["values"])
    return {tuple(row[: par["m"]]): row[par["m"] :] for row in stored["rows"]}


# ---------------------------------------------------------------------------- Sections 2 and 3
def exponential_bounds(M, top):
    """Rlo[i] <= Q exp(-i/M) <= Rup[i] for 0 <= i <= top (Section 2)."""
    lo, up = 0, Q
    for j in range(TAYLOR_TERMS, 0, -1):
        lo, up = Q - cdiv(up, M * j), Q - lo // (M * j)
    r1lo, r1up = lo, up
    rlo, rup = [Q], [Q]
    for _ in range(top):
        rlo.append(rlo[-1] * r1lo // Q)
        rup.append(cdiv(rup[-1] * r1up, Q))
    return rlo, rup


def weights(par):
    """The weights W_c, the cell masses P_c and the tail term ET (Section 3)."""
    M, b, m = par["M"], par["b"], par["m"]
    n_tail = par["T"] * M
    rlo, rup = exponential_bounds(M, max(b[-1], n_tail))
    c_lambda = Q - M * (Q - rup[1])
    c_mu = M * (Q - rlo[1]) - rlo[1]

    def numerator(i, cells):
        return (rup[i] * c_lambda if i < cells else 0) + (rup[i - 1] * c_mu if i >= 1 else 0)

    W = []
    for c in range(m - 1):
        # cells is n_c, the number of mesh intervals of the bounded gap cell c
        cells = b[c + 1] - b[c]
        qlo = Q - rup[cells]
        W.append([cdiv(cdiv(numerator(i, cells), 1 << 14), qlo) for i in range(cells + 1)])
    last = [cdiv(numerator(i, n_tail), 1 << 76) for i in range(n_tail + 1)]
    last[n_tail] += cdiv(rup[n_tail], 1 << 14)
    W.append(last)
    P = [cdiv(rup[b[c]] - rlo[b[c + 1]], 1 << 14) for c in range(m - 1)]
    P.append(cdiv(rup[b[-1]], 1 << 14))
    ET = cdiv(rup[n_tail], 1 << 30)
    return W, P, ET


# ---------------------------------------------------------------------------- Section 4
def all_keys(m, k):
    """The keys in lexicographic order."""
    return [key for key in itertools.product(range(k + 1), repeat=m) if 1 <= sum(key) <= k]


def convolve(u, v):
    """ceil((u * v)(s) / D) for all s, where u * v is the convolution of two integer lists.

    The lists are packed into two long integers with 16 bytes for each entry, so that one
    multiplication gives all the sums of products; no sum reaches 2^128 (checked).
    """
    if min(len(u), len(v)) * max(u) * max(v) >= 1 << 128:
        raise BadInputError("a convolution sum would not fit into 128 bits")
    packed_u = int.from_bytes(b"".join(x.to_bytes(16, "little") for x in u), "little")
    packed_v = int.from_bytes(b"".join(x.to_bytes(16, "little") for x in v), "little")
    length = len(u) + len(v) - 1
    raw = (packed_u * packed_v).to_bytes(16 * length, "little")
    return [cdiv(int.from_bytes(raw[16 * s : 16 * s + 16], "little"), D) for s in range(length)]


def weight_vectors(par, W):
    """V_kappa for every key (Section 4)."""
    V = {}
    for key in all_keys(par["m"], par["k"]):
        c = max(i for i, count in enumerate(key) if count)
        if sum(key) == 1:
            V[key] = W[c]
        else:
            shorter = key[:c] + (key[c] - 1,) + key[c + 1 :]
            V[key] = convolve(V[shorter], W[c])
    return V


# ---------------------------------------------------------------------------- Sections 5 and 6
def distance_table(par):
    """G(j, d) for 0 <= j <= J and 0 <= d < n (Section 5), as a list of n lists."""
    k, M, n, nu = par["k"], par["M"], par["n"], par["nu"]
    alpha = par["hd"] ** 2 * n * nu
    gamma = M * par["hn"] ** 2
    J = k * (par["b"][-1] + par["T"] * M)
    # e[i] is eta_i and ct[t + nu] is chi(t) of Section 5
    e = [1 if i in (0, nu) else 2 for i in range(nu + 1)]
    ct = [sum(e[i] * e[i - t] for i in range(nu + 1) if 0 <= i - t <= nu) for t in range(-nu, nu + 1)]
    scale = alpha * M
    G = [[0] * (J + 1) for _ in range(n)]
    for j in range(J + 1):
        aj2 = (alpha * j) ** 2
        dist = [cdiv(ceil_sqrt((aj2 + (gamma * tau) ** 2) * F * F), scale) for tau in range(n * nu + 1)]
        for d in range(n):
            total = sum(ct[t + nu] * dist[abs(d * nu + t)] for t in range(-nu, nu + 1))
            G[d][j] = cdiv(total, 4 * nu * nu)
    return G


def edge_table(par, V, ET):
    """Tab(kappa, d) for every key (Section 6)."""
    G = distance_table(par)
    b, n = par["b"], par["n"]
    table = {}
    for key, vector in V.items():
        base = sum(count * b[c] for c, count in enumerate(key))
        tail = key[-1] * ET
        table[key] = [
            cdiv(sum(x * y for x, y in zip(vector, G[d][base : base + len(vector)], strict=True)), D) + tail
            for d in range(n)
        ]
    return table


# ---------------------------------------------------------------------------- Section 7
def pairs(k):
    return [(i, j) for i in range(k + 1) for j in range(i + 1, k + 1)]


def edge_rows(par, table, g):
    """The table rows of the edges {i, j} of a block with gap tuple g."""
    m = par["m"]
    rows = {}
    for i, j in pairs(par["k"]):
        key = tuple(g[i:j].count(c) for c in range(m))
        rows[i, j] = rows[j, i] = table[key]
    return rows


def best_path(k, cost):
    """min over the orders of the interior points; cost[i][j] may be integers or numpy arrays.

    dp[mask, v] is the least cost of a path from point 0 through the interior points in mask that
    ends at v.  Masks are taken in increasing order, so every dp entry is final when it is used.
    """
    inner = k - 1
    dp = {(1 << v, v): cost[0, v + 1] for v in range(inner)}
    for mask in range(1, 1 << inner):
        for v in range(inner):
            if not mask >> v & 1:
                continue
            here = dp.pop((mask, v))
            if mask == (1 << inner) - 1:
                dp["end", v] = here + cost[v + 1, k]
                continue
            for w in range(inner):
                if mask >> w & 1:
                    continue
                candidate = here + cost[v + 1, w + 1]
                target = (mask | 1 << w, w)
                if target not in dp:
                    dp[target] = candidate
                elif np is not None and isinstance(candidate, np.ndarray):
                    np.minimum(dp[target], candidate, out=dp[target])
                else:
                    dp[target] = min(dp[target], candidate)
    ends = [dp["end", v] for v in range(inner)]
    if np is not None and isinstance(ends[0], np.ndarray):
        return np.minimum.reduce(ends)
    return min(ends)


def cell_sum_plain(par, table, g):
    """S_g by a loop over all height tuples (no numpy)."""
    k, n = par["k"], par["n"]
    rows = edge_rows(par, table, g)
    total = 0
    for a in itertools.product(range(n), repeat=k + 1):
        cost = {(i, j): rows[i, j][abs(a[i] - a[j])] for i in range(k + 1) for j in range(k + 1) if i != j}
        total += best_path(k, cost)
    return total


def interior_paths(k, cost):
    """path[u, v]: the least cost of a path from u to v through all the interior points 1, ..., k - 1.

    The interior points, with u first and v last, form a block of k - 2 gaps, and path[u, v] is its
    best_path; path[v, u] is the same number, because cost[i, j] = cost[j, i].  For k = 3 the path is
    the edge from 1 to 2.  For k = 2 it is the point 1 alone and costs nothing.
    """
    inner = range(1, k)
    if k == 2:
        return {(1, 1): 0}
    path = {}
    for u, v in itertools.combinations(inner, 2):
        order = [u, *(i for i in inner if i not in (u, v)), v]
        block = {(i, j): cost[order[i], order[j]] for i in range(k - 1) for j in range(k - 1) if i != j}
        path[u, v] = path[v, u] = best_path(k - 2, block) if k > 3 else cost[u, v]
    return path


def least(arrays):
    """The minimum, entry by entry, of numpy arrays of one shape; the first of them receives it."""
    arrays = iter(arrays)
    best = next(arrays)
    for other in arrays:
        np.minimum(best, other, out=best)
    return best


def cell_sums_numpy(par, table, tuples):
    """S_g with numpy, for gap tuples that differ only in g_1 and g_k.

    An order of the interior points begins with some point u and ends with some point v, so
        cost(g, a) = min over u and v of E_0u + path[u, v] + E_vk        (see interior_paths).
    Two of the three identities of Section 7 shorten the work here, Shared paths in the first two items
    and Reflection in the third (cell_sums uses Reversal):
      - path[u, v] depends neither on g_1 and g_k nor on a_0 and a_k, so it serves all the tuples;
      - E_0u depends neither on g_k nor on a_k, so before[v] = min over u of E_0u + path[u, v] serves
        the tuples with the same g_1;
      - the height tuples with a_1 = y and with a_1 = n - 1 - y contribute equally to S_g, so a_1 runs
        over the lower half of the heights and counts twice, or once if it is the middle one (n odd).
    The heights a_0, a_k and a_1 are looped over, and those of further interior points as long as an
    array would have more than MAX_ARRAY entries.  The heights of the other interior points are the
    axes of the arrays: an array has length 1 along the axes of the heights on which it does not
    depend, and numpy repeats it there when two arrays are combined.  Every cost in an array is that
    of a path, so the bound tested in cell_sums excludes an overflow of the 64-bit integers.
    """
    k, n = par["k"], par["n"]
    inner = range(1, k)
    rows = {
        g: {pair: np.array(row, dtype=np.int64) for pair, row in edge_rows(par, table, g).items()}
        for g in tuples
    }
    looped = 1  # the number of interior points whose heights are looped over; the others have axes
    while looped < k - 2 and n ** (k - 1 - looped) > MAX_ARRAY:
        looped += 1
    free = k - 1 - looped
    axes = [np.arange(n).reshape([n if i == axis else 1 for i in range(free)]) for axis in range(free)]
    totals = dict.fromkeys(tuples, 0)
    for fixed in itertools.product(range((n + 1) // 2), *[range(n)] * (looped - 1)):
        weight = 1 if 2 * fixed[0] == n - 1 else 2
        heights = [None, *fixed, *axes]  # heights[i] is a_i for the interior point i: a number or an array
        cost = {
            (i, j): rows[tuples[0]][i, j][np.abs(heights[i] - heights[j])]
            for i in inner
            for j in inner
            if i != j
        }
        path = interior_paths(k, cost)
        for first in sorted({g[0] for g in tuples}):
            members = [g for g in tuples if g[0] == first]
            for a_first in range(n):
                start = {u: rows[members[0]][0, u][np.abs(heights[u] - a_first)] for u in inner}
                before = {v: least(start[u] + path[u, v] for u in inner if (u, v) in path) for v in inner}
                for g in members:
                    for a_last in range(n):
                        ends = (before[v] + rows[g][v, k][np.abs(heights[v] - a_last)] for v in inner)
                        totals[g] += weight * int(least(ends).sum())
    return [totals[g] for g in tuples]


def cell_sums_chunk(job):
    """The sums of gap tuples that differ only in g_1 and g_k, given by their indices."""
    par, table, indices = job
    m, k = par["m"], par["k"]
    tuples = [tuple(index // m**i % m for i in range(k)) for index in indices]
    if np is None:
        return [cell_sum_plain(par, table, g) for g in tuples]
    return cell_sums_numpy(par, table, tuples)


def open_log(path, par, table):
    """Open the log of cell sums for appending; return the handle and the sums it already holds.

    The head of the log names the parameters and the table, so that a log is never continued with other
    data.  A last line without a line end, left by an interrupted run, is dropped.
    """
    rows = "\n".join(" ".join(str(x) for x in (*key, *row)) for key, row in table.items())
    head = [LOG_MAGIC, *parameter_lines(par), "table " + hashlib.sha256(rows.encode("ascii")).hexdigest()]
    done = {}
    lines = []
    if os.path.exists(path):
        try:
            with open(path, "r+", encoding="ascii", newline="") as handle:
                text = handle.read()
                complete = text.rfind("\n") + 1
                handle.truncate(complete)
        except UnicodeDecodeError as err:
            raise BadInputError(f"{path}: a byte that is not ASCII in the log") from err
        lines = text[:complete].split("\n")[:-1]
    if lines and lines[: len(head)] != head:
        raise BadInputError(f"{path}: this log belongs to another computation")
    for line in lines[len(head) :]:
        fields = line.split()
        if len(fields) != 3 or fields[0] != "sum" or not (fields[1].isdigit() and fields[2].isdigit()):
            raise BadInputError(f"{path}: malformed line '{line}'")
        index, value = int(fields[1]), int(fields[2])
        if index >= par["m"] ** par["k"] or done.get(index, value) != value:
            raise BadInputError(f"{path}: inconsistent line '{line}'")
        done[index] = value
    handle = open(path, "a", encoding="ascii", newline="")  # noqa: SIM115 (closed by the caller)
    if not lines:
        handle.write("".join(line + "\n" for line in head))
        handle.flush()
    return handle, done


def cell_sums(par, table, processes, log_path=None):
    """S_g for every gap tuple, in index order (Section 7)."""
    k, m, n = par["k"], par["m"], par["n"]
    # The bound for the 64-bit integers of cell_sums_numpy: k * max(Tab) * n^(k-1) < 2^63.  Every cost in an
    # array there is that of a path of at most k edges, so at most k * max(Tab), and the only sums of costs
    # that numpy forms are those of the entries of one array, which has at most n^(k-2) of them (Section 9):
    # the bound has a factor n to spare.  A whole cell sum can be larger: it is added up with Python integers.
    if k * max(max(row) for row in table.values()) * n ** (k - 1) >= 1 << 63:
        raise BadInputError("a sum of path costs over the interior heights would not fit into 63 bits")
    count = m**k
    log, done = open_log(log_path, par, table) if log_path else (None, {})
    if done:
        print(f"  {len(done)} cell sums taken from {log_path}", file=sys.stderr, flush=True)
    # Reversal (Section 7): a gap tuple and the tuple read backwards have the same sum, so one of the
    # two is computed and the other receives a copy.  The one computed is that whose gaps without the
    # last, g_1, ..., g_{k-1}, have the smaller index.  Unless g_2, ..., g_{k-1} read the same
    # backwards, they alone decide this, so the tuples that share them (a job, see below) are then
    # computed together or not at all.  The log holds the computed sums only.
    backwards = []
    for index in range(count):
        g = [index // m**i % m for i in range(k)]
        backwards.append(sum(c * m**i for i, c in enumerate(reversed(g))))
    for index, value in list(done.items()):
        done.setdefault(backwards[index], value)
    front = m ** (k - 1)  # index % front is the index of g_1, ..., g_{k-1}
    todo = [i for i in range(count) if i not in done and i % front <= backwards[i] % front]
    # Shared paths (Section 7): a job consists of the tuples to compute that differ only in g_1 and g_k.
    groups = {}
    for index in todo:
        groups.setdefault(index // m % m ** (k - 2), []).append(index)
    jobs = [(par, table, groups[middle]) for middle in sorted(groups)]
    start = time.time()
    if processes == 1:
        chunks = map(cell_sums_chunk, jobs)
        pool = None
    else:
        pool = Pool(processes)
        chunks = pool.imap(cell_sums_chunk, jobs)
    for number, (job, chunk) in enumerate(zip(jobs, chunks, strict=True), start=1):
        for index, value in zip(job[2], chunk, strict=True):
            done[index] = done[backwards[index]] = value
        if log is not None:
            log.write("".join(f"sum {index} {value}\n" for index, value in zip(job[2], chunk, strict=True)))
            log.flush()
            os.fsync(log.fileno())
        if number % 64 == 0 or number == len(jobs):
            print(
                f"  cell sums {len(done)} of {count}, {time.time() - start:.0f} s",
                file=sys.stderr,
                flush=True,
            )
    if pool is not None:
        pool.close()
        pool.join()
    if log is not None:
        log.close()
    return [done[index] for index in range(count)]


# ---------------------------------------------------------------------------- Section 8
def total_bound(par, P, sums):
    """The total A_0 (Section 8)."""
    m = par["m"]
    level = sums
    for _ in range(par["k"]):
        level = [
            cdiv(sum(P[c] * level[i + c * (len(level) // m)] for c in range(m)), D)
            for i in range(len(level) // m)
        ]
    return level[0]


def decimal_up(numerator, denominator, digits=12):
    """numerator / denominator rounded up to the given number of decimals."""
    scaled = cdiv(numerator * 10**digits, denominator)
    return f"{scaled // 10**digits}.{scaled % 10**digits:0{digits}d}"


# ---------------------------------------------------------------------------- the program (Section 10)
def compute(par, processes, log_path=None):
    if par["b"][-1] > MAX_BOUNDARY:
        raise BadInputError("the last boundary is above 2^20; this program does not provide the memory")
    W, P, ET = weights(par)
    table = edge_table(par, weight_vectors(par, W), ET)
    print(f"  table of {len(table)} keys done", file=sys.stderr, flush=True)
    sums = cell_sums(par, table, processes, log_path)
    return {"P": P, "ET": ET, "table": table, "S": sums, "total": total_bound(par, P, sums)}


def option(argv, name):
    """Remove 'name VALUE' from the argument list and return VALUE, or None if the option is absent."""
    if name not in argv:
        return None
    position = argv.index(name)
    if position + 1 >= len(argv):
        raise BadInputError(f"{name} needs a value")
    value = argv[position + 1]
    del argv[position : position + 2]
    return value


def main(argv):
    if not argv:
        raise BadInputError(__doc__)
    spec, argv = argv[0], list(argv[1:])  # the spec file comes first, the options after it
    processes = option(argv, "-j")
    if processes is None:
        processes = "1"
    digits = processes.lstrip("0")
    if not (processes.isascii() and processes.isdigit()) or not digits:
        raise BadInputError("-j needs a positive number of processes, written with digits")
    # ten or more digits: more than MAX_PROCESSES, and not converted to an integer
    processes = MAX_PROCESSES if len(digits) > 9 else min(int(digits), MAX_PROCESSES)
    log_path = option(argv, "--log")
    write = "--write" in argv
    if [a for a in argv if a != "--write"] or argv.count("--write") > 1:
        raise BadInputError(__doc__)
    par = read_spec(spec)
    # Problems with the values file are reported before the computation, not after it.
    if write and os.path.exists(par["values"]):
        raise BadInputError(f"{par['values']} exists already")
    stored = None if write else read_values(par["values"])
    if stored is not None:
        if not same_parameters(par, stored):
            print("REJECTED: the parameters of the values file are not those of the spec file")
            return 1
        check_counts(par, stored)
    start = time.time()
    result = compute(par, processes, log_path)
    print(f"  time {time.time() - start:.1f} s, {processes} process(es)", file=sys.stderr, flush=True)
    if write:
        with open(par["values"], "x", encoding="ascii", newline="\n") as handle:
            handle.write("\n".join(values_lines(par, result)) + "\n")
        print(f"wrote {par['values']}")
    else:
        difference = first_difference(result, stored)
        if difference:
            print(f"REJECTED: {difference}")
            return 1
        print("the stored values agree with the recomputed values")
    k, n = par["k"], par["n"]
    denominator = n ** (k + 1) * F * k * par["hn"]
    numerator = result["total"] * par["hd"]
    print(f"total {result['total']}")
    print(f"bound {decimal_up(numerator, denominator)} (rounded up)")
    accepted = numerator * par["theta_d"] <= par["theta_n"] * denominator
    relation = "<=" if accepted else ">"
    print(f"bound {relation} {par['theta_n']}/{par['theta_d']}")
    print("ACCEPTED" if accepted else "REJECTED: the bound exceeds the threshold")
    return 0 if accepted else 1


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except (BadInputError, OSError) as error:  # OSError: a log or values file that cannot be written
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(2)
    except MemoryError:
        print("ERROR: not enough memory for these parameters", file=sys.stderr)
        sys.exit(2)
