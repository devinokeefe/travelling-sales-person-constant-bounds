# Makes a log for `tspcheck --log` from the log of the Python checker (check_bound.py).
# usage: python runs/convert_python_log.py HEAD_LOG PY_LOG OUT
# HEAD_LOG: a log written by the Lean executable for the same spec (its head is taken: the line
#           `tspcheck-log 1`, the seven parameter lines, the line `table MARK`).
# PY_LOG:   the log of the Python checker (head `tsp-block-log 1`, the same parameter lines, then
#           lines `sum INDEX VALUE`).  The Python checker computes one gap tuple of each pair
#           (g, reversed g); a line `sum i v` gives `sum i v` and `sum rev(i) v`, where rev(i) is the
#           index of the reversed digits of i in base m (index = sum of g_j * m^(j-1)).
# The result must hold every index 0 .. m^k - 1 exactly once; it is written in index order.
# The values found in this way are candidates only: they rest on the reversal symmetry, which the
# Lean development does not use and does not prove.
import io, sys

if len(sys.argv) != 4:
    sys.exit("usage: python runs/convert_python_log.py HEAD_LOG PY_LOG OUT")
head_log, py_log, out = sys.argv[1:4]
head = []
for line in io.open(head_log, encoding="ascii"):
    if line.startswith("sum "):
        break
    head.append(line.rstrip("\n"))
assert head[0] == "tspcheck-log 1" and len(head) == 9 and head[8].startswith("table "), head
py = [l.rstrip("\n") for l in io.open(py_log, encoding="ascii")]
assert py[0] == "tsp-block-log 1" and py[1:8] == head[1:8], "the parameter lines differ"
assert py[8].startswith("table ")
k = int(head[1].split()[1])
m = len(head[4].split())          # "gaps b_1 ... b_{m-1}": m - 1 boundaries
count = m ** k


def rev(i):
    r = 0
    for _ in range(k):
        r = r * m + i % m
        i //= m
    return r


sums = {}
lines = 0
for l in py[9:]:
    f = l.split()
    if not f:
        continue
    assert f[0] == "sum" and len(f) == 3, l
    i, v = int(f[1]), int(f[2])
    lines += 1
    for j in (i, rev(i)):
        assert 0 <= j < count
        if j in sums:
            assert j == i == rev(i) and sums[j] == v, "index %d twice" % j
        sums[j] = v
assert len(sums) == count, "%d of %d indices" % (len(sums), count)
with io.open(out, "w", encoding="ascii", newline="\n") as f:
    f.write("".join(x + "\n" for x in head))
    for j in range(count):
        f.write("sum %d %d\n" % (j, sums[j]))
print("%d lines of the Python log give %d sums" % (lines, count))
