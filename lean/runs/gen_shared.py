# Writes the Lean files of an evaluation in pieces by the routine of TSPShared/Impl.lean:
#   Results/<MOD>/P<t>.lean   one piece for each tuple t = (g_2, ..., g_J): the four values
#                             A_J(g_1, t), g_1 = 0..m-1, in one theorem (by native_decide), and one
#                             corollary for each of them
#   Results/<MOD>.lean        the total from the m^J values A_J
#   runs/<TAG>_pieces.txt     the module name and the names of the pieces, for runs/run_pieces.py
# usage (from the folder of the Lean project): python runs/gen_shared.py PAR MOD J LEVELS_FILE TOTAL PARTS TAG
# PAR is the name of the parameter set in Results/Params.lean (k5, k9, ...), MOD the module name
# (K5S, K9S), LEVELS_FILE the output of `tspcheck SPEC --levels J FILE` (lines "A g_1 ... g_J value"),
# TOTAL the candidate for the total, PARTS the number of parts of the table of G.
# Examples (the commands that wrote the shipped files):
#   python runs/gen_shared.py k5 K5S 4 runs/k5s_levels4.txt 1761033937996622 64 k5s
#   python runs/gen_shared.py k6 K6S 2 runs/k6s_levels2.txt 12593568504391125 64 k6s
#   python runs/gen_shared.py k7 K7S 2 runs/k7s_levels2.txt 92054418307910785 64 k7s
#   python runs/gen_shared.py k8 K8S 2 runs/k8_levels_stored.txt 628708228549677266 64 k8s
#   python runs/gen_shared.py k9 K9S 4 runs/k9s_levels4.txt 4430997795015293889 64 k9s
# The values of LEVELS_FILE and TOTAL are candidates only: each becomes the right-hand side of a
# theorem that Lean then has to prove by its own evaluation, and a wrong one makes its piece fail.
# The pieces compute their units in Lean's pool of threads (first argument 0 of `AofShared`); the
# size of the pool is the number in `weakLeanArgs = ["-jN"]` of lakefile.toml, which the driver sets.
# Existing piece files are overwritten only if their text changes (so that lake keeps what is built).
import io, itertools, os, sys

par, mod, J, levels_file, total, parts, tag = sys.argv[1:8]
J = int(J); total = int(total); parts = int(parts)
assert J >= 1
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
values = {}
order = []
for line in io.open(levels_file, encoding="ascii"):
    f = line.split()
    if not f:
        continue
    assert f[0] == "A" and len(f) == J + 2, line
    g = tuple(int(x) for x in f[1:J + 1])
    assert g not in values
    values[g] = int(f[J + 1])
    order.append(g)
mm = max(g[0] for g in order) + 1
tuplesJ = list(itertools.product(range(mm), repeat=J))
assert order == tuplesJ, "the levels file does not list the tuples in order"

low = mod.lower()
def lst(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"
def und(xs):
    return "_".join(str(x) for x in xs)

def write_if_changed(path, text):
    if os.path.exists(path) and io.open(path, encoding="utf-8").read() == text:
        return False
    io.open(path, "w", encoding="utf-8", newline="\n").write(text)
    return True

os.makedirs(os.path.join(root, "Results", mod), exist_ok=True)
names = []
written = 0
for t in itertools.product(range(mm), repeat=J - 1):
    name = "P" + "".join(str(x) for x in t)
    names.append(name)
    vals = [values[(g1,) + t] for g1 in range(mm)]
    tl = lst(t)
    text = """/-
One piece of the evaluation for `%s` by the routine of `TSPShared/Impl.lean`: the values
`A_%d(g_1, %s)` of RECIPE.md Section 8 for `g_1 = 0, …, %d`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem %s_P_%s :
    (List.range (m %s)).map (fun g1 => Spec.A %s (g1 :: %s))
      = %s := by
  rw [← Correct.AofShared_eq_A %s 0 %d %s]; native_decide
""" % (par, J, ", ".join(str(x) for x in t) if t else "-", mm - 1,
       low, und(t) if t else "all", par, par, tl, lst(vals), par, parts, tl)
    for g1 in range(mm):
        text += """
theorem %s_A_%s : Spec.A %s %s = %d :=
  Correct.A_of_list %s %s _ %s_P_%s %d (by decide)
""" % (low, und((g1,) + t), par, lst((g1,) + t), vals[g1], par, tl, low, und(t) if t else "all", g1)
    text += "\nend Results\n"
    if write_if_changed(os.path.join(root, "Results", mod, name + ".lean"), text):
        written += 1

imports = "".join("import Results.%s.%s\n" % (mod, n) for n in names)
pairs = ",\n       ".join("(%s, %d)" % (lst(g), values[g]) for g in tuplesJ)
tuples = ", ".join(lst(g) for g in tuplesJ)
lemmas = ", ".join("%s_A_%s" % (low, und(g)) for g in tuplesJ)
gnames = ", ".join("g_%d" % i for i in range(1, J + 1)) if J <= 3 else "g_1, …, g_%d" % J
text = """/-
The result for `%s`, from the %d values `A_%d(%s)` (four in each file of `Results/%s/`,
computed by the routine of `TSPShared/Impl.lean`).
-/
import TSPBound.Theorems
import TSPShared.Theorems
import Results.Params
%s
namespace Results
open Spec

set_option maxRecDepth 100000 in
theorem %s_level%d :
    (tuples %d (m %s)).map (fun g => (g, A %s g))
      = [%s] := by
  have ht : tuples %d (m %s) = [%s] := by
    decide
  rw [ht]
  simp only [List.map_cons, List.map_nil, %s]

theorem %s_total : Spec.total %s = %d := by
  rw [← Correct.totalFrom_eq_total %s %d _ (by decide) %s_level%d.symm]; native_decide

theorem %s_accepts : Spec.Accepts %s := by
  unfold Spec.Accepts; rw [%s_total]; decide

end Results

#print axioms Results.%s_total
#print axioms Results.%s_accepts
""" % (par, len(tuplesJ), J, gnames, mod, imports, low, J, J, par, par, pairs, J, par, tuples, lemmas,
       low, par, total, par, J, low, J, low, par, low, low, low)
if write_if_changed(os.path.join(root, "Results", mod + ".lean"), text):
    written += 1
io.open(os.path.join(root, "runs", tag + "_pieces.txt"), "w", encoding="ascii", newline="\n").write(
    mod + "\n" + "".join(n + "\n" for n in names))
print("module %s: %d pieces, %d files written or changed" % (mod, len(names), written))
