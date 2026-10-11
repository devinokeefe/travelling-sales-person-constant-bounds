# Writes the Lean files of an evaluation in pieces:
#   Results/<MOD>/A<i><j>.lean   one theorem  A <par> [i, j] = value   (by native_decide)
#   Results/<MOD>.lean           the total from the 16 pieces
# usage: python gen_pieces.py PAR MOD LEVELS_FILE TOTAL THREADS [only-missing]
# PAR is the name of the parameter set in Results/Params.lean (k5, k8, ...), MOD the module name
# (K5P, K8), LEVELS_FILE the output of `tspcheck SPEC --levels 2 FILE`.
# With "only-missing", piece files whose .olean exists are left alone (so that the number of threads
# can be changed for the pieces not yet evaluated).
import io, os, sys

par, mod, levels_file, total, threads = sys.argv[1:6]
only_missing = len(sys.argv) > 6
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
values = []
for line in io.open(levels_file, encoding="ascii"):
    f = line.split()
    assert f[0] == "A" and len(f) == 4
    values.append((int(f[1]), int(f[2]), int(f[3])))
assert len(values) == 16 and [(i, j) for i, j, _ in values] == [(i, j) for i in range(4) for j in range(4)]

os.makedirs(os.path.join(root, "Results", mod), exist_ok=True)
low = mod.lower()
for i, j, v in values:
    name = "A%d%d" % (i, j)
    olean = os.path.join(root, ".lake", "build", "lib", "lean", "Results", mod, name + ".olean")
    if only_missing and os.path.exists(olean):
        continue
    text = """/-
One piece of the evaluation for `%s`: the value `A_2(%d, %d)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem %s_A_%d_%d : Spec.A %s [%d, %d] = %d := by
  rw [← Correct.AofPar_eq_A %s %s [%d, %d]]; native_decide

end Results
""" % (par, i, j, low, i, j, par, i, j, v, par, threads, i, j)
    io.open(os.path.join(root, "Results", mod, name + ".lean"), "w", encoding="utf-8", newline="\n").write(text)

imports = "".join("import Results.%s.A%d%d\n" % (mod, i, j) for i, j, _ in values)
pairs = ",\n       ".join("([%d, %d], %d)" % (i, j, v) for i, j, v in values)
tuples = ", ".join("[%d, %d]" % (i, j) for i, j, _ in values)
lemmas = ", ".join("%s_A_%d_%d" % (low, i, j) for i, j, _ in values)
text = """/-
The result for `%s`, from the sixteen values `A_2(g_1, g_2)` (one file each in `Results/%s/`).
-/
import TSPBound.Theorems
import Results.Params
%s
namespace Results
open Spec

theorem %s_level2 :
    (tuples 2 (m %s)).map (fun g => (g, A %s g))
      = [%s] := by
  have ht : tuples 2 (m %s) = [%s] := by
    decide
  rw [ht]
  simp only [List.map_cons, List.map_nil, %s]

theorem %s_total : Spec.total %s = %s := by
  rw [← Correct.totalFrom_eq_total %s 2 _ (by decide) %s_level2.symm]; native_decide

theorem %s_accepts : Spec.Accepts %s := by
  unfold Spec.Accepts; rw [%s_total]; decide

end Results

#print axioms Results.%s_total
#print axioms Results.%s_accepts
""" % (par, mod, imports, low, par, par, pairs, par, tuples, lemmas, low, par, total, par, low, low, par, low, low, low)
io.open(os.path.join(root, "Results", mod + ".lean"), "w", encoding="utf-8", newline="\n").write(text)
print("written", mod)
