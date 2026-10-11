/-
The two small test cases.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem tiny_total : Spec.total tiny = 1907697663974 := by
  rw [← Correct.totalPar_eq tiny 2]; native_decide

theorem tiny_accepts : Spec.Accepts tiny := by
  unfold Spec.Accepts; rw [tiny_total]; decide

theorem k4_total : Spec.total k4 = 237407881468644 := by
  rw [← Correct.totalPar_eq k4 2]; native_decide

theorem k4_accepts : Spec.Accepts k4 := by
  unfold Spec.Accepts; rw [k4_total]; decide

end Results

#print axioms Results.tiny_total
#print axioms Results.tiny_accepts
#print axioms Results.k4_total
#print axioms Results.k4_accepts
