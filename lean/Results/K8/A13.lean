/-
One piece of the evaluation for `k8`: the value `A_2(1, 3)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_1_3 : Spec.A k8 [1, 3] = 679377868392256100 := by
  rw [← Correct.AofPar_eq_A k8 4 [1, 3]]; native_decide

end Results
