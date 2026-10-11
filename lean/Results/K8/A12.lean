/-
One piece of the evaluation for `k8`: the value `A_2(1, 2)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_1_2 : Spec.A k8 [1, 2] = 624081897596963510 := by
  rw [← Correct.AofPar_eq_A k8 4 [1, 2]]; native_decide

end Results
