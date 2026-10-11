/-
One piece of the evaluation for `k8`: the value `A_2(3, 0)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_3_0 : Spec.A k8 [3, 0] = 652444375969107769 := by
  rw [← Correct.AofPar_eq_A k8 4 [3, 0]]; native_decide

end Results
