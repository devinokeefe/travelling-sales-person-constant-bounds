/-
One piece of the evaluation for `k8`: the value `A_2(1, 0)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_1_0 : Spec.A k8 [1, 0] = 579104800847496960 := by
  rw [← Correct.AofPar_eq_A k8 4 [1, 0]]; native_decide

end Results
