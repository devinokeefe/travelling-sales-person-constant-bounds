/-
One piece of the evaluation for `k8`: the value `A_2(2, 1)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_2_1 : Spec.A k8 [2, 1] = 617175333547216685 := by
  rw [← Correct.AofPar_eq_A k8 4 [2, 1]]; native_decide

end Results
