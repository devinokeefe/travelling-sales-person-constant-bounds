/-
One piece of the evaluation for `k8`: the value `A_2(2, 3)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_2_3 : Spec.A k8 [2, 3] = 694948698166673744 := by
  rw [← Correct.AofPar_eq_A k8 4 [2, 3]]; native_decide

end Results
