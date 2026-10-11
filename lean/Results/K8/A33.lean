/-
One piece of the evaluation for `k8`: the value `A_2(3, 3)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_3_3 : Spec.A k8 [3, 3] = 744317543041174092 := by
  rw [← Correct.AofPar_eq_A k8 4 [3, 3]]; native_decide

end Results
