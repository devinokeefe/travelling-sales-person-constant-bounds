/-
One piece of the evaluation for `k8`: the value `A_2(1, 1)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_1_1 : Spec.A k8 [1, 1] = 598521617449355668 := by
  rw [← Correct.AofPar_eq_A k8 4 [1, 1]]; native_decide

end Results
