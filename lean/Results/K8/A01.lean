/-
One piece of the evaluation for `k8`: the value `A_2(0, 1)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k8_A_0_1 : Spec.A k8 [0, 1] = 588095994177266409 := by
  rw [← Correct.AofPar_eq_A k8 4 [0, 1]]; native_decide

end Results
