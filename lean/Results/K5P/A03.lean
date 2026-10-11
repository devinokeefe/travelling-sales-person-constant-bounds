/-
One piece of the evaluation for `k5`: the value `A_2(0, 3)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k5p_A_0_3 : Spec.A k5 [0, 3] = 1955028022408841 := by
  rw [← Correct.AofPar_eq_A k5 1 [0, 3]]; native_decide

end Results
