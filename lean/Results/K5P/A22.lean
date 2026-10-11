/-
One piece of the evaluation for `k5`: the value `A_2(2, 2)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k5p_A_2_2 : Spec.A k5 [2, 2] = 1815295202580286 := by
  rw [← Correct.AofPar_eq_A k5 1 [2, 2]]; native_decide

end Results
