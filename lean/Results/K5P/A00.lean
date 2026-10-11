/-
One piece of the evaluation for `k5`: the value `A_2(0, 0)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k5p_A_0_0 : Spec.A k5 [0, 0] = 1484445613767419 := by
  rw [← Correct.AofPar_eq_A k5 1 [0, 0]]; native_decide

end Results
