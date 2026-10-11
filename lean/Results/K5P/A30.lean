/-
One piece of the evaluation for `k5`: the value `A_2(3, 0)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k5p_A_3_0 : Spec.A k5 [3, 0] = 1876505854713677 := by
  rw [← Correct.AofPar_eq_A k5 1 [3, 0]]; native_decide

end Results
