/-
One piece of the evaluation for `k5`: the value `A_2(1, 3)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k5p_A_1_3 : Spec.A k5 [1, 3] = 1989575010450887 := by
  rw [← Correct.AofPar_eq_A k5 1 [1, 3]]; native_decide

end Results
