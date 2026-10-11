/-
One piece of the evaluation for `k5`: the value `A_2(1, 1)` of RECIPE.md Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k5p_A_1_1 : Spec.A k5 [1, 1] = 1621349765003821 := by
  rw [← Correct.AofPar_eq_A k5 1 [1, 1]]; native_decide

end Results
