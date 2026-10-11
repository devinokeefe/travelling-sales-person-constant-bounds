/-
One piece of the evaluation for `k6` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k6s_P_3 :
    (List.range (m k6)).map (fun g1 => Spec.A k6 (g1 :: [3]))
      = [13758588737819275, 13965734133349429, 14416392723264310, 15821531400483560] := by
  rw [← Correct.AofShared_eq_A k6 0 64 [3]]; native_decide

theorem k6s_A_0_3 : Spec.A k6 [0, 3] = 13758588737819275 :=
  Correct.A_of_list k6 [3] _ k6s_P_3 0 (by decide)

theorem k6s_A_1_3 : Spec.A k6 [1, 3] = 13965734133349429 :=
  Correct.A_of_list k6 [3] _ k6s_P_3 1 (by decide)

theorem k6s_A_2_3 : Spec.A k6 [2, 3] = 14416392723264310 :=
  Correct.A_of_list k6 [3] _ k6s_P_3 2 (by decide)

theorem k6s_A_3_3 : Spec.A k6 [3, 3] = 15821531400483560 :=
  Correct.A_of_list k6 [3] _ k6s_P_3 3 (by decide)

end Results
