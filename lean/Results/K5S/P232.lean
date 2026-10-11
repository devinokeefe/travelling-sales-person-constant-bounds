/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 3, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_3_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 3, 2]))
      = [2018455177909380, 2056177102568739, 2133766070581258, 2369750257477601] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 3, 2]]; native_decide

theorem k5s_A_0_2_3_2 : Spec.A k5 [0, 2, 3, 2] = 2018455177909380 :=
  Correct.A_of_list k5 [2, 3, 2] _ k5s_P_2_3_2 0 (by decide)

theorem k5s_A_1_2_3_2 : Spec.A k5 [1, 2, 3, 2] = 2056177102568739 :=
  Correct.A_of_list k5 [2, 3, 2] _ k5s_P_2_3_2 1 (by decide)

theorem k5s_A_2_2_3_2 : Spec.A k5 [2, 2, 3, 2] = 2133766070581258 :=
  Correct.A_of_list k5 [2, 3, 2] _ k5s_P_2_3_2 2 (by decide)

theorem k5s_A_3_2_3_2 : Spec.A k5 [3, 2, 3, 2] = 2369750257477601 :=
  Correct.A_of_list k5 [2, 3, 2] _ k5s_P_2_3_2 3 (by decide)

end Results
