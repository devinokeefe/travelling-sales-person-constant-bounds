/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_1_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 1, 2]))
      = [1929549671256889, 1964068178898268, 2039187619754358, 2273375270166199] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 1, 2]]; native_decide

theorem k5s_A_0_3_1_2 : Spec.A k5 [0, 3, 1, 2] = 1929549671256889 :=
  Correct.A_of_list k5 [3, 1, 2] _ k5s_P_3_1_2 0 (by decide)

theorem k5s_A_1_3_1_2 : Spec.A k5 [1, 3, 1, 2] = 1964068178898268 :=
  Correct.A_of_list k5 [3, 1, 2] _ k5s_P_3_1_2 1 (by decide)

theorem k5s_A_2_3_1_2 : Spec.A k5 [2, 3, 1, 2] = 2039187619754358 :=
  Correct.A_of_list k5 [3, 1, 2] _ k5s_P_3_1_2 2 (by decide)

theorem k5s_A_3_3_1_2 : Spec.A k5 [3, 3, 1, 2] = 2273375270166199 :=
  Correct.A_of_list k5 [3, 1, 2] _ k5s_P_3_1_2 3 (by decide)

end Results
