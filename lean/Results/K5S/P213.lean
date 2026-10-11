/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 1, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_1_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 1, 3]))
      = [1922714580625908, 1963328722967898, 2043128753564837, 2280843194150232] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 1, 3]]; native_decide

theorem k5s_A_0_2_1_3 : Spec.A k5 [0, 2, 1, 3] = 1922714580625908 :=
  Correct.A_of_list k5 [2, 1, 3] _ k5s_P_2_1_3 0 (by decide)

theorem k5s_A_1_2_1_3 : Spec.A k5 [1, 2, 1, 3] = 1963328722967898 :=
  Correct.A_of_list k5 [2, 1, 3] _ k5s_P_2_1_3 1 (by decide)

theorem k5s_A_2_2_1_3 : Spec.A k5 [2, 2, 1, 3] = 2043128753564837 :=
  Correct.A_of_list k5 [2, 1, 3] _ k5s_P_2_1_3 2 (by decide)

theorem k5s_A_3_2_1_3 : Spec.A k5 [3, 2, 1, 3] = 2280843194150232 :=
  Correct.A_of_list k5 [2, 1, 3] _ k5s_P_2_1_3 3 (by decide)

end Results
