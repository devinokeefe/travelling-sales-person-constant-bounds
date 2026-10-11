/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 2, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_2_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 2, 3]))
      = [2264879099408766, 2299398726744078, 2374493892308718, 2608681542720560] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 2, 3]]; native_decide

theorem k5s_A_0_3_2_3 : Spec.A k5 [0, 3, 2, 3] = 2264879099408766 :=
  Correct.A_of_list k5 [3, 2, 3] _ k5s_P_3_2_3 0 (by decide)

theorem k5s_A_1_3_2_3 : Spec.A k5 [1, 3, 2, 3] = 2299398726744078 :=
  Correct.A_of_list k5 [3, 2, 3] _ k5s_P_3_2_3 1 (by decide)

theorem k5s_A_2_3_2_3 : Spec.A k5 [2, 3, 2, 3] = 2374493892308718 :=
  Correct.A_of_list k5 [3, 2, 3] _ k5s_P_3_2_3 2 (by decide)

theorem k5s_A_3_3_2_3 : Spec.A k5 [3, 3, 2, 3] = 2608681542720560 :=
  Correct.A_of_list k5 [3, 2, 3] _ k5s_P_3_2_3 3 (by decide)

end Results
