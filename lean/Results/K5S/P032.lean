/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 3, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_3_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 3, 2]))
      = [1845718575924829, 1892344903405037, 1980459741901872, 2229197625497132] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 3, 2]]; native_decide

theorem k5s_A_0_0_3_2 : Spec.A k5 [0, 0, 3, 2] = 1845718575924829 :=
  Correct.A_of_list k5 [0, 3, 2] _ k5s_P_0_3_2 0 (by decide)

theorem k5s_A_1_0_3_2 : Spec.A k5 [1, 0, 3, 2] = 1892344903405037 :=
  Correct.A_of_list k5 [0, 3, 2] _ k5s_P_0_3_2 1 (by decide)

theorem k5s_A_2_0_3_2 : Spec.A k5 [2, 0, 3, 2] = 1980459741901872 :=
  Correct.A_of_list k5 [0, 3, 2] _ k5s_P_0_3_2 2 (by decide)

theorem k5s_A_3_0_3_2 : Spec.A k5 [3, 0, 3, 2] = 2229197625497132 :=
  Correct.A_of_list k5 [0, 3, 2] _ k5s_P_0_3_2 3 (by decide)

end Results
