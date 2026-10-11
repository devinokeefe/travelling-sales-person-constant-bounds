/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_1_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 1, 2]))
      = [1669097025709149, 1709668113607685, 1789446004663027, 2027212876326127] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 1, 2]]; native_decide

theorem k5s_A_0_2_1_2 : Spec.A k5 [0, 2, 1, 2] = 1669097025709149 :=
  Correct.A_of_list k5 [2, 1, 2] _ k5s_P_2_1_2 0 (by decide)

theorem k5s_A_1_2_1_2 : Spec.A k5 [1, 2, 1, 2] = 1709668113607685 :=
  Correct.A_of_list k5 [2, 1, 2] _ k5s_P_2_1_2 1 (by decide)

theorem k5s_A_2_2_1_2 : Spec.A k5 [2, 2, 1, 2] = 1789446004663027 :=
  Correct.A_of_list k5 [2, 1, 2] _ k5s_P_2_1_2 2 (by decide)

theorem k5s_A_3_2_1_2 : Spec.A k5 [3, 2, 1, 2] = 2027212876326127 :=
  Correct.A_of_list k5 [2, 1, 2] _ k5s_P_2_1_2 3 (by decide)

end Results
