/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 0, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_0_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 0, 3]))
      = [4585424741885359588, 4641348105945226396, 4744674200267812085, 5047710014544766913] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 0, 3]]; native_decide

theorem k9s_A_0_2_0_3 : Spec.A k9 [0, 2, 0, 3] = 4585424741885359588 :=
  Correct.A_of_list k9 [2, 0, 3] _ k9s_P_2_0_3 0 (by decide)

theorem k9s_A_1_2_0_3 : Spec.A k9 [1, 2, 0, 3] = 4641348105945226396 :=
  Correct.A_of_list k9 [2, 0, 3] _ k9s_P_2_0_3 1 (by decide)

theorem k9s_A_2_2_0_3 : Spec.A k9 [2, 2, 0, 3] = 4744674200267812085 :=
  Correct.A_of_list k9 [2, 0, 3] _ k9s_P_2_0_3 2 (by decide)

theorem k9s_A_3_2_0_3 : Spec.A k9 [3, 2, 0, 3] = 5047710014544766913 :=
  Correct.A_of_list k9 [2, 0, 3] _ k9s_P_2_0_3 3 (by decide)

end Results
