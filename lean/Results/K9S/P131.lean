/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 3, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_3_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 3, 1]))
      = [4540607687858691627, 4595260114292462686, 4698946726837238339, 5004010982779998949] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 3, 1]]; native_decide

theorem k9s_A_0_1_3_1 : Spec.A k9 [0, 1, 3, 1] = 4540607687858691627 :=
  Correct.A_of_list k9 [1, 3, 1] _ k9s_P_1_3_1 0 (by decide)

theorem k9s_A_1_1_3_1 : Spec.A k9 [1, 1, 3, 1] = 4595260114292462686 :=
  Correct.A_of_list k9 [1, 3, 1] _ k9s_P_1_3_1 1 (by decide)

theorem k9s_A_2_1_3_1 : Spec.A k9 [2, 1, 3, 1] = 4698946726837238339 :=
  Correct.A_of_list k9 [1, 3, 1] _ k9s_P_1_3_1 2 (by decide)

theorem k9s_A_3_1_3_1 : Spec.A k9 [3, 1, 3, 1] = 5004010982779998949 :=
  Correct.A_of_list k9 [1, 3, 1] _ k9s_P_1_3_1 3 (by decide)

end Results
