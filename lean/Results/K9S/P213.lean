/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 1, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_1_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 1, 3]))
      = [4686896864352697369, 4739620844429519460, 4840229562249718916, 5139852956207667017] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 1, 3]]; native_decide

theorem k9s_A_0_2_1_3 : Spec.A k9 [0, 2, 1, 3] = 4686896864352697369 :=
  Correct.A_of_list k9 [2, 1, 3] _ k9s_P_2_1_3 0 (by decide)

theorem k9s_A_1_2_1_3 : Spec.A k9 [1, 2, 1, 3] = 4739620844429519460 :=
  Correct.A_of_list k9 [2, 1, 3] _ k9s_P_2_1_3 1 (by decide)

theorem k9s_A_2_2_1_3 : Spec.A k9 [2, 2, 1, 3] = 4840229562249718916 :=
  Correct.A_of_list k9 [2, 1, 3] _ k9s_P_2_1_3 2 (by decide)

theorem k9s_A_3_2_1_3 : Spec.A k9 [3, 2, 1, 3] = 5139852956207667017 :=
  Correct.A_of_list k9 [2, 1, 3] _ k9s_P_2_1_3 3 (by decide)

end Results
