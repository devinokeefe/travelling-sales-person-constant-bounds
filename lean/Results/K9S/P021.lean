/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 2, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_2_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 2, 1]))
      = [4069204703196409808, 4130937057755394386, 4243393056516976568, 4560812701882466836] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 2, 1]]; native_decide

theorem k9s_A_0_0_2_1 : Spec.A k9 [0, 0, 2, 1] = 4069204703196409808 :=
  Correct.A_of_list k9 [0, 2, 1] _ k9s_P_0_2_1 0 (by decide)

theorem k9s_A_1_0_2_1 : Spec.A k9 [1, 0, 2, 1] = 4130937057755394386 :=
  Correct.A_of_list k9 [0, 2, 1] _ k9s_P_0_2_1 1 (by decide)

theorem k9s_A_2_0_2_1 : Spec.A k9 [2, 0, 2, 1] = 4243393056516976568 :=
  Correct.A_of_list k9 [0, 2, 1] _ k9s_P_0_2_1 2 (by decide)

theorem k9s_A_3_0_2_1 : Spec.A k9 [3, 0, 2, 1] = 4560812701882466836 :=
  Correct.A_of_list k9 [0, 2, 1] _ k9s_P_0_2_1 3 (by decide)

end Results
