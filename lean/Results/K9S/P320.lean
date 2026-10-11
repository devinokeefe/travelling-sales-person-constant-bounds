/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 2, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_2_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 2, 0]))
      = [4544309055774991913, 4584546080904849318, 4674143601935345576, 4963007729285471781] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 2, 0]]; native_decide

theorem k9s_A_0_3_2_0 : Spec.A k9 [0, 3, 2, 0] = 4544309055774991913 :=
  Correct.A_of_list k9 [3, 2, 0] _ k9s_P_3_2_0 0 (by decide)

theorem k9s_A_1_3_2_0 : Spec.A k9 [1, 3, 2, 0] = 4584546080904849318 :=
  Correct.A_of_list k9 [3, 2, 0] _ k9s_P_3_2_0 1 (by decide)

theorem k9s_A_2_3_2_0 : Spec.A k9 [2, 3, 2, 0] = 4674143601935345576 :=
  Correct.A_of_list k9 [3, 2, 0] _ k9s_P_3_2_0 2 (by decide)

theorem k9s_A_3_3_2_0 : Spec.A k9 [3, 3, 2, 0] = 4963007729285471781 :=
  Correct.A_of_list k9 [3, 2, 0] _ k9s_P_3_2_0 3 (by decide)

end Results
