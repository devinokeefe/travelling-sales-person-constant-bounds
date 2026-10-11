/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_1_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 1, 2]))
      = [4693240706300749994, 4733913299329847690, 4823723391082842446, 5112736448218153401] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 1, 2]]; native_decide

theorem k9s_A_0_3_1_2 : Spec.A k9 [0, 3, 1, 2] = 4693240706300749994 :=
  Correct.A_of_list k9 [3, 1, 2] _ k9s_P_3_1_2 0 (by decide)

theorem k9s_A_1_3_1_2 : Spec.A k9 [1, 3, 1, 2] = 4733913299329847690 :=
  Correct.A_of_list k9 [3, 1, 2] _ k9s_P_3_1_2 1 (by decide)

theorem k9s_A_2_3_1_2 : Spec.A k9 [2, 3, 1, 2] = 4823723391082842446 :=
  Correct.A_of_list k9 [3, 1, 2] _ k9s_P_3_1_2 2 (by decide)

theorem k9s_A_3_3_1_2 : Spec.A k9 [3, 3, 1, 2] = 5112736448218153401 :=
  Correct.A_of_list k9 [3, 1, 2] _ k9s_P_3_1_2 3 (by decide)

end Results
