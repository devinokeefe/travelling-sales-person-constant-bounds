/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 3, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_3_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 3, 0]))
      = [4431834852988372238, 4486744032532042645, 4590739340690340027, 4896175963974972759] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 3, 0]]; native_decide

theorem k9s_A_0_1_3_0 : Spec.A k9 [0, 1, 3, 0] = 4431834852988372238 :=
  Correct.A_of_list k9 [1, 3, 0] _ k9s_P_1_3_0 0 (by decide)

theorem k9s_A_1_1_3_0 : Spec.A k9 [1, 1, 3, 0] = 4486744032532042645 :=
  Correct.A_of_list k9 [1, 3, 0] _ k9s_P_1_3_0 1 (by decide)

theorem k9s_A_2_1_3_0 : Spec.A k9 [2, 1, 3, 0] = 4590739340690340027 :=
  Correct.A_of_list k9 [1, 3, 0] _ k9s_P_1_3_0 2 (by decide)

theorem k9s_A_3_1_3_0 : Spec.A k9 [3, 1, 3, 0] = 4896175963974972759 :=
  Correct.A_of_list k9 [1, 3, 0] _ k9s_P_1_3_0 3 (by decide)

end Results
