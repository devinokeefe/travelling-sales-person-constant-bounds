/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_1_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 1, 2]))
      = [4343142839131451066, 4395671563616454166, 4496116810677773147, 4795402477397190182] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 1, 2]]; native_decide

theorem k9s_A_0_2_1_2 : Spec.A k9 [0, 2, 1, 2] = 4343142839131451066 :=
  Correct.A_of_list k9 [2, 1, 2] _ k9s_P_2_1_2 0 (by decide)

theorem k9s_A_1_2_1_2 : Spec.A k9 [1, 2, 1, 2] = 4395671563616454166 :=
  Correct.A_of_list k9 [2, 1, 2] _ k9s_P_2_1_2 1 (by decide)

theorem k9s_A_2_2_1_2 : Spec.A k9 [2, 2, 1, 2] = 4496116810677773147 :=
  Correct.A_of_list k9 [2, 1, 2] _ k9s_P_2_1_2 2 (by decide)

theorem k9s_A_3_2_1_2 : Spec.A k9 [3, 2, 1, 2] = 4795402477397190182 :=
  Correct.A_of_list k9 [2, 1, 2] _ k9s_P_2_1_2 3 (by decide)

end Results
