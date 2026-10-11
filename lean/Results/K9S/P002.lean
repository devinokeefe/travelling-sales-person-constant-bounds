/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 0, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_0_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 0, 2]))
      = [3907861053524335719, 3974084338653873288, 4091283049863400844, 4414281232611510706] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 0, 2]]; native_decide

theorem k9s_A_0_0_0_2 : Spec.A k9 [0, 0, 0, 2] = 3907861053524335719 :=
  Correct.A_of_list k9 [0, 0, 2] _ k9s_P_0_0_2 0 (by decide)

theorem k9s_A_1_0_0_2 : Spec.A k9 [1, 0, 0, 2] = 3974084338653873288 :=
  Correct.A_of_list k9 [0, 0, 2] _ k9s_P_0_0_2 1 (by decide)

theorem k9s_A_2_0_0_2 : Spec.A k9 [2, 0, 0, 2] = 4091283049863400844 :=
  Correct.A_of_list k9 [0, 0, 2] _ k9s_P_0_0_2 2 (by decide)

theorem k9s_A_3_0_0_2 : Spec.A k9 [3, 0, 0, 2] = 4414281232611510706 :=
  Correct.A_of_list k9 [0, 0, 2] _ k9s_P_0_0_2 3 (by decide)

end Results
