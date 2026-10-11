/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 0, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_0_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 0, 3]))
      = [4954364350976213283, 4995769788661481273, 5086067079602134708, 5375384382988270608] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 0, 3]]; native_decide

theorem k9s_A_0_3_0_3 : Spec.A k9 [0, 3, 0, 3] = 4954364350976213283 :=
  Correct.A_of_list k9 [3, 0, 3] _ k9s_P_3_0_3 0 (by decide)

theorem k9s_A_1_3_0_3 : Spec.A k9 [1, 3, 0, 3] = 4995769788661481273 :=
  Correct.A_of_list k9 [3, 0, 3] _ k9s_P_3_0_3 1 (by decide)

theorem k9s_A_2_3_0_3 : Spec.A k9 [2, 3, 0, 3] = 5086067079602134708 :=
  Correct.A_of_list k9 [3, 0, 3] _ k9s_P_3_0_3 2 (by decide)

theorem k9s_A_3_3_0_3 : Spec.A k9 [3, 3, 0, 3] = 5375384382988270608 :=
  Correct.A_of_list k9 [3, 0, 3] _ k9s_P_3_0_3 3 (by decide)

end Results
