/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 3, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_3_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 3, 3]))
      = [4991706516919496686, 5045839878814189787, 5148795635180339123, 5453011541181669471] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 3, 3]]; native_decide

theorem k9s_A_0_1_3_3 : Spec.A k9 [0, 1, 3, 3] = 4991706516919496686 :=
  Correct.A_of_list k9 [1, 3, 3] _ k9s_P_1_3_3 0 (by decide)

theorem k9s_A_1_1_3_3 : Spec.A k9 [1, 1, 3, 3] = 5045839878814189787 :=
  Correct.A_of_list k9 [1, 3, 3] _ k9s_P_1_3_3 1 (by decide)

theorem k9s_A_2_1_3_3 : Spec.A k9 [2, 1, 3, 3] = 5148795635180339123 :=
  Correct.A_of_list k9 [1, 3, 3] _ k9s_P_1_3_3 2 (by decide)

theorem k9s_A_3_1_3_3 : Spec.A k9 [3, 1, 3, 3] = 5453011541181669471 :=
  Correct.A_of_list k9 [1, 3, 3] _ k9s_P_1_3_3 3 (by decide)

end Results
