/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 1, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_1_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 1, 3]))
      = [1717600488629652, 1767526092067971, 1857832296250593, 2108170676194828] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 1, 3]]; native_decide

theorem k5s_A_0_0_1_3 : Spec.A k5 [0, 0, 1, 3] = 1717600488629652 :=
  Correct.A_of_list k5 [0, 1, 3] _ k5s_P_0_1_3 0 (by decide)

theorem k5s_A_1_0_1_3 : Spec.A k5 [1, 0, 1, 3] = 1767526092067971 :=
  Correct.A_of_list k5 [0, 1, 3] _ k5s_P_0_1_3 1 (by decide)

theorem k5s_A_2_0_1_3 : Spec.A k5 [2, 0, 1, 3] = 1857832296250593 :=
  Correct.A_of_list k5 [0, 1, 3] _ k5s_P_0_1_3 2 (by decide)

theorem k5s_A_3_0_1_3 : Spec.A k5 [3, 0, 1, 3] = 2108170676194828 :=
  Correct.A_of_list k5 [0, 1, 3] _ k5s_P_0_1_3 3 (by decide)

end Results
