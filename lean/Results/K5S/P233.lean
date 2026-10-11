/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 3, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_3_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 3, 3]))
      = [2257095419515794, 2294887421271378, 2372578457066203, 2608696797480788] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 3, 3]]; native_decide

theorem k5s_A_0_2_3_3 : Spec.A k5 [0, 2, 3, 3] = 2257095419515794 :=
  Correct.A_of_list k5 [2, 3, 3] _ k5s_P_2_3_3 0 (by decide)

theorem k5s_A_1_2_3_3 : Spec.A k5 [1, 2, 3, 3] = 2294887421271378 :=
  Correct.A_of_list k5 [2, 3, 3] _ k5s_P_2_3_3 1 (by decide)

theorem k5s_A_2_2_3_3 : Spec.A k5 [2, 2, 3, 3] = 2372578457066203 :=
  Correct.A_of_list k5 [2, 3, 3] _ k5s_P_2_3_3 2 (by decide)

theorem k5s_A_3_2_3_3 : Spec.A k5 [3, 2, 3, 3] = 2608696797480788 :=
  Correct.A_of_list k5 [2, 3, 3] _ k5s_P_2_3_3 3 (by decide)

end Results
