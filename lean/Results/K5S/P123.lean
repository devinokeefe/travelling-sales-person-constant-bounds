/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 2, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_2_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 2, 3]))
      = [1909146222285147, 1953786627487175, 2037722285005659, 2280869868796462] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 2, 3]]; native_decide

theorem k5s_A_0_1_2_3 : Spec.A k5 [0, 1, 2, 3] = 1909146222285147 :=
  Correct.A_of_list k5 [1, 2, 3] _ k5s_P_1_2_3 0 (by decide)

theorem k5s_A_1_1_2_3 : Spec.A k5 [1, 1, 2, 3] = 1953786627487175 :=
  Correct.A_of_list k5 [1, 2, 3] _ k5s_P_1_2_3 1 (by decide)

theorem k5s_A_2_1_2_3 : Spec.A k5 [2, 1, 2, 3] = 2037722285005659 :=
  Correct.A_of_list k5 [1, 2, 3] _ k5s_P_1_2_3 2 (by decide)

theorem k5s_A_3_1_2_3 : Spec.A k5 [3, 1, 2, 3] = 2280869868796462 :=
  Correct.A_of_list k5 [1, 2, 3] _ k5s_P_1_2_3 3 (by decide)

end Results
