/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_1_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 1, 2]))
      = [1546774206203801, 1595388446762149, 1682847716166882, 1928452960952293] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 1, 2]]; native_decide

theorem k5s_A_0_1_1_2 : Spec.A k5 [0, 1, 1, 2] = 1546774206203801 :=
  Correct.A_of_list k5 [1, 1, 2] _ k5s_P_1_1_2 0 (by decide)

theorem k5s_A_1_1_1_2 : Spec.A k5 [1, 1, 1, 2] = 1595388446762149 :=
  Correct.A_of_list k5 [1, 1, 2] _ k5s_P_1_1_2 1 (by decide)

theorem k5s_A_2_1_1_2 : Spec.A k5 [2, 1, 1, 2] = 1682847716166882 :=
  Correct.A_of_list k5 [1, 1, 2] _ k5s_P_1_1_2 2 (by decide)

theorem k5s_A_3_1_1_2 : Spec.A k5 [3, 1, 1, 2] = 1928452960952293 :=
  Correct.A_of_list k5 [1, 1, 2] _ k5s_P_1_1_2 3 (by decide)

end Results
