/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 3, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_3_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 3, 2]))
      = [1918127123948211, 1961757427054427, 2044884210159817, 2287021176651661] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 3, 2]]; native_decide

theorem k5s_A_0_1_3_2 : Spec.A k5 [0, 1, 3, 2] = 1918127123948211 :=
  Correct.A_of_list k5 [1, 3, 2] _ k5s_P_1_3_2 0 (by decide)

theorem k5s_A_1_1_3_2 : Spec.A k5 [1, 1, 3, 2] = 1961757427054427 :=
  Correct.A_of_list k5 [1, 3, 2] _ k5s_P_1_3_2 1 (by decide)

theorem k5s_A_2_1_3_2 : Spec.A k5 [2, 1, 3, 2] = 2044884210159817 :=
  Correct.A_of_list k5 [1, 3, 2] _ k5s_P_1_3_2 2 (by decide)

theorem k5s_A_3_1_3_2 : Spec.A k5 [3, 1, 3, 2] = 2287021176651661 :=
  Correct.A_of_list k5 [1, 3, 2] _ k5s_P_1_3_2 3 (by decide)

end Results
