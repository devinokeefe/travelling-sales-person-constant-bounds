/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 0, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_0_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 0, 3]))
      = [1624667705002728, 1676518559173037, 1769271834121198, 2022516380692383] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 0, 3]]; native_decide

theorem k5s_A_0_0_0_3 : Spec.A k5 [0, 0, 0, 3] = 1624667705002728 :=
  Correct.A_of_list k5 [0, 0, 3] _ k5s_P_0_0_3 0 (by decide)

theorem k5s_A_1_0_0_3 : Spec.A k5 [1, 0, 0, 3] = 1676518559173037 :=
  Correct.A_of_list k5 [0, 0, 3] _ k5s_P_0_0_3 1 (by decide)

theorem k5s_A_2_0_0_3 : Spec.A k5 [2, 0, 0, 3] = 1769271834121198 :=
  Correct.A_of_list k5 [0, 0, 3] _ k5s_P_0_0_3 2 (by decide)

theorem k5s_A_3_0_0_3 : Spec.A k5 [3, 0, 0, 3] = 2022516380692383 :=
  Correct.A_of_list k5 [0, 0, 3] _ k5s_P_0_0_3 3 (by decide)

end Results
