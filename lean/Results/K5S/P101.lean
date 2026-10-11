/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 0, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_0_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 0, 1]))
      = [1322844495258585, 1375105215383815, 1465578252035119, 1715018711946628] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 0, 1]]; native_decide

theorem k5s_A_0_1_0_1 : Spec.A k5 [0, 1, 0, 1] = 1322844495258585 :=
  Correct.A_of_list k5 [1, 0, 1] _ k5s_P_1_0_1 0 (by decide)

theorem k5s_A_1_1_0_1 : Spec.A k5 [1, 1, 0, 1] = 1375105215383815 :=
  Correct.A_of_list k5 [1, 0, 1] _ k5s_P_1_0_1 1 (by decide)

theorem k5s_A_2_1_0_1 : Spec.A k5 [2, 1, 0, 1] = 1465578252035119 :=
  Correct.A_of_list k5 [1, 0, 1] _ k5s_P_1_0_1 2 (by decide)

theorem k5s_A_3_1_0_1 : Spec.A k5 [3, 1, 0, 1] = 1715018711946628 :=
  Correct.A_of_list k5 [1, 0, 1] _ k5s_P_1_0_1 3 (by decide)

end Results
