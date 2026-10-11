/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 2, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_2_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 2, 1]))
      = [1921569709949180, 1956063140569994, 2031158306134635, 2265345956546476] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 2, 1]]; native_decide

theorem k5s_A_0_3_2_1 : Spec.A k5 [0, 3, 2, 1] = 1921569709949180 :=
  Correct.A_of_list k5 [3, 2, 1] _ k5s_P_3_2_1 0 (by decide)

theorem k5s_A_1_3_2_1 : Spec.A k5 [1, 3, 2, 1] = 1956063140569994 :=
  Correct.A_of_list k5 [3, 2, 1] _ k5s_P_3_2_1 1 (by decide)

theorem k5s_A_2_3_2_1 : Spec.A k5 [2, 3, 2, 1] = 2031158306134635 :=
  Correct.A_of_list k5 [3, 2, 1] _ k5s_P_3_2_1 2 (by decide)

theorem k5s_A_3_3_2_1 : Spec.A k5 [3, 3, 2, 1] = 2265345956546476 :=
  Correct.A_of_list k5 [3, 2, 1] _ k5s_P_3_2_1 3 (by decide)

end Results
