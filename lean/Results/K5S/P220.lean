/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 2, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_2_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 2, 0]))
      = [1597805400750621, 1637001969166783, 1715402061187358, 1951804113155782] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 2, 0]]; native_decide

theorem k5s_A_0_2_2_0 : Spec.A k5 [0, 2, 2, 0] = 1597805400750621 :=
  Correct.A_of_list k5 [2, 2, 0] _ k5s_P_2_2_0 0 (by decide)

theorem k5s_A_1_2_2_0 : Spec.A k5 [1, 2, 2, 0] = 1637001969166783 :=
  Correct.A_of_list k5 [2, 2, 0] _ k5s_P_2_2_0 1 (by decide)

theorem k5s_A_2_2_2_0 : Spec.A k5 [2, 2, 2, 0] = 1715402061187358 :=
  Correct.A_of_list k5 [2, 2, 0] _ k5s_P_2_2_0 2 (by decide)

theorem k5s_A_3_2_2_0 : Spec.A k5 [3, 2, 2, 0] = 1951804113155782 :=
  Correct.A_of_list k5 [2, 2, 0] _ k5s_P_2_2_0 3 (by decide)

end Results
