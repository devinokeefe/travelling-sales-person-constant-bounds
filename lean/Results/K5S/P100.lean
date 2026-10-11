/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 0, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_0_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 0, 0]))
      = [1223824147898818, 1276118637361203, 1366748749086605, 1616709039484067] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 0, 0]]; native_decide

theorem k5s_A_0_1_0_0 : Spec.A k5 [0, 1, 0, 0] = 1223824147898818 :=
  Correct.A_of_list k5 [1, 0, 0] _ k5s_P_1_0_0 0 (by decide)

theorem k5s_A_1_1_0_0 : Spec.A k5 [1, 1, 0, 0] = 1276118637361203 :=
  Correct.A_of_list k5 [1, 0, 0] _ k5s_P_1_0_0 1 (by decide)

theorem k5s_A_2_1_0_0 : Spec.A k5 [2, 1, 0, 0] = 1366748749086605 :=
  Correct.A_of_list k5 [1, 0, 0] _ k5s_P_1_0_0 2 (by decide)

theorem k5s_A_3_1_0_0 : Spec.A k5 [3, 1, 0, 0] = 1616709039484067 :=
  Correct.A_of_list k5 [1, 0, 0] _ k5s_P_1_0_0 3 (by decide)

end Results
