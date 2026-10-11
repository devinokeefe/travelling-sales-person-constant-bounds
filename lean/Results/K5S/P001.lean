/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 0, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_0_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 0, 1]))
      = [1221561702625111, 1275132883917692, 1368024302318563, 1620230959256688] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 0, 1]]; native_decide

theorem k5s_A_0_0_0_1 : Spec.A k5 [0, 0, 0, 1] = 1221561702625111 :=
  Correct.A_of_list k5 [0, 0, 1] _ k5s_P_0_0_1 0 (by decide)

theorem k5s_A_1_0_0_1 : Spec.A k5 [1, 0, 0, 1] = 1275132883917692 :=
  Correct.A_of_list k5 [0, 0, 1] _ k5s_P_0_0_1 1 (by decide)

theorem k5s_A_2_0_0_1 : Spec.A k5 [2, 0, 0, 1] = 1368024302318563 :=
  Correct.A_of_list k5 [0, 0, 1] _ k5s_P_0_0_1 2 (by decide)

theorem k5s_A_3_0_0_1 : Spec.A k5 [3, 0, 0, 1] = 1620230959256688 :=
  Correct.A_of_list k5 [0, 0, 1] _ k5s_P_0_0_1 3 (by decide)

end Results
