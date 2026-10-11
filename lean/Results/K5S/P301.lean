/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 0, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_0_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 0, 1]))
      = [1739383672913297, 1774027420487100, 1849160181274676, 2083359028034297] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 0, 1]]; native_decide

theorem k5s_A_0_3_0_1 : Spec.A k5 [0, 3, 0, 1] = 1739383672913297 :=
  Correct.A_of_list k5 [3, 0, 1] _ k5s_P_3_0_1 0 (by decide)

theorem k5s_A_1_3_0_1 : Spec.A k5 [1, 3, 0, 1] = 1774027420487100 :=
  Correct.A_of_list k5 [3, 0, 1] _ k5s_P_3_0_1 1 (by decide)

theorem k5s_A_2_3_0_1 : Spec.A k5 [2, 3, 0, 1] = 1849160181274676 :=
  Correct.A_of_list k5 [3, 0, 1] _ k5s_P_3_0_1 2 (by decide)

theorem k5s_A_3_3_0_1 : Spec.A k5 [3, 3, 0, 1] = 2083359028034297 :=
  Correct.A_of_list k5 [3, 0, 1] _ k5s_P_3_0_1 3 (by decide)

end Results
