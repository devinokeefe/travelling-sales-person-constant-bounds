/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 0, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_0_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 0, 2]))
      = [1587622498891614, 1630625636201836, 1712350680149471, 1952083707018438] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 0, 2]]; native_decide

theorem k5s_A_0_2_0_2 : Spec.A k5 [0, 2, 0, 2] = 1587622498891614 :=
  Correct.A_of_list k5 [2, 0, 2] _ k5s_P_2_0_2 0 (by decide)

theorem k5s_A_1_2_0_2 : Spec.A k5 [1, 2, 0, 2] = 1630625636201836 :=
  Correct.A_of_list k5 [2, 0, 2] _ k5s_P_2_0_2 1 (by decide)

theorem k5s_A_2_2_0_2 : Spec.A k5 [2, 2, 0, 2] = 1712350680149471 :=
  Correct.A_of_list k5 [2, 0, 2] _ k5s_P_2_0_2 2 (by decide)

theorem k5s_A_3_2_0_2 : Spec.A k5 [3, 2, 0, 2] = 1952083707018438 :=
  Correct.A_of_list k5 [2, 0, 2] _ k5s_P_2_0_2 3 (by decide)

end Results
