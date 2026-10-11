/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 3, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_3_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 3, 1]))
      = [1752557003014916, 1799287308595538, 1887549351718811, 2136658253795794] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 3, 1]]; native_decide

theorem k5s_A_0_0_3_1 : Spec.A k5 [0, 0, 3, 1] = 1752557003014916 :=
  Correct.A_of_list k5 [0, 3, 1] _ k5s_P_0_3_1 0 (by decide)

theorem k5s_A_1_0_3_1 : Spec.A k5 [1, 0, 3, 1] = 1799287308595538 :=
  Correct.A_of_list k5 [0, 3, 1] _ k5s_P_0_3_1 1 (by decide)

theorem k5s_A_2_0_3_1 : Spec.A k5 [2, 0, 3, 1] = 1887549351718811 :=
  Correct.A_of_list k5 [0, 3, 1] _ k5s_P_0_3_1 2 (by decide)

theorem k5s_A_3_0_3_1 : Spec.A k5 [3, 0, 3, 1] = 2136658253795794 :=
  Correct.A_of_list k5 [0, 3, 1] _ k5s_P_0_3_1 3 (by decide)

end Results
