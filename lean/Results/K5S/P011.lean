/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_1_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 1, 1]))
      = [1333851497633091, 1386457293478038, 1479018569665471, 1731396690872696] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 1, 1]]; native_decide

theorem k5s_A_0_0_1_1 : Spec.A k5 [0, 0, 1, 1] = 1333851497633091 :=
  Correct.A_of_list k5 [0, 1, 1] _ k5s_P_0_1_1 0 (by decide)

theorem k5s_A_1_0_1_1 : Spec.A k5 [1, 0, 1, 1] = 1386457293478038 :=
  Correct.A_of_list k5 [0, 1, 1] _ k5s_P_0_1_1 1 (by decide)

theorem k5s_A_2_0_1_1 : Spec.A k5 [2, 0, 1, 1] = 1479018569665471 :=
  Correct.A_of_list k5 [0, 1, 1] _ k5s_P_0_1_1 2 (by decide)

theorem k5s_A_3_0_1_1 : Spec.A k5 [3, 0, 1, 1] = 1731396690872696 :=
  Correct.A_of_list k5 [0, 1, 1] _ k5s_P_0_1_1 3 (by decide)

end Results
