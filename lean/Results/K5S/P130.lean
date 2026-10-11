/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 3, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_3_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 3, 0]))
      = [1758134801775140, 1801816412036733, 1884970759419151, 2127207246291116] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 3, 0]]; native_decide

theorem k5s_A_0_1_3_0 : Spec.A k5 [0, 1, 3, 0] = 1758134801775140 :=
  Correct.A_of_list k5 [1, 3, 0] _ k5s_P_1_3_0 0 (by decide)

theorem k5s_A_1_1_3_0 : Spec.A k5 [1, 1, 3, 0] = 1801816412036733 :=
  Correct.A_of_list k5 [1, 3, 0] _ k5s_P_1_3_0 1 (by decide)

theorem k5s_A_2_1_3_0 : Spec.A k5 [2, 1, 3, 0] = 1884970759419151 :=
  Correct.A_of_list k5 [1, 3, 0] _ k5s_P_1_3_0 2 (by decide)

theorem k5s_A_3_1_3_0 : Spec.A k5 [3, 1, 3, 0] = 2127207246291116 :=
  Correct.A_of_list k5 [1, 3, 0] _ k5s_P_1_3_0 3 (by decide)

end Results
