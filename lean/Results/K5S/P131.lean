/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 3, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_3_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 3, 1]))
      = [1825368797116719, 1869051223056023, 1952223556056856, 2194387921437551] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 3, 1]]; native_decide

theorem k5s_A_0_1_3_1 : Spec.A k5 [0, 1, 3, 1] = 1825368797116719 :=
  Correct.A_of_list k5 [1, 3, 1] _ k5s_P_1_3_1 0 (by decide)

theorem k5s_A_1_1_3_1 : Spec.A k5 [1, 1, 3, 1] = 1869051223056023 :=
  Correct.A_of_list k5 [1, 3, 1] _ k5s_P_1_3_1 1 (by decide)

theorem k5s_A_2_1_3_1 : Spec.A k5 [2, 1, 3, 1] = 1952223556056856 :=
  Correct.A_of_list k5 [1, 3, 1] _ k5s_P_1_3_1 2 (by decide)

theorem k5s_A_3_1_3_1 : Spec.A k5 [3, 1, 3, 1] = 2194387921437551 :=
  Correct.A_of_list k5 [1, 3, 1] _ k5s_P_1_3_1 3 (by decide)

end Results
