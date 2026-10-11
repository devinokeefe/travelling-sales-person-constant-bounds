/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 2, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_2_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 2, 3]))
      = [2015301074833837, 2054494607290173, 2133232196935881, 2370627798427456] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 2, 3]]; native_decide

theorem k5s_A_0_2_2_3 : Spec.A k5 [0, 2, 2, 3] = 2015301074833837 :=
  Correct.A_of_list k5 [2, 2, 3] _ k5s_P_2_2_3 0 (by decide)

theorem k5s_A_1_2_2_3 : Spec.A k5 [1, 2, 2, 3] = 2054494607290173 :=
  Correct.A_of_list k5 [2, 2, 3] _ k5s_P_2_2_3 1 (by decide)

theorem k5s_A_2_2_2_3 : Spec.A k5 [2, 2, 2, 3] = 2133232196935881 :=
  Correct.A_of_list k5 [2, 2, 3] _ k5s_P_2_2_3 2 (by decide)

theorem k5s_A_3_2_2_3 : Spec.A k5 [3, 2, 2, 3] = 2370627798427456 :=
  Correct.A_of_list k5 [2, 2, 3] _ k5s_P_2_2_3 3 (by decide)

end Results
