/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 0, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_0_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 0, 0]))
      = [1122927052217369, 1175279000784466, 1266806503974894, 1516511765353861] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 0, 0]]; native_decide

theorem k5s_A_0_0_0_0 : Spec.A k5 [0, 0, 0, 0] = 1122927052217369 :=
  Correct.A_of_list k5 [0, 0, 0] _ k5s_P_0_0_0 0 (by decide)

theorem k5s_A_1_0_0_0 : Spec.A k5 [1, 0, 0, 0] = 1175279000784466 :=
  Correct.A_of_list k5 [0, 0, 0] _ k5s_P_0_0_0 1 (by decide)

theorem k5s_A_2_0_0_0 : Spec.A k5 [2, 0, 0, 0] = 1266806503974894 :=
  Correct.A_of_list k5 [0, 0, 0] _ k5s_P_0_0_0 2 (by decide)

theorem k5s_A_3_0_0_0 : Spec.A k5 [3, 0, 0, 0] = 1516511765353861 :=
  Correct.A_of_list k5 [0, 0, 0] _ k5s_P_0_0_0 3 (by decide)

end Results
