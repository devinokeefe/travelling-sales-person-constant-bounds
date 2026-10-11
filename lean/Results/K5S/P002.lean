/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 0, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_0_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 0, 2]))
      = [1354750095030426, 1407359311561692, 1500034937844638, 1752665403959632] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 0, 2]]; native_decide

theorem k5s_A_0_0_0_2 : Spec.A k5 [0, 0, 0, 2] = 1354750095030426 :=
  Correct.A_of_list k5 [0, 0, 2] _ k5s_P_0_0_2 0 (by decide)

theorem k5s_A_1_0_0_2 : Spec.A k5 [1, 0, 0, 2] = 1407359311561692 :=
  Correct.A_of_list k5 [0, 0, 2] _ k5s_P_0_0_2 1 (by decide)

theorem k5s_A_2_0_0_2 : Spec.A k5 [2, 0, 0, 2] = 1500034937844638 :=
  Correct.A_of_list k5 [0, 0, 2] _ k5s_P_0_0_2 2 (by decide)

theorem k5s_A_3_0_0_2 : Spec.A k5 [3, 0, 0, 2] = 1752665403959632 :=
  Correct.A_of_list k5 [0, 0, 2] _ k5s_P_0_0_2 3 (by decide)

end Results
