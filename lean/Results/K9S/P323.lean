/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 2, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_2_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 2, 3]))
      = [5144472124189597744, 5185111106375847366, 5275103491527277870, 5564120906693175065] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 2, 3]]; native_decide

theorem k9s_A_0_3_2_3 : Spec.A k9 [0, 3, 2, 3] = 5144472124189597744 :=
  Correct.A_of_list k9 [3, 2, 3] _ k9s_P_3_2_3 0 (by decide)

theorem k9s_A_1_3_2_3 : Spec.A k9 [1, 3, 2, 3] = 5185111106375847366 :=
  Correct.A_of_list k9 [3, 2, 3] _ k9s_P_3_2_3 1 (by decide)

theorem k9s_A_2_3_2_3 : Spec.A k9 [2, 3, 2, 3] = 5275103491527277870 :=
  Correct.A_of_list k9 [3, 2, 3] _ k9s_P_3_2_3 2 (by decide)

theorem k9s_A_3_3_2_3 : Spec.A k9 [3, 3, 2, 3] = 5564120906693175065 :=
  Correct.A_of_list k9 [3, 2, 3] _ k9s_P_3_2_3 3 (by decide)

end Results
