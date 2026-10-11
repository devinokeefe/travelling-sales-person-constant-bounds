/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 0, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_0_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 0, 0]))
      = [3661890020817969413, 3732175285428107787, 3850915215842282762, 4173020801662153761] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 0, 0]]; native_decide

theorem k9s_A_0_1_0_0 : Spec.A k9 [0, 1, 0, 0] = 3661890020817969413 :=
  Correct.A_of_list k9 [1, 0, 0] _ k9s_P_1_0_0 0 (by decide)

theorem k9s_A_1_1_0_0 : Spec.A k9 [1, 1, 0, 0] = 3732175285428107787 :=
  Correct.A_of_list k9 [1, 0, 0] _ k9s_P_1_0_0 1 (by decide)

theorem k9s_A_2_1_0_0 : Spec.A k9 [2, 1, 0, 0] = 3850915215842282762 :=
  Correct.A_of_list k9 [1, 0, 0] _ k9s_P_1_0_0 2 (by decide)

theorem k9s_A_3_1_0_0 : Spec.A k9 [3, 1, 0, 0] = 4173020801662153761 :=
  Correct.A_of_list k9 [1, 0, 0] _ k9s_P_1_0_0 3 (by decide)

end Results
