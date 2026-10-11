/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_1_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 1, 2]))
      = [4172905041905149804, 4235732976031976055, 4346663538698184080, 4659315696100018852] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 1, 2]]; native_decide

theorem k9s_A_0_1_1_2 : Spec.A k9 [0, 1, 1, 2] = 4172905041905149804 :=
  Correct.A_of_list k9 [1, 1, 2] _ k9s_P_1_1_2 0 (by decide)

theorem k9s_A_1_1_1_2 : Spec.A k9 [1, 1, 1, 2] = 4235732976031976055 :=
  Correct.A_of_list k9 [1, 1, 2] _ k9s_P_1_1_2 1 (by decide)

theorem k9s_A_2_1_1_2 : Spec.A k9 [2, 1, 1, 2] = 4346663538698184080 :=
  Correct.A_of_list k9 [1, 1, 2] _ k9s_P_1_1_2 2 (by decide)

theorem k9s_A_3_1_1_2 : Spec.A k9 [3, 1, 1, 2] = 4659315696100018852 :=
  Correct.A_of_list k9 [1, 1, 2] _ k9s_P_1_1_2 3 (by decide)

end Results
