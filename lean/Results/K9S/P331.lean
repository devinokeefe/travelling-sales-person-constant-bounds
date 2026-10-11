/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 3, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_3_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 3, 1]))
      = [4986418352252185506, 5026632146948706910, 5116234266740552272, 5405074269639244902] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 3, 1]]; native_decide

theorem k9s_A_0_3_3_1 : Spec.A k9 [0, 3, 3, 1] = 4986418352252185506 :=
  Correct.A_of_list k9 [3, 3, 1] _ k9s_P_3_3_1 0 (by decide)

theorem k9s_A_1_3_3_1 : Spec.A k9 [1, 3, 3, 1] = 5026632146948706910 :=
  Correct.A_of_list k9 [3, 3, 1] _ k9s_P_3_3_1 1 (by decide)

theorem k9s_A_2_3_3_1 : Spec.A k9 [2, 3, 3, 1] = 5116234266740552272 :=
  Correct.A_of_list k9 [3, 3, 1] _ k9s_P_3_3_1 2 (by decide)

theorem k9s_A_3_3_3_1 : Spec.A k9 [3, 3, 3, 1] = 5405074269639244902 :=
  Correct.A_of_list k9 [3, 3, 1] _ k9s_P_3_3_1 3 (by decide)

end Results
