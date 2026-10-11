/-
One piece of the evaluation for `k8` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k8s_P_2 :
    (List.range (m k8)).map (fun g1 => Spec.A k8 (g1 :: [2]))
      = [615334704174186517, 624081897596963510, 641010879847966918, 691578329411084145] := by
  rw [← Correct.AofShared_eq_A k8 0 64 [2]]; native_decide

theorem k8s_A_0_2 : Spec.A k8 [0, 2] = 615334704174186517 :=
  Correct.A_of_list k8 [2] _ k8s_P_2 0 (by decide)

theorem k8s_A_1_2 : Spec.A k8 [1, 2] = 624081897596963510 :=
  Correct.A_of_list k8 [2] _ k8s_P_2 1 (by decide)

theorem k8s_A_2_2 : Spec.A k8 [2, 2] = 641010879847966918 :=
  Correct.A_of_list k8 [2] _ k8s_P_2 2 (by decide)

theorem k8s_A_3_2 : Spec.A k8 [3, 2] = 691578329411084145 :=
  Correct.A_of_list k8 [2] _ k8s_P_2 3 (by decide)

end Results
