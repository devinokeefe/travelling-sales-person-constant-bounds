/-
One piece of the evaluation for `k8` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k8s_P_1 :
    (List.range (m k8)).map (fun g1 => Spec.A k8 (g1 :: [1]))
      = [588095994177266409, 598521617449355668, 617175333547216685, 669787912978070825] := by
  rw [← Correct.AofShared_eq_A k8 0 64 [1]]; native_decide

theorem k8s_A_0_1 : Spec.A k8 [0, 1] = 588095994177266409 :=
  Correct.A_of_list k8 [1] _ k8s_P_1 0 (by decide)

theorem k8s_A_1_1 : Spec.A k8 [1, 1] = 598521617449355668 :=
  Correct.A_of_list k8 [1] _ k8s_P_1 1 (by decide)

theorem k8s_A_2_1 : Spec.A k8 [2, 1] = 617175333547216685 :=
  Correct.A_of_list k8 [1] _ k8s_P_1 2 (by decide)

theorem k8s_A_3_1 : Spec.A k8 [3, 1] = 669787912978070825 :=
  Correct.A_of_list k8 [1] _ k8s_P_1 3 (by decide)

end Results
