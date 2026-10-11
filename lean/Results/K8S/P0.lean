/-
One piece of the evaluation for `k8` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k8s_P_0 :
    (List.range (m k8)).map (fun g1 => Spec.A k8 (g1 :: [0]))
      = [568273626724957733, 579104800847496960, 598563575843554789, 652444375969107769] := by
  rw [← Correct.AofShared_eq_A k8 0 64 [0]]; native_decide

theorem k8s_A_0_0 : Spec.A k8 [0, 0] = 568273626724957733 :=
  Correct.A_of_list k8 [0] _ k8s_P_0 0 (by decide)

theorem k8s_A_1_0 : Spec.A k8 [1, 0] = 579104800847496960 :=
  Correct.A_of_list k8 [0] _ k8s_P_0 1 (by decide)

theorem k8s_A_2_0 : Spec.A k8 [2, 0] = 598563575843554789 :=
  Correct.A_of_list k8 [0] _ k8s_P_0 2 (by decide)

theorem k8s_A_3_0 : Spec.A k8 [3, 0] = 652444375969107769 :=
  Correct.A_of_list k8 [0] _ k8s_P_0 3 (by decide)

end Results
