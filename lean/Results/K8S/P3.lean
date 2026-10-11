/-
One piece of the evaluation for `k8` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k8s_P_3 :
    (List.range (m k8)).map (fun g1 => Spec.A k8 (g1 :: [3]))
      = [672294378470616322, 679377868392256100, 694948698166673744, 744317543041174092] := by
  rw [← Correct.AofShared_eq_A k8 0 64 [3]]; native_decide

theorem k8s_A_0_3 : Spec.A k8 [0, 3] = 672294378470616322 :=
  Correct.A_of_list k8 [3] _ k8s_P_3 0 (by decide)

theorem k8s_A_1_3 : Spec.A k8 [1, 3] = 679377868392256100 :=
  Correct.A_of_list k8 [3] _ k8s_P_3 1 (by decide)

theorem k8s_A_2_3 : Spec.A k8 [2, 3] = 694948698166673744 :=
  Correct.A_of_list k8 [3] _ k8s_P_3 2 (by decide)

theorem k8s_A_3_3 : Spec.A k8 [3, 3] = 744317543041174092 :=
  Correct.A_of_list k8 [3] _ k8s_P_3 3 (by decide)

end Results
