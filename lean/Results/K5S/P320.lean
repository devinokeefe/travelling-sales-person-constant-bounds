/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 2, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_2_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 2, 0]))
      = [1850424791211667, 1884908145259695, 1960003310824335, 2194190961236177] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 2, 0]]; native_decide

theorem k5s_A_0_3_2_0 : Spec.A k5 [0, 3, 2, 0] = 1850424791211667 :=
  Correct.A_of_list k5 [3, 2, 0] _ k5s_P_3_2_0 0 (by decide)

theorem k5s_A_1_3_2_0 : Spec.A k5 [1, 3, 2, 0] = 1884908145259695 :=
  Correct.A_of_list k5 [3, 2, 0] _ k5s_P_3_2_0 1 (by decide)

theorem k5s_A_2_3_2_0 : Spec.A k5 [2, 3, 2, 0] = 1960003310824335 :=
  Correct.A_of_list k5 [3, 2, 0] _ k5s_P_3_2_0 2 (by decide)

theorem k5s_A_3_3_2_0 : Spec.A k5 [3, 3, 2, 0] = 2194190961236177 :=
  Correct.A_of_list k5 [3, 2, 0] _ k5s_P_3_2_0 3 (by decide)

end Results
