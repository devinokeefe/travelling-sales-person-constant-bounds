/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_1_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 1, 1]))
      = [4524066225138861897, 4564553445727432504, 4654275225857719304, 4943209182193573210] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 1, 1]]; native_decide

theorem k9s_A_0_3_1_1 : Spec.A k9 [0, 3, 1, 1] = 4524066225138861897 :=
  Correct.A_of_list k9 [3, 1, 1] _ k9s_P_3_1_1 0 (by decide)

theorem k9s_A_1_3_1_1 : Spec.A k9 [1, 3, 1, 1] = 4564553445727432504 :=
  Correct.A_of_list k9 [3, 1, 1] _ k9s_P_3_1_1 1 (by decide)

theorem k9s_A_2_3_1_1 : Spec.A k9 [2, 3, 1, 1] = 4654275225857719304 :=
  Correct.A_of_list k9 [3, 1, 1] _ k9s_P_3_1_1 2 (by decide)

theorem k9s_A_3_3_1_1 : Spec.A k9 [3, 3, 1, 1] = 4943209182193573210 :=
  Correct.A_of_list k9 [3, 1, 1] _ k9s_P_3_1_1 3 (by decide)

end Results
