/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_1_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 1, 0]))
      = [4022629051456750788, 4077066604108346535, 4178815308900202316, 4478980845008039741] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 1, 0]]; native_decide

theorem k9s_A_0_2_1_0 : Spec.A k9 [0, 2, 1, 0] = 4022629051456750788 :=
  Correct.A_of_list k9 [2, 1, 0] _ k9s_P_2_1_0 0 (by decide)

theorem k9s_A_1_2_1_0 : Spec.A k9 [1, 2, 1, 0] = 4077066604108346535 :=
  Correct.A_of_list k9 [2, 1, 0] _ k9s_P_2_1_0 1 (by decide)

theorem k9s_A_2_2_1_0 : Spec.A k9 [2, 2, 1, 0] = 4178815308900202316 :=
  Correct.A_of_list k9 [2, 1, 0] _ k9s_P_2_1_0 2 (by decide)

theorem k9s_A_3_2_1_0 : Spec.A k9 [3, 2, 1, 0] = 4478980845008039741 :=
  Correct.A_of_list k9 [2, 1, 0] _ k9s_P_2_1_0 3 (by decide)

end Results
