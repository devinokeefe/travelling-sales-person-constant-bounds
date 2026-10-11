/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_1_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 1, 1]))
      = [4168745297562702167, 4222032682743828399, 4322678647715841431, 4621790850405358003] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 1, 1]]; native_decide

theorem k9s_A_0_2_1_1 : Spec.A k9 [0, 2, 1, 1] = 4168745297562702167 :=
  Correct.A_of_list k9 [2, 1, 1] _ k9s_P_2_1_1 0 (by decide)

theorem k9s_A_1_2_1_1 : Spec.A k9 [1, 2, 1, 1] = 4222032682743828399 :=
  Correct.A_of_list k9 [2, 1, 1] _ k9s_P_2_1_1 1 (by decide)

theorem k9s_A_2_2_1_1 : Spec.A k9 [2, 2, 1, 1] = 4322678647715841431 :=
  Correct.A_of_list k9 [2, 1, 1] _ k9s_P_2_1_1 2 (by decide)

theorem k9s_A_3_2_1_1 : Spec.A k9 [3, 2, 1, 1] = 4621790850405358003 :=
  Correct.A_of_list k9 [2, 1, 1] _ k9s_P_2_1_1 3 (by decide)

end Results
