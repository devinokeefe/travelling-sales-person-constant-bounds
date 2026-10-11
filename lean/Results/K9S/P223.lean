/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 2, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_2_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 2, 3]))
      = [4814676644148220309, 4864456563462188181, 4962403399787647910, 5260406751943207540] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 2, 3]]; native_decide

theorem k9s_A_0_2_2_3 : Spec.A k9 [0, 2, 2, 3] = 4814676644148220309 :=
  Correct.A_of_list k9 [2, 2, 3] _ k9s_P_2_2_3 0 (by decide)

theorem k9s_A_1_2_2_3 : Spec.A k9 [1, 2, 2, 3] = 4864456563462188181 :=
  Correct.A_of_list k9 [2, 2, 3] _ k9s_P_2_2_3 1 (by decide)

theorem k9s_A_2_2_2_3 : Spec.A k9 [2, 2, 2, 3] = 4962403399787647910 :=
  Correct.A_of_list k9 [2, 2, 3] _ k9s_P_2_2_3 2 (by decide)

theorem k9s_A_3_2_2_3 : Spec.A k9 [3, 2, 2, 3] = 5260406751943207540 :=
  Correct.A_of_list k9 [2, 2, 3] _ k9s_P_2_2_3 3 (by decide)

end Results
