/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 2, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_2_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 2, 0]))
      = [4049587785828686099, 4110219686585706097, 4219376743986504991, 4529930252691115430] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 2, 0]]; native_decide

theorem k9s_A_0_1_2_0 : Spec.A k9 [0, 1, 2, 0] = 4049587785828686099 :=
  Correct.A_of_list k9 [1, 2, 0] _ k9s_P_1_2_0 0 (by decide)

theorem k9s_A_1_1_2_0 : Spec.A k9 [1, 1, 2, 0] = 4110219686585706097 :=
  Correct.A_of_list k9 [1, 2, 0] _ k9s_P_1_2_0 1 (by decide)

theorem k9s_A_2_1_2_0 : Spec.A k9 [2, 1, 2, 0] = 4219376743986504991 :=
  Correct.A_of_list k9 [1, 2, 0] _ k9s_P_1_2_0 2 (by decide)

theorem k9s_A_3_1_2_0 : Spec.A k9 [3, 1, 2, 0] = 4529930252691115430 :=
  Correct.A_of_list k9 [1, 2, 0] _ k9s_P_1_2_0 3 (by decide)

end Results
