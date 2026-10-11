/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 2, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_2_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 2, 1]))
      = [4182064669047148959, 4240877925660314461, 4348315418521209971, 4657267771807893409] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 2, 1]]; native_decide

theorem k9s_A_0_1_2_1 : Spec.A k9 [0, 1, 2, 1] = 4182064669047148959 :=
  Correct.A_of_list k9 [1, 2, 1] _ k9s_P_1_2_1 0 (by decide)

theorem k9s_A_1_1_2_1 : Spec.A k9 [1, 1, 2, 1] = 4240877925660314461 :=
  Correct.A_of_list k9 [1, 2, 1] _ k9s_P_1_2_1 1 (by decide)

theorem k9s_A_2_1_2_1 : Spec.A k9 [2, 1, 2, 1] = 4348315418521209971 :=
  Correct.A_of_list k9 [1, 2, 1] _ k9s_P_1_2_1 2 (by decide)

theorem k9s_A_3_1_2_1 : Spec.A k9 [3, 1, 2, 1] = 4657267771807893409 :=
  Correct.A_of_list k9 [1, 2, 1] _ k9s_P_1_2_1 3 (by decide)

end Results
