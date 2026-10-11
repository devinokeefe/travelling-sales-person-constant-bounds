/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 0, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_0_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 0, 3]))
      = [4285919336573236285, 4348749515595198224, 4463746019734086610, 4784588875297117854] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 0, 3]]; native_decide

theorem k9s_A_0_0_0_3 : Spec.A k9 [0, 0, 0, 3] = 4285919336573236285 :=
  Correct.A_of_list k9 [0, 0, 3] _ k9s_P_0_0_3 0 (by decide)

theorem k9s_A_1_0_0_3 : Spec.A k9 [1, 0, 0, 3] = 4348749515595198224 :=
  Correct.A_of_list k9 [0, 0, 3] _ k9s_P_0_0_3 1 (by decide)

theorem k9s_A_2_0_0_3 : Spec.A k9 [2, 0, 0, 3] = 4463746019734086610 :=
  Correct.A_of_list k9 [0, 0, 3] _ k9s_P_0_0_3 2 (by decide)

theorem k9s_A_3_0_0_3 : Spec.A k9 [3, 0, 0, 3] = 4784588875297117854 :=
  Correct.A_of_list k9 [0, 0, 3] _ k9s_P_0_0_3 3 (by decide)

end Results
