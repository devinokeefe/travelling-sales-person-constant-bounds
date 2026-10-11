/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 0, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_0_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 0, 2]))
      = [4037557398943992516, 4103717982558510374, 4218655294948685733, 4536609105148458916] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 0, 2]]; native_decide

theorem k9s_A_0_1_0_2 : Spec.A k9 [0, 1, 0, 2] = 4037557398943992516 :=
  Correct.A_of_list k9 [1, 0, 2] _ k9s_P_1_0_2 0 (by decide)

theorem k9s_A_1_1_0_2 : Spec.A k9 [1, 1, 0, 2] = 4103717982558510374 :=
  Correct.A_of_list k9 [1, 0, 2] _ k9s_P_1_0_2 1 (by decide)

theorem k9s_A_2_1_0_2 : Spec.A k9 [2, 1, 0, 2] = 4218655294948685733 :=
  Correct.A_of_list k9 [1, 0, 2] _ k9s_P_1_0_2 2 (by decide)

theorem k9s_A_3_1_0_2 : Spec.A k9 [3, 1, 0, 2] = 4536609105148458916 :=
  Correct.A_of_list k9 [1, 0, 2] _ k9s_P_1_0_2 3 (by decide)

end Results
