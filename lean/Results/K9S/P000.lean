/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 0, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_0_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 0, 0]))
      = [3516643664015913165, 3587066576551658530, 3708343134946999366, 4035679182105898288] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 0, 0]]; native_decide

theorem k9s_A_0_0_0_0 : Spec.A k9 [0, 0, 0, 0] = 3516643664015913165 :=
  Correct.A_of_list k9 [0, 0, 0] _ k9s_P_0_0_0 0 (by decide)

theorem k9s_A_1_0_0_0 : Spec.A k9 [1, 0, 0, 0] = 3587066576551658530 :=
  Correct.A_of_list k9 [0, 0, 0] _ k9s_P_0_0_0 1 (by decide)

theorem k9s_A_2_0_0_0 : Spec.A k9 [2, 0, 0, 0] = 3708343134946999366 :=
  Correct.A_of_list k9 [0, 0, 0] _ k9s_P_0_0_0 2 (by decide)

theorem k9s_A_3_0_0_0 : Spec.A k9 [3, 0, 0, 0] = 4035679182105898288 :=
  Correct.A_of_list k9 [0, 0, 0] _ k9s_P_0_0_0 3 (by decide)

end Results
