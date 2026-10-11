/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_1_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 1, 2]))
      = [4051161365113884455, 4115262406535313031, 4230285049522856412, 4549900134398232129] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 1, 2]]; native_decide

theorem k9s_A_0_0_1_2 : Spec.A k9 [0, 0, 1, 2] = 4051161365113884455 :=
  Correct.A_of_list k9 [0, 1, 2] _ k9s_P_0_1_2 0 (by decide)

theorem k9s_A_1_0_1_2 : Spec.A k9 [1, 0, 1, 2] = 4115262406535313031 :=
  Correct.A_of_list k9 [0, 1, 2] _ k9s_P_0_1_2 1 (by decide)

theorem k9s_A_2_0_1_2 : Spec.A k9 [2, 0, 1, 2] = 4230285049522856412 :=
  Correct.A_of_list k9 [0, 1, 2] _ k9s_P_0_1_2 2 (by decide)

theorem k9s_A_3_0_1_2 : Spec.A k9 [3, 0, 1, 2] = 4549900134398232129 :=
  Correct.A_of_list k9 [0, 1, 2] _ k9s_P_0_1_2 3 (by decide)

end Results
