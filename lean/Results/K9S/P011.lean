/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_1_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 1, 1]))
      = [3857056258535001182, 3924422043383070347, 4042495207074475537, 4365613460666631718] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 1, 1]]; native_decide

theorem k9s_A_0_0_1_1 : Spec.A k9 [0, 0, 1, 1] = 3857056258535001182 :=
  Correct.A_of_list k9 [0, 1, 1] _ k9s_P_0_1_1 0 (by decide)

theorem k9s_A_1_0_1_1 : Spec.A k9 [1, 0, 1, 1] = 3924422043383070347 :=
  Correct.A_of_list k9 [0, 1, 1] _ k9s_P_0_1_1 1 (by decide)

theorem k9s_A_2_0_1_1 : Spec.A k9 [2, 0, 1, 1] = 4042495207074475537 :=
  Correct.A_of_list k9 [0, 1, 1] _ k9s_P_0_1_1 2 (by decide)

theorem k9s_A_3_0_1_1 : Spec.A k9 [3, 0, 1, 1] = 4365613460666631718 :=
  Correct.A_of_list k9 [0, 1, 1] _ k9s_P_0_1_1 3 (by decide)

end Results
