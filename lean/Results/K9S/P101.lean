/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 0, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_0_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 0, 1]))
      = [3831192628041506773, 3899750879518985892, 4016831585513051179, 4336827851035402174] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 0, 1]]; native_decide

theorem k9s_A_0_1_0_1 : Spec.A k9 [0, 1, 0, 1] = 3831192628041506773 :=
  Correct.A_of_list k9 [1, 0, 1] _ k9s_P_1_0_1 0 (by decide)

theorem k9s_A_1_1_0_1 : Spec.A k9 [1, 1, 0, 1] = 3899750879518985892 :=
  Correct.A_of_list k9 [1, 0, 1] _ k9s_P_1_0_1 1 (by decide)

theorem k9s_A_2_1_0_1 : Spec.A k9 [2, 1, 0, 1] = 4016831585513051179 :=
  Correct.A_of_list k9 [1, 0, 1] _ k9s_P_1_0_1 2 (by decide)

theorem k9s_A_3_1_0_1 : Spec.A k9 [3, 1, 0, 1] = 4336827851035402174 :=
  Correct.A_of_list k9 [1, 0, 1] _ k9s_P_1_0_1 3 (by decide)

end Results
