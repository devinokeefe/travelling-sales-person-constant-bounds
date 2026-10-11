/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 3, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_3_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 3, 2]))
      = [4583522293916805909, 4639211229693954946, 4746862525219024887, 5058450219262919317] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 3, 2]]; native_decide

theorem k9s_A_0_0_3_2 : Spec.A k9 [0, 0, 3, 2] = 4583522293916805909 :=
  Correct.A_of_list k9 [0, 3, 2] _ k9s_P_0_3_2 0 (by decide)

theorem k9s_A_1_0_3_2 : Spec.A k9 [1, 0, 3, 2] = 4639211229693954946 :=
  Correct.A_of_list k9 [0, 3, 2] _ k9s_P_0_3_2 1 (by decide)

theorem k9s_A_2_0_3_2 : Spec.A k9 [2, 0, 3, 2] = 4746862525219024887 :=
  Correct.A_of_list k9 [0, 3, 2] _ k9s_P_0_3_2 2 (by decide)

theorem k9s_A_3_0_3_2 : Spec.A k9 [3, 0, 3, 2] = 5058450219262919317 :=
  Correct.A_of_list k9 [0, 3, 2] _ k9s_P_0_3_2 3 (by decide)

end Results
