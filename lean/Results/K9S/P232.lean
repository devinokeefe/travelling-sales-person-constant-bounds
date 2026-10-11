/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 3, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_3_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 3, 2]))
      = [4808551740286909020, 4855964252930177657, 4952042579057532655, 5247275818508763927] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 3, 2]]; native_decide

theorem k9s_A_0_2_3_2 : Spec.A k9 [0, 2, 3, 2] = 4808551740286909020 :=
  Correct.A_of_list k9 [2, 3, 2] _ k9s_P_2_3_2 0 (by decide)

theorem k9s_A_1_2_3_2 : Spec.A k9 [1, 2, 3, 2] = 4855964252930177657 :=
  Correct.A_of_list k9 [2, 3, 2] _ k9s_P_2_3_2 1 (by decide)

theorem k9s_A_2_2_3_2 : Spec.A k9 [2, 2, 3, 2] = 4952042579057532655 :=
  Correct.A_of_list k9 [2, 3, 2] _ k9s_P_2_3_2 2 (by decide)

theorem k9s_A_3_2_3_2 : Spec.A k9 [3, 2, 3, 2] = 5247275818508763927 :=
  Correct.A_of_list k9 [2, 3, 2] _ k9s_P_2_3_2 3 (by decide)

end Results
