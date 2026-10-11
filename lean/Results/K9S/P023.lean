/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 2, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_2_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 2, 3]))
      = [4569936050543699003, 4628078436332014676, 4736298385639602637, 5047603162766786393] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 2, 3]]; native_decide

theorem k9s_A_0_0_2_3 : Spec.A k9 [0, 0, 2, 3] = 4569936050543699003 :=
  Correct.A_of_list k9 [0, 2, 3] _ k9s_P_0_2_3 0 (by decide)

theorem k9s_A_1_0_2_3 : Spec.A k9 [1, 0, 2, 3] = 4628078436332014676 :=
  Correct.A_of_list k9 [0, 2, 3] _ k9s_P_0_2_3 1 (by decide)

theorem k9s_A_2_0_2_3 : Spec.A k9 [2, 0, 2, 3] = 4736298385639602637 :=
  Correct.A_of_list k9 [0, 2, 3] _ k9s_P_0_2_3 2 (by decide)

theorem k9s_A_3_0_2_3 : Spec.A k9 [3, 0, 2, 3] = 5047603162766786393 :=
  Correct.A_of_list k9 [0, 2, 3] _ k9s_P_0_2_3 3 (by decide)

end Results
