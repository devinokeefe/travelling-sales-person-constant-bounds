/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 3, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_3_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 3, 1]))
      = [4674100895151770611, 4721432964673846356, 4817308812737282432, 5112116764013772991] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 3, 1]]; native_decide

theorem k9s_A_0_2_3_1 : Spec.A k9 [0, 2, 3, 1] = 4674100895151770611 :=
  Correct.A_of_list k9 [2, 3, 1] _ k9s_P_2_3_1 0 (by decide)

theorem k9s_A_1_2_3_1 : Spec.A k9 [1, 2, 3, 1] = 4721432964673846356 :=
  Correct.A_of_list k9 [2, 3, 1] _ k9s_P_2_3_1 1 (by decide)

theorem k9s_A_2_2_3_1 : Spec.A k9 [2, 2, 3, 1] = 4817308812737282432 :=
  Correct.A_of_list k9 [2, 3, 1] _ k9s_P_2_3_1 2 (by decide)

theorem k9s_A_3_2_3_1 : Spec.A k9 [3, 2, 3, 1] = 5112116764013772991 :=
  Correct.A_of_list k9 [2, 3, 1] _ k9s_P_2_3_1 3 (by decide)

end Results
