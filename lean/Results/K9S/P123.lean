/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 2, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_2_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 2, 3]))
      = [4669630287656572384, 4726414420783820483, 4832045256831674317, 5139002644694662803] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 2, 3]]; native_decide

theorem k9s_A_0_1_2_3 : Spec.A k9 [0, 1, 2, 3] = 4669630287656572384 :=
  Correct.A_of_list k9 [1, 2, 3] _ k9s_P_1_2_3 0 (by decide)

theorem k9s_A_1_1_2_3 : Spec.A k9 [1, 1, 2, 3] = 4726414420783820483 :=
  Correct.A_of_list k9 [1, 2, 3] _ k9s_P_1_2_3 1 (by decide)

theorem k9s_A_2_1_2_3 : Spec.A k9 [2, 1, 2, 3] = 4832045256831674317 :=
  Correct.A_of_list k9 [1, 2, 3] _ k9s_P_1_2_3 2 (by decide)

theorem k9s_A_3_1_2_3 : Spec.A k9 [3, 1, 2, 3] = 5139002644694662803 :=
  Correct.A_of_list k9 [1, 2, 3] _ k9s_P_1_2_3 3 (by decide)

end Results
