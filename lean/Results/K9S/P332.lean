/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 3, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_3_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 3, 2]))
      = [5122309241288749645, 5162568419529851805, 5252218930022432175, 5541058932921124805] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 3, 2]]; native_decide

theorem k9s_A_0_3_3_2 : Spec.A k9 [0, 3, 3, 2] = 5122309241288749645 :=
  Correct.A_of_list k9 [3, 3, 2] _ k9s_P_3_3_2 0 (by decide)

theorem k9s_A_1_3_3_2 : Spec.A k9 [1, 3, 3, 2] = 5162568419529851805 :=
  Correct.A_of_list k9 [3, 3, 2] _ k9s_P_3_3_2 1 (by decide)

theorem k9s_A_2_3_3_2 : Spec.A k9 [2, 3, 3, 2] = 5252218930022432175 :=
  Correct.A_of_list k9 [3, 3, 2] _ k9s_P_3_3_2 2 (by decide)

theorem k9s_A_3_3_3_2 : Spec.A k9 [3, 3, 3, 2] = 5541058932921124805 :=
  Correct.A_of_list k9 [3, 3, 2] _ k9s_P_3_3_2 3 (by decide)

end Results
