/-
One piece of the evaluation for `k6` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k6s_P_1 :
    (List.range (m k6)).map (fun g1 => Spec.A k6 (g1 :: [1]))
      = [11466206318087604, 11757193394463477, 12280707821748347, 13757065197141819] := by
  rw [← Correct.AofShared_eq_A k6 0 64 [1]]; native_decide

theorem k6s_A_0_1 : Spec.A k6 [0, 1] = 11466206318087604 :=
  Correct.A_of_list k6 [1] _ k6s_P_1 0 (by decide)

theorem k6s_A_1_1 : Spec.A k6 [1, 1] = 11757193394463477 :=
  Correct.A_of_list k6 [1] _ k6s_P_1 1 (by decide)

theorem k6s_A_2_1 : Spec.A k6 [2, 1] = 12280707821748347 :=
  Correct.A_of_list k6 [1] _ k6s_P_1 2 (by decide)

theorem k6s_A_3_1 : Spec.A k6 [3, 1] = 13757065197141819 :=
  Correct.A_of_list k6 [1] _ k6s_P_1 3 (by decide)

end Results
