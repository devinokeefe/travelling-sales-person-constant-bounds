/-
One piece of the evaluation for `k6` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k6s_P_0 :
    (List.range (m k6)).map (fun g1 => Spec.A k6 (g1 :: [0]))
      = [10924631223287195, 11231415334948327, 11780328691848360, 13291203959747565] := by
  rw [← Correct.AofShared_eq_A k6 0 64 [0]]; native_decide

theorem k6s_A_0_0 : Spec.A k6 [0, 0] = 10924631223287195 :=
  Correct.A_of_list k6 [0] _ k6s_P_0 0 (by decide)

theorem k6s_A_1_0 : Spec.A k6 [1, 0] = 11231415334948327 :=
  Correct.A_of_list k6 [0] _ k6s_P_0 1 (by decide)

theorem k6s_A_2_0 : Spec.A k6 [2, 0] = 11780328691848360 :=
  Correct.A_of_list k6 [0] _ k6s_P_0 2 (by decide)

theorem k6s_A_3_0 : Spec.A k6 [3, 0] = 13291203959747565 :=
  Correct.A_of_list k6 [0] _ k6s_P_0 3 (by decide)

end Results
