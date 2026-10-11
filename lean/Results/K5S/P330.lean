/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 3, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_3_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 3, 0]))
      = [2101175588432566, 2135646433429462, 2210741598994102, 2444929249405944] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 3, 0]]; native_decide

theorem k5s_A_0_3_3_0 : Spec.A k5 [0, 3, 3, 0] = 2101175588432566 :=
  Correct.A_of_list k5 [3, 3, 0] _ k5s_P_3_3_0 0 (by decide)

theorem k5s_A_1_3_3_0 : Spec.A k5 [1, 3, 3, 0] = 2135646433429462 :=
  Correct.A_of_list k5 [3, 3, 0] _ k5s_P_3_3_0 1 (by decide)

theorem k5s_A_2_3_3_0 : Spec.A k5 [2, 3, 3, 0] = 2210741598994102 :=
  Correct.A_of_list k5 [3, 3, 0] _ k5s_P_3_3_0 2 (by decide)

theorem k5s_A_3_3_3_0 : Spec.A k5 [3, 3, 3, 0] = 2444929249405944 :=
  Correct.A_of_list k5 [3, 3, 0] _ k5s_P_3_3_0 3 (by decide)

end Results
