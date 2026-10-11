/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 2, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_2_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 2, 0]))
      = [1481984533952931, 1529123238162176, 1615251605281110, 1859889577998341] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 2, 0]]; native_decide

theorem k5s_A_0_1_2_0 : Spec.A k5 [0, 1, 2, 0] = 1481984533952931 :=
  Correct.A_of_list k5 [1, 2, 0] _ k5s_P_1_2_0 0 (by decide)

theorem k5s_A_1_1_2_0 : Spec.A k5 [1, 1, 2, 0] = 1529123238162176 :=
  Correct.A_of_list k5 [1, 2, 0] _ k5s_P_1_2_0 1 (by decide)

theorem k5s_A_2_1_2_0 : Spec.A k5 [2, 1, 2, 0] = 1615251605281110 :=
  Correct.A_of_list k5 [1, 2, 0] _ k5s_P_1_2_0 2 (by decide)

theorem k5s_A_3_1_2_0 : Spec.A k5 [3, 1, 2, 0] = 1859889577998341 :=
  Correct.A_of_list k5 [1, 2, 0] _ k5s_P_1_2_0 3 (by decide)

end Results
