/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 0, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_0_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 0, 2]))
      = [1860890060035878, 1895518279646523, 1970654035360873, 2204857898432707] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 0, 2]]; native_decide

theorem k5s_A_0_3_0_2 : Spec.A k5 [0, 3, 0, 2] = 1860890060035878 :=
  Correct.A_of_list k5 [3, 0, 2] _ k5s_P_3_0_2 0 (by decide)

theorem k5s_A_1_3_0_2 : Spec.A k5 [1, 3, 0, 2] = 1895518279646523 :=
  Correct.A_of_list k5 [3, 0, 2] _ k5s_P_3_0_2 1 (by decide)

theorem k5s_A_2_3_0_2 : Spec.A k5 [2, 3, 0, 2] = 1970654035360873 :=
  Correct.A_of_list k5 [3, 0, 2] _ k5s_P_3_0_2 2 (by decide)

theorem k5s_A_3_3_0_2 : Spec.A k5 [3, 3, 0, 2] = 2204857898432707 :=
  Correct.A_of_list k5 [3, 0, 2] _ k5s_P_3_0_2 3 (by decide)

end Results
