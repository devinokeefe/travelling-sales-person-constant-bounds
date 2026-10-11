/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 2, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_2_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 2, 2]))
      = [1771368573082605, 1810457033548801, 1889011571564309, 2125833213243495] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 2, 2]]; native_decide

theorem k5s_A_0_2_2_2 : Spec.A k5 [0, 2, 2, 2] = 1771368573082605 :=
  Correct.A_of_list k5 [2, 2, 2] _ k5s_P_2_2_2 0 (by decide)

theorem k5s_A_1_2_2_2 : Spec.A k5 [1, 2, 2, 2] = 1810457033548801 :=
  Correct.A_of_list k5 [2, 2, 2] _ k5s_P_2_2_2 1 (by decide)

theorem k5s_A_2_2_2_2 : Spec.A k5 [2, 2, 2, 2] = 1889011571564309 :=
  Correct.A_of_list k5 [2, 2, 2] _ k5s_P_2_2_2 2 (by decide)

theorem k5s_A_3_2_2_2 : Spec.A k5 [3, 2, 2, 2] = 2125833213243495 :=
  Correct.A_of_list k5 [2, 2, 2] _ k5s_P_2_2_2 3 (by decide)

end Results
