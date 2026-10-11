/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 3, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_3_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 3, 1]))
      = [1925778803942379, 1963457291835654, 2040980527866701, 2276895642571828] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 3, 1]]; native_decide

theorem k5s_A_0_2_3_1 : Spec.A k5 [0, 2, 3, 1] = 1925778803942379 :=
  Correct.A_of_list k5 [2, 3, 1] _ k5s_P_2_3_1 0 (by decide)

theorem k5s_A_1_2_3_1 : Spec.A k5 [1, 2, 3, 1] = 1963457291835654 :=
  Correct.A_of_list k5 [2, 3, 1] _ k5s_P_2_3_1 1 (by decide)

theorem k5s_A_2_2_3_1 : Spec.A k5 [2, 2, 3, 1] = 2040980527866701 :=
  Correct.A_of_list k5 [2, 3, 1] _ k5s_P_2_3_1 2 (by decide)

theorem k5s_A_3_2_3_1 : Spec.A k5 [3, 2, 3, 1] = 2276895642571828 :=
  Correct.A_of_list k5 [2, 3, 1] _ k5s_P_2_3_1 3 (by decide)

end Results
