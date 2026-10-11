/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 2, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_2_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 2, 1]))
      = [1477839255725465, 1527228816331795, 1616867145064704, 1867269728077790] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 2, 1]]; native_decide

theorem k5s_A_0_0_2_1 : Spec.A k5 [0, 0, 2, 1] = 1477839255725465 :=
  Correct.A_of_list k5 [0, 2, 1] _ k5s_P_0_2_1 0 (by decide)

theorem k5s_A_1_0_2_1 : Spec.A k5 [1, 0, 2, 1] = 1527228816331795 :=
  Correct.A_of_list k5 [0, 2, 1] _ k5s_P_0_2_1 1 (by decide)

theorem k5s_A_2_0_2_1 : Spec.A k5 [2, 0, 2, 1] = 1616867145064704 :=
  Correct.A_of_list k5 [0, 2, 1] _ k5s_P_0_2_1 2 (by decide)

theorem k5s_A_3_0_2_1 : Spec.A k5 [3, 0, 2, 1] = 1867269728077790 :=
  Correct.A_of_list k5 [0, 2, 1] _ k5s_P_0_2_1 3 (by decide)

end Results
