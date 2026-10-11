/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 2, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_2_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 2, 2]))
      = [1585313821319056, 1633280218703360, 1721480009787843, 1969963862687782] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 2, 2]]; native_decide

theorem k5s_A_0_0_2_2 : Spec.A k5 [0, 0, 2, 2] = 1585313821319056 :=
  Correct.A_of_list k5 [0, 2, 2] _ k5s_P_0_2_2 0 (by decide)

theorem k5s_A_1_0_2_2 : Spec.A k5 [1, 0, 2, 2] = 1633280218703360 :=
  Correct.A_of_list k5 [0, 2, 2] _ k5s_P_0_2_2 1 (by decide)

theorem k5s_A_2_0_2_2 : Spec.A k5 [2, 0, 2, 2] = 1721480009787843 :=
  Correct.A_of_list k5 [0, 2, 2] _ k5s_P_0_2_2 2 (by decide)

theorem k5s_A_3_0_2_2 : Spec.A k5 [3, 0, 2, 2] = 1969963862687782 :=
  Correct.A_of_list k5 [0, 2, 2] _ k5s_P_0_2_2 3 (by decide)

end Results
