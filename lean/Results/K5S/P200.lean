/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 0, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_0_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 0, 0]))
      = [1365772269073884, 1410649842599856, 1494440959316383, 1736890799550810] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 0, 0]]; native_decide

theorem k5s_A_0_2_0_0 : Spec.A k5 [0, 2, 0, 0] = 1365772269073884 :=
  Correct.A_of_list k5 [2, 0, 0] _ k5s_P_2_0_0 0 (by decide)

theorem k5s_A_1_2_0_0 : Spec.A k5 [1, 2, 0, 0] = 1410649842599856 :=
  Correct.A_of_list k5 [2, 0, 0] _ k5s_P_2_0_0 1 (by decide)

theorem k5s_A_2_2_0_0 : Spec.A k5 [2, 2, 0, 0] = 1494440959316383 :=
  Correct.A_of_list k5 [2, 0, 0] _ k5s_P_2_0_0 2 (by decide)

theorem k5s_A_3_2_0_0 : Spec.A k5 [3, 2, 0, 0] = 1736890799550810 :=
  Correct.A_of_list k5 [2, 0, 0] _ k5s_P_2_0_0 3 (by decide)

end Results
