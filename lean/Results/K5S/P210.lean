/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_1_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 1, 0]))
      = [1469779859339522, 1511493884200509, 1592287421537190, 1831166140850301] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 1, 0]]; native_decide

theorem k5s_A_0_2_1_0 : Spec.A k5 [0, 2, 1, 0] = 1469779859339522 :=
  Correct.A_of_list k5 [2, 1, 0] _ k5s_P_2_1_0 0 (by decide)

theorem k5s_A_1_2_1_0 : Spec.A k5 [1, 2, 1, 0] = 1511493884200509 :=
  Correct.A_of_list k5 [2, 1, 0] _ k5s_P_2_1_0 1 (by decide)

theorem k5s_A_2_2_1_0 : Spec.A k5 [2, 2, 1, 0] = 1592287421537190 :=
  Correct.A_of_list k5 [2, 1, 0] _ k5s_P_2_1_0 2 (by decide)

theorem k5s_A_3_2_1_0 : Spec.A k5 [3, 2, 1, 0] = 1831166140850301 :=
  Correct.A_of_list k5 [2, 1, 0] _ k5s_P_2_1_0 3 (by decide)

end Results
