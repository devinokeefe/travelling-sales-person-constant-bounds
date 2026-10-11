/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 3, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_3_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 3, 0]))
      = [1685082407757532, 1731818781506290, 1820050767701444, 2069087034917438] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 3, 0]]; native_decide

theorem k5s_A_0_0_3_0 : Spec.A k5 [0, 0, 3, 0] = 1685082407757532 :=
  Correct.A_of_list k5 [0, 3, 0] _ k5s_P_0_3_0 0 (by decide)

theorem k5s_A_1_0_3_0 : Spec.A k5 [1, 0, 3, 0] = 1731818781506290 :=
  Correct.A_of_list k5 [0, 3, 0] _ k5s_P_0_3_0 1 (by decide)

theorem k5s_A_2_0_3_0 : Spec.A k5 [2, 0, 3, 0] = 1820050767701444 :=
  Correct.A_of_list k5 [0, 3, 0] _ k5s_P_0_3_0 2 (by decide)

theorem k5s_A_3_0_3_0 : Spec.A k5 [3, 0, 3, 0] = 2069087034917438 :=
  Correct.A_of_list k5 [0, 3, 0] _ k5s_P_0_3_0 3 (by decide)

end Results
