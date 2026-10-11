/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 0, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_0_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 0, 3]))
      = [2123392691630100, 2158035877855902, 2233187551482011, 2467386150831128] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 0, 3]]; native_decide

theorem k5s_A_0_3_0_3 : Spec.A k5 [0, 3, 0, 3] = 2123392691630100 :=
  Correct.A_of_list k5 [3, 0, 3] _ k5s_P_3_0_3 0 (by decide)

theorem k5s_A_1_3_0_3 : Spec.A k5 [1, 3, 0, 3] = 2158035877855902 :=
  Correct.A_of_list k5 [3, 0, 3] _ k5s_P_3_0_3 1 (by decide)

theorem k5s_A_2_3_0_3 : Spec.A k5 [2, 3, 0, 3] = 2233187551482011 :=
  Correct.A_of_list k5 [3, 0, 3] _ k5s_P_3_0_3 2 (by decide)

theorem k5s_A_3_3_0_3 : Spec.A k5 [3, 3, 0, 3] = 2467386150831128 :=
  Correct.A_of_list k5 [3, 0, 3] _ k5s_P_3_0_3 3 (by decide)

end Results
