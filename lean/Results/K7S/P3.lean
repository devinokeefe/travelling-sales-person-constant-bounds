/-
One piece of the evaluation for `k7` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k7s_P_3 :
    (List.range (m k7)).map (fun g1 => Spec.A k7 (g1 :: [3]))
      = [99328726430602459, 100509654084779895, 103104954259639154, 111333144555530177] := by
  rw [← Correct.AofShared_eq_A k7 0 64 [3]]; native_decide

theorem k7s_A_0_3 : Spec.A k7 [0, 3] = 99328726430602459 :=
  Correct.A_of_list k7 [3] _ k7s_P_3 0 (by decide)

theorem k7s_A_1_3 : Spec.A k7 [1, 3] = 100509654084779895 :=
  Correct.A_of_list k7 [3] _ k7s_P_3 1 (by decide)

theorem k7s_A_2_3 : Spec.A k7 [2, 3] = 103104954259639154 :=
  Correct.A_of_list k7 [3] _ k7s_P_3 2 (by decide)

theorem k7s_A_3_3 : Spec.A k7 [3, 3] = 111333144555530177 :=
  Correct.A_of_list k7 [3] _ k7s_P_3 3 (by decide)

end Results
