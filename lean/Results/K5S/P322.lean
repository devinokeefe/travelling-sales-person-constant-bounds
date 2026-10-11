/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 2, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_2_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 2, 2]))
      = [2020669334791647, 2055180430351210, 2130275595915851, 2364463246327692] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 2, 2]]; native_decide

theorem k5s_A_0_3_2_2 : Spec.A k5 [0, 3, 2, 2] = 2020669334791647 :=
  Correct.A_of_list k5 [3, 2, 2] _ k5s_P_3_2_2 0 (by decide)

theorem k5s_A_1_3_2_2 : Spec.A k5 [1, 3, 2, 2] = 2055180430351210 :=
  Correct.A_of_list k5 [3, 2, 2] _ k5s_P_3_2_2 1 (by decide)

theorem k5s_A_2_3_2_2 : Spec.A k5 [2, 3, 2, 2] = 2130275595915851 :=
  Correct.A_of_list k5 [3, 2, 2] _ k5s_P_3_2_2 2 (by decide)

theorem k5s_A_3_3_2_2 : Spec.A k5 [3, 3, 2, 2] = 2364463246327692 :=
  Correct.A_of_list k5 [3, 2, 2] _ k5s_P_3_2_2 3 (by decide)

end Results
