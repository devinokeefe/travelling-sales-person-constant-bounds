/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 0, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_0_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 0, 3]))
      = [1719231709086670, 1770492047644526, 1859992458386807, 2108117505369126] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 0, 3]]; native_decide

theorem k5s_A_0_1_0_3 : Spec.A k5 [0, 1, 0, 3] = 1719231709086670 :=
  Correct.A_of_list k5 [1, 0, 3] _ k5s_P_1_0_3 0 (by decide)

theorem k5s_A_1_1_0_3 : Spec.A k5 [1, 1, 0, 3] = 1770492047644526 :=
  Correct.A_of_list k5 [1, 0, 3] _ k5s_P_1_0_3 1 (by decide)

theorem k5s_A_2_1_0_3 : Spec.A k5 [2, 1, 0, 3] = 1859992458386807 :=
  Correct.A_of_list k5 [1, 0, 3] _ k5s_P_1_0_3 2 (by decide)

theorem k5s_A_3_1_0_3 : Spec.A k5 [3, 1, 0, 3] = 2108117505369126 :=
  Correct.A_of_list k5 [1, 0, 3] _ k5s_P_1_0_3 3 (by decide)

end Results
