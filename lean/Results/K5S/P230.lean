/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 3, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_3_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 3, 0]))
      = [1858710374457704, 1896462918371615, 1974053064163178, 2210066473370446] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 3, 0]]; native_decide

theorem k5s_A_0_2_3_0 : Spec.A k5 [0, 2, 3, 0] = 1858710374457704 :=
  Correct.A_of_list k5 [2, 3, 0] _ k5s_P_2_3_0 0 (by decide)

theorem k5s_A_1_2_3_0 : Spec.A k5 [1, 2, 3, 0] = 1896462918371615 :=
  Correct.A_of_list k5 [2, 3, 0] _ k5s_P_2_3_0 1 (by decide)

theorem k5s_A_2_2_3_0 : Spec.A k5 [2, 2, 3, 0] = 1974053064163178 :=
  Correct.A_of_list k5 [2, 3, 0] _ k5s_P_2_3_0 2 (by decide)

theorem k5s_A_3_2_3_0 : Spec.A k5 [3, 2, 3, 0] = 2210066473370446 :=
  Correct.A_of_list k5 [2, 3, 0] _ k5s_P_2_3_0 3 (by decide)

end Results
