/-
One piece of the evaluation for `k7` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k7s_P_2 :
    (List.range (m k7)).map (fun g1 => Spec.A k7 (g1 :: [2]))
      = [89824721872373839, 91284682469147212, 94108691122742900, 102540574682687362] := by
  rw [← Correct.AofShared_eq_A k7 0 64 [2]]; native_decide

theorem k7s_A_0_2 : Spec.A k7 [0, 2] = 89824721872373839 :=
  Correct.A_of_list k7 [2] _ k7s_P_2 0 (by decide)

theorem k7s_A_1_2 : Spec.A k7 [1, 2] = 91284682469147212 :=
  Correct.A_of_list k7 [2] _ k7s_P_2 1 (by decide)

theorem k7s_A_2_2 : Spec.A k7 [2, 2] = 94108691122742900 :=
  Correct.A_of_list k7 [2] _ k7s_P_2 2 (by decide)

theorem k7s_A_3_2 : Spec.A k7 [3, 2] = 102540574682687362 :=
  Correct.A_of_list k7 [2] _ k7s_P_2 3 (by decide)

end Results
