/-
One piece of the evaluation for `k7` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k7s_P_0 :
    (List.range (m k7)).map (fun g1 => Spec.A k7 (g1 :: [0]))
      = [81979461003020301, 83783620494564571, 87024621763306514, 95999800209169200] := by
  rw [← Correct.AofShared_eq_A k7 0 64 [0]]; native_decide

theorem k7s_A_0_0 : Spec.A k7 [0, 0] = 81979461003020301 :=
  Correct.A_of_list k7 [0] _ k7s_P_0 0 (by decide)

theorem k7s_A_1_0 : Spec.A k7 [1, 0] = 83783620494564571 :=
  Correct.A_of_list k7 [0] _ k7s_P_0 1 (by decide)

theorem k7s_A_2_0 : Spec.A k7 [2, 0] = 87024621763306514 :=
  Correct.A_of_list k7 [0] _ k7s_P_0 2 (by decide)

theorem k7s_A_3_0 : Spec.A k7 [3, 0] = 95999800209169200 :=
  Correct.A_of_list k7 [0] _ k7s_P_0 3 (by decide)

end Results
