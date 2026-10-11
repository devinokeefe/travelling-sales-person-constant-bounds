/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 2, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_2_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 2, 1]))
      = [1560393105478985, 1606422137754778, 1691486816319339, 1935378254055201] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 2, 1]]; native_decide

theorem k5s_A_0_1_2_1 : Spec.A k5 [0, 1, 2, 1] = 1560393105478985 :=
  Correct.A_of_list k5 [1, 2, 1] _ k5s_P_1_2_1 0 (by decide)

theorem k5s_A_1_1_2_1 : Spec.A k5 [1, 1, 2, 1] = 1606422137754778 :=
  Correct.A_of_list k5 [1, 2, 1] _ k5s_P_1_2_1 1 (by decide)

theorem k5s_A_2_1_2_1 : Spec.A k5 [2, 1, 2, 1] = 1691486816319339 :=
  Correct.A_of_list k5 [1, 2, 1] _ k5s_P_1_2_1 2 (by decide)

theorem k5s_A_3_1_2_1 : Spec.A k5 [3, 1, 2, 1] = 1935378254055201 :=
  Correct.A_of_list k5 [1, 2, 1] _ k5s_P_1_2_1 3 (by decide)

end Results
