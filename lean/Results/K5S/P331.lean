/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 3, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_3_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 3, 1]))
      = [2167928150830590, 2202398995827486, 2277494161392127, 2511681811803969] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 3, 1]]; native_decide

theorem k5s_A_0_3_3_1 : Spec.A k5 [0, 3, 3, 1] = 2167928150830590 :=
  Correct.A_of_list k5 [3, 3, 1] _ k5s_P_3_3_1 0 (by decide)

theorem k5s_A_1_3_3_1 : Spec.A k5 [1, 3, 3, 1] = 2202398995827486 :=
  Correct.A_of_list k5 [3, 3, 1] _ k5s_P_3_3_1 1 (by decide)

theorem k5s_A_2_3_3_1 : Spec.A k5 [2, 3, 3, 1] = 2277494161392127 :=
  Correct.A_of_list k5 [3, 3, 1] _ k5s_P_3_3_1 2 (by decide)

theorem k5s_A_3_3_3_1 : Spec.A k5 [3, 3, 3, 1] = 2511681811803969 :=
  Correct.A_of_list k5 [3, 3, 1] _ k5s_P_3_3_1 3 (by decide)

end Results
