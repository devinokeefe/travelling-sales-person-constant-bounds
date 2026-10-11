/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 3, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_3_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 3, 3]))
      = [2499872137299716, 2534342982296612, 2609438147861252, 2843625798273094] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 3, 3]]; native_decide

theorem k5s_A_0_3_3_3 : Spec.A k5 [0, 3, 3, 3] = 2499872137299716 :=
  Correct.A_of_list k5 [3, 3, 3] _ k5s_P_3_3_3 0 (by decide)

theorem k5s_A_1_3_3_3 : Spec.A k5 [1, 3, 3, 3] = 2534342982296612 :=
  Correct.A_of_list k5 [3, 3, 3] _ k5s_P_3_3_3 1 (by decide)

theorem k5s_A_2_3_3_3 : Spec.A k5 [2, 3, 3, 3] = 2609438147861252 :=
  Correct.A_of_list k5 [3, 3, 3] _ k5s_P_3_3_3 2 (by decide)

theorem k5s_A_3_3_3_3 : Spec.A k5 [3, 3, 3, 3] = 2843625798273094 :=
  Correct.A_of_list k5 [3, 3, 3] _ k5s_P_3_3_3 3 (by decide)

end Results
