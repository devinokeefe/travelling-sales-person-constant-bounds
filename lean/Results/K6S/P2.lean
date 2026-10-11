/-
One piece of the evaluation for `k6` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k6s_P_2 :
    (List.range (m k6)).map (fun g1 => Spec.A k6 (g1 :: [2]))
      = [12198349404618991, 12442122627019056, 12920642013469075, 14347792078815327] := by
  rw [← Correct.AofShared_eq_A k6 0 64 [2]]; native_decide

theorem k6s_A_0_2 : Spec.A k6 [0, 2] = 12198349404618991 :=
  Correct.A_of_list k6 [2] _ k6s_P_2 0 (by decide)

theorem k6s_A_1_2 : Spec.A k6 [1, 2] = 12442122627019056 :=
  Correct.A_of_list k6 [2] _ k6s_P_2 1 (by decide)

theorem k6s_A_2_2 : Spec.A k6 [2, 2] = 12920642013469075 :=
  Correct.A_of_list k6 [2] _ k6s_P_2 2 (by decide)

theorem k6s_A_3_2 : Spec.A k6 [3, 2] = 14347792078815327 :=
  Correct.A_of_list k6 [2] _ k6s_P_2 3 (by decide)

end Results
