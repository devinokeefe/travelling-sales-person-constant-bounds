/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 1, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_1_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 1, 3]))
      = [1803600581338889, 1851440144313805, 1938323183044769, 2183973717207022] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 1, 3]]; native_decide

theorem k5s_A_0_1_1_3 : Spec.A k5 [0, 1, 1, 3] = 1803600581338889 :=
  Correct.A_of_list k5 [1, 1, 3] _ k5s_P_1_1_3 0 (by decide)

theorem k5s_A_1_1_1_3 : Spec.A k5 [1, 1, 1, 3] = 1851440144313805 :=
  Correct.A_of_list k5 [1, 1, 3] _ k5s_P_1_1_3 1 (by decide)

theorem k5s_A_2_1_1_3 : Spec.A k5 [2, 1, 1, 3] = 1938323183044769 :=
  Correct.A_of_list k5 [1, 1, 3] _ k5s_P_1_1_3 2 (by decide)

theorem k5s_A_3_1_1_3 : Spec.A k5 [3, 1, 1, 3] = 2183973717207022 :=
  Correct.A_of_list k5 [1, 1, 3] _ k5s_P_1_1_3 3 (by decide)

end Results
