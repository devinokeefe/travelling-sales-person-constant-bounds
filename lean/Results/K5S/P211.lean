/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_2_1_1 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [2, 1, 1]))
      = [1556624369124986, 1597613571234380, 1677631997883368, 1915580251258714] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [2, 1, 1]]; native_decide

theorem k5s_A_0_2_1_1 : Spec.A k5 [0, 2, 1, 1] = 1556624369124986 :=
  Correct.A_of_list k5 [2, 1, 1] _ k5s_P_2_1_1 0 (by decide)

theorem k5s_A_1_2_1_1 : Spec.A k5 [1, 2, 1, 1] = 1597613571234380 :=
  Correct.A_of_list k5 [2, 1, 1] _ k5s_P_2_1_1 1 (by decide)

theorem k5s_A_2_2_1_1 : Spec.A k5 [2, 2, 1, 1] = 1677631997883368 :=
  Correct.A_of_list k5 [2, 1, 1] _ k5s_P_2_1_1 2 (by decide)

theorem k5s_A_3_2_1_1 : Spec.A k5 [3, 2, 1, 1] = 1915580251258714 :=
  Correct.A_of_list k5 [2, 1, 1] _ k5s_P_2_1_1 3 (by decide)

end Results
