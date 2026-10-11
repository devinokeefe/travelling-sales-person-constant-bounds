/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 2, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_2_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 2, 2]))
      = [1663322082775009, 1708597471483072, 1792969723804804, 2036478767134406] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 2, 2]]; native_decide

theorem k5s_A_0_1_2_2 : Spec.A k5 [0, 1, 2, 2] = 1663322082775009 :=
  Correct.A_of_list k5 [1, 2, 2] _ k5s_P_1_2_2 0 (by decide)

theorem k5s_A_1_1_2_2 : Spec.A k5 [1, 1, 2, 2] = 1708597471483072 :=
  Correct.A_of_list k5 [1, 2, 2] _ k5s_P_1_2_2 1 (by decide)

theorem k5s_A_2_1_2_2 : Spec.A k5 [2, 1, 2, 2] = 1792969723804804 :=
  Correct.A_of_list k5 [1, 2, 2] _ k5s_P_1_2_2 2 (by decide)

theorem k5s_A_3_1_2_2 : Spec.A k5 [3, 1, 2, 2] = 2036478767134406 :=
  Correct.A_of_list k5 [1, 2, 2] _ k5s_P_1_2_2 3 (by decide)

end Results
