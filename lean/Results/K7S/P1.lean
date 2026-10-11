/-
One piece of the evaluation for `k7` by the routine of `TSPShared/Impl.lean`: the values
`A_2(g_1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k7s_P_1 :
    (List.range (m k7)).map (fun g1 => Spec.A k7 (g1 :: [1]))
      = [85281560812081318, 87019685609216215, 90128893306977555, 98898064873812567] := by
  rw [← Correct.AofShared_eq_A k7 0 64 [1]]; native_decide

theorem k7s_A_0_1 : Spec.A k7 [0, 1] = 85281560812081318 :=
  Correct.A_of_list k7 [1] _ k7s_P_1 0 (by decide)

theorem k7s_A_1_1 : Spec.A k7 [1, 1] = 87019685609216215 :=
  Correct.A_of_list k7 [1] _ k7s_P_1 1 (by decide)

theorem k7s_A_2_1 : Spec.A k7 [2, 1] = 90128893306977555 :=
  Correct.A_of_list k7 [1] _ k7s_P_1 2 (by decide)

theorem k7s_A_3_1 : Spec.A k7 [3, 1] = 98898064873812567 :=
  Correct.A_of_list k7 [1] _ k7s_P_1 3 (by decide)

end Results
