/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 2, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_2_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 2, 2]))
      = [4487213797524234882, 4536887151169528469, 4634753361833467556, 4931868783540260447] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 2, 2]]; native_decide

theorem k9s_A_0_2_2_2 : Spec.A k9 [0, 2, 2, 2] = 4487213797524234882 :=
  Correct.A_of_list k9 [2, 2, 2] _ k9s_P_2_2_2 0 (by decide)

theorem k9s_A_1_2_2_2 : Spec.A k9 [1, 2, 2, 2] = 4536887151169528469 :=
  Correct.A_of_list k9 [2, 2, 2] _ k9s_P_2_2_2 1 (by decide)

theorem k9s_A_2_2_2_2 : Spec.A k9 [2, 2, 2, 2] = 4634753361833467556 :=
  Correct.A_of_list k9 [2, 2, 2] _ k9s_P_2_2_2 2 (by decide)

theorem k9s_A_3_2_2_2 : Spec.A k9 [3, 2, 2, 2] = 4931868783540260447 :=
  Correct.A_of_list k9 [2, 2, 2] _ k9s_P_2_2_2 3 (by decide)

end Results
