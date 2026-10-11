/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_3_1_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [3, 1, 0]))
      = [1737710968577392, 1772221148243246, 1847329620433402, 2081517270845244] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [3, 1, 0]]; native_decide

theorem k5s_A_0_3_1_0 : Spec.A k5 [0, 3, 1, 0] = 1737710968577392 :=
  Correct.A_of_list k5 [3, 1, 0] _ k5s_P_3_1_0 0 (by decide)

theorem k5s_A_1_3_1_0 : Spec.A k5 [1, 3, 1, 0] = 1772221148243246 :=
  Correct.A_of_list k5 [3, 1, 0] _ k5s_P_3_1_0 1 (by decide)

theorem k5s_A_2_3_1_0 : Spec.A k5 [2, 3, 1, 0] = 1847329620433402 :=
  Correct.A_of_list k5 [3, 1, 0] _ k5s_P_3_1_0 2 (by decide)

theorem k5s_A_3_3_1_0 : Spec.A k5 [3, 3, 1, 0] = 2081517270845244 :=
  Correct.A_of_list k5 [3, 1, 0] _ k5s_P_3_1_0 3 (by decide)

end Results
