/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 3, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_3_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 3, 0]))
      = [4878136381453321213, 4918327197147017128, 5007903281655390432, 5296743284554083062] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 3, 0]]; native_decide

theorem k9s_A_0_3_3_0 : Spec.A k9 [0, 3, 3, 0] = 4878136381453321213 :=
  Correct.A_of_list k9 [3, 3, 0] _ k9s_P_3_3_0 0 (by decide)

theorem k9s_A_1_3_3_0 : Spec.A k9 [1, 3, 3, 0] = 4918327197147017128 :=
  Correct.A_of_list k9 [3, 3, 0] _ k9s_P_3_3_0 1 (by decide)

theorem k9s_A_2_3_3_0 : Spec.A k9 [2, 3, 3, 0] = 5007903281655390432 :=
  Correct.A_of_list k9 [3, 3, 0] _ k9s_P_3_3_0 2 (by decide)

theorem k9s_A_3_3_3_0 : Spec.A k9 [3, 3, 3, 0] = 5296743284554083062 :=
  Correct.A_of_list k9 [3, 3, 0] _ k9s_P_3_3_0 3 (by decide)

end Results
