/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 3, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_3_3 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 3, 3]))
      = [2084773089843641, 2131295096037521, 2219215686834234, 2467487987294899] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 3, 3]]; native_decide

theorem k5s_A_0_0_3_3 : Spec.A k5 [0, 0, 3, 3] = 2084773089843641 :=
  Correct.A_of_list k5 [0, 3, 3] _ k5s_P_0_3_3 0 (by decide)

theorem k5s_A_1_0_3_3 : Spec.A k5 [1, 0, 3, 3] = 2131295096037521 :=
  Correct.A_of_list k5 [0, 3, 3] _ k5s_P_0_3_3 1 (by decide)

theorem k5s_A_2_0_3_3 : Spec.A k5 [2, 0, 3, 3] = 2219215686834234 :=
  Correct.A_of_list k5 [0, 3, 3] _ k5s_P_0_3_3 2 (by decide)

theorem k5s_A_3_0_3_3 : Spec.A k5 [3, 0, 3, 3] = 2467487987294899 :=
  Correct.A_of_list k5 [0, 3, 3] _ k5s_P_0_3_3 3 (by decide)

end Results
