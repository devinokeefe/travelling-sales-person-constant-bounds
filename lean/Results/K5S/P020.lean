/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 2, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_2_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 2, 0]))
      = [1394205253186787, 1445022166490720, 1536303582694035, 1788487015034713] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 2, 0]]; native_decide

theorem k5s_A_0_0_2_0 : Spec.A k5 [0, 0, 2, 0] = 1394205253186787 :=
  Correct.A_of_list k5 [0, 2, 0] _ k5s_P_0_2_0 0 (by decide)

theorem k5s_A_1_0_2_0 : Spec.A k5 [1, 0, 2, 0] = 1445022166490720 :=
  Correct.A_of_list k5 [0, 2, 0] _ k5s_P_0_2_0 1 (by decide)

theorem k5s_A_2_0_2_0 : Spec.A k5 [2, 0, 2, 0] = 1536303582694035 :=
  Correct.A_of_list k5 [0, 2, 0] _ k5s_P_0_2_0 2 (by decide)

theorem k5s_A_3_0_2_0 : Spec.A k5 [3, 0, 2, 0] = 1788487015034713 :=
  Correct.A_of_list k5 [0, 2, 0] _ k5s_P_0_2_0 3 (by decide)

end Results
