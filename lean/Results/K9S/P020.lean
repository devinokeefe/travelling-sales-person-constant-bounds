/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 2, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_2_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 2, 0]))
      = [3928309035469041497, 3992419782365692913, 4107488422938303118, 4428200000404246970] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 2, 0]]; native_decide

theorem k9s_A_0_0_2_0 : Spec.A k9 [0, 0, 2, 0] = 3928309035469041497 :=
  Correct.A_of_list k9 [0, 2, 0] _ k9s_P_0_2_0 0 (by decide)

theorem k9s_A_1_0_2_0 : Spec.A k9 [1, 0, 2, 0] = 3992419782365692913 :=
  Correct.A_of_list k9 [0, 2, 0] _ k9s_P_0_2_0 1 (by decide)

theorem k9s_A_2_0_2_0 : Spec.A k9 [2, 0, 2, 0] = 4107488422938303118 :=
  Correct.A_of_list k9 [0, 2, 0] _ k9s_P_0_2_0 2 (by decide)

theorem k9s_A_3_0_2_0 : Spec.A k9 [3, 0, 2, 0] = 4428200000404246970 :=
  Correct.A_of_list k9 [0, 2, 0] _ k9s_P_0_2_0 3 (by decide)

end Results
