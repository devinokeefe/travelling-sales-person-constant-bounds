/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 0, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_0_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 0, 0]))
      = [4257993314547194241, 4299137870971217194, 4389249485402584567, 4678356039948451891] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 0, 0]]; native_decide

theorem k9s_A_0_3_0_0 : Spec.A k9 [0, 3, 0, 0] = 4257993314547194241 :=
  Correct.A_of_list k9 [3, 0, 0] _ k9s_P_3_0_0 0 (by decide)

theorem k9s_A_1_3_0_0 : Spec.A k9 [1, 3, 0, 0] = 4299137870971217194 :=
  Correct.A_of_list k9 [3, 0, 0] _ k9s_P_3_0_0 1 (by decide)

theorem k9s_A_2_3_0_0 : Spec.A k9 [2, 3, 0, 0] = 4389249485402584567 :=
  Correct.A_of_list k9 [3, 0, 0] _ k9s_P_3_0_0 2 (by decide)

theorem k9s_A_3_3_0_0 : Spec.A k9 [3, 3, 0, 0] = 4678356039948451891 :=
  Correct.A_of_list k9 [3, 0, 0] _ k9s_P_3_0_0 3 (by decide)

end Results
