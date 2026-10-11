/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 2, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_2_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 2, 0]))
      = [4210954209507811958, 4261204294535141881, 4359051678695982747, 4655111976640068861] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 2, 0]]; native_decide

theorem k9s_A_0_2_2_0 : Spec.A k9 [0, 2, 2, 0] = 4210954209507811958 :=
  Correct.A_of_list k9 [2, 2, 0] _ k9s_P_2_2_0 0 (by decide)

theorem k9s_A_1_2_2_0 : Spec.A k9 [1, 2, 2, 0] = 4261204294535141881 :=
  Correct.A_of_list k9 [2, 2, 0] _ k9s_P_2_2_0 1 (by decide)

theorem k9s_A_2_2_2_0 : Spec.A k9 [2, 2, 2, 0] = 4359051678695982747 :=
  Correct.A_of_list k9 [2, 2, 0] _ k9s_P_2_2_0 2 (by decide)

theorem k9s_A_3_2_2_0 : Spec.A k9 [3, 2, 2, 0] = 4655111976640068861 :=
  Correct.A_of_list k9 [2, 2, 0] _ k9s_P_2_2_0 3 (by decide)

end Results
