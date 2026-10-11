/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_1_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 1, 0]))
      = [4387077779299000533, 4427614885162653401, 4517327065455855162, 4806246906173878465] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 1, 0]]; native_decide

theorem k9s_A_0_3_1_0 : Spec.A k9 [0, 3, 1, 0] = 4387077779299000533 :=
  Correct.A_of_list k9 [3, 1, 0] _ k9s_P_3_1_0 0 (by decide)

theorem k9s_A_1_3_1_0 : Spec.A k9 [1, 3, 1, 0] = 4427614885162653401 :=
  Correct.A_of_list k9 [3, 1, 0] _ k9s_P_3_1_0 1 (by decide)

theorem k9s_A_2_3_1_0 : Spec.A k9 [2, 3, 1, 0] = 4517327065455855162 :=
  Correct.A_of_list k9 [3, 1, 0] _ k9s_P_3_1_0 2 (by decide)

theorem k9s_A_3_3_1_0 : Spec.A k9 [3, 3, 1, 0] = 4806246906173878465 :=
  Correct.A_of_list k9 [3, 1, 0] _ k9s_P_3_1_0 3 (by decide)

end Results
