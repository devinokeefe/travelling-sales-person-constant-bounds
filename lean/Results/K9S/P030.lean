/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 3, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_3_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 3, 0]))
      = [4336408731759638158, 4392788110028432503, 4501609293823221846, 4815938731999478204] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 3, 0]]; native_decide

theorem k9s_A_0_0_3_0 : Spec.A k9 [0, 0, 3, 0] = 4336408731759638158 :=
  Correct.A_of_list k9 [0, 3, 0] _ k9s_P_0_3_0 0 (by decide)

theorem k9s_A_1_0_3_0 : Spec.A k9 [1, 0, 3, 0] = 4392788110028432503 :=
  Correct.A_of_list k9 [0, 3, 0] _ k9s_P_0_3_0 1 (by decide)

theorem k9s_A_2_0_3_0 : Spec.A k9 [2, 0, 3, 0] = 4501609293823221846 :=
  Correct.A_of_list k9 [0, 3, 0] _ k9s_P_0_3_0 2 (by decide)

theorem k9s_A_3_0_3_0 : Spec.A k9 [3, 0, 3, 0] = 4815938731999478204 :=
  Correct.A_of_list k9 [0, 3, 0] _ k9s_P_0_3_0 3 (by decide)

end Results
