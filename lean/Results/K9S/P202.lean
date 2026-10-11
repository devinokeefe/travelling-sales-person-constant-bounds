/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 2, 0, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_2_0_2 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [2, 0, 2]))
      = [4224279962683516534, 4280782620199760789, 4384594435064755599, 4687348433847889910] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [2, 0, 2]]; native_decide

theorem k9s_A_0_2_0_2 : Spec.A k9 [0, 2, 0, 2] = 4224279962683516534 :=
  Correct.A_of_list k9 [2, 0, 2] _ k9s_P_2_0_2 0 (by decide)

theorem k9s_A_1_2_0_2 : Spec.A k9 [1, 2, 0, 2] = 4280782620199760789 :=
  Correct.A_of_list k9 [2, 0, 2] _ k9s_P_2_0_2 1 (by decide)

theorem k9s_A_2_2_0_2 : Spec.A k9 [2, 2, 0, 2] = 4384594435064755599 :=
  Correct.A_of_list k9 [2, 0, 2] _ k9s_P_2_0_2 2 (by decide)

theorem k9s_A_3_2_0_2 : Spec.A k9 [3, 2, 0, 2] = 4687348433847889910 :=
  Correct.A_of_list k9 [2, 0, 2] _ k9s_P_2_0_2 3 (by decide)

end Results
