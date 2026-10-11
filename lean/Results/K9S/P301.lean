/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 3, 0, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_3_0_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [3, 0, 1]))
      = [4408360087704950588, 4449267930245282726, 4539256632326701840, 4828301831132789631] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [3, 0, 1]]; native_decide

theorem k9s_A_0_3_0_1 : Spec.A k9 [0, 3, 0, 1] = 4408360087704950588 :=
  Correct.A_of_list k9 [3, 0, 1] _ k9s_P_3_0_1 0 (by decide)

theorem k9s_A_1_3_0_1 : Spec.A k9 [1, 3, 0, 1] = 4449267930245282726 :=
  Correct.A_of_list k9 [3, 0, 1] _ k9s_P_3_0_1 1 (by decide)

theorem k9s_A_2_3_0_1 : Spec.A k9 [2, 3, 0, 1] = 4539256632326701840 :=
  Correct.A_of_list k9 [3, 0, 1] _ k9s_P_3_0_1 2 (by decide)

theorem k9s_A_3_3_0_1 : Spec.A k9 [3, 3, 0, 1] = 4828301831132789631 :=
  Correct.A_of_list k9 [3, 0, 1] _ k9s_P_3_0_1 3 (by decide)

end Results
