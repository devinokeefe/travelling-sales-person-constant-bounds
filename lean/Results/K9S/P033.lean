/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 3, 3)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_3_3 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 3, 3]))
      = [4900404990399387665, 4955797757568189865, 5062956688952404419, 5373403994395655151] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 3, 3]]; native_decide

theorem k9s_A_0_0_3_3 : Spec.A k9 [0, 0, 3, 3] = 4900404990399387665 :=
  Correct.A_of_list k9 [0, 3, 3] _ k9s_P_0_3_3 0 (by decide)

theorem k9s_A_1_0_3_3 : Spec.A k9 [1, 0, 3, 3] = 4955797757568189865 :=
  Correct.A_of_list k9 [0, 3, 3] _ k9s_P_0_3_3 1 (by decide)

theorem k9s_A_2_0_3_3 : Spec.A k9 [2, 0, 3, 3] = 5062956688952404419 :=
  Correct.A_of_list k9 [0, 3, 3] _ k9s_P_0_3_3 2 (by decide)

theorem k9s_A_3_0_3_3 : Spec.A k9 [3, 0, 3, 3] = 5373403994395655151 :=
  Correct.A_of_list k9 [0, 3, 3] _ k9s_P_0_3_3 3 (by decide)

end Results
