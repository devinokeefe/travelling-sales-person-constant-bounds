/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 1, 2)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_0_1_2 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [0, 1, 2]))
      = [1456443719244042, 1507599265336983, 1598944805012746, 1850257295802433] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [0, 1, 2]]; native_decide

theorem k5s_A_0_0_1_2 : Spec.A k5 [0, 0, 1, 2] = 1456443719244042 :=
  Correct.A_of_list k5 [0, 1, 2] _ k5s_P_0_1_2 0 (by decide)

theorem k5s_A_1_0_1_2 : Spec.A k5 [1, 0, 1, 2] = 1507599265336983 :=
  Correct.A_of_list k5 [0, 1, 2] _ k5s_P_0_1_2 1 (by decide)

theorem k5s_A_2_0_1_2 : Spec.A k5 [2, 0, 1, 2] = 1598944805012746 :=
  Correct.A_of_list k5 [0, 1, 2] _ k5s_P_0_1_2 2 (by decide)

theorem k5s_A_3_0_1_2 : Spec.A k5 [3, 0, 1, 2] = 1850257295802433 :=
  Correct.A_of_list k5 [0, 1, 2] _ k5s_P_0_1_2 3 (by decide)

end Results
