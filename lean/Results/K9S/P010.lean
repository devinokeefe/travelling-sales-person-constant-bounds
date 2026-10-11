/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 0, 1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_0_1_0 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [0, 1, 0]))
      = [3693441263528503401, 3763151318336851882, 3883382281459511624, 4208937405176250179] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [0, 1, 0]]; native_decide

theorem k9s_A_0_0_1_0 : Spec.A k9 [0, 0, 1, 0] = 3693441263528503401 :=
  Correct.A_of_list k9 [0, 1, 0] _ k9s_P_0_1_0 0 (by decide)

theorem k9s_A_1_0_1_0 : Spec.A k9 [1, 0, 1, 0] = 3763151318336851882 :=
  Correct.A_of_list k9 [0, 1, 0] _ k9s_P_0_1_0 1 (by decide)

theorem k9s_A_2_0_1_0 : Spec.A k9 [2, 0, 1, 0] = 3883382281459511624 :=
  Correct.A_of_list k9 [0, 1, 0] _ k9s_P_0_1_0 2 (by decide)

theorem k9s_A_3_0_1_0 : Spec.A k9 [3, 0, 1, 0] = 4208937405176250179 :=
  Correct.A_of_list k9 [0, 1, 0] _ k9s_P_0_1_0 3 (by decide)

end Results
