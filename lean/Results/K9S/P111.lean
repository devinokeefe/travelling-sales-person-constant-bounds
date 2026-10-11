/-
One piece of the evaluation for `k9` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 1, 1)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k9s_P_1_1_1 :
    (List.range (m k9)).map (fun g1 => Spec.A k9 (g1 :: [1, 1, 1]))
      = [3989890721861127577, 4054608442701710251, 4166973413670803284, 4481440482190753567] := by
  rw [← Correct.AofShared_eq_A k9 0 64 [1, 1, 1]]; native_decide

theorem k9s_A_0_1_1_1 : Spec.A k9 [0, 1, 1, 1] = 3989890721861127577 :=
  Correct.A_of_list k9 [1, 1, 1] _ k9s_P_1_1_1 0 (by decide)

theorem k9s_A_1_1_1_1 : Spec.A k9 [1, 1, 1, 1] = 4054608442701710251 :=
  Correct.A_of_list k9 [1, 1, 1] _ k9s_P_1_1_1 1 (by decide)

theorem k9s_A_2_1_1_1 : Spec.A k9 [2, 1, 1, 1] = 4166973413670803284 :=
  Correct.A_of_list k9 [1, 1, 1] _ k9s_P_1_1_1 2 (by decide)

theorem k9s_A_3_1_1_1 : Spec.A k9 [3, 1, 1, 1] = 4481440482190753567 :=
  Correct.A_of_list k9 [1, 1, 1] _ k9s_P_1_1_1 3 (by decide)

end Results
