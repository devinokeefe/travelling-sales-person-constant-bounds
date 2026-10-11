/-
One piece of the evaluation for `k5` by the routine of `TSPShared/Impl.lean`: the values
`A_4(g_1, 1, 1, 0)` of RECIPE.md Section 8 for `g_1 = 0, …, 3`.
-/
import TSPShared.Theorems
import Results.Params

namespace Results
open Spec

theorem k5s_P_1_1_0 :
    (List.range (m k5)).map (fun g1 => Spec.A k5 (g1 :: [1, 1, 0]))
      = [1337808753048349, 1388205778817064, 1477092450952735, 1724862472842984] := by
  rw [← Correct.AofShared_eq_A k5 0 64 [1, 1, 0]]; native_decide

theorem k5s_A_0_1_1_0 : Spec.A k5 [0, 1, 1, 0] = 1337808753048349 :=
  Correct.A_of_list k5 [1, 1, 0] _ k5s_P_1_1_0 0 (by decide)

theorem k5s_A_1_1_1_0 : Spec.A k5 [1, 1, 1, 0] = 1388205778817064 :=
  Correct.A_of_list k5 [1, 1, 0] _ k5s_P_1_1_0 1 (by decide)

theorem k5s_A_2_1_1_0 : Spec.A k5 [2, 1, 1, 0] = 1477092450952735 :=
  Correct.A_of_list k5 [1, 1, 0] _ k5s_P_1_1_0 2 (by decide)

theorem k5s_A_3_1_1_0 : Spec.A k5 [3, 1, 1, 0] = 1724862472842984 :=
  Correct.A_of_list k5 [1, 1, 0] _ k5s_P_1_1_0 3 (by decide)

end Results
