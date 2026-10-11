/-
The result for `k7`, from the 16 values `A_2(g_1, g_2)` (four in each file of `Results/K7S/`,
computed by the routine of `TSPShared/Impl.lean`).
-/
import TSPBound.Theorems
import TSPShared.Theorems
import Results.Params
import Results.K7S.P0
import Results.K7S.P1
import Results.K7S.P2
import Results.K7S.P3

namespace Results
open Spec

set_option maxRecDepth 100000 in
theorem k7s_level2 :
    (tuples 2 (m k7)).map (fun g => (g, A k7 g))
      = [([0, 0], 81979461003020301),
       ([0, 1], 85281560812081318),
       ([0, 2], 89824721872373839),
       ([0, 3], 99328726430602459),
       ([1, 0], 83783620494564571),
       ([1, 1], 87019685609216215),
       ([1, 2], 91284682469147212),
       ([1, 3], 100509654084779895),
       ([2, 0], 87024621763306514),
       ([2, 1], 90128893306977555),
       ([2, 2], 94108691122742900),
       ([2, 3], 103104954259639154),
       ([3, 0], 95999800209169200),
       ([3, 1], 98898064873812567),
       ([3, 2], 102540574682687362),
       ([3, 3], 111333144555530177)] := by
  have ht : tuples 2 (m k7) = [[0, 0], [0, 1], [0, 2], [0, 3], [1, 0], [1, 1], [1, 2], [1, 3], [2, 0], [2, 1], [2, 2], [2, 3], [3, 0], [3, 1], [3, 2], [3, 3]] := by
    decide
  rw [ht]
  simp only [List.map_cons, List.map_nil, k7s_A_0_0, k7s_A_0_1, k7s_A_0_2, k7s_A_0_3, k7s_A_1_0, k7s_A_1_1, k7s_A_1_2, k7s_A_1_3, k7s_A_2_0, k7s_A_2_1, k7s_A_2_2, k7s_A_2_3, k7s_A_3_0, k7s_A_3_1, k7s_A_3_2, k7s_A_3_3]

theorem k7s_total : Spec.total k7 = 92054418307910785 := by
  rw [← Correct.totalFrom_eq_total k7 2 _ (by decide) k7s_level2.symm]; native_decide

theorem k7s_accepts : Spec.Accepts k7 := by
  unfold Spec.Accepts; rw [k7s_total]; decide

end Results

#print axioms Results.k7s_total
#print axioms Results.k7s_accepts
