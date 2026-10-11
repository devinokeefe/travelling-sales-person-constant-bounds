/-
The result for `k6`, from the 16 values `A_2(g_1, g_2)` (four in each file of `Results/K6S/`,
computed by the routine of `TSPShared/Impl.lean`).
-/
import TSPBound.Theorems
import TSPShared.Theorems
import Results.Params
import Results.K6S.P0
import Results.K6S.P1
import Results.K6S.P2
import Results.K6S.P3

namespace Results
open Spec

set_option maxRecDepth 100000 in
theorem k6s_level2 :
    (tuples 2 (m k6)).map (fun g => (g, A k6 g))
      = [([0, 0], 10924631223287195),
       ([0, 1], 11466206318087604),
       ([0, 2], 12198349404618991),
       ([0, 3], 13758588737819275),
       ([1, 0], 11231415334948327),
       ([1, 1], 11757193394463477),
       ([1, 2], 12442122627019056),
       ([1, 3], 13965734133349429),
       ([2, 0], 11780328691848360),
       ([2, 1], 12280707821748347),
       ([2, 2], 12920642013469075),
       ([2, 3], 14416392723264310),
       ([3, 0], 13291203959747565),
       ([3, 1], 13757065197141819),
       ([3, 2], 14347792078815327),
       ([3, 3], 15821531400483560)] := by
  have ht : tuples 2 (m k6) = [[0, 0], [0, 1], [0, 2], [0, 3], [1, 0], [1, 1], [1, 2], [1, 3], [2, 0], [2, 1], [2, 2], [2, 3], [3, 0], [3, 1], [3, 2], [3, 3]] := by
    decide
  rw [ht]
  simp only [List.map_cons, List.map_nil, k6s_A_0_0, k6s_A_0_1, k6s_A_0_2, k6s_A_0_3, k6s_A_1_0, k6s_A_1_1, k6s_A_1_2, k6s_A_1_3, k6s_A_2_0, k6s_A_2_1, k6s_A_2_2, k6s_A_2_3, k6s_A_3_0, k6s_A_3_1, k6s_A_3_2, k6s_A_3_3]

theorem k6s_total : Spec.total k6 = 12593568504391125 := by
  rw [← Correct.totalFrom_eq_total k6 2 _ (by decide) k6s_level2.symm]; native_decide

theorem k6s_accepts : Spec.Accepts k6 := by
  unfold Spec.Accepts; rw [k6s_total]; decide

end Results

#print axioms Results.k6s_total
#print axioms Results.k6s_accepts
