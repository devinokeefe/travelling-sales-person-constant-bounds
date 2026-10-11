/-
The result for `k8`, from the 16 values `A_2(g_1, g_2)` (four in each file of `Results/K8S/`,
computed by the routine of `TSPShared/Impl.lean`).
-/
import TSPBound.Theorems
import TSPShared.Theorems
import Results.Params
import Results.K8S.P0
import Results.K8S.P1
import Results.K8S.P2
import Results.K8S.P3

namespace Results
open Spec

set_option maxRecDepth 100000 in
theorem k8s_level2 :
    (tuples 2 (m k8)).map (fun g => (g, A k8 g))
      = [([0, 0], 568273626724957733),
       ([0, 1], 588095994177266409),
       ([0, 2], 615334704174186517),
       ([0, 3], 672294378470616322),
       ([1, 0], 579104800847496960),
       ([1, 1], 598521617449355668),
       ([1, 2], 624081897596963510),
       ([1, 3], 679377868392256100),
       ([2, 0], 598563575843554789),
       ([2, 1], 617175333547216685),
       ([2, 2], 641010879847966918),
       ([2, 3], 694948698166673744),
       ([3, 0], 652444375969107769),
       ([3, 1], 669787912978070825),
       ([3, 2], 691578329411084145),
       ([3, 3], 744317543041174092)] := by
  have ht : tuples 2 (m k8) = [[0, 0], [0, 1], [0, 2], [0, 3], [1, 0], [1, 1], [1, 2], [1, 3], [2, 0], [2, 1], [2, 2], [2, 3], [3, 0], [3, 1], [3, 2], [3, 3]] := by
    decide
  rw [ht]
  simp only [List.map_cons, List.map_nil, k8s_A_0_0, k8s_A_0_1, k8s_A_0_2, k8s_A_0_3, k8s_A_1_0, k8s_A_1_1, k8s_A_1_2, k8s_A_1_3, k8s_A_2_0, k8s_A_2_1, k8s_A_2_2, k8s_A_2_3, k8s_A_3_0, k8s_A_3_1, k8s_A_3_2, k8s_A_3_3]

theorem k8s_total : Spec.total k8 = 628708228549677266 := by
  rw [← Correct.totalFrom_eq_total k8 2 _ (by decide) k8s_level2.symm]; native_decide

theorem k8s_accepts : Spec.Accepts k8 := by
  unfold Spec.Accepts; rw [k8s_total]; decide

end Results

#print axioms Results.k8s_total
#print axioms Results.k8s_accepts
