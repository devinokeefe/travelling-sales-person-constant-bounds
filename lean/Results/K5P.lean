/-
The result for `k5`, from the sixteen values `A_2(g_1, g_2)` (one file each in `Results/K5P/`).
-/
import TSPBound.Theorems
import Results.Params
import Results.K5P.A00
import Results.K5P.A01
import Results.K5P.A02
import Results.K5P.A03
import Results.K5P.A10
import Results.K5P.A11
import Results.K5P.A12
import Results.K5P.A13
import Results.K5P.A20
import Results.K5P.A21
import Results.K5P.A22
import Results.K5P.A23
import Results.K5P.A30
import Results.K5P.A31
import Results.K5P.A32
import Results.K5P.A33

namespace Results
open Spec

theorem k5p_level2 :
    (tuples 2 (m k5)).map (fun g => (g, A k5 g))
      = [([0, 0], 1484445613767419),
       ([0, 1], 1573080074211120),
       ([0, 2], 1694476901499429),
       ([0, 3], 1955028022408841),
       ([1, 0], 1534955863847791),
       ([1, 1], 1621349765003821),
       ([1, 2], 1735287296558586),
       ([1, 3], 1989575010450887),
       ([2, 0], 1625738631793433),
       ([2, 1], 1708409803156266),
       ([2, 2], 1815295202580286),
       ([2, 3], 2064692999291740),
       ([3, 0], 1876505854713677),
       ([3, 1], 1954354406960598),
       ([3, 2], 2053539143562234),
       ([3, 3], 2298884362149285)] := by
  have ht : tuples 2 (m k5) = [[0, 0], [0, 1], [0, 2], [0, 3], [1, 0], [1, 1], [1, 2], [1, 3], [2, 0], [2, 1], [2, 2], [2, 3], [3, 0], [3, 1], [3, 2], [3, 3]] := by
    decide
  rw [ht]
  simp only [List.map_cons, List.map_nil, k5p_A_0_0, k5p_A_0_1, k5p_A_0_2, k5p_A_0_3, k5p_A_1_0, k5p_A_1_1, k5p_A_1_2, k5p_A_1_3, k5p_A_2_0, k5p_A_2_1, k5p_A_2_2, k5p_A_2_3, k5p_A_3_0, k5p_A_3_1, k5p_A_3_2, k5p_A_3_3]

theorem k5p_total : Spec.total k5 = 1761033937996622 := by
  rw [← Correct.totalFrom_eq_total k5 2 _ (by decide) k5p_level2.symm]; native_decide

theorem k5p_accepts : Spec.Accepts k5 := by
  unfold Spec.Accepts; rw [k5p_total]; decide

end Results

#print axioms Results.k5p_total
#print axioms Results.k5p_accepts
