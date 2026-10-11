/-
The result for k = 6: the total of the recipe and the test of Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k6_total : Spec.total k6 = 12593568504391125 := by
  rw [← Correct.AofPar_nil k6 4]; native_decide

theorem k6_accepts : Spec.Accepts k6 := by
  unfold Spec.Accepts; rw [k6_total]; decide

end Results

#print axioms Results.k6_total
#print axioms Results.k6_accepts
