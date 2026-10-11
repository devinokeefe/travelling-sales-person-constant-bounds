/-
The result for k = 5: the total of the recipe and the test of Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k5_total : Spec.total k5 = 1761033937996622 := by
  rw [← Correct.AofPar_nil k5 4]; native_decide

theorem k5_accepts : Spec.Accepts k5 := by
  unfold Spec.Accepts; rw [k5_total]; decide

end Results

#print axioms Results.k5_total
#print axioms Results.k5_accepts
