/-
The result for k = 7: the total of the recipe and the test of Section 8.
-/
import TSPBound.Theorems
import Results.Params

namespace Results
open Spec

theorem k7_total : Spec.total k7 = 92054418307910785 := by
  rw [← Correct.AofPar_nil k7 4]; native_decide

theorem k7_accepts : Spec.Accepts k7 := by
  unfold Spec.Accepts; rw [k7_total]; decide

end Results

#print axioms Results.k7_total
#print axioms Results.k7_accepts
