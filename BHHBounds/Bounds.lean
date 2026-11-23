import BHHBounds.LowerBound
import BHHBounds.UpperBound

/-!
# Bounds on the Beardwood–Halton–Hammersley constant

`0.650928770 ≤ β ≤ 0.8549326`. The statements `expectedTourLength_lower_bound` and
`expectedTourLength_upper_bound` do not assume that a BHH constant exists.
-/

namespace BHHBounds

/-- Every BHH constant `β` satisfies `0.650928770 ≤ β ≤ 0.8549326`. -/
theorem bhh_bounds (β : ℝ) (hβ : IsBHHConstant β) :
    (650928770 : ℝ) / 10 ^ 9 ≤ β ∧ β ≤ (8549326 : ℝ) / 10 ^ 7 :=
  ⟨bhh_lower_bound β hβ, bhh_upper_bound β hβ⟩

end BHHBounds
