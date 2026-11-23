import BHHBounds.LowerBound
import BHHBounds.UpperBound

/-!
# Combined Two-Sided Bounds for the Planar Euclidean TSP (BHH) Constant

Collects the unconditional end-to-end lower and upper bounds on every
Beardwood–Halton–Hammersley constant `β` (`IsBHHConstant β`):
```
  650928770 / 10 ^ 9 ≤ β ∧ β ≤ 8549326 / 10 ^ 7
```
(i.e. `0.650928770 ≤ β ≤ 0.8549326`).
-/

namespace BHHBounds

/-- **Combined Headline Theorem:** Every Beardwood–Halton–Hammersley constant `β`
(`IsBHHConstant β`) satisfies `0.650928770 ≤ β ≤ 0.8549326` unconditionally, with zero
external hypotheses. -/
theorem bhh_bounds (β : ℝ) (hβ : IsBHHConstant β) :
    (650928770 : ℝ) / 10 ^ 9 ≤ β ∧ β ≤ (8549326 : ℝ) / 10 ^ 7 :=
  ⟨bhh_lower_bound β hβ, bhh_upper_bound β hβ⟩

end BHHBounds
