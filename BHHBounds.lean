import BHHBounds.Bounds

/-!
# Formalized Two-Sided Bounds for the Planar Beardwood–Halton–Hammersley Constant

Root library entry point re-exporting `BHHBounds.Bounds`:
- `BHHBounds.bhh_lower_bound`: `(650928770 : ℝ) / 10 ^ 9 ≤ β` (`0.650928770 ≤ β`)
- `BHHBounds.bhh_upper_bound`: `β ≤ (8549326 : ℝ) / 10 ^ 7` (`β ≤ 0.8549326`)
- `BHHBounds.bhh_bounds`: `(650928770 : ℝ) / 10 ^ 9 ≤ β ∧ β ≤ (8549326 : ℝ) / 10 ^ 7`

All theorems are unconditional given `BHHBounds.IsBHHConstant β`, with zero `sorryAx`,
zero custom axioms, and zero external hypotheses.
-/
