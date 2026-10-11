/-
`Spec` is written with natural numbers, where `x - y` is 0 if `x < y` and `x / 0` is 0.  RECIPE.md
means ordinary subtraction of integers and never divides by zero.  `Exact p` lists the conditions
under which the two readings agree in Sections 1 to 3, together with the two divisors of Section 5.
It is proved here, by evaluation (`native_decide`), for the parameter sets `k5`, …, `k9` only.  The
theorems `…_total` do not use it: it is a separate statement about how `Spec` may be read.

The subtractions and divisors of `Spec` that `Exact` does not cover, and why each is harmless:

- `b - 1` in `cdiv a b`: not truncated when `b ≥ 1`, that is, whenever the divisor is not zero;
- `i - 1` in `num` (Section 3): only in the term with the guard `i ≥ 1`;
- `κ_c - 1` in `reduce`: called only at the last cell with `κ_c > 0` (`Spec.lastPos_spec`);
- `m p - 1` in `Tab`: `m p ≥ 1` for every `p`;
- `j - i` in `keyOf`: called with the smaller index first;
- `p.k - 1` in `cost`: `k ≥ 2` for allowed parameters (`…_allowed` in `Results/Params.lean`);
- `absDiff x y`, which is `|x - y|`: of its two truncated differences one is 0;
- `13 - j` and `p.k - g.length`: termination measures only;
- the divisor `(m p) ^ i` and the modulus `m p` in `gapOfIndex`: positive for every `p`;
- all remaining divisors are powers of 2; differences of integers (`Int`) occur in `sumZ`, `chi`, `G`.
-/
import TSPBound.Spec
import Results.Params

namespace Results
open Spec

/-- No subtraction of Sections 1 to 3 is truncated, and no divisor is zero. -/
def Exact (p : Params) : Prop :=
  -- divisors `M·j`, `α·M`, `4ν²`
  0 < p.M ∧ 0 < p.nu ∧ 0 < alpha p * p.M ∧
  -- Section 2: `lo_j = Q - ceil(up_{j+1} / (M·j))`, `up_j = Q - floor(lo_{j+1} / (M·j))`
  (∀ j ∈ List.range' 1 12,
    cdiv (up p.M (j + 1)) (p.M * j) ≤ Q ∧ lo p.M (j + 1) / (p.M * j) ≤ Q) ∧
  -- Section 3: `C_λ = Q - M·(Q - up_1)`, `C_μ = M·(Q - lo_1) - lo_1`
  up p.M 1 ≤ Q ∧ p.M * (Q - up p.M 1) ≤ Q ∧
  lo p.M 1 ≤ Q ∧ lo p.M 1 ≤ p.M * (Q - lo p.M 1) ∧
  -- `n_c = b_{c+1} - b_c`, the divisor `Q - Rup[n_c]`, and `Rup[b_c] - Rlo[b_{c+1}]`
  (∀ c ∈ List.range (m p - 1),
    bd p c ≤ bd p (c + 1) ∧ Rup p.M (ncell p c) < Q ∧ Rlo p.M (bd p (c + 1)) ≤ Rup p.M (bd p c))

instance (p : Params) : Decidable (Exact p) := by unfold Exact; infer_instance

theorem k5_exact : Exact k5 := by native_decide
theorem k6_exact : Exact k6 := by native_decide
theorem k7_exact : Exact k7 := by native_decide
theorem k8_exact : Exact k8 := by native_decide
theorem k9_exact : Exact k9 := by native_decide

end Results

#print axioms Results.k8_exact
