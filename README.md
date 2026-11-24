# Bounds for the Euclidean travelling salesman constant

By a theorem of Beardwood, Halton and Hammersley, the length of a shortest tour through n independent
uniform random points in the unit square, divided by √n, converges almost surely to a constant β. This
repository proves in Lean 4, with Mathlib, that

$$0.650928770 \le \beta \le 0.8549326.$$

The best earlier bounds were 0.6421 ≤ β ≤ 0.8810, by Dong and Cao
([arXiv:2610.02809](https://arxiv.org/abs/2610.02809)). Numerical estimates put β near 0.71.

## Statement

The theorems are in [`LowerBound.lean`](BHHBounds/LowerBound.lean),
[`UpperBound.lean`](BHHBounds/UpperBound.lean) and [`Bounds.lean`](BHHBounds/Bounds.lean):

```lean
theorem expectedTourLength_lower_bound :
    ∀ ε > 0, ∀ᶠ n : ℕ in Filter.atTop,
      (650928770 : ℝ) / 10 ^ 9 - ε ≤ expectedTourLength n / Real.sqrt (n : ℝ)

theorem expectedTourLength_upper_bound :
    ∀ ε > 0, ∀ᶠ n : ℕ in Filter.atTop,
      expectedTourLength n / Real.sqrt (n : ℝ) ≤ (8549326 : ℝ) / 10 ^ 7 + ε

theorem bhh_bounds (β : ℝ) (hβ : IsBHHConstant β) :
    (650928770 : ℝ) / 10 ^ 9 ≤ β ∧ β ≤ (8549326 : ℝ) / 10 ^ 7
```

Here `expectedTourLength n` is the expected length of a shortest tour through n independent uniform
points of the unit square. The first two theorems do not mention β. The third is about any β that
satisfies the following definition, from [`Defs.lean`](BHHBounds/Defs.lean):

```lean
def tourLength {n : ℕ} (x : Fin n → Pt) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
    euclidDist (x (σ i)) (x (σ (finRotate n i)))

def IsBHHConstant (β : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Pt),
    (∀ i, Measurable (X i)) → ProbabilityTheory.iIndepFun X P →
    (∀ i, P.map (X i) = volume.restrict unitSquare) →
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => tourLength (fun i : Fin n => X i ω) / Real.sqrt (n : ℝ))
      Filter.atTop (nhds β)
```

## Building

With [elan](https://github.com/leanprover/elan) installed, which fetches the toolchain pinned in
`lean-toolchain`:

```bash
lake exe cache get
lake build
```

The build includes the audit of axioms. The 24 shards of the lower bound take a few minutes on a
multi-core machine. `Upper/Cert4.lean` is a single computation that took about 2.5 hours on one thread
of an i9-14900K.

## Licence

[MIT](LICENSE). Citation metadata is in [`CITATION.cff`](CITATION.cff).
