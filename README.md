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

## What is checked, and what is not

- **The proofs.** The Lean kernel checks every proof, from the definitions in `Defs.lean` to the three
  theorems above. There is no `sorry` and no added axiom.
- **The computations.** 33 finite computations run as compiled code (`native_decide`), which the kernel
  does not check and which Lean records as axioms. The lower bound uses 28: the 24 shards of triangle
  boxes, the base integral, and three checks that the certificate is well formed. The upper bound uses
  5: four cost tables and the fixed point of the dynamic programme.
  [`Audit.lean`](BHHBounds/Audit.lean) lists them, and the build fails if the list changes.
- **The constant.** That β exists is the theorem of Beardwood, Halton and Hammersley, which is not
  formalised here. `bhh_bounds` says that any β satisfying `IsBHHConstant` lies in the interval.
- **The definitions.** That `tourLength`, `expectedTourLength` and `IsBHHConstant` say what is intended
  can only be checked by reading them. They are the first 70 lines of `Defs.lean`.
- **The exposition.** There is no paper for this version. The outline below and the header of each
  file are all the prose there is.

## Outline of the proofs

**Lower bound.** The proof builds a feasible dual solution for the 2-factor relaxation of the tour,
with subtour constraints on isolated triangles
([`Dual/TwoFactorMoat.lean`](BHHBounds/Dual/TwoFactorMoat.lean)). Each point gets a potential that is a
step function of the distance to its second-nearest neighbour, and each isolated triangle whose shape
falls in one of 2,923 boxes gets a moat. The resulting bound holds for every configuration of points
([`Dual/FiniteN.lean`](BHHBounds/Dual/FiniteN.lean)). Its expectation converges to a sum of integrals
over a Poisson process (the rest of [`Dual/`](BHHBounds/Dual)), and integer interval arithmetic bounds
these from below by 0.645497734 for the potentials and 0.005431036 for the moats
([`Cert/`](BHHBounds/Cert)). [`Geometry/`](BHHBounds/Geometry) supplies the areas of intersections and
unions of disks.

**Upper bound.** The square is cut into strips of height proportional to 1/√n. Within a strip, a path
that joins each point only to points at most four places away in horizontal order is built by an
automaton with 56 states ([`Upper/Automaton.lean`](BHHBounds/Upper/Automaton.lean),
[`Upper/Automaton4.lean`](BHHBounds/Upper/Automaton4.lean)). A dynamic programme over discretised gaps
and heights bounds the expected length of the best such path per point
([`Upper/DP.lean`](BHHBounds/Upper/DP.lean)), and a potential certifying the value 0.8549326 is checked
in integers ([`Upper/Cert4.lean`](BHHBounds/Upper/Cert4.lean)). Poissonisation and joining the strips
in serpentine order pass from one strip to n uniform points
([`Upper/PoissonCoupling.lean`](BHHBounds/Upper/PoissonCoupling.lean)).

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

## Earlier version

The tag [`v1.0.0`](../../tree/v1.0.0) holds an earlier paper, which proves β < 0.8618 by a different
computation, with three independent checkers in C, Rust and Python.

## Licence

[MIT](LICENSE). Citation metadata is in [`CITATION.cff`](CITATION.cff).
