# BHHBounds: End-to-End Lean 4 Bounds for the Planar Euclidean TSP Constant

[![Lean 4](https://img.shields.io/badge/Lean-v4.31.0-blue.svg)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

A **100% self-contained, end-to-end Lean 4 + Mathlib formalization** proving unconditional two-sided bounds on the planar Euclidean Traveling Salesperson Problem (Beardwood–Halton–Hammersley, BHH) constant $\beta$:

$$\frac{650\,928\,770}{10^9} \;=\; 0.650928770 \;\le\; \beta \;\le\; 0.8549326 \;=\; \frac{8\,549\,326}{10^7}.$$

Every theorem compiles under Lean `v4.31.0` with **zero errors, zero warnings, zero `sorryAx`, zero custom axioms, and zero external hypotheses** beyond the bare definition `BHHBounds.IsBHHConstant β`.

---

## Headline Theorems

All three main theorems are assembled in [`BHHBounds/Bounds.lean`](BHHBounds/Bounds.lean) (and re-exported by [`BHHBounds.lean`](BHHBounds.lean)):

| Bound | Lean Theorem | Exact Rational Statement | Decimal Value | Hypotheses Beyond `IsBHHConstant β` |
|---|---|---|---|---|
| **Lower bound** | `BHHBounds.bhh_lower_bound` ([`LowerBound.lean`](BHHBounds/LowerBound.lean)) | `(650928770 : ℝ) / 10 ^ 9 ≤ β` | `β ≥ 0.650928770` | None (unconditional) |
| **Upper bound** | `BHHBounds.bhh_upper_bound` ([`UpperBound.lean`](BHHBounds/UpperBound.lean)) | `β ≤ (8549326 : ℝ) / 10 ^ 7` | `β ≤ 0.8549326` | None (unconditional) |
| **Two-sided** | `BHHBounds.bhh_bounds` ([`Bounds.lean`](BHHBounds/Bounds.lean)) | `(650928770 : ℝ) / 10 ^ 9 ≤ β ∧ β ≤ (8549326 : ℝ) / 10 ^ 7` | `0.650928770 ≤ β ≤ 0.8549326` | None (unconditional) |

### Definition of `IsBHHConstant` ([`BHHBounds/Defs.lean`](BHHBounds/Defs.lean))

```lean
/-- Length of the shortest closed tour visiting `x 0, ..., x (n-1)` in some cyclic order. -/
def tourLength {n : ℕ} (x : Fin n → Pt) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
    euclidDist (x (σ i)) (x (σ (finRotate n i)))

/-- `β` is the Beardwood–Halton–Hammersley constant if, for every sequence of i.i.d. uniform
random points `X_0, X_1, ...` in `[0, 1]²`, `tourLength (X_0, ..., X_{n-1}) / √n → β` a.s. -/
def IsBHHConstant (β : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Pt),
    (∀ i, Measurable (X i)) → ProbabilityTheory.iIndepFun X P →
    (∀ i, P.map (X i) = volume.restrict unitSquare) →
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => tourLength (fun i : Fin n => X i ω) / Real.sqrt (n : ℝ))
      Filter.atTop (nhds β)
```

---

## Proof Overview

### 1. Lower Bound (`β ≥ 0.650928770`) — 2-Factor + Triangle-Moat LP Dual

The lower bound is proved completely from scratch in Lean 4 by constructing a feasible dual solution to the Held–Karp / 2-factor relaxation augmented with pairwise-disjoint isolated 3-vertex subtour-elimination moats:

1. **Deterministic Combinatorial LP Dual** ([`Dual/TwoFactorMoat.lean`](BHHBounds/Dual/TwoFactorMoat.lean)):
   Proves `twoFactor_moat_dual_lower_bound`: for any symmetric distance matrix `d`, any vertex potentials `π`, and any pairwise-disjoint family `F` of isolated subsets with nonnegative moat widths `y S` satisfying half-clearance non-interference, every Hamiltonian tour has length at least the 2-factor dual plus the net moat gain of `F`.
2. **Planar Measure & Disk-Union Geometry** ([`Geometry/`](BHHBounds/Geometry)):
   Exact Lebesgue area formulas for disks (`volume_disk`), polar and radial Bochner integration (`lintegral_polar_eq`, `integral_radial_eq`), two-disk lens intersections (`diskInterArea`, `volume_disk_inter`, `diskInterArea_antitone_d`), and three-disk union area bounds (`threeDiskArea`, `threeDiskArea_scale_le`).
3. **Finite-$n$ Pointwise Dual & Poisson Limits** ([`Dual/`](BHHBounds/Dual)):
   Assigns each vertex a step potential `stepPot rho w` evaluated at its rescaled second-nearest-neighbor distance `nn2`, and activates telescoping moat levels on isolated canonical triangles whose rescaled shape `(L, (x, y))` falls in one of 2,923 pairwise-disjoint open boxes inside the quarter-lens symmetry domain.
   - `FiniteN.pointwise_dual_lower_bound` proves the deterministic finite-$n$ lower bound for every point configuration `X : Fin n → Pt`.
   - `BaseLimit.baseTerm1_lower_tendsto` and `BaseLimit.basePen_upper_tendsto` pass the 1D 2-factor expectation to `baseIntegral rho w` via exchangeability, 2D Abel summation, radial change of variables, and dominated convergence.
   - `TriangleGeom`, `TriangleCond`, and `TriangleLimit.levelGain_tendsto` pass each triangle-moat level expectation to `levelGain` via 3-point rigid-motion/polar Jacobians, exact finite-$n$ binomial survival expectations, and nested dominated convergence.
   - `Expectation.bhh_ge_base_add_trianglePlan` combines all terms with `Asymptotics.le_of_eventually_expectedTourLength`.
4. **Certified Fixed-Point Integer Arithmetic** ([`Cert/`](BHHBounds/Cert)):
   A zero-Mathlib integer verification kernel (`Cert/Kernel.lean`) evaluates sound interval-arithmetic bounds for the 1D base integral (`645,497,734 / 10^9`) and all 2,923 triangle-moat boxes split across 24 shards (`+5,431,036 / 10^9`, total `650,928,770 / 10^9`). Soundness of every arithmetic, exponential, trigonometric, and geometric bound is proved against real Mathlib integrals in `ArithSound.lean`, `GeomSound.lean`, `BaseSound.lean`, and `BoxSound.lean`.

### 2. Upper Bound (`β ≤ 0.8549326`) — Bandwidth-4 Concave DP Strip Automaton

The upper bound is proved unconditionally via a bandwidth-4 strip traversal strategy:

1. **Finite-State Strip Automaton & Concave DP** ([`Upper/Automaton.lean`](BHHBounds/Upper/Automaton.lean), [`AutomatonSound.lean`](BHHBounds/Upper/AutomatonSound.lean), [`DP.lean`](BHHBounds/Upper/DP.lean), [`Automaton4.lean`](BHHBounds/Upper/Automaton4.lean)):
   Formalizes a 56-state bandwidth-4 strip automaton, proves tour-reconstruction soundness (`AutomatonSound`), and establishes the concave dynamic-programming operator `dpOp`.
2. **Rational Exponential-Bin Costs & Certified Fixed Point** ([`Upper/Costs.lean`](BHHBounds/Upper/Costs.lean), [`ExpBins.lean`](BHHBounds/Upper/ExpBins.lean), [`Cert4Spec.lean`](BHHBounds/Upper/Cert4Spec.lean), [`CostTableSound.lean`](BHHBounds/Upper/CostTableSound.lean), [`Cert4.lean`](BHHBounds/Upper/Cert4.lean)):
   Verifies exact rational upper bounds for the exponential-bin transition cost tables (`costFlat1..4_checked`) and the 56-state DP fixed-point certificate (`checkFixedPoint4_dpPotential4`) at `U = 8549326 / 10^7`.
3. **Poisson Renewal, Superposition Coupling & Serpentine Stitching** ([`Upper/TourHelpers.lean`](BHHBounds/Upper/TourHelpers.lean), [`StripDPBound.lean`](BHHBounds/Upper/StripDPBound.lean), [`PoissonRenewal.lean`](BHHBounds/Upper/PoissonRenewal.lean), [`PoissonSuperposition.lean`](BHHBounds/Upper/PoissonSuperposition.lean), [`PoissonCoupling.lean`](BHHBounds/Upper/PoissonCoupling.lean), [`ToBHHBase.lean`](BHHBounds/Upper/ToBHHBase.lean)):
   Couples i.i.d. uniform points in `[0, 1]²` to a Poisson point process across strips of width $O(1/\sqrt{n})$, stitches strip subtours into a global Hamiltonian tour, and bridges the resulting bound directly to `BHHBounds.IsBHHConstant β` via `Asymptotics.expectedTourLength_div_sqrt_tendsto`.

---

## Repository Structure

```
BHHBounds.lean                  Root library entry point (re-exports BHHBounds.Bounds)
BHHBounds/
├── Defs.lean                   Core definitions (Pt, euclidDist, disk, tourLength, IsBHHConstant)
├── Asymptotics.lean            Bridge: IsBHHConstant β → expectedTourLength n / √n → β
├── LowerBound.lean             Headline lower bound: bhh_lower_bound (0.650928770 ≤ β)
├── UpperBound.lean             Headline upper bound: bhh_upper_bound (β ≤ 0.8549326)
├── Bounds.lean                 Combined two-sided theorem: bhh_bounds
├── Audit.lean                  #print axioms audit for all headline theorems
├── Geometry/
│   ├── DiskMeasure.lean        Disk area, rigid-motion invariance, polar/radial integration
│   ├── DiskIntersection.lean   Two-disk lens intersection area, monotonicity, union bounds
│   └── ThreeDiskArea.lean      Quarter-lens canonical triangles and three-disk area scaling
├── Dual/
│   ├── TwoFactorMoat.lean      Combinatorial 2-factor + disjoint moat LP dual lower bound
│   ├── PoissonIntegrals.lean   ValidStepPot, ValidBox, Abel summation, base & triangle integrals
│   ├── FiniteN.lean            Binomial-to-Poisson limits, hit-count formulas, pointwise dual
│   ├── BaseLimit.lean          1D base expectation limits (baseTerm1, basePenMarg, basePenInter)
│   ├── TriangleGeom.lean       3-point Jacobian change of variables on unitSquarePi 3
│   ├── TriangleCond.lean       Conditional Z-expectation & pointwise convergence (triCondVal)
│   ├── TriangleLimit.lean      Exact triangle-moat level limit (levelGain_tendsto)
│   └── Expectation.lean        Full expectation assembly: baseIntegral + trianglePlanIntegral ≤ β
├── Cert/
│   ├── Kernel.lean             Zero-Mathlib fixed-point integer arithmetic & box verifier kernel
│   ├── Data.lean               Step potential tables, angle table, base_cert_verified
│   ├── Shards/Shard00..23.lean 24 parallel native_decide box shards (2,923 boxes total)
│   ├── AllShards.lean          Shard aggregation + structural checks (total_cert_verified)
│   ├── ArithSound.lean         Soundness of integer sqrt, exp, trig, and interval arithmetic
│   ├── GeomSound.lean          Soundness of integer disk-intersection and 3-disk area bounds
│   ├── BaseSound.lean          Soundness of baseVerifyInt against baseIntegral
│   └── BoxSound.lean           Soundness of verifyBoxInt / verifyShardInt against plan integrals
└── Upper/
    ├── Automaton.lean          Bandwidth-k strip automaton data structures & transitions
    ├── AutomatonSound.lean     Tour-reconstruction soundness of strip automaton runs
    ├── DP.lean                 Concave dynamic-programming operator & induction
    ├── Automaton4.lean         Concrete 56-state bandwidth-4 automaton instantiation
    ├── Costs.lean              Analytic exponential-bin expected edge costs
    ├── ExpBins.lean            Exponential distribution bin partitioning & integrals
    ├── Cert4Spec.lean          Fixed-point integer DP checker specification & soundness
    ├── CostTableSound.lean     Soundness of costFlat1..4 rational tables
    ├── Cert4.lean              Verified DP fixed-point certificate (U = 8549326 / 10^7)
    ├── TourHelpers.lean        Serpentine stitching & deterministic 4√n + 4 tour bound
    ├── StripDPBound.lean       Expected strip tour length bound from concave DP potential
    ├── PoissonRenewal.lean     Poisson renewal process construction on strips
    ├── PoissonSuperposition.lean Superposition coupling across strips
    ├── PoissonCoupling.lean    De-Poissonization to fixed-n i.i.d. uniform points on [0, 1]²
    └── ToBHHBase.lean          Bridge from concave DP certificate to IsBHHConstant β
```

---

## Building and Auditing

### Standard Lake Build

Requires [elan](https://github.com/leanprover/elan) (which automatically installs the toolchain pinned in [`lean-toolchain`](lean-toolchain), `leanprover/lean4:v4.31.0`):

```bash
lake exe cache get
lake build
lake env lean BHHBounds/Audit.lean
```

> **Note on certificate verification time:** Checking all 24 lower-bound shards (`Cert/Shards/Shard00..23.lean`) runs in parallel in a few minutes on a multi-core CPU; `Upper/Cert4.lean` checks the full 56-state bandwidth-4 concave DP fixed point via `native_decide` and is the single longest-running module (~2.5 hours single-threaded on an i9-14900K).

### Using a Prebuilt Mathlib Cache (`build.py`)

If you already have a local Mathlib checkout matching [`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json):

```bash
python build.py --cache /path/to/mathlib-checkout --threads 4 BHHBounds BHHBounds.Audit
```

---

## Axiom Audit

Running `BHHBounds/Audit.lean` confirms that all headline theorems depend **only** on Lean's three standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`) plus the explicit finite integer `native_decide` certificate checks (28 for the lower bound, 5 for the upper bound). Zero `sorryAx` and zero custom axioms appear anywhere in the project.

See [`VERIFICATION.txt`](VERIFICATION.txt) for the complete verbatim build and `#print axioms` transcript.

---

## License & Citation

This codebase is released under the [MIT License](LICENSE). Citation metadata is provided in [`CITATION.cff`](CITATION.cff).
