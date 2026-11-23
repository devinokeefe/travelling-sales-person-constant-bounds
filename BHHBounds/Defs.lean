import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Definitions

Points of the plane, Euclidean distance, disks, the length of a shortest tour, the uniform measure
on `[0, 1]²`, and the predicate `IsBHHConstant`.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace BHHBounds

noncomputable section

/-- A point of the Euclidean plane `ℝ²`, equipped with product Lebesgue measure `volume`. -/
abbrev Pt := ℝ × ℝ

/-- Squared Euclidean distance on `ℝ²`. -/
def sqDist (a b : Pt) : ℝ := (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2

/-- Euclidean distance on `ℝ²`. -/
def euclidDist (a b : Pt) : ℝ := Real.sqrt (sqDist a b)

/-- Euclidean norm on `ℝ²`. -/
def euclidNorm (a : Pt) : ℝ := Real.sqrt (a.1 ^ 2 + a.2 ^ 2)

/-- Closed Euclidean disk `B(c, ρ) = {z : ‖z - c‖ ≤ ρ}` (for `ρ ≥ 0`). -/
def disk (c : Pt) (ρ : ℝ) : Set Pt := {z : Pt | sqDist z c ≤ ρ ^ 2}

/-- Area of the union of closed disks of radius `ρ` centered at `y 0, ..., y (k-1)`. -/
def unionDiskArea {k : ℕ} (y : Fin k → Pt) (ρ : ℝ) : ℝ :=
  (volume (⋃ i, disk (y i) ρ)).toReal

/-- Length of the shortest closed tour visiting `x 0, ..., x (n-1)` in some cyclic order. -/
def tourLength {n : ℕ} (x : Fin n → Pt) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
    euclidDist (x (σ i)) (x (σ (finRotate n i)))

/-- The closed unit square `[0, 1]²`. -/
def unitSquare : Set Pt := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

/-- Uniform probability measure on `[0, 1]²`, defined as the product of uniform `[0, 1]` measures. -/
def unitSquareMeasure : Measure Pt :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))

/-- Product probability measure for `n` i.i.d. uniform points in `[0, 1]²`. -/
def unitSquarePi (n : ℕ) : Measure (Fin n → Pt) :=
  Measure.pi fun _ : Fin n => unitSquareMeasure

/-- Expected shortest tour length of `n` i.i.d. uniform points in `[0, 1]²`. -/
def expectedTourLength (n : ℕ) : ℝ :=
  ∫ x : Fin n → Pt, tourLength x ∂(unitSquarePi n)

/-- `β` is the Beardwood–Halton–Hammersley constant if, for every sequence of i.i.d. uniform
random points `X_0, X_1, ...` in `[0, 1]²`, `tourLength (X_0, ..., X_{n-1}) / √n → β` a.s. -/
def IsBHHConstant (β : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Pt),
    (∀ i, Measurable (X i)) → ProbabilityTheory.iIndepFun X P →
    (∀ i, P.map (X i) = volume.restrict unitSquare) →
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => tourLength (fun i : Fin n => X i ω) / Real.sqrt (n : ℝ))
      Filter.atTop (nhds β)

/-! ## Elementary Distance Lemmas -/

lemma sqDist_nonneg (a b : Pt) : 0 ≤ sqDist a b := by
  unfold sqDist; positivity

lemma sqDist_symm (a b : Pt) : sqDist a b = sqDist b a := by
  unfold sqDist; ring

lemma sqDist_self (a : Pt) : sqDist a a = 0 := by
  unfold sqDist; ring

lemma euclidDist_nonneg (a b : Pt) : 0 ≤ euclidDist a b :=
  Real.sqrt_nonneg _

lemma euclidDist_symm (a b : Pt) : euclidDist a b = euclidDist b a := by
  unfold euclidDist; rw [sqDist_symm]

lemma euclidDist_self (a : Pt) : euclidDist a a = 0 := by
  unfold euclidDist; rw [sqDist_self, Real.sqrt_zero]

lemma euclidDist_sq (a b : Pt) : euclidDist a b ^ 2 = sqDist a b :=
  Real.sq_sqrt (sqDist_nonneg a b)

lemma euclidDist_triangle (a b c : Pt) : euclidDist a c ≤ euclidDist a b + euclidDist b c := by
  have hab := euclidDist_nonneg a b
  have hbc := euclidDist_nonneg b c
  rw [← Real.sqrt_sq (by linarith : 0 ≤ euclidDist a b + euclidDist b c)]
  apply Real.sqrt_le_sqrt
  have hcs : ((a.1 - b.1) * (b.1 - c.1) + (a.2 - b.2) * (b.2 - c.2)) ^ 2 ≤
      sqDist a b * sqDist b c := by
    unfold sqDist; nlinarith [sq_nonneg ((a.1 - b.1) * (b.2 - c.2) - (a.2 - b.2) * (b.1 - c.1))]
  have hprod : (a.1 - b.1) * (b.1 - c.1) + (a.2 - b.2) * (b.2 - c.2) ≤
      euclidDist a b * euclidDist b c := by
    have h1 : (a.1 - b.1) * (b.1 - c.1) + (a.2 - b.2) * (b.2 - c.2) ≤
        Real.sqrt (sqDist a b * sqDist b c) := Real.le_sqrt_of_sq_le hcs
    rwa [Real.sqrt_mul (sqDist_nonneg a b)] at h1
  have hsq_ab := euclidDist_sq a b
  have hsq_bc := euclidDist_sq b c
  unfold sqDist at hsq_ab hsq_bc ⊢
  nlinarith

lemma euclidDist_le_iff {a b : Pt} {r : ℝ} (hr : 0 ≤ r) :
    euclidDist a b ≤ r ↔ sqDist a b ≤ r ^ 2 := by
  unfold euclidDist
  constructor
  · intro h
    have := mul_self_le_mul_self (Real.sqrt_nonneg _) h
    rwa [Real.mul_self_sqrt (sqDist_nonneg a b), ← sq] at this
  · intro h
    rw [← Real.sqrt_sq hr]
    exact Real.sqrt_le_sqrt h

lemma measurableSet_disk (c : Pt) (ρ : ℝ) : MeasurableSet (disk c ρ) := by
  unfold disk sqDist
  exact measurableSet_le (by fun_prop) measurable_const

lemma continuous_euclidDist : Continuous (fun p : Pt × Pt => euclidDist p.1 p.2) := by
  unfold euclidDist sqDist
  fun_prop

end

end BHHBounds
