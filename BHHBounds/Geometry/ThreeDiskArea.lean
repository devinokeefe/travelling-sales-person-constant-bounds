import BHHBounds.Geometry.DiskMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Elementary Three-Disk Union Area Upper Bound

Proves the elementary 7-region planar decomposition upper bound on the union area of three
closed disks of radius R centered at the vertices of a canonical triangle:
  	hreeDiskArea r w ≤ π + r² y / 2 + (chordArea r + chordArea (r ‖w‖) + chordArea (r ‖w - e₁‖)) / 2 + excessX r w
together with scaling to arbitrary radius R > 0 (	hreeDiskArea_scale_le) and the
6th-order polynomial upper bound chordArea_le_poly6.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace BHHBounds.Geometry

noncomputable section

/-- The open quarter-lens `L_q = {0 < x < 1/2, y > 0, (1 - x)² + y² < 1}`. -/
def quarterLens : Set Pt :=
  {w : Pt | 0 < w.1 ∧ w.1 < 1 / 2 ∧ 0 < w.2 ∧ (1 - w.1) ^ 2 + w.2 ^ 2 < 1}

lemma measurableSet_quarterLens : MeasurableSet quarterLens := by
  unfold quarterLens
  have h1 : MeasurableSet {w : Pt | 0 < w.1} := measurableSet_lt measurable_const measurable_fst
  have h2 : MeasurableSet {w : Pt | w.1 < (1 / 2 : ℝ)} := measurableSet_lt measurable_fst measurable_const
  have h3 : MeasurableSet {w : Pt | 0 < w.2} := measurableSet_lt measurable_const measurable_snd
  have h4 : MeasurableSet {w : Pt | (1 - w.1) ^ 2 + w.2 ^ 2 < 1} :=
    measurableSet_lt (by fun_prop) measurable_const
  exact h1.inter (h2.inter (h3.inter h4))

lemma quarterLens_norm_lt_one {w : Pt} (hw : w ∈ quarterLens) : w.1 ^ 2 + w.2 ^ 2 < 1 := by
  rcases hw with ⟨hx0, hx1, _, hcirc⟩
  nlinarith

lemma quarterLens_euclidNorm_lt_one {w : Pt} (hw : w ∈ quarterLens) : euclidNorm w < 1 := by
  unfold euclidNorm
  rw [Real.sqrt_lt' zero_lt_one, one_pow]
  exact quarterLens_norm_lt_one hw

lemma quarterLens_euclidNorm_sub_lt_one {w : Pt} (hw : w ∈ quarterLens) : euclidNorm (1 - w.1, w.2) < 1 := by
  unfold euclidNorm
  rw [Real.sqrt_lt' zero_lt_one, one_pow]
  exact hw.2.2.2

/-- Canonical triangle configuration with longest side `A = (0,0)`, `B = (r,0)` and third vertex `C = (r x, r y)`. -/
def triCfg (r : ℝ) (w : Pt) : Fin 3 → Pt :=
  ![(0 : Pt), (r, 0), (r * w.1, r * w.2)]

/-- Union area of the three unit disks at `triCfg r w`. -/
def threeDiskArea (r : ℝ) (w : Pt) : ℝ := unionDiskArea (triCfg r w) 1

/-- Chord area function `c(d) = 2 ∫₀ᵈ √(1 - u²/4) du`. -/
def chordArea (d : ℝ) : ℝ :=
  2 * ∫ u in (0 : ℝ)..d, Real.sqrt (1 - u ^ 2 / 4)

/-- 6th-order polynomial upper bound for `c(d)`. -/
def chordPoly6 (d : ℝ) : ℝ :=
  2 * d - (1 / 12) * d ^ 3 - (1 / 320) * d ^ 5 - (1 / 3584) * d ^ 7
    - (5 / 147456) * d ^ 9 - (7 / 1441792) * d ^ 11 - (21 / 27262976) * d ^ 13

/-- Opposite-vertex disk excess `X(r, w)` across the longest side `AB`. -/
def excessX (r : ℝ) (w : Pt) : ℝ :=
  ∫ s in (0 : ℝ)..r,
    max 0 (Real.sqrt (max 0 (1 - (s - r * w.1) ^ 2)) - r * w.2 - Real.sqrt (1 - (min s (r - s)) ^ 2))

/-- Complete elementary upper bound on `threeDiskArea r w`. -/
def threeDiskAreaBound (r : ℝ) (w : Pt) : ℝ :=
  Real.pi + r ^ 2 * w.2 / 2
    + (chordArea r + chordArea (r * euclidNorm w) + chordArea (r * euclidNorm (1 - w.1, w.2))) / 2
    + excessX r w

/-! ## Section 1: Analytic Properties of `chordArea` and `a ↦ a^(-5/2)` -/

lemma chordArea_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ chordArea d := by
  unfold chordArea
  apply mul_nonneg (by norm_num)
  exact intervalIntegral.integral_nonneg hd (fun _ _ => Real.sqrt_nonneg _)

lemma chordArea_monoOn : MonotoneOn chordArea (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  unfold chordArea
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hint : ∀ x y, IntervalIntegrable (fun u : ℝ => Real.sqrt (1 - u ^ 2 / 4)) volume x y :=
    fun x y => (by fun_prop : Continuous fun u : ℝ => Real.sqrt (1 - u ^ 2 / 4)).intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)]
  have hnn : 0 ≤ ∫ u in a..b, Real.sqrt (1 - u ^ 2 / 4) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Real.sqrt_nonneg _)
  linarith

lemma chordArea_concaveOn : ConcaveOn ℝ (Icc (0 : ℝ) 1) chordArea := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have aux : ∀ u v t : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 → 0 ≤ t → t ≤ 1 →
      (1 - t) * chordArea u + t * chordArea v ≤ chordArea ((1 - t) * u + t * v) := by
    intro u v t hu huv hv ht0 ht1
    set m : ℝ := (1 - t) * u + t * v
    have hum : u ≤ m := by dsimp only [m]; nlinarith
    have hmv : m ≤ v := by dsimp only [m]; nlinarith
    have hm0 : 0 ≤ m := hu.trans hum
    have hm1 : m ≤ 1 := hmv.trans hv
    have hint : ∀ p q, IntervalIntegrable (fun s : ℝ => Real.sqrt (1 - s ^ 2 / 4)) volume p q :=
      fun p q => (by fun_prop : Continuous fun s : ℝ => Real.sqrt (1 - s ^ 2 / 4)).intervalIntegrable p q
    have hbm : chordArea v - chordArea m ≤ 2 * (v - m) * Real.sqrt (1 - m ^ 2 / 4) := by
      unfold chordArea
      have hsub : (∫ s in (0 : ℝ)..v, Real.sqrt (1 - s ^ 2 / 4)) -
          (∫ s in (0 : ℝ)..m, Real.sqrt (1 - s ^ 2 / 4)) =
          ∫ s in m..v, Real.sqrt (1 - s ^ 2 / 4) := by
        linarith [intervalIntegral.integral_add_adjacent_intervals (hint 0 m) (hint m v)]
      rw [← mul_sub, hsub]
      have hle : ∫ s in m..v, Real.sqrt (1 - s ^ 2 / 4) ≤
          ∫ _s in m..v, Real.sqrt (1 - m ^ 2 / 4) := by
        apply intervalIntegral.integral_mono_on hmv (hint m v) intervalIntegrable_const
        intro s hs
        apply Real.sqrt_le_sqrt
        nlinarith [hs.1, hm0]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hle
      linarith
    have hma : 2 * (m - u) * Real.sqrt (1 - m ^ 2 / 4) ≤ chordArea m - chordArea u := by
      unfold chordArea
      have hsub : (∫ s in (0 : ℝ)..m, Real.sqrt (1 - s ^ 2 / 4)) -
          (∫ s in (0 : ℝ)..u, Real.sqrt (1 - s ^ 2 / 4)) =
          ∫ s in u..m, Real.sqrt (1 - s ^ 2 / 4) := by
        linarith [intervalIntegral.integral_add_adjacent_intervals (hint 0 u) (hint u m)]
      rw [← mul_sub, hsub]
      have hge : ∫ _s in u..m, Real.sqrt (1 - m ^ 2 / 4) ≤
          ∫ s in u..m, Real.sqrt (1 - s ^ 2 / 4) := by
        apply intervalIntegral.integral_mono_on hum intervalIntegrable_const (hint u m)
        intro s hs
        apply Real.sqrt_le_sqrt
        nlinarith [hs.1, hs.2, hu]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hge
      linarith
    have hbal : t * (v - m) = (1 - t) * (m - u) := by dsimp only [m]; ring
    have h1 := mul_le_mul_of_nonneg_left hbm ht0
    have h2 := mul_le_mul_of_nonneg_left hma (by linarith : 0 ≤ 1 - t)
    nlinarith [h1, h2, hbal]
  have ha1 : a = 1 - b := by linarith
  subst ha1
  rcases le_total x y with hxy | hyx
  · simpa [smul_eq_mul] using aux x y b hx.1 hxy hy.2 hb (by linarith)
  · have h := aux y x (1 - b) hy.1 hyx hx.2 (by linarith) (by linarith)
    have h1 : (1 - (1 - b)) * y + (1 - b) * x = (1 - b) * x + b * y := by ring
    have h2 : (1 - (1 - b)) * chordArea y + (1 - b) * chordArea x =
        (1 - b) * chordArea x + b * chordArea y := by ring
    rw [h1, h2] at h
    simpa [smul_eq_mul] using h

lemma sqrt_one_sub_le_poly6 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    Real.sqrt (1 - t) ≤
      1 - t / 2 - t ^ 2 / 8 - t ^ 3 / 16 - 5 / 128 * t ^ 4 - 7 / 256 * t ^ 5 - 21 / 1024 * t ^ 6 := by
  set P : ℝ := 1 - t / 2 - t ^ 2 / 8 - t ^ 3 / 16 - 5 / 128 * t ^ 4 - 7 / 256 * t ^ 5 - 21 / 1024 * t ^ 6
  have hP_nn : 0 ≤ P := by
    have ht2 : t ^ 2 ≤ 1 / 16 := by nlinarith
    have ht3 : t ^ 3 ≤ 1 / 64 := by nlinarith
    have ht4 : t ^ 4 ≤ 1 / 256 := by nlinarith
    have ht5 : t ^ 5 ≤ 1 / 1024 := by nlinarith
    have ht6 : t ^ 6 ≤ 1 / 4096 := by nlinarith
    dsimp only [P]; linarith
  rw [Real.sqrt_le_left hP_nn]
  have hdiff : P ^ 2 - (1 - t) =
      (33 / 1024) * t ^ 7 + (165 / 16384) * t ^ 8 + (77 / 16384) * t ^ 9 +
      (77 / 32768) * t ^ 10 + (147 / 131072) * t ^ 11 + (441 / 1048576) * t ^ 12 := by
    dsimp only [P]; ring
  have hnn : 0 ≤ P ^ 2 - (1 - t) := by rw [hdiff]; positivity
  linarith

lemma chordArea_le_poly6 {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    chordArea d ≤ chordPoly6 d := by
  unfold chordArea chordPoly6
  let g : ℝ → ℝ := fun u =>
    1 - u ^ 2 / 8 - u ^ 4 / 128 - u ^ 6 / 1024 - 5 / 32768 * u ^ 8 -
      7 / 262144 * u ^ 10 - 21 / 4194304 * u ^ 12
  have hpt : ∀ u ∈ Icc (0 : ℝ) d, Real.sqrt (1 - u ^ 2 / 4) ≤ g u := by
    intro u hu
    have ht0 : 0 ≤ u ^ 2 / 4 := by positivity
    have ht1 : u ^ 2 / 4 ≤ 1 / 4 := by nlinarith [hu.1, hu.2, hd1]
    have h := sqrt_one_sub_le_poly6 ht0 ht1
    refine h.trans_eq ?_
    dsimp only [g]; ring
  have hint1 : IntervalIntegrable (fun u : ℝ => Real.sqrt (1 - u ^ 2 / 4)) volume 0 d :=
    (by fun_prop : Continuous fun u : ℝ => Real.sqrt (1 - u ^ 2 / 4)).intervalIntegrable 0 d
  have hint2 : IntervalIntegrable g volume 0 d :=
    (by fun_prop : Continuous g).intervalIntegrable 0 d
  have hle := intervalIntegral.integral_mono_on hd0 hint1 hint2 hpt
  have hval : 2 * ∫ u in (0 : ℝ)..d, g u =
      2 * d - (1 / 12) * d ^ 3 - (1 / 320) * d ^ 5 - (1 / 3584) * d ^ 7
        - (5 / 147456) * d ^ 9 - (7 / 1441792) * d ^ 11 - (21 / 27262976) * d ^ 13 := by
    have hp : ∀ k : ℕ, ∫ u in (0 : ℝ)..d, u ^ k = d ^ (k + 1) / (k + 1 : ℝ) := by
      intro k; simp [integral_pow]
    dsimp only [g]
    have hsub : ∀ (f₁ f₂ : ℝ → ℝ), Continuous f₁ → Continuous f₂ →
        ∫ u in (0 : ℝ)..d, (f₁ u - f₂ u) = (∫ u in (0 : ℝ)..d, f₁ u) - (∫ u in (0 : ℝ)..d, f₂ u) :=
      fun f₁ f₂ h₁ h₂ => intervalIntegral.integral_sub (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)
    rw [hsub _ _ (by fun_prop) (by fun_prop),
        hsub _ _ (by fun_prop) (by fun_prop),
        hsub _ _ (by fun_prop) (by fun_prop),
        hsub _ _ (by fun_prop) (by fun_prop),
        hsub _ _ (by fun_prop) (by fun_prop),
        hsub _ _ (by fun_prop) (by fun_prop)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one,
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul, hp]
    norm_num; ring
  linarith

/-! ## Section 2: Elementary 7-Region Decomposition & Union Area Upper Bound -/

/-- Dot product on `Pt = ℝ × ℝ`. -/
@[inline] def dot2 (a b : Pt) : ℝ := a.1 * b.1 + a.2 * b.2

/-- Area of the closed triangle `Δ = conv{(0,0), (r,0), (p,v)}` (`r > 0, v > 0`) is `r * v / 2`. -/
lemma volume_closedTriangle {r p v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    volume {z : Pt | 0 ≤ z.2 ∧ 0 ≤ v * z.1 - p * z.2 ∧ 0 ≤ v * (r - z.1) - (r - p) * z.2} =
      ENNReal.ofReal (r * v / 2) := by
  let Δ : Set Pt := {z : Pt | 0 ≤ z.2 ∧ 0 ≤ v * z.1 - p * z.2 ∧ 0 ≤ v * (r - z.1) - (r - p) * z.2}
  have hmeas : MeasurableSet Δ := by
    have h1 : MeasurableSet {z : Pt | (0 : ℝ) ≤ z.2} := measurableSet_le measurable_const measurable_snd
    have h2 : MeasurableSet {z : Pt | (0 : ℝ) ≤ v * z.1 - p * z.2} := measurableSet_le measurable_const (by fun_prop)
    have h3 : MeasurableSet {z : Pt | (0 : ℝ) ≤ v * (r - z.1) - (r - p) * z.2} :=
      measurableSet_le measurable_const (by fun_prop)
    exact h1.inter (h2.inter h3)
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
  have hslice : ∀ y : ℝ, volume ((fun x => (x, y)) ⁻¹' Δ) =
      if y ∈ Icc (0 : ℝ) v then ENNReal.ofReal (r * (1 - y / v)) else 0 := by
    intro y
    by_cases hy : y ∈ Icc (0 : ℝ) v
    · rw [if_pos hy]
      have heq : (fun x => (x, y)) ⁻¹' Δ = Icc (p * y / v) (r - (r - p) * y / v) := by
        ext x
        simp only [Set.mem_preimage, Δ, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · rintro ⟨_, h1, h2⟩
          constructor
          · rw [div_le_iff₀ hv]; linarith
          · have h3 : (r - p) * y / v ≤ r - x := by rw [div_le_iff₀ hv]; nlinarith
            linarith
        · rintro ⟨h1, h2⟩
          refine ⟨hy.1, ?_, ?_⟩
          · rw [div_le_iff₀ hv] at h1; linarith
          · have h3 : (r - p) * y / v ≤ r - x := by linarith
            rw [div_le_iff₀ hv] at h3; nlinarith
      rw [heq, Real.volume_Icc]
      congr 1; field_simp [ne_of_gt hv]; ring
    · rw [if_neg hy]
      have hempty : (fun x => (x, y)) ⁻¹' Δ = ∅ := by
        ext x
        simp only [Set.mem_preimage, Δ, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h0, h1, h2⟩
        have hsum : 0 ≤ r * (v - y) := by linarith
        have hyv : y ≤ v := by nlinarith
        exact hy ⟨h0, hyv⟩
      rw [hempty, measure_empty]
  simp_rw [hslice]
  have hsupp : Function.support (fun y : ℝ => if y ∈ Icc (0 : ℝ) v then ENNReal.ofReal (r * (1 - y / v)) else 0) ⊆
      Icc 0 v := by
    intro y hy
    by_contra hnot
    exact hy (if_neg hnot)
  rw [← setLIntegral_eq_of_support_subset hsupp]
  have heq : ∀ y ∈ Icc (0 : ℝ) v,
      (if y ∈ Icc (0 : ℝ) v then ENNReal.ofReal (r * (1 - y / v)) else 0) = ENNReal.ofReal (r * (1 - y / v)) :=
    fun y hy => if_pos hy
  rw [setLIntegral_congr_fun measurableSet_Icc heq]
  have hint : IntegrableOn (fun y : ℝ => r * (1 - y / v)) (Icc 0 v) volume :=
    (by fun_prop : Continuous fun y : ℝ => r * (1 - y / v)).integrableOn_Icc
  have hnn : ∀ y ∈ Icc (0 : ℝ) v, 0 ≤ r * (1 - y / v) := by
    intro y hy
    have : y / v ≤ 1 := (div_le_one hv).mpr hy.2
    nlinarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Icc hnn)]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hv)]
  rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const ((by fun_prop : Continuous fun y => y / v).intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one,
      intervalIntegral.integral_div, integral_id]
  field_simp [ne_of_gt hv]; ring

/-- Area of the two endpoint unit disks in the exterior half-strip `[0, d] × (-∞, 0]` (`0 < d ≤ 1`)
equals `chordArea d / 2`. -/
lemma volume_strip_two_disks {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    volume ((disk (0 : Pt) 1 ∪ disk (d, 0) 1) ∩ {z : Pt | 0 ≤ z.1 ∧ z.1 ≤ d ∧ z.2 ≤ 0}) =
      ENNReal.ofReal (chordArea d / 2) := by
  let E : Set Pt := (disk (0 : Pt) 1 ∪ disk (d, 0) 1) ∩ {z : Pt | 0 ≤ z.1 ∧ z.1 ≤ d ∧ z.2 ≤ 0}
  have hmeas : MeasurableSet E := by
    refine MeasurableSet.inter ((measurableSet_disk 0 1).union (measurableSet_disk (d, 0) 1)) ?_
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        (measurableSet_le measurable_snd measurable_const))
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have hslice : ∀ s : ℝ, volume ((fun y => (s, y)) ⁻¹' E) =
      if s ∈ Icc (0 : ℝ) d then ENNReal.ofReal (Real.sqrt (1 - (min s (d - s)) ^ 2)) else 0 := by
    intro s
    by_cases hs : s ∈ Icc (0 : ℝ) d
    · rw [if_pos hs]
      set m : ℝ := min s (d - s)
      have hm0 : 0 ≤ m := le_min hs.1 (by linarith [hs.2])
      have hm1 : m ≤ 1 := (min_le_left _ _).trans (hs.2.trans hd1)
      have h1m2 : 0 ≤ 1 - m ^ 2 := by nlinarith
      have heq : (fun y => (s, y)) ⁻¹' E = Icc (-Real.sqrt (1 - m ^ 2)) 0 := by
        ext y
        simp only [Set.mem_preimage, E, Set.mem_inter_iff, Set.mem_union, disk, sqDist,
          Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, one_pow, Set.mem_Icc]
        constructor
        · rintro ⟨h1 | h2, _, _, hy0⟩
          · refine ⟨?_, hy0⟩
            have hmy : m ^ 2 ≤ s ^ 2 := by
              have : m ≤ s := min_le_left _ _
              nlinarith
            have hy2 : y ^ 2 ≤ 1 - m ^ 2 := by linarith
            have : (-y) ^ 2 ≤ (Real.sqrt (1 - m ^ 2)) ^ 2 := by rw [Real.sq_sqrt h1m2]; linarith
            nlinarith [Real.sqrt_nonneg (1 - m ^ 2)]
          · refine ⟨?_, hy0⟩
            have hmy : m ^ 2 ≤ (d - s) ^ 2 := by
              have : m ≤ d - s := min_le_right _ _
              nlinarith
            have hy2 : y ^ 2 ≤ 1 - m ^ 2 := by linarith
            have : (-y) ^ 2 ≤ (Real.sqrt (1 - m ^ 2)) ^ 2 := by rw [Real.sq_sqrt h1m2]; linarith
            nlinarith [Real.sqrt_nonneg (1 - m ^ 2)]
        · rintro ⟨hlo, hy0⟩
          refine ⟨?_, hs.1, hs.2, hy0⟩
          have hy2 : y ^ 2 ≤ 1 - m ^ 2 := by
            have : (-y) ≤ Real.sqrt (1 - m ^ 2) := by linarith
            have hsq : (-y) ^ 2 ≤ (Real.sqrt (1 - m ^ 2)) ^ 2 := by nlinarith
            rw [Real.sq_sqrt h1m2] at hsq; linarith
          rcases le_total s (d - s) with hle | hle
          · left
            have : m = s := min_eq_left hle
            rw [this] at hy2; linarith
          · right
            have : m = d - s := min_eq_right hle
            rw [this] at hy2; linarith
      rw [heq, Real.volume_Icc]
      congr 1; ring
    · rw [if_neg hs]
      have hempty : (fun y => (s, y)) ⁻¹' E = ∅ := by
        ext y
        simp only [Set.mem_preimage, E, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, h1, h2, _⟩; exact hs ⟨h1, h2⟩
      rw [hempty, measure_empty]
  simp_rw [hslice]
  have hsupp : Function.support (fun s : ℝ =>
      if s ∈ Icc (0 : ℝ) d then ENNReal.ofReal (Real.sqrt (1 - (min s (d - s)) ^ 2)) else 0) ⊆ Icc 0 d := by
    intro s hs; by_contra hnot; exact hs (if_neg hnot)
  rw [← setLIntegral_eq_of_support_subset hsupp]
  rw [setLIntegral_congr_fun measurableSet_Icc (fun s hs => if_pos hs)]
  have hint : IntegrableOn (fun s : ℝ => Real.sqrt (1 - (min s (d - s)) ^ 2)) (Icc 0 d) volume :=
    (by fun_prop : Continuous fun s : ℝ => Real.sqrt (1 - (min s (d - s)) ^ 2)).integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Icc (fun _ _ => Real.sqrt_nonneg _))]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hd0)]
  -- Split `[0, d]` at `d / 2` and substitute `u = 2 * s`
  have hcont : Continuous fun s : ℝ => Real.sqrt (1 - (min s (d - s)) ^ 2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 (d / 2)) (hcont.intervalIntegrable (d / 2) d)]
  have hleft : ∫ s in (0 : ℝ)..(d / 2), Real.sqrt (1 - (min s (d - s)) ^ 2) =
      ∫ s in (0 : ℝ)..(d / 2), Real.sqrt (1 - s ^ 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ d / 2)] at hs
    dsimp only
    rw [min_eq_left (by linarith [hs.2])]
  have hright : ∫ s in (d / 2)..d, Real.sqrt (1 - (min s (d - s)) ^ 2) =
      ∫ s in (0 : ℝ)..(d / 2), Real.sqrt (1 - s ^ 2) := by
    have h1 : ∫ s in (d / 2)..d, Real.sqrt (1 - (min s (d - s)) ^ 2) =
        ∫ s in (d / 2)..d, Real.sqrt (1 - (d - s) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by linarith : d / 2 ≤ d)] at hs
      dsimp only
      rw [min_eq_right (by linarith [hs.1])]
    rw [h1, intervalIntegral.integral_comp_sub_left (fun t => Real.sqrt (1 - t ^ 2)) d]
    simp [show d - d / 2 = d / 2 by ring]
  rw [hleft, hright]
  unfold chordArea
  have hsub : ∫ u in (0 : ℝ)..d, Real.sqrt (1 - u ^ 2 / 4) =
      2 * ∫ s in (0 : ℝ)..(d / 2), Real.sqrt (1 - s ^ 2) := by
    have h := intervalIntegral.integral_comp_mul_left (fun u : ℝ => Real.sqrt (1 - u ^ 2 / 4))
      (by norm_num : (2 : ℝ) ≠ 0) (a := 0) (b := d / 2)
    have hsim : (fun s : ℝ => Real.sqrt (1 - (2 * s) ^ 2 / 4)) = fun s => Real.sqrt (1 - s ^ 2) := by
      funext s; congr 1; ring
    rw [hsim] at h
    rw [show 2 * (0 : ℝ) = 0 by ring, show 2 * (d / 2) = d by ring, smul_eq_mul] at h
    linarith
  linarith

/-- **Lemma 2 (No Bulge Across Non-Longest Side):**
In coordinates `U = (0,0)`, `V = (d,0)`, `W = (p, v)` (`0 < d ≤ 1`, `v > 0`),
if `W` is strictly farther than `d` from at least one of `U, V`, then `disk W 1` adds no points
outside `disk U 1 ∪ disk V 1` in the exterior half-strip `[0, d] × (-∞, 0]`. -/
lemma no_bulge_nonlongest {d p v : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hv : 0 < v)
    (hnon : d ^ 2 < p ^ 2 + v ^ 2 ∨ d ^ 2 < (d - p) ^ 2 + v ^ 2) :
    disk (p, v) 1 ∩ {z : Pt | 0 ≤ z.1 ∧ z.1 ≤ d ∧ z.2 ≤ 0} ⊆
      disk (0 : Pt) 1 ∪ disk (d, 0) 1 := by
  intro z ⟨hzW, hs0, hsd, hy0⟩
  by_contra hnot
  simp only [Set.mem_union, not_or, disk, sqDist, Set.mem_setOf_eq,
    Prod.fst_zero, Prod.snd_zero, sub_zero, one_pow, not_le] at hnot
  simp only [disk, sqDist, Set.mem_setOf_eq, one_pow] at hzW
  -- Helper: given `0 ≤ t ≤ d / 2`, `t² + h² > 1`, `(t - q)² + (h + v)² ≤ 1` (`h ≥ 0`),
  -- deduce both `q² + v² < d²` and `(d - q)² + v² < d²`.
  have core : ∀ t q h : ℝ, 0 ≤ t → t ≤ d / 2 → 0 ≤ h → 1 < t ^ 2 + h ^ 2 →
      (t - q) ^ 2 + (h + v) ^ 2 ≤ 1 → q ^ 2 + v ^ 2 < d ^ 2 ∧ (d - q) ^ 2 + v ^ 2 < d ^ 2 := by
    intro t q h ht0 htd hh0 hout hin
    have hdiff : q ^ 2 + v ^ 2 - 2 * t * q + 2 * h * v < 0 := by nlinarith
    have hh_pos : 0 < h := by
      have : t ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith
    have hq_pos : 0 < q := by
      by_contra hq0; push Not at hq0
      nlinarith [mul_nonneg ht0 (neg_nonneg.mpr hq0)]
    have h2 : q ^ 2 + v ^ 2 < d * q := by
      have h1 : 2 * t * q ≤ d * q := by nlinarith
      nlinarith [mul_pos hh_pos hv]
    have hq_lt : q < d := by nlinarith [sq_nonneg v]
    constructor
    · nlinarith
    · nlinarith
  rcases le_total z.1 (d / 2) with hle | hge
  · have ⟨h1, h2⟩ := core z.1 p (-z.2) hs0 hle (by linarith) (by linarith [hnot.1]) (by linarith [hzW])
    rcases hnon with h | h <;> linarith
  · have ⟨h1, h2⟩ := core (d - z.1) (d - p) (-z.2) (by linarith) (by linarith) (by linarith)
      (by linarith [hnot.2]) (by linarith [hzW])
    have h2' : p ^ 2 + v ^ 2 < d ^ 2 := by linarith
    rcases hnon with h | h <;> linarith

/-- Excess volume of `disk (p, v) 1 \ (disk 0 1 ∪ disk (d, 0) 1)` inside `[0, d] × (-∞, 0]`. -/
lemma volume_strip_excess_le {r x y : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    volume ((disk (r * x, r * y) 1 \ (disk (0 : Pt) 1 ∪ disk (r, 0) 1)) ∩
        {z : Pt | 0 ≤ z.1 ∧ z.1 ≤ r ∧ z.2 ≤ 0}) ≤ ENNReal.ofReal (excessX r (x, y)) := by
  let E : Set Pt := (disk (r * x, r * y) 1 \ (disk (0 : Pt) 1 ∪ disk (r, 0) 1)) ∩
    {z : Pt | 0 ≤ z.1 ∧ z.1 ≤ r ∧ z.2 ≤ 0}
  have hmeas : MeasurableSet E := by
    refine MeasurableSet.inter (MeasurableSet.diff (measurableSet_disk (r * x, r * y) 1)
      ((measurableSet_disk 0 1).union (measurableSet_disk (r, 0) 1))) ?_
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        (measurableSet_le measurable_snd measurable_const))
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  let f : ℝ → ℝ := fun s =>
    max 0 (Real.sqrt (max 0 (1 - (s - r * x) ^ 2)) - r * y - Real.sqrt (1 - (min s (r - s)) ^ 2))
  have hslice : ∀ s : ℝ, volume ((fun t => (s, t)) ⁻¹' E) ≤
      if s ∈ Icc (0 : ℝ) r then ENNReal.ofReal (f s) else 0 := by
    intro s
    by_cases hs : s ∈ Icc (0 : ℝ) r
    · rw [if_pos hs]
      set m : ℝ := min s (r - s)
      have hm0 : 0 ≤ m := le_min hs.1 (by linarith [hs.2])
      have hm1 : m ≤ 1 := (min_le_left _ _).trans (hs.2.trans hr1)
      have h1m2 : 0 ≤ 1 - m ^ 2 := by nlinarith
      set hi : ℝ := Real.sqrt (max 0 (1 - (s - r * x) ^ 2)) - r * y
      set lo : ℝ := Real.sqrt (1 - m ^ 2)
      have hsub : (fun t => (s, t)) ⁻¹' E ⊆ Icc (-hi) (-lo) := by
        intro t ht
        simp only [Set.mem_preimage, E, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_union,
          not_or, disk, sqDist, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero,
          one_pow, not_le] at ht
        rcases ht with ⟨⟨hin, hout1, hout2⟩, _, _, ht0⟩
        simp only [Set.mem_Icc]
        constructor
        · have h1 : 0 ≤ 1 - (s - r * x) ^ 2 := by nlinarith [sq_nonneg (t - r * y)]
          have h2 : (r * y - t) ^ 2 ≤ (Real.sqrt (max 0 (1 - (s - r * x) ^ 2))) ^ 2 := by
            rw [Real.sq_sqrt (le_max_left _ _), max_eq_right h1]; linarith
          have h3 : r * y - t ≤ Real.sqrt (max 0 (1 - (s - r * x) ^ 2)) := by
            nlinarith [Real.sqrt_nonneg (max 0 (1 - (s - r * x) ^ 2))]
          dsimp only [hi]; linarith
        · have hgt : 1 - m ^ 2 < (-t) ^ 2 := by
            rcases le_total s (r - s) with hle | hle
            · have : m = s := min_eq_left hle
              rw [this]; linarith
            · have : m = r - s := min_eq_right hle
              rw [this]; linarith
          have hsq : lo ^ 2 < (-t) ^ 2 := by dsimp only [lo]; rw [Real.sq_sqrt h1m2]; exact hgt
          have : lo < -t := by nlinarith [Real.sqrt_nonneg (1 - m ^ 2)]
          linarith
      calc volume ((fun t => (s, t)) ⁻¹' E)
          ≤ volume (Icc (-hi) (-lo)) := measure_mono hsub
        _ = ENNReal.ofReal (hi - lo) := by rw [Real.volume_Icc]; congr 1; ring
        _ ≤ ENNReal.ofReal (f s) := ENNReal.ofReal_le_ofReal (le_max_right 0 (hi - lo))
    · rw [if_neg hs]
      have hempty : (fun t => (s, t)) ⁻¹' E = ∅ := by
        ext t
        simp only [Set.mem_preimage, E, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, h1, h2, _⟩; exact hs ⟨h1, h2⟩
      rw [hempty, measure_empty]
  calc ∫⁻ s : ℝ, volume ((fun t => (s, t)) ⁻¹' E)
      ≤ ∫⁻ s : ℝ, (if s ∈ Icc (0 : ℝ) r then ENNReal.ofReal (f s) else 0) := lintegral_mono hslice
    _ = ∫⁻ s in Icc (0 : ℝ) r, ENNReal.ofReal (f s) := by
        have hsupp : Function.support (fun s : ℝ => if s ∈ Icc (0 : ℝ) r then ENNReal.ofReal (f s) else 0) ⊆
            Icc 0 r := fun s hs => by by_contra hnot; exact hs (if_neg hnot)
        rw [← setLIntegral_eq_of_support_subset hsupp]
        exact setLIntegral_congr_fun measurableSet_Icc (fun s hs => if_pos hs)
    _ = ENNReal.ofReal (excessX r (x, y)) := by
        have hint : IntegrableOn f (Icc 0 r) volume :=
          (by fun_prop : Continuous f).integrableOn_Icc
        rw [← ofReal_integral_eq_lintegral_ofReal hint
            (ae_restrict_of_forall_mem measurableSet_Icc (fun s _ => le_max_left _ _))]
        congr 1
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hr0)]
        rfl

/-- **Corner Test for `excessX r w = 0`:**
If the meeting point `Q = (r/2, -√(1 - r²/4))` lies outside the interior of `disk (r x, r y) 1`,
then `excessX r (x, y) = 0`. -/
lemma excessX_eq_zero_of_corner {r : ℝ} {w : Pt} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hx0 : 0 ≤ w.1) (hx1 : w.1 ≤ 1 / 2) (hy0 : 0 ≤ w.2)
    (hQ : 1 ≤ (r / 2 - r * w.1) ^ 2 + (r * w.2 + Real.sqrt (1 - r ^ 2 / 4)) ^ 2) :
    excessX r w = 0 := by
  unfold excessX
  set p : ℝ := r * w.1
  set v : ℝ := r * w.2
  have hp0 : 0 ≤ p := mul_nonneg (le_of_lt hr0) hx0
  have hp_le : p ≤ r / 2 := by dsimp only [p]; nlinarith
  have hv0 : 0 ≤ v := mul_nonneg (le_of_lt hr0) hy0
  have h1r4 : 0 ≤ 1 - r ^ 2 / 4 := by nlinarith
  have hQ_alg : 0 ≤ p ^ 2 + v ^ 2 - r * p + 2 * v * Real.sqrt (1 - r ^ 2 / 4) := by
    have hsq : Real.sqrt (1 - r ^ 2 / 4) ^ 2 = 1 - r ^ 2 / 4 := Real.sq_sqrt h1r4
    nlinarith [hQ, hsq]
  have hzero : ∀ s ∈ uIcc (0 : ℝ) r,
      max 0 (Real.sqrt (max 0 (1 - (s - p) ^ 2)) - v - Real.sqrt (1 - (min s (r - s)) ^ 2)) = 0 := by
    intro s hs
    rw [uIcc_of_le (le_of_lt hr0)] at hs
    apply max_eq_left
    set m : ℝ := min s (r - s)
    have hm0 : 0 ≤ m := le_min hs.1 (by linarith [hs.2])
    have hm_le : m ≤ r / 2 := by
      rcases le_total s (r / 2) with h | h
      · exact (min_le_left _ _).trans h
      · exact (min_le_right _ _).trans (by linarith)
    have h1m2 : 0 ≤ 1 - m ^ 2 := by nlinarith
    have hsq_ge : Real.sqrt (1 - r ^ 2 / 4) ≤ Real.sqrt (1 - m ^ 2) := by
      apply Real.sqrt_le_sqrt; nlinarith
    by_cases hneg : 1 - (s - p) ^ 2 ≤ 0
    · rw [max_eq_left hneg, Real.sqrt_zero]
      linarith [Real.sqrt_nonneg (1 - m ^ 2)]
    · push Not at hneg
      rw [max_eq_right (le_of_lt hneg)]
      have hrhs_nn : 0 ≤ v + Real.sqrt (1 - m ^ 2) := add_nonneg hv0 (Real.sqrt_nonneg _)
      suffices hle : Real.sqrt (1 - (s - p) ^ 2) ≤ v + Real.sqrt (1 - m ^ 2) by linarith
      rw [Real.sqrt_le_left hrhs_nn]
      have hsqm : Real.sqrt (1 - m ^ 2) ^ 2 = 1 - m ^ 2 := Real.sq_sqrt h1m2
      -- Compare `(1 - (s - p)²) ≤ (v + √(1 - m²))²` on both halves `[0, r/2]` and `[r/2, r]`
      rcases le_total s (r / 2) with hle | hge
      · have hms : m = s := min_eq_left (by linarith)
        have h1 : 2 * s * p ≤ r * p := by nlinarith
        have h2 : 2 * v * Real.sqrt (1 - r ^ 2 / 4) ≤ 2 * v * Real.sqrt (1 - m ^ 2) :=
          mul_le_mul_of_nonneg_left hsq_ge (by linarith)
        rw [hms] at hsqm h2 ⊢
        nlinarith only [hQ_alg, hsqm, h1, h2]
      · have hms : m = r - s := min_eq_right (by linarith)
        set t : ℝ := r - s
        set q : ℝ := r - p
        have hq0 : 0 ≤ q := by dsimp only [q]; linarith
        have ht_le : t ≤ r / 2 := by dsimp only [t]; linarith
        have hid : q ^ 2 - r * q = p ^ 2 - r * p := by dsimp only [q]; ring
        have h1 : 2 * t * q ≤ r * q := by nlinarith
        have h2 : 2 * v * Real.sqrt (1 - r ^ 2 / 4) ≤ 2 * v * Real.sqrt (1 - m ^ 2) :=
          mul_le_mul_of_nonneg_left hsq_ge (by linarith)
        have hsp : s - p = q - t := by dsimp only [q, t]; ring
        have hmt : m = t := hms
        rw [hmt] at hsqm h2 ⊢
        nlinarith only [hQ_alg, hid, hsqm, h1, h2, hsp]
  rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]

/-- Geometric upper bound on the union area of three unit disks: for every `r ∈ (0, 1)` and
`w ∈ quarterLens`, the union area of the three unit disks at `A = (0, 0)`, `B = (r, 0)`,
`C = (r * w.1, r * w.2)` satisfies `0 < threeDiskArea r w ≤ threeDiskAreaBound r w`. -/
theorem threeDiskArea_le {r : ℝ} {w : Pt} (hr : r ∈ Ioo (0 : ℝ) 1) (hw : w ∈ quarterLens) :
    0 < threeDiskArea r w ∧ threeDiskArea r w ≤ threeDiskAreaBound r w := by
  have hr0 : 0 < r := hr.1
  have hr1 : r ≤ 1 := le_of_lt hr.2
  set A : Pt := (0, 0)
  set B : Pt := (r, 0)
  set p : ℝ := r * w.1
  set v : ℝ := r * w.2
  set C : Pt := (p, v)
  have hp0 : 0 < p := mul_pos hr0 hw.1
  have hpr : p < r := by dsimp only [p]; nlinarith [hw.2.1]
  have hv0 : 0 < v := mul_pos hr0 hw.2.2.1
  have hUeq : (⋃ i : Fin 3, disk (triCfg r w i) 1) = disk A 1 ∪ disk B 1 ∪ disk C 1 := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · left; left; exact hi
      · left; right; simpa [triCfg, B] using hi
      · right; simpa [triCfg, C, p, v] using hi
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, by simpa [triCfg, B] using h⟩
      · exact ⟨2, by simpa [triCfg, C, p, v] using h⟩
  set U : Set Pt := disk A 1 ∪ disk B 1 ∪ disk C 1
  -- Define the 7 regions covering `ℝ²`: Δ, three vertex normal cones S_A, S_B, S_C, three exterior strips R_AB, R_CA, R_BC
  let Δ : Set Pt := {z : Pt | 0 ≤ z.2 ∧ 0 ≤ v * z.1 - p * z.2 ∧ 0 ≤ v * (r - z.1) - (r - p) * z.2}
  let SA : Set Pt := {z : Pt | dot2 (z - A) (B - A) ≤ 0 ∧ dot2 (z - A) (C - A) ≤ 0}
  let SB : Set Pt := {z : Pt | dot2 (z - B) (A - B) ≤ 0 ∧ dot2 (z - B) (C - B) ≤ 0}
  let SC : Set Pt := {z : Pt | dot2 (z - C) (A - C) ≤ 0 ∧ dot2 (z - C) (B - C) ≤ 0}
  let RAB : Set Pt := {z : Pt | 0 ≤ z.1 ∧ z.1 ≤ r ∧ z.2 ≤ 0}
  let RCA : Set Pt := {z : Pt | 0 ≤ dot2 (z - A) (C - A) ∧ dot2 (z - A) (C - A) ≤ sqDist C A ∧ v * z.1 - p * z.2 ≤ 0}
  let RBC : Set Pt := {z : Pt | 0 ≤ dot2 (z - B) (C - B) ∧ dot2 (z - B) (C - B) ≤ sqDist C B ∧ v * (r - z.1) - (r - p) * z.2 ≤ 0}
  -- Step 1: The 7 regions cover `ℝ²`
  have hcover : ∀ z : Pt, z ∈ Δ ∨ z ∈ SA ∨ z ∈ SB ∨ z ∈ SC ∨ z ∈ RAB ∨ z ∈ RCA ∨ z ∈ RBC := by
    intro z
    by_cases hz2 : z.2 ≤ 0
    · by_cases hz1l : z.1 < 0
      · right; left
        simp only [SA, dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, sub_zero, Set.mem_setOf_eq]
        constructor <;> nlinarith
      · by_cases hz1r : r < z.1
        · right; right; left
          simp only [SB, dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, zero_sub, sub_zero, Set.mem_setOf_eq]
          constructor <;> nlinarith
        · right; right; right; right; left
          exact ⟨le_of_not_gt hz1l, le_of_not_gt hz1r, hz2⟩
    · push Not at hz2
      by_cases hCA : 0 ≤ v * z.1 - p * z.2
      · by_cases hBC : 0 ≤ v * (r - z.1) - (r - p) * z.2
        · left; exact ⟨le_of_lt hz2, hCA, hBC⟩
        · push Not at hBC
          by_cases hdB : dot2 (z - B) (C - B) < 0
          · right; right; left
            simp only [SB, dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, zero_sub, sub_zero, Set.mem_setOf_eq] at hdB ⊢
            refine ⟨?_, le_of_lt hdB⟩
            have hzv : 0 < z.2 * v := mul_pos hz2 hv0
            have hzr : 0 < z.1 - r := by nlinarith [hdB, hzv, hpr]
            nlinarith [hzr, hr0]
          · push Not at hdB
            by_cases hdB2 : dot2 (z - B) (C - B) ≤ sqDist C B
            · right; right; right; right; right; right
              exact ⟨hdB, hdB2, le_of_lt hBC⟩
            · push Not at hdB2
              have hCB : dot2 (z - C) (B - C) < 0 := by
                simp only [dot2, sqDist, B, C, Prod.fst_sub, Prod.snd_sub, sub_zero] at hdB2 ⊢; nlinarith
              by_cases hCA2 : dot2 (z - C) (A - C) ≤ 0
              · right; right; right; left; exact ⟨hCA2, le_of_lt hCB⟩
              · push Not at hCA2
                -- Then `z.1 < p` and `z.2 > v`, contradicting `0 ≤ v * z.1 - p * z.2`.
                simp only [dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, zero_sub] at hCB hCA2
                have hz1p : z.1 < p := by nlinarith
                have hz2v : v < z.2 := by nlinarith
                nlinarith
      · push Not at hCA
        by_cases hdA : dot2 (z - A) (C - A) < 0
        · right; left
          simp only [SA, dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, sub_zero, Set.mem_setOf_eq] at hdA ⊢
          refine ⟨?_, le_of_lt hdA⟩
          have hzv : 0 < z.2 * v := mul_pos hz2 hv0
          have hz1 : z.1 < 0 := by nlinarith [hdA, hzv, hp0]
          nlinarith [hz1, hr0]
        · push Not at hdA
          by_cases hdA2 : dot2 (z - A) (C - A) ≤ sqDist C A
          · right; right; right; right; right; left
            exact ⟨hdA, hdA2, le_of_lt hCA⟩
          · push Not at hdA2
            have hAC : dot2 (z - C) (A - C) < 0 := by
              simp only [dot2, sqDist, A, C, Prod.fst_sub, Prod.snd_sub, zero_sub, sub_zero] at hdA2 ⊢; nlinarith
            by_cases hBC2 : dot2 (z - C) (B - C) ≤ 0
            · right; right; right; left; exact ⟨le_of_lt hAC, hBC2⟩
            · push Not at hBC2
              simp only [dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, zero_sub] at hAC hBC2
              have hz1p : p < z.1 := by nlinarith
              have hz2v : v < z.2 := by nlinarith
              have hBCout : v * (r - z.1) - (r - p) * z.2 < 0 := by nlinarith
              by_cases hdB : dot2 (z - B) (C - B) < 0
              · right; right; left
                simp only [SB, dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, zero_sub, sub_zero, Set.mem_setOf_eq] at hdB ⊢
                refine ⟨?_, le_of_lt hdB⟩
                have hzv : 0 < z.2 * v := mul_pos hz2 hv0
                have hzr : 0 < z.1 - r := by nlinarith [hdB, hzv, hpr]
                nlinarith [hzr, hr0]
              · push Not at hdB
                right; right; right; right; right; right
                refine ⟨hdB, ?_, le_of_lt hBCout⟩
                simp only [dot2, sqDist, B, C, Prod.fst_sub, Prod.snd_sub, sub_zero] at hBC2 ⊢
                nlinarith
  -- Step 2: Inside each vertex cone `S_V`, `U ∩ S_V ⊆ disk V 1 ∩ S_V`.
  have hconeA : U ∩ SA ⊆ disk A 1 ∩ SA := by
    intro z ⟨hzU, hzS⟩
    refine ⟨?_, hzS⟩
    simp only [SA, dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, sub_zero, Set.mem_setOf_eq] at hzS
    simp only [U, Set.mem_union, disk, sqDist, A, B, C, Set.mem_setOf_eq, sub_zero, one_pow] at hzU ⊢
    rcases hzU with (h | h) | h <;> nlinarith [hzS.1, hzS.2]
  have hconeB : U ∩ SB ⊆ disk B 1 ∩ SB := by
    intro z ⟨hzU, hzS⟩
    refine ⟨?_, hzS⟩
    simp only [SB, dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, zero_sub, sub_zero, Set.mem_setOf_eq] at hzS
    simp only [U, Set.mem_union, disk, sqDist, A, B, C, Set.mem_setOf_eq, sub_zero, one_pow] at hzU ⊢
    rcases hzU with (h | h) | h <;> nlinarith [hzS.1, hzS.2]
  have hconeC : U ∩ SC ⊆ disk C 1 ∩ SC := by
    intro z ⟨hzU, hzS⟩
    refine ⟨?_, hzS⟩
    simp only [SC, dot2, A, B, C, Prod.fst_sub, Prod.snd_sub, zero_sub, Set.mem_setOf_eq] at hzS
    simp only [U, Set.mem_union, disk, sqDist, A, B, C, Set.mem_setOf_eq, sub_zero, one_pow] at hzU ⊢
    rcases hzU with (h | h) | h <;> nlinarith [hzS.1, hzS.2]
  -- Step 3: Total volume of the 3 vertex cones is at most `π` (a.e.-disjoint translates inside `disk 0 1`).
  have hcones_vol : volume (disk A 1 ∩ SA) + volume (disk B 1 ∩ SB) + volume (disk C 1 ∩ SC) ≤
      ENNReal.ofReal Real.pi := by
    let TA : Set Pt := {u : Pt | sqDist u 0 ≤ 1 ∧ dot2 u (B - A) ≤ 0 ∧ dot2 u (C - A) ≤ 0}
    let TB : Set Pt := {u : Pt | sqDist u 0 ≤ 1 ∧ dot2 u (A - B) ≤ 0 ∧ dot2 u (C - B) ≤ 0}
    let TC : Set Pt := {u : Pt | sqDist u 0 ≤ 1 ∧ dot2 u (A - C) ≤ 0 ∧ dot2 u (B - C) ≤ 0}
    have hTA : volume (disk A 1 ∩ SA) = volume TA := by
      congr 1; ext u
      have huA : u - A = u := by ext <;> simp [A]
      simp [TA, disk, SA, A, sqDist, huA]
    have hTB : volume (disk B 1 ∩ SB) = volume TB := by
      rw [← measure_preimage_add_right volume B (disk B 1 ∩ SB)]
      congr 1; ext u
      simp only [Set.mem_preimage, Set.mem_inter_iff, disk, SB, TB, sqDist, dot2, Set.mem_setOf_eq,
        Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, add_sub_cancel_right,
        Prod.fst_zero, Prod.snd_zero, sub_zero, one_pow]
    have hTC : volume (disk C 1 ∩ SC) = volume TC := by
      rw [← measure_preimage_add_right volume C (disk C 1 ∩ SC)]
      congr 1; ext u
      simp only [Set.mem_preimage, Set.mem_inter_iff, disk, SC, TC, sqDist, dot2, Set.mem_setOf_eq,
        Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, add_sub_cancel_right,
        Prod.fst_zero, Prod.snd_zero, sub_zero, one_pow]
    rw [hTA, hTB, hTC]
    have hmCone : ∀ (v₁ v₂ : Pt), MeasurableSet {u : Pt | sqDist u 0 ≤ 1 ∧ dot2 u v₁ ≤ 0 ∧ dot2 u v₂ ≤ 0} := by
      intro v₁ v₂
      have h1 : MeasurableSet {u : Pt | sqDist u 0 ≤ 1} := by
        unfold sqDist; exact measurableSet_le (by fun_prop) measurable_const
      have h2 : MeasurableSet {u : Pt | dot2 u v₁ ≤ 0} := by
        unfold dot2; exact measurableSet_le (by fun_prop) measurable_const
      have h3 : MeasurableSet {u : Pt | dot2 u v₂ ≤ 0} := by
        unfold dot2; exact measurableSet_le (by fun_prop) measurable_const
      exact h1.inter (h2.inter h3)
    have hmB : MeasurableSet TB := hmCone (A - B) (C - B)
    have hmC : MeasurableSet TC := hmCone (A - C) (B - C)
    have hdAB : volume (TA ∩ TB) = 0 := by
      refine measure_mono_null (t := {u : Pt | r * u.1 + 0 * u.2 = 0}) ?_ (volume_line_zero (Or.inl (ne_of_gt hr0)))
      intro u ⟨huA, huB⟩
      simp only [TA, TB, dot2, A, B, Prod.fst_sub, Prod.snd_sub, zero_sub, sub_zero, Set.mem_setOf_eq] at huA huB ⊢
      linarith [huA.2.1, huB.2.1]
    have hdAC : volume (TA ∩ TC) = 0 := by
      refine measure_mono_null (t := {u : Pt | p * u.1 + v * u.2 = 0}) ?_ (volume_line_zero (Or.inr (ne_of_gt hv0)))
      intro u ⟨huA, huC⟩
      simp only [TA, TC, dot2, A, C, Prod.fst_sub, Prod.snd_sub, zero_sub, sub_zero, Set.mem_setOf_eq] at huA huC ⊢
      linarith [huA.2.2, huC.2.1]
    have hdBC : volume (TB ∩ TC) = 0 := by
      refine measure_mono_null (t := {u : Pt | (p - r) * u.1 + v * u.2 = 0}) ?_ (volume_line_zero (Or.inr (ne_of_gt hv0)))
      intro u ⟨huB, huC⟩
      simp only [TB, TC, dot2, B, C, Prod.fst_sub, Prod.snd_sub, zero_sub, sub_zero, Set.mem_setOf_eq] at huB huC ⊢
      linarith [huB.2.2, huC.2.2]
    have hdisjABC : volume ((TA ∪ TB) ∩ TC) = 0 := by
      rw [Set.union_inter_distrib_right]
      exact measure_union_null hdAC hdBC
    have hsum1 : volume TA + volume TB = volume (TA ∪ TB) := by
      rw [← measure_union_add_inter TA hmB, hdAB, add_zero]
    have hsum2 : volume (TA ∪ TB) + volume TC = volume ((TA ∪ TB) ∪ TC) := by
      rw [← measure_union_add_inter (TA ∪ TB) hmC, hdisjABC, add_zero]
    rw [hsum1, hsum2, ← volume_disk_one 0]
    apply measure_mono
    intro u hu
    rcases hu with (h | h) | h <;> simpa [disk, one_pow] using h.1
  -- Step 4: Strip `R_AB` has volume `≤ chordArea r / 2 + excessX r w`
  have hRAB_vol : volume (U ∩ RAB) ≤ ENNReal.ofReal (chordArea r / 2) + ENNReal.ofReal (excessX r w) := by
    have hsub : U ∩ RAB ⊆ ((disk A 1 ∪ disk B 1) ∩ RAB) ∪ ((disk C 1 \ (disk A 1 ∪ disk B 1)) ∩ RAB) := by
      intro z ⟨hzU, hzR⟩
      by_cases h12 : z ∈ disk A 1 ∪ disk B 1
      · left; exact ⟨h12, hzR⟩
      · right
        rcases hzU with h | hC
        · exact absurd h h12
        · exact ⟨⟨hC, h12⟩, hzR⟩
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    exact add_le_add (le_of_eq (volume_strip_two_disks hr0 hr1)) (volume_strip_excess_le hr0 hr1)
  -- Step 5: Strip `R_CA` has volume at most `chordArea (r * euclidNorm w) / 2`.
  have hRCA_vol : volume (U ∩ RCA) ≤ ENNReal.ofReal (chordArea (r * euclidNorm w) / 2) := by
    set d2 : ℝ := r * euclidNorm w
    have hd2_sq : d2 ^ 2 = p ^ 2 + v ^ 2 := by
      dsimp only [d2, euclidNorm, p, v]
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hd2_pos : 0 < d2 := mul_pos hr0 (Real.sqrt_pos.mpr (by nlinarith [hw.1, hw.2.2.1]))
    have hd2_lt_r : d2 < r := by
      have := quarterLens_euclidNorm_lt_one hw; nlinarith
    have hd2_le1 : d2 ≤ 1 := le_of_lt (hd2_lt_r.trans hr.2)
    -- Map `RCA` to `[0, d2] × (-∞, 0]` by rotation aligning `C - A = (p, v)` with `(d2, 0)` and reflecting `y`
    set c : ℝ := p / d2
    set s : ℝ := v / d2
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      dsimp only [c, s]; field_simp [ne_of_gt hd2_pos]; linarith [hd2_sq]
    let R := rotLinearEquiv c s hcs
    let T : Pt → Pt := fun z => reflYLinearEquiv (R z)
    have hmpT : MeasurePreserving T volume volume :=
      measurePreserving_reflY.comp (measurePreserving_rotLinearEquiv c s hcs)
    have hT_sq : ∀ z₁ z₂, sqDist (T z₁) (T z₂) = sqDist z₁ z₂ := by
      intro z₁ z₂
      have hrefl : sqDist (reflYLinearEquiv (R z₁)) (reflYLinearEquiv (R z₂)) = sqDist (R z₁) (R z₂) := by
        simp only [reflYLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sqDist]; ring
      rw [show T z₁ = reflYLinearEquiv (R z₁) from rfl, show T z₂ = reflYLinearEquiv (R z₂) from rfl,
          hrefl, rotLinearEquiv_sqDist]
    have hTA : T A = 0 := by
      ext <;> simp [T, R, A, rotLinearEquiv, reflYLinearEquiv]
    have hTC : T C = (d2, 0) := by
      ext
      · simp only [T, R, C, rotLinearEquiv, reflYLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, c, s]
        field_simp [ne_of_gt hd2_pos]; linarith [hd2_sq]
      · simp only [T, R, C, rotLinearEquiv, reflYLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, c, s]
        field_simp [ne_of_gt hd2_pos]; ring
    set pB : ℝ := c * r
    set vB : ℝ := s * r
    have hTB : T B = (pB, vB) := by
      ext <;> simp [T, R, B, rotLinearEquiv, reflYLinearEquiv, pB, vB]
    have hvB_pos : 0 < vB := mul_pos (div_pos hv0 hd2_pos) hr0
    have hBnon : d2 ^ 2 < pB ^ 2 + vB ^ 2 ∨ d2 ^ 2 < (d2 - pB) ^ 2 + vB ^ 2 := by
      left
      have : pB ^ 2 + vB ^ 2 = r ^ 2 := by
        have : pB ^ 2 + vB ^ 2 = (c ^ 2 + s ^ 2) * r ^ 2 := by dsimp only [pB, vB]; ring
        rw [this, hcs, one_mul]
      rw [this]; nlinarith
    let Target : Set Pt := (disk (0 : Pt) 1 ∪ disk (d2, 0) 1) ∩ {z : Pt | 0 ≤ z.1 ∧ z.1 ≤ d2 ∧ z.2 ≤ 0}
    have hmeasT : MeasurableSet Target := by
      refine MeasurableSet.inter ((measurableSet_disk 0 1).union (measurableSet_disk (d2, 0) 1)) ?_
      exact (measurableSet_le measurable_const measurable_fst).inter
        ((measurableSet_le measurable_fst measurable_const).inter
          (measurableSet_le measurable_snd measurable_const))
    have hsub : U ∩ RCA ⊆ T ⁻¹' Target := by
      intro z ⟨hzU, hzR⟩
      simp only [Set.mem_preimage, Target, Set.mem_inter_iff]
      have hzR' : 0 ≤ (T z).1 ∧ (T z).1 ≤ d2 ∧ (T z).2 ≤ 0 := by
        simp only [RCA, dot2, sqDist, A, C, Prod.fst_sub, Prod.snd_sub, sub_zero, Set.mem_setOf_eq] at hzR
        simp only [T, R, rotLinearEquiv, reflYLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, c, s]
        refine ⟨?_, ?_, ?_⟩
        · have : p / d2 * z.1 + v / d2 * z.2 = (z.1 * p + z.2 * v) / d2 := by ring
          rw [this]; exact div_nonneg hzR.1 (le_of_lt hd2_pos)
        · have : p / d2 * z.1 + v / d2 * z.2 = (z.1 * p + z.2 * v) / d2 := by ring
          rw [this, div_le_iff₀ hd2_pos]; linarith [hzR.2.1, hd2_sq]
        · have : -(-(v / d2) * z.1 + p / d2 * z.2) = (v * z.1 - p * z.2) / d2 := by ring
          rw [this]; exact div_nonpos_of_nonpos_of_nonneg hzR.2.2 (le_of_lt hd2_pos)
      refine ⟨?_, hzR'⟩
      rcases hzU with (hA | hB) | hC
      · left; simp only [disk, Set.mem_setOf_eq] at hA ⊢; rw [← hTA, hT_sq]; exact hA
      · have hTBmem : T z ∈ disk (pB, vB) 1 := by
          simp only [disk, Set.mem_setOf_eq] at hB ⊢; rw [← hTB, hT_sq]; exact hB
        exact no_bulge_nonlongest hd2_pos hd2_le1 hvB_pos hBnon ⟨hTBmem, hzR'⟩
      · right; simp only [disk, Set.mem_setOf_eq] at hC ⊢; rw [← hTC, hT_sq]; exact hC
    calc volume (U ∩ RCA)
        ≤ volume (T ⁻¹' Target) := measure_mono hsub
      _ = volume Target := hmpT.measure_preimage hmeasT.nullMeasurableSet
      _ = ENNReal.ofReal (chordArea d2 / 2) := volume_strip_two_disks hd2_pos hd2_le1
  -- Step 6: Strip `R_BC` has volume at most `chordArea (r * euclidNorm (1 - w.1, w.2)) / 2`.
  have hRBC_vol : volume (U ∩ RBC) ≤ ENNReal.ofReal (chordArea (r * euclidNorm (1 - w.1, w.2)) / 2) := by
    set d3 : ℝ := r * euclidNorm (1 - w.1, w.2)
    have hd3_sq : d3 ^ 2 = (p - r) ^ 2 + v ^ 2 := by
      dsimp only [d3, euclidNorm, p, v]
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hd3_pos : 0 < d3 := mul_pos hr0 (Real.sqrt_pos.mpr (by nlinarith [hw.2.2.1]))
    have hd3_lt_r : d3 < r := by
      have := quarterLens_euclidNorm_sub_lt_one hw; nlinarith
    have hd3_le1 : d3 ≤ 1 := le_of_lt (hd3_lt_r.trans hr.2)
    set c : ℝ := (p - r) / d3
    set s : ℝ := v / d3
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      dsimp only [c, s]; field_simp [ne_of_gt hd3_pos]; linarith [hd3_sq]
    let R := rotLinearEquiv c s hcs
    let T : Pt → Pt := fun z => R (z + (-B))
    have hmpShift : MeasurePreserving (fun z : Pt => z + (-B)) volume volume :=
      measurePreserving_add_right volume (-B)
    have hmpT : MeasurePreserving T volume volume :=
      (measurePreserving_rotLinearEquiv c s hcs).comp hmpShift
    have hT_sq : ∀ z₁ z₂, sqDist (T z₁) (T z₂) = sqDist z₁ z₂ := by
      intro z₁ z₂
      show sqDist (R (z₁ + -B)) (R (z₂ + -B)) = sqDist z₁ z₂
      rw [rotLinearEquiv_sqDist]
      simp only [sqDist, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]; ring
    have hTB : T B = 0 := by
      have : B + -B = 0 := add_neg_cancel B
      show R (B + -B) = 0
      rw [this, R.map_zero]
    have hTC : T C = (d3, 0) := by
      ext
      · simp only [T, R, B, C, rotLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
          Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, neg_zero, add_zero, c, s]
        field_simp [ne_of_gt hd3_pos]; linarith [hd3_sq]
      · simp only [T, R, B, C, rotLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
          Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, neg_zero, add_zero, c, s]
        field_simp [ne_of_gt hd3_pos]; ring
    set pA : ℝ := c * (-r)
    set vA : ℝ := -s * (-r)
    have hTA : T A = (pA, vA) := by
      ext <;> simp [T, R, A, B, rotLinearEquiv, pA, vA]
    have hvA_pos : 0 < vA := by
      have : vA = (v / d3) * r := by dsimp only [vA, s]; ring
      rw [this]; exact mul_pos (div_pos hv0 hd3_pos) hr0
    have hAnon : d3 ^ 2 < pA ^ 2 + vA ^ 2 ∨ d3 ^ 2 < (d3 - pA) ^ 2 + vA ^ 2 := by
      left
      have : pA ^ 2 + vA ^ 2 = r ^ 2 := by
        have : pA ^ 2 + vA ^ 2 = (c ^ 2 + s ^ 2) * r ^ 2 := by dsimp only [pA, vA]; ring
        rw [this, hcs, one_mul]
      rw [this]; nlinarith
    let Target : Set Pt := (disk (0 : Pt) 1 ∪ disk (d3, 0) 1) ∩ {z : Pt | 0 ≤ z.1 ∧ z.1 ≤ d3 ∧ z.2 ≤ 0}
    have hmeasT : MeasurableSet Target := by
      refine MeasurableSet.inter ((measurableSet_disk 0 1).union (measurableSet_disk (d3, 0) 1)) ?_
      exact (measurableSet_le measurable_const measurable_fst).inter
        ((measurableSet_le measurable_fst measurable_const).inter
          (measurableSet_le measurable_snd measurable_const))
    have hsub : U ∩ RBC ⊆ T ⁻¹' Target := by
      intro z ⟨hzU, hzR⟩
      simp only [Set.mem_preimage, Target, Set.mem_inter_iff]
      have hzR' : 0 ≤ (T z).1 ∧ (T z).1 ≤ d3 ∧ (T z).2 ≤ 0 := by
        simp only [RBC, dot2, sqDist, B, C, Prod.fst_sub, Prod.snd_sub, sub_zero, Set.mem_setOf_eq] at hzR
        simp only [T, R, B, rotLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
          Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, neg_zero, add_zero, c, s]
        refine ⟨?_, ?_, ?_⟩
        · have : (p - r) / d3 * (z.1 + -r) + v / d3 * z.2 = ((z.1 - r) * (p - r) + z.2 * v) / d3 := by ring
          rw [this]; exact div_nonneg hzR.1 (le_of_lt hd3_pos)
        · have : (p - r) / d3 * (z.1 + -r) + v / d3 * z.2 = ((z.1 - r) * (p - r) + z.2 * v) / d3 := by ring
          rw [this, div_le_iff₀ hd3_pos]; linarith [hzR.2.1, hd3_sq]
        · have : -(v / d3) * (z.1 + -r) + (p - r) / d3 * z.2 = (v * (r - z.1) - (r - p) * z.2) / d3 := by ring
          rw [this]; exact div_nonpos_of_nonpos_of_nonneg hzR.2.2 (le_of_lt hd3_pos)
      refine ⟨?_, hzR'⟩
      rcases hzU with (hA | hB) | hC
      · have hTAmem : T z ∈ disk (pA, vA) 1 := by
          simp only [disk, Set.mem_setOf_eq] at hA ⊢; rw [← hTA, hT_sq]; exact hA
        exact no_bulge_nonlongest hd3_pos hd3_le1 hvA_pos hAnon ⟨hTAmem, hzR'⟩
      · left; simp only [disk, Set.mem_setOf_eq] at hB ⊢; rw [← hTB, hT_sq]; exact hB
      · right; simp only [disk, Set.mem_setOf_eq] at hC ⊢; rw [← hTC, hT_sq]; exact hC
    calc volume (U ∩ RBC)
        ≤ volume (T ⁻¹' Target) := measure_mono hsub
      _ = volume Target := hmpT.measure_preimage hmeasT.nullMeasurableSet
      _ = ENNReal.ofReal (chordArea d3 / 2) := volume_strip_two_disks hd3_pos hd3_le1
  -- Step 7: Combine all 7 regions by subadditivity.
  have hUcov : U ⊆ Δ ∪ (disk A 1 ∩ SA) ∪ (disk B 1 ∩ SB) ∪ (disk C 1 ∩ SC) ∪
      (U ∩ RAB) ∪ (U ∩ RCA) ∪ (U ∩ RBC) := by
    intro z hzU
    rcases hcover z with h | h | h | h | h | h | h
    · left; left; left; left; left; left; exact h
    · left; left; left; left; left; right; exact hconeA ⟨hzU, h⟩
    · left; left; left; left; right; exact hconeB ⟨hzU, h⟩
    · left; left; left; right; exact hconeC ⟨hzU, h⟩
    · left; left; right; exact ⟨hzU, h⟩
    · left; right; exact ⟨hzU, h⟩
    · right; exact ⟨hzU, h⟩
  have hX_nn : 0 ≤ excessX r w :=
    intervalIntegral.integral_nonneg (le_of_lt hr0) (fun _ _ => le_max_left _ _)
  have hc1_nn : 0 ≤ chordArea r / 2 := div_nonneg (chordArea_nonneg (le_of_lt hr0)) (by norm_num)
  have hc2_nn : 0 ≤ chordArea (r * euclidNorm w) / 2 :=
    div_nonneg (chordArea_nonneg (mul_nonneg (le_of_lt hr0) (Real.sqrt_nonneg _))) (by norm_num)
  have hc3_nn : 0 ≤ chordArea (r * euclidNorm (1 - w.1, w.2)) / 2 :=
    div_nonneg (chordArea_nonneg (mul_nonneg (le_of_lt hr0) (Real.sqrt_nonneg _))) (by norm_num)
  have hΔ_vol : volume Δ = ENNReal.ofReal (r ^ 2 * w.2 / 2) := by
    rw [volume_closedTriangle hr0 hv0]; congr 1; dsimp only [v]; ring
  have hvol_le : volume U ≤ ENNReal.ofReal (threeDiskAreaBound r w) := by
    have hsubadd : volume U ≤ volume Δ + (volume (disk A 1 ∩ SA) + volume (disk B 1 ∩ SB) +
        volume (disk C 1 ∩ SC)) + volume (U ∩ RAB) + volume (U ∩ RCA) + volume (U ∩ RBC) := by
      have h1 : volume U ≤ volume Δ + volume (disk A 1 ∩ SA) + volume (disk B 1 ∩ SB) +
          volume (disk C 1 ∩ SC) + volume (U ∩ RAB) + volume (U ∩ RCA) + volume (U ∩ RBC) := by
        refine (measure_mono hUcov).trans ?_
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
      calc volume U ≤ _ := h1
        _ = volume Δ + (volume (disk A 1 ∩ SA) + volume (disk B 1 ∩ SB) +
            volume (disk C 1 ∩ SC)) + volume (U ∩ RAB) + volume (U ∩ RCA) + volume (U ∩ RBC) := by
          simp only [add_assoc]
    calc volume U
        ≤ ENNReal.ofReal (r ^ 2 * w.2 / 2) + ENNReal.ofReal Real.pi +
          (ENNReal.ofReal (chordArea r / 2) + ENNReal.ofReal (excessX r w)) +
          ENNReal.ofReal (chordArea (r * euclidNorm w) / 2) +
          ENNReal.ofReal (chordArea (r * euclidNorm (1 - w.1, w.2)) / 2) := by
            refine hsubadd.trans ?_
            rw [hΔ_vol]
            exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl hcones_vol) hRAB_vol) hRCA_vol) hRBC_vol
      _ = ENNReal.ofReal (threeDiskAreaBound r w) := by
            have hw2 : 0 ≤ w.2 := le_of_lt hw.2.2.1
            have h1 : 0 ≤ r ^ 2 * w.2 / 2 := by positivity
            have h2 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
            rw [← ENNReal.ofReal_add h1 h2,
                ← ENNReal.ofReal_add hc1_nn hX_nn,
                ← ENNReal.ofReal_add (add_nonneg h1 h2) (add_nonneg hc1_nn hX_nn),
                ← ENNReal.ofReal_add (by linarith) hc2_nn,
                ← ENNReal.ofReal_add (by linarith) hc3_nn]
            congr 1; unfold threeDiskAreaBound; ring
  have hfin : volume U ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol_le
  have hvol_ge : ENNReal.ofReal Real.pi ≤ volume U := by
    rw [← volume_disk_one A]
    exact measure_mono (fun z hz => Or.inl (Or.inl hz))
  have hbound_nn : 0 ≤ threeDiskAreaBound r w := by
    have hw2 : 0 ≤ w.2 := le_of_lt hw.2.2.1
    unfold threeDiskAreaBound; linarith [Real.pi_pos, show 0 ≤ r ^ 2 * w.2 / 2 by positivity]
  unfold threeDiskArea unionDiskArea
  rw [hUeq]
  constructor
  · have hpos := ENNReal.toReal_mono hfin hvol_ge
    rw [ENNReal.toReal_ofReal (le_of_lt Real.pi_pos)] at hpos
    exact lt_of_lt_of_le Real.pi_pos hpos
  · have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_le
    rwa [ENNReal.toReal_ofReal hbound_nn] at hhi

end

/-- Scaled 3-disk union area upper bound for arbitrary radius `R > 0` and longest side `L ∈ (0, R)`. -/
lemma threeDiskArea_scale_le {L R : ℝ} {w : Pt} (hL : 0 < L) (hLR : L < R) (hw : w ∈ quarterLens) :
    unionDiskArea ![((0 : ℝ), (0 : ℝ)), (L, 0), (L * w.1, L * w.2)] R ≤
      R ^ 2 * threeDiskAreaBound (L / R) w := by
  have hR : 0 < R := hL.trans hLR
  have hr0 : 0 < L / R := div_pos hL hR
  have hr1 : L / R < 1 := (div_lt_one hR).mpr hLR
  have hcfg : (fun i : Fin 3 => (R * (triCfg (L / R) w i).1, R * (triCfg (L / R) w i).2)) =
      ![((0 : ℝ), (0 : ℝ)), (L, 0), (L * w.1, L * w.2)] := by
    funext i
    fin_cases i
    · ext <;> simp [triCfg]
    · ext
      · change R * (L / R) = L; field_simp [ne_of_gt hR]
      · simp [triCfg]
    · ext
      · change R * ((L / R) * w.1) = L * w.1; field_simp [ne_of_gt hR]
      · change R * ((L / R) * w.2) = L * w.2; field_simp [ne_of_gt hR]
  rw [← hcfg, unionDiskArea_scale (triCfg (L / R) w) hR]
  exact mul_le_mul_of_nonneg_left (threeDiskArea_le ⟨hr0, hr1⟩ hw).2 (sq_nonneg R)

end BHHBounds.Geometry
