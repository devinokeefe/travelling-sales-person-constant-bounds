import BHHBounds.Geometry.DiskMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Area of the intersection of two disks

`diskInterArea d r₁ r₂` is the area of the intersection of two closed disks of radii `r₁, r₂` at
center distance `d` (`volume_disk_inter`), written through the circular segment area
`segArea c = 2 * ∫ t in c..1, √(1 - t²)`. It is antitone in `d` (`diskInterArea_antitone_d`).
-/

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace BHHBounds.Geometry

noncomputable section

/-! ## Circular Segment Area `segArea` -/

/-- Unit circular segment area `S(c) = 2 ∫_c^1 √(1 - t²) dt` for `c ∈ [-1, 1]`. -/
def segArea (c : ℝ) : ℝ :=
  2 * ∫ t in c..(1 : ℝ), Real.sqrt (1 - t ^ 2)

lemma segArea_one : segArea 1 = 0 := by
  unfold segArea; simp

lemma segArea_nonneg {c : ℝ} (hc : c ≤ 1) : 0 ≤ segArea c := by
  unfold segArea
  exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hc fun _ _ => Real.sqrt_nonneg _)

lemma segArea_antitoneOn : AntitoneOn segArea (Icc (-1 : ℝ) 1) := by
  intro a ha b hb hab
  unfold segArea
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - t ^ 2)) volume u v :=
    fun u v => (by fun_prop : Continuous fun t : ℝ => Real.sqrt (1 - t ^ 2)).intervalIntegrable u v
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hint a b) (hint b 1)
  have hnn : 0 ≤ ∫ t in a..b, Real.sqrt (1 - t ^ 2) :=
    intervalIntegral.integral_nonneg hab fun _ _ => Real.sqrt_nonneg _
  linarith

/-- Elementary algebraic tangent inequality: for all `t ∈ [-1, 1]` and `m ∈ (-1, 1)`,
`√(1 - t²) ≤ (1 - m t) / √(1 - m²)`. -/
lemma sqrt_one_sub_sq_le_tangent {t m : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hm : |m| < 1) :
    Real.sqrt (1 - t ^ 2) ≤ (1 - m * t) / Real.sqrt (1 - m ^ 2) := by
  have hm2 : 0 < 1 - m ^ 2 := by
    have h1 := abs_lt.mp hm; nlinarith
  have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hmt : 0 ≤ 1 - m * t := by
    have h1 := abs_lt.mp hm; nlinarith [ht.1, ht.2]
  have hsq_pos : 0 < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hm2
  rw [le_div_iff₀ hsq_pos, ← Real.sqrt_mul ht2, Real.sqrt_le_left hmt]
  nlinarith [sq_nonneg (t - m)]

/-- Midpoint-tangent bound on `segArea`:
for any `-1 ≤ a < b ≤ 1` with `m = (a + b) / 2`,
`segArea a - segArea b ≤ 2 * (b - a) * √(1 - m²)`. -/
lemma segArea_sub_le_midpoint {a b : ℝ} (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    segArea a - segArea b ≤ 2 * (b - a) * Real.sqrt (1 - ((a + b) / 2) ^ 2) := by
  let m : ℝ := (a + b) / 2
  have hm_abs : |m| < 1 := by
    rw [abs_lt]; constructor <;> dsimp only [m] <;> linarith
  have hm2 : 0 < 1 - m ^ 2 := by
    have h1 := abs_lt.mp hm_abs; nlinarith
  have hsq_pos : 0 < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hm2
  have hint1 : ∀ u v : ℝ, IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - t ^ 2)) volume u v :=
    fun u v => (by fun_prop : Continuous fun t : ℝ => Real.sqrt (1 - t ^ 2)).intervalIntegrable u v
  have hdiff : segArea a - segArea b = 2 * ∫ t in a..b, Real.sqrt (1 - t ^ 2) := by
    unfold segArea
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hint1 a b) (hint1 b 1)
    linarith
  rw [hdiff]
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 - m * t) / Real.sqrt (1 - m ^ 2)) volume a b :=
    (by fun_prop : Continuous fun t : ℝ => (1 - m * t) / Real.sqrt (1 - m ^ 2)).intervalIntegrable a b
  have hmono := intervalIntegral.integral_mono_on (le_of_lt hab) (hint1 a b) hint2
    (fun t ht => sqrt_one_sub_sq_le_tangent ⟨ha.trans ht.1, ht.2.trans hb⟩ hm_abs)
  have heval : ∫ t in a..b, (1 - m * t) / Real.sqrt (1 - m ^ 2) =
      (b - a) * Real.sqrt (1 - m ^ 2) := by
    have hdiv : (∫ t in a..b, (1 - m * t) / Real.sqrt (1 - m ^ 2)) =
        (∫ t in a..b, (1 - m * t)) / Real.sqrt (1 - m ^ 2) := by
      simp_rw [div_eq_mul_inv]
      exact intervalIntegral.integral_mul_const _ _
    rw [hdiv]
    have hlin : ∫ t in a..b, (1 - m * t) = (b - a) * (1 - m ^ 2) := by
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => m * t)
        intervalIntegrable_const
        ((continuous_const.mul continuous_id).intervalIntegrable a b),
        intervalIntegral.integral_const, smul_eq_mul, mul_one,
        intervalIntegral.integral_const_mul, integral_id]
      dsimp only [m]; ring
    rw [hlin, div_eq_iff (ne_of_gt hsq_pos), mul_assoc, Real.mul_self_sqrt (le_of_lt hm2)]
  linarith

/-- Slope upper bound on `segArea c - segArea b` for `c ∈ [a, b]`: if `t_min ≤ |t|` for all
`t ∈ [a, b]` (with `0 ≤ t_min ≤ 1`), then `segArea c - segArea b ≤ 2 * √(1 - t_min²) * (b - c)`. -/
lemma segArea_sub_le_slope {a b c t_min : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (ht_min : ∀ t ∈ Icc a b, t_min ^ 2 ≤ t ^ 2) :
    segArea c - segArea b ≤ 2 * Real.sqrt (1 - t_min ^ 2) * (b - c) := by
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - t ^ 2)) volume u v :=
    fun u v => (by fun_prop : Continuous fun t : ℝ => Real.sqrt (1 - t ^ 2)).intervalIntegrable u v
  have hdiff : segArea c - segArea b = 2 * ∫ t in c..b, Real.sqrt (1 - t ^ 2) := by
    unfold segArea
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hint c b) (hint b 1)
    linarith
  rw [hdiff]
  have hle : ∫ t in c..b, Real.sqrt (1 - t ^ 2) ≤
      ∫ _ in c..b, Real.sqrt (1 - t_min ^ 2) := by
    refine intervalIntegral.integral_mono_on hcb (hint c b) intervalIntegrable_const ?_
    intro t ht
    exact Real.sqrt_le_sqrt (by linarith [ht_min t ⟨hac.trans ht.1, ht.2⟩])
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  linarith

/-- Fundamental theorem of calculus for `segArea (-1) = π`. -/
lemma segArea_neg_one : segArea (-1) = Real.pi := by
  unfold segArea
  let F : ℝ → ℝ := fun t => t * Real.sqrt (1 - t ^ 2) + Real.arcsin t
  have hcont : ContinuousOn F (Icc (-1 : ℝ) 1) := by unfold F; fun_prop
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (2 * Real.sqrt (1 - t ^ 2)) t := by
    intro t ht
    have h1t2 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hsq : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr h1t2
    have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
      have := (hasDerivAt_pow 2 t).const_sub 1
      refine this.congr_deriv ?_; norm_num
    have h2 : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
        (-2 * t / (2 * Real.sqrt (1 - t ^ 2))) t := h1.sqrt (ne_of_gt h1t2)
    have h3 : HasDerivAt (fun x : ℝ => x * Real.sqrt (1 - x ^ 2))
        (1 * Real.sqrt (1 - t ^ 2) + t * (-2 * t / (2 * Real.sqrt (1 - t ^ 2)))) t :=
      (hasDerivAt_id t).mul h2
    have h4 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - t ^ 2)) t :=
      Real.hasDerivAt_arcsin (by linarith [ht.1]) (by linarith [ht.2])
    refine (h3.add h4).congr_deriv ?_
    field_simp [ne_of_gt hsq]
    nlinarith [Real.sq_sqrt (le_of_lt h1t2)]
  have hint : IntervalIntegrable (fun t : ℝ => 2 * Real.sqrt (1 - t ^ 2)) volume (-1) 1 :=
    (by fun_prop : Continuous fun t : ℝ => 2 * Real.sqrt (1 - t ^ 2)).intervalIntegrable (-1) 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (-1 : ℝ) ≤ 1)
    hcont hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  rw [hftc]
  dsimp only [F]
  norm_num [Real.arcsin_one, Real.arcsin_neg_one]

lemma segArea_le_pi {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) : segArea c ≤ Real.pi := by
  rw [← segArea_neg_one]
  exact segArea_antitoneOn (by norm_num) hc hc.1

/-! ## Area of a Circular Cap via Fubini -/

/-- The area of the right circular cap `{z ∈ disk (0, 0) r | r * c ≤ z.1}` for `r > 0` and
`c ∈ [-1, 1]` equals `r² * segArea c`. -/
lemma volume_disk_cap_right {r c : ℝ} (hr : 0 < r) (hc : c ∈ Icc (-1 : ℝ) 1) :
    volume {z : Pt | z.1 ^ 2 + z.2 ^ 2 ≤ r ^ 2 ∧ r * c ≤ z.1} =
      ENNReal.ofReal (r ^ 2 * segArea c) := by
  let S : Set Pt := {z : Pt | z.1 ^ 2 + z.2 ^ 2 ≤ r ^ 2 ∧ r * c ≤ z.1}
  have hmeas : MeasurableSet S := by
    have h1 : MeasurableSet {z : Pt | z.1 ^ 2 + z.2 ^ 2 ≤ r ^ 2} :=
      measurableSet_le (by fun_prop) measurable_const
    have h2 : MeasurableSet {z : Pt | r * c ≤ z.1} :=
      measurableSet_le measurable_const measurable_fst
    exact h1.inter h2
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have hslice : ∀ x : ℝ, volume ((fun y => (x, y)) ⁻¹' S) =
      if x ∈ Icc (r * c) r then ENNReal.ofReal (2 * Real.sqrt (r ^ 2 - x ^ 2)) else 0 := by
    intro x
    by_cases hx : x ∈ Icc (r * c) r
    · rw [if_pos hx]
      have hrx : 0 ≤ r ^ 2 - x ^ 2 := by
        have h1 : -r ≤ r * c := by nlinarith [hc.1]
        nlinarith [hx.1, hx.2]
      have heq : (fun y => (x, y)) ⁻¹' S =
          Icc (-Real.sqrt (r ^ 2 - x ^ 2)) (Real.sqrt (r ^ 2 - x ^ 2)) := by
        ext y
        simp only [Set.mem_preimage, S, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · intro ⟨hsq, _⟩
          have hy2 : y ^ 2 ≤ r ^ 2 - x ^ 2 := by linarith
          have habs : |y| ≤ Real.sqrt (r ^ 2 - x ^ 2) := by
            rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hy2
          exact abs_le.mp habs
        · intro hy
          refine ⟨?_, hx.1⟩
          have habs : |y| ≤ Real.sqrt (r ^ 2 - x ^ 2) := abs_le.mpr hy
          have hy2 : y ^ 2 ≤ r ^ 2 - x ^ 2 := by
            have := mul_self_le_mul_self (abs_nonneg y) habs
            rw [abs_mul_abs_self, Real.mul_self_sqrt hrx] at this
            nlinarith
          linarith
      rw [heq, Real.volume_Icc]
      congr 1; ring
    · rw [if_neg hx]
      have hempty : (fun y => (x, y)) ⁻¹' S = ∅ := by
        ext y
        simp only [Set.mem_preimage, S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hsq hrc
        apply hx
        refine ⟨hrc, ?_⟩
        nlinarith [sq_nonneg y]
      rw [hempty, measure_empty]
  simp_rw [hslice]
  have hrc_le : r * c ≤ r := by nlinarith [hc.2]
  have hsupp : ∫⁻ x : ℝ, (if x ∈ Icc (r * c) r then
      ENNReal.ofReal (2 * Real.sqrt (r ^ 2 - x ^ 2)) else 0) =
      ∫⁻ x in Icc (r * c) r, ENNReal.ofReal (2 * Real.sqrt (r ^ 2 - x ^ 2)) := by
    rw [← lintegral_indicator measurableSet_Icc]
    congr 1; funext x; simp [Set.indicator]
  rw [hsupp, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrc_le]
    -- Change of variables `x = r * t`
    have hcov : ∫ x in (r * c)..r, 2 * Real.sqrt (r ^ 2 - x ^ 2) =
        r ^ 2 * (2 * ∫ t in c..1, Real.sqrt (1 - t ^ 2)) := by
      have h1 := intervalIntegral.integral_comp_mul_left (f := fun x : ℝ => 2 * Real.sqrt (r ^ 2 - x ^ 2))
        (a := c) (b := 1) (c := r) (ne_of_gt hr)
      rw [mul_one, smul_eq_mul] at h1
      have hr_ne : r ≠ 0 := ne_of_gt hr
      have h2 : ∫ x in (r * c)..r, 2 * Real.sqrt (r ^ 2 - x ^ 2) =
          r * ∫ t in c..1, 2 * Real.sqrt (r ^ 2 - (r * t) ^ 2) := by
        have := congrArg (r * ·) h1
        rw [← mul_assoc, mul_inv_cancel₀ hr_ne, one_mul] at this
        exact this.symm
      rw [h2]
      have hsimp : ∀ t : ℝ, 2 * Real.sqrt (r ^ 2 - (r * t) ^ 2) =
          (2 * r) * Real.sqrt (1 - t ^ 2) := fun t => by
        have hfac : r ^ 2 - (r * t) ^ 2 = r ^ 2 * (1 - t ^ 2) := by ring
        rw [hfac, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq (le_of_lt hr)]; ring
      simp_rw [hsimp, intervalIntegral.integral_const_mul]
      ring
    rw [hcov]; rfl
  · exact ((by fun_prop : Continuous fun x : ℝ => 2 * Real.sqrt (r ^ 2 - x ^ 2)).integrableOn_Icc)
  · exact Eventually.of_forall fun _ => by positivity

/-! ## Exact Two-Disk Intersection Area -/

/-- Exact area of the intersection of two closed disks of radii `r₁, r₂ ≥ 0` at center distance
`d ≥ 0`. -/
def diskInterArea (d r₁ r₂ : ℝ) : ℝ :=
  if r₁ ≤ 0 ∨ r₂ ≤ 0 ∨ r₁ + r₂ ≤ d then 0
  else if d ≤ |r₁ - r₂| then Real.pi * (min r₁ r₂) ^ 2
  else
    let c₁ := (d ^ 2 + r₁ ^ 2 - r₂ ^ 2) / (2 * d * r₁)
    let c₂ := (d ^ 2 + r₂ ^ 2 - r₁ ^ 2) / (2 * d * r₂)
    r₁ ^ 2 * segArea c₁ + r₂ ^ 2 * segArea c₂

lemma diskInterArea_nonneg (d r₁ r₂ : ℝ) :
    0 ≤ diskInterArea d r₁ r₂ := by
  unfold diskInterArea
  split_ifs with h1 h2
  · exact le_rfl
  · positivity
  · push Not at h1 h2
    rcases h1 with ⟨hr₁p, hr₂p, hlt⟩
    have hd_pos : 0 < d := lt_of_le_of_lt (abs_nonneg _) h2
    have hdiff : r₁ - r₂ < d ∧ r₂ - r₁ < d := by
      have := abs_lt.mp h2; constructor <;> linarith
    have hc1 : (d ^ 2 + r₁ ^ 2 - r₂ ^ 2) / (2 * d * r₁) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [hdiff.1, hdiff.2]
    have hc2 : (d ^ 2 + r₂ ^ 2 - r₁ ^ 2) / (2 * d * r₂) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [hdiff.1, hdiff.2]
    exact add_nonneg (mul_nonneg (sq_nonneg _) (segArea_nonneg hc1))
      (mul_nonneg (sq_nonneg _) (segArea_nonneg hc2))

/-- Exact volume of the intersection of two disks on the x-axis: `disk (0,0) r₁ ∩ disk (d,0) r₂`. -/
lemma volume_disk_inter_axis {d r₁ r₂ : ℝ} (hd : 0 ≤ d) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    volume (disk (0 : Pt) r₁ ∩ disk (d, 0) r₂) = ENNReal.ofReal (diskInterArea d r₁ r₂) := by
  unfold diskInterArea
  split_ifs with h1 h2
  · -- Case 1: `r₁ ≤ 0 ∨ r₂ ≤ 0 ∨ r₁ + r₂ ≤ d`
    rw [ENNReal.ofReal_zero]
    rcases h1 with hr1z | hr2z | hsep
    · have hr1e : r₁ = 0 := le_antisymm hr1z hr₁
      subst hr1e
      have hsub : disk (0 : Pt) 0 ∩ disk (d, 0) r₂ ⊆ {(0 : Pt)} := by
        intro z hz
        have h0 : z.1 ^ 2 + z.2 ^ 2 ≤ 0 := by simpa [disk, sqDist] using hz.1
        have hz1 : z.1 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
        have hz2 : z.2 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
        exact Set.mem_singleton_iff.mpr (Prod.ext hz1 hz2)
      exact measure_mono_null hsub (measure_singleton _)
    · have hr2e : r₂ = 0 := le_antisymm hr2z hr₂
      subst hr2e
      have hsub : disk (0 : Pt) r₁ ∩ disk (d, 0) 0 ⊆ {(d, 0)} := by
        intro z hz
        have h0 : (z.1 - d) ^ 2 + z.2 ^ 2 ≤ 0 := by simpa [disk, sqDist] using hz.2
        have hz1 : z.1 = d := by nlinarith [sq_nonneg (z.1 - d), sq_nonneg z.2]
        have hz2 : z.2 = 0 := by nlinarith [sq_nonneg (z.1 - d), sq_nonneg z.2]
        exact Set.mem_singleton_iff.mpr (Prod.ext hz1 hz2)
      exact measure_mono_null hsub (measure_singleton _)
    · -- Separated or tangent: intersection lies on the vertical line `z.1 = r₁` (or `{0}`)
      have hsub : disk (0 : Pt) r₁ ∩ disk (d, 0) r₂ ⊆ {z : Pt | 1 * z.1 + 0 * z.2 = r₁} := by
        intro z ⟨hA, hB⟩
        simp only [disk, sqDist, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero] at hA hB
        simp only [Set.mem_setOf_eq, one_mul, zero_mul, add_zero]
        have h1 : z.1 ≤ r₁ := by nlinarith [sq_nonneg z.2]
        have h2 : d - z.1 ≤ r₂ := by nlinarith [sq_nonneg z.2]
        linarith
      exact measure_mono_null hsub (volume_line_zero (Or.inl one_ne_zero))
  · -- Case 2: one disk contained in the other (`d ≤ |r₁ - r₂|`)
    push Not at h1
    rcases h1 with ⟨hr₁p, hr₂p, _⟩
    by_cases hle : r₁ ≤ r₂
    · rw [min_eq_left hle]
      have hsub : disk (0 : Pt) r₁ ⊆ disk (d, 0) r₂ := by
        intro z hz
        rw [disk, Set.mem_setOf_eq] at hz ⊢
        have hdist : euclidDist z (0 : Pt) ≤ r₁ := (euclidDist_le_iff hr₁).mpr hz
        have h0d : euclidDist (0 : Pt) (d, 0) = d := by
          unfold euclidDist sqDist; simp [Real.sqrt_sq hd]
        have htri : euclidDist z (d, 0) ≤ r₂ := by
          have habs : d ≤ r₂ - r₁ := by rwa [abs_of_nonpos (by linarith), neg_sub] at h2
          linarith [euclidDist_triangle z (0 : Pt) (d, 0)]
        exact (euclidDist_le_iff hr₂).mp htri
      rw [Set.inter_eq_left.mpr hsub, volume_disk _ hr₁]
    · push Not at hle
      rw [min_eq_right (le_of_lt hle)]
      have hsub : disk (d, 0) r₂ ⊆ disk (0 : Pt) r₁ := by
        intro z hz
        rw [disk, Set.mem_setOf_eq] at hz ⊢
        have hdist : euclidDist z (d, 0) ≤ r₂ := (euclidDist_le_iff hr₂).mpr hz
        have hd0 : euclidDist (d, 0) (0 : Pt) = d := by
          unfold euclidDist sqDist; simp [Real.sqrt_sq hd]
        have htri : euclidDist z (0 : Pt) ≤ r₁ := by
          have habs : d ≤ r₁ - r₂ := by rwa [abs_of_pos (by linarith)] at h2
          linarith [euclidDist_triangle z (d, 0) (0 : Pt)]
        exact (euclidDist_le_iff hr₁).mp htri
      rw [Set.inter_eq_right.mpr hsub, volume_disk _ hr₂]
  · -- Case 3: proper intersection `|r₁ - r₂| < d < r₁ + r₂`
    push Not at h1 h2
    rcases h1 with ⟨hr₁p, hr₂p, hlt⟩
    have hd_pos : 0 < d := lt_of_le_of_lt (abs_nonneg _) h2
    have hdiff : r₁ - r₂ < d ∧ r₂ - r₁ < d := by
      have := abs_lt.mp h2; constructor <;> linarith
    let xStar : ℝ := (d ^ 2 + r₁ ^ 2 - r₂ ^ 2) / (2 * d)
    let c₁ : ℝ := (d ^ 2 + r₁ ^ 2 - r₂ ^ 2) / (2 * d * r₁)
    let c₂ : ℝ := (d ^ 2 + r₂ ^ 2 - r₁ ^ 2) / (2 * d * r₂)
    have hc1_mem : c₁ ∈ Icc (-1 : ℝ) 1 := by
      constructor
      · dsimp only [c₁]; rw [le_div_iff₀ (by positivity)]; nlinarith [hlt]
      · dsimp only [c₁]; rw [div_le_iff₀ (by positivity)]; nlinarith [hdiff.1, hdiff.2]
    have hc2_mem : c₂ ∈ Icc (-1 : ℝ) 1 := by
      constructor
      · dsimp only [c₂]; rw [le_div_iff₀ (by positivity)]; nlinarith [hlt]
      · dsimp only [c₂]; rw [div_le_iff₀ (by positivity)]; nlinarith [hdiff.1, hdiff.2]
    have hx1 : r₁ * c₁ = xStar := by dsimp only [c₁, xStar]; field_simp [ne_of_gt hd_pos, ne_of_gt hr₁p]
    have hx2 : d - r₂ * c₂ = xStar := by dsimp only [c₂, xStar]; field_simp [ne_of_gt hd_pos, ne_of_gt hr₂p]; ring
    let Cap1 : Set Pt := {z : Pt | z.1 ^ 2 + z.2 ^ 2 ≤ r₁ ^ 2 ∧ xStar ≤ z.1}
    let Cap2 : Set Pt := {z : Pt | (z.1 - d) ^ 2 + z.2 ^ 2 ≤ r₂ ^ 2 ∧ z.1 ≤ xStar}
    have hU : disk (0 : Pt) r₁ ∩ disk (d, 0) r₂ = Cap1 ∪ Cap2 := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_union, disk, sqDist, Set.mem_setOf_eq,
        Prod.fst_zero, Prod.snd_zero, sub_zero, Cap1, Cap2]
      have hrad : (z.1 - d) ^ 2 - z.1 ^ 2 = 2 * d * (xStar - z.1) + (r₂ ^ 2 - r₁ ^ 2) := by
        dsimp only [xStar]; field_simp [ne_of_gt hd_pos]; ring
      constructor
      · rintro ⟨hA, hB⟩
        rcases le_total xStar z.1 with hge | hle
        · exact Or.inl ⟨hA, hge⟩
        · exact Or.inr ⟨hB, hle⟩
      · rintro (⟨hA, hge⟩ | ⟨hB, hle⟩)
        · exact ⟨hA, by nlinarith⟩
        · exact ⟨by nlinarith, hB⟩
    have hinter_zero : volume (Cap1 ∩ Cap2) = 0 := by
      have hsub : Cap1 ∩ Cap2 ⊆ {z : Pt | 1 * z.1 + 0 * z.2 = xStar} := by
        intro z ⟨hA, hB⟩
        simp only [Set.mem_setOf_eq, one_mul, zero_mul, add_zero]
        linarith [hA.2, hB.2]
      exact measure_mono_null hsub (volume_line_zero (Or.inl one_ne_zero))
    have hmeas1 : MeasurableSet Cap1 := by
      have h1 : MeasurableSet {z : Pt | z.1 ^ 2 + z.2 ^ 2 ≤ r₁ ^ 2} :=
        measurableSet_le (by fun_prop) measurable_const
      have h2 : MeasurableSet {z : Pt | xStar ≤ z.1} :=
        measurableSet_le measurable_const measurable_fst
      exact h1.inter h2
    have hmeas2 : MeasurableSet Cap2 := by
      have h1 : MeasurableSet {z : Pt | (z.1 - d) ^ 2 + z.2 ^ 2 ≤ r₂ ^ 2} :=
        measurableSet_le (by fun_prop) measurable_const
      have h2 : MeasurableSet {z : Pt | z.1 ≤ xStar} :=
        measurableSet_le measurable_fst measurable_const
      exact h1.inter h2
    have hvol1 : volume Cap1 = ENNReal.ofReal (r₁ ^ 2 * segArea c₁) := by
      have heq : Cap1 = {z : Pt | z.1 ^ 2 + z.2 ^ 2 ≤ r₁ ^ 2 ∧ r₁ * c₁ ≤ z.1} := by
        ext z; simp only [Cap1, hx1]
      rw [heq]; exact volume_disk_cap_right hr₁p hc1_mem
    have hvol2 : volume Cap2 = ENNReal.ofReal (r₂ ^ 2 * segArea c₂) := by
      -- Map `z ↦ (d - z.1, z.2)` (measure-preserving reflection + translation)
      let T : Pt → Pt := fun z => (d - z.1, z.2)
      have hmp : MeasurePreserving T volume volume := by
        have h1 : MeasurePreserving (fun z : Pt => (-z.1, z.2)) volume volume := by
          let L : Pt ≃ₗ[ℝ] Pt :=
            { toFun := fun p => (-p.1, p.2), invFun := fun p => (-p.1, p.2),
              left_inv := fun p => by ext <;> simp, right_inv := fun p => by ext <;> simp,
              map_add' := fun p q => by ext; (dsimp; ring); rfl,
              map_smul' := fun a p => by ext <;> simp }
          let b := Module.Basis.finTwoProd ℝ
          have hdet : LinearMap.det L.toLinearMap = -1 := by
            rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
            simp [LinearMap.toMatrix_apply, L, b]
          refine ⟨L.toLinearMap.continuous_of_finiteDimensional.measurable, ?_⟩
          change Measure.map L.toLinearMap volume = volume
          rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
          norm_num
        have h2 : MeasurePreserving (fun z : Pt => (d, (0 : ℝ)) + z) volume volume :=
          measurePreserving_add_left volume (d, (0 : ℝ))
        have hcomp : T = (fun z : Pt => (d, (0 : ℝ)) + z) ∘ (fun z : Pt => (-z.1, z.2)) := by
          funext z; ext <;> simp [T, sub_eq_add_neg]
        rw [hcomp]; exact h2.comp h1
      let Cap2' : Set Pt := {z : Pt | z.1 ^ 2 + z.2 ^ 2 ≤ r₂ ^ 2 ∧ r₂ * c₂ ≤ z.1}
      have hpre : Cap2 = T ⁻¹' Cap2' := by
        ext z
        simp only [Cap2, Cap2', Set.mem_preimage, Set.mem_setOf_eq, T]
        constructor
        · intro ⟨hsq, hle⟩
          refine ⟨by nlinarith, by linarith⟩
        · intro ⟨hsq, hge⟩
          refine ⟨by nlinarith, by linarith⟩
      have hmeas2' : MeasurableSet Cap2' := by
        have h1 : MeasurableSet {z : Pt | z.1 ^ 2 + z.2 ^ 2 ≤ r₂ ^ 2} :=
          measurableSet_le (by fun_prop) measurable_const
        have h2 : MeasurableSet {z : Pt | r₂ * c₂ ≤ z.1} :=
          measurableSet_le measurable_const measurable_fst
        exact h1.inter h2
      rw [hpre, hmp.measure_preimage hmeas2'.nullMeasurableSet]
      exact volume_disk_cap_right hr₂p hc2_mem
    have hdisj_ae : volume (Cap1 ∪ Cap2) = volume Cap1 + volume Cap2 := by
      have h1 := measure_union_add_inter (μ := volume) Cap1 hmeas2
      rw [hinter_zero, add_zero] at h1
      exact h1
    rw [hU, hdisj_ae, hvol1, hvol2, ← ENNReal.ofReal_add
      (mul_nonneg (sq_nonneg _) (segArea_nonneg hc1_mem.2))
      (mul_nonneg (sq_nonneg _) (segArea_nonneg hc2_mem.2))]

/-- Volume of the intersection of two disks, for arbitrary centers `p, q ∈ ℝ²` and radii `r₁, r₂ ≥ 0`. -/
theorem volume_disk_inter (p q : Pt) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    volume (disk p r₁ ∩ disk q r₂) = ENNReal.ofReal (diskInterArea (euclidDist p q) r₁ r₂) := by
  let d : ℝ := euclidDist p q
  have hd : 0 ≤ d := euclidDist_nonneg p q
  by_cases hd0 : d = 0
  · have hpq : p = q := by
      have hsq : sqDist p q = 0 := by
        have := euclidDist_sq p q; rw [show euclidDist p q = 0 from hd0] at this; linarith
      unfold sqDist at hsq
      ext <;> nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    subst hpq
    -- Translate by `-p` to origin
    let T : Pt → Pt := fun z => z + p
    have hmp : MeasurePreserving T volume volume := measurePreserving_add_right volume p
    have hpre : T ⁻¹' (disk p r₁ ∩ disk p r₂) = disk (0 : Pt) r₁ ∩ disk (0, 0) r₂ := by
      ext z; simp [T, disk, sqDist]
    have hmeas : MeasurableSet (disk p r₁ ∩ disk p r₂) :=
      (measurableSet_disk p r₁).inter (measurableSet_disk p r₂)
    rw [← hmp.measure_preimage hmeas.nullMeasurableSet, hpre,
      show euclidDist p p = 0 from euclidDist_self p]
    exact volume_disk_inter_axis le_rfl hr₁ hr₂
  · have hd_pos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    let c : ℝ := (q.1 - p.1) / d
    let s : ℝ := (q.2 - p.2) / d
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      dsimp only [c, s]
      have hsq : (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 = d ^ 2 := by
        have := euclidDist_sq p q; unfold sqDist at this; linarith
      field_simp [ne_of_gt hd_pos]; linarith
    let R := rotLinearEquiv c s hcs
    let T : Pt → Pt := fun z => R (z - p)
    have hmp : MeasurePreserving T volume volume :=
      (measurePreserving_rotLinearEquiv c s hcs).comp (measurePreserving_sub_right volume p)
    have hTq : T q = (d, 0) := by
      dsimp only [T, R, rotLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, c, s]
      have hsq : (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 = d ^ 2 := by
        have := euclidDist_sq p q; unfold sqDist at this; linarith
      ext
      · dsimp; field_simp [ne_of_gt hd_pos]; linarith
      · dsimp; field_simp [ne_of_gt hd_pos]; ring
    have hTp : T p = (0 : Pt) := by
      dsimp only [T]; rw [sub_self, map_zero]
    have hsqT : ∀ a b : Pt, sqDist (T a) (T b) = sqDist a b := fun a b => by
      dsimp only [T]; rw [rotLinearEquiv_sqDist]; unfold sqDist; simp
    have hpre : disk p r₁ ∩ disk q r₂ = T ⁻¹' (disk (0 : Pt) r₁ ∩ disk (d, 0) r₂) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, disk, Set.mem_setOf_eq]
      rw [← hTp, ← hTq, hsqT, hsqT]
    have hmeas : MeasurableSet (disk (0 : Pt) r₁ ∩ disk (d, 0) r₂) :=
      (measurableSet_disk _ _).inter (measurableSet_disk _ _)
    rw [hpre, hmp.measure_preimage hmeas.nullMeasurableSet]
    exact volume_disk_inter_axis hd hr₁ hr₂

/-- `diskInterArea d r₁ r₂` is antitone in `d ≥ 0`. -/
lemma diskInterArea_antitone_d {r₁ r₂ d₁ d₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hd₁ : 0 ≤ d₁) (hd₁₂ : d₁ ≤ d₂) :
    diskInterArea d₂ r₁ r₂ ≤ diskInterArea d₁ r₁ r₂ := by
  have hd₂ : 0 ≤ d₂ := hd₁.trans hd₁₂
  -- Geometric 5-line proof via Fubini slice lengths of `disk 0 r₁ ∩ disk (d, 0) r₂`
  -- At each vertical line `y`, the horizontal slice of `disk 0 r₁` is `[-a, a]` and of
  -- `disk (d, 0) r₂` is `[d - b, d + b]`; their intersection length `max 0 (min a (d + b) - max (-a) (d - b))`
  -- is nonincreasing in `d ≥ 0`
  rw [← ENNReal.ofReal_le_ofReal_iff (diskInterArea_nonneg d₁ r₁ r₂),
    ← volume_disk_inter_axis hd₁ hr₁ hr₂, ← volume_disk_inter_axis hd₂ hr₁ hr₂]
  have hmeas1 : MeasurableSet (disk (0 : Pt) r₁ ∩ disk (d₁, 0) r₂) :=
    (measurableSet_disk _ _).inter (measurableSet_disk _ _)
  have hmeas2 : MeasurableSet (disk (0 : Pt) r₁ ∩ disk (d₂, 0) r₂) :=
    (measurableSet_disk _ _).inter (measurableSet_disk _ _)
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas1, Measure.prod_apply_symm hmeas2]
  refine lintegral_mono fun y => ?_
  -- Compare 1D intervals at height `y`
  by_cases hy : y ^ 2 ≤ r₁ ^ 2 ∧ y ^ 2 ≤ r₂ ^ 2
  · let a : ℝ := Real.sqrt (r₁ ^ 2 - y ^ 2)
    let b : ℝ := Real.sqrt (r₂ ^ 2 - y ^ 2)
    have ha : 0 ≤ a := Real.sqrt_nonneg _
    have hb : 0 ≤ b := Real.sqrt_nonneg _
    have hslice : ∀ d : ℝ,
        (fun x => (x, y)) ⁻¹' (disk (0 : Pt) r₁ ∩ disk (d, 0) r₂) =
          Icc (max (-a) (d - b)) (min a (d + b)) := fun d => by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, disk, sqDist, Set.mem_setOf_eq,
        Prod.fst_zero, Prod.snd_zero, sub_zero, Set.mem_Icc, max_le_iff, le_min_iff]
      have hA : x ^ 2 + y ^ 2 ≤ r₁ ^ 2 ↔ -a ≤ x ∧ x ≤ a := by
        rw [← abs_le, ← sq_le_sq₀ (abs_nonneg x) ha, sq_abs, Real.sq_sqrt (by linarith [hy.1])]
        constructor <;> intro h <;> linarith
      have hB : (x - d) ^ 2 + y ^ 2 ≤ r₂ ^ 2 ↔ d - b ≤ x ∧ x ≤ d + b := by
        have : (x - d) ^ 2 + y ^ 2 ≤ r₂ ^ 2 ↔ |x - d| ≤ b := by
          rw [← sq_le_sq₀ (abs_nonneg _) hb, sq_abs, Real.sq_sqrt (by linarith [hy.2])]
          constructor <;> intro h <;> linarith
        rw [this, abs_le]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [hA, hB]; tauto
    rw [hslice d₁, hslice d₂, Real.volume_Icc, Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    -- `min a (d + b) - max (-a) (d - b) = min (2a) (min (2b) (a + b - d))` (for `d ≥ 0`) is decreasing in `d`
    have hlen : ∀ d : ℝ, 0 ≤ d →
        min a (d + b) - max (-a) (d - b) = min (min (2 * a) (2 * b)) (a + b - d) := fun d hd0 => by
      rcases le_total a (d + b) with h1 | h1 <;> rcases le_total (-a) (d - b) with h2 | h2
      · rw [min_eq_left h1, max_eq_right h2]
        have : a + b - d ≤ 2 * a := by linarith
        have : a + b - d ≤ 2 * b := by linarith
        rw [min_eq_right (le_min (by linarith) (by linarith))]; ring
      · rw [min_eq_left h1, max_eq_left h2]
        have : 2 * a ≤ 2 * b := by linarith
        have : 2 * a ≤ a + b - d := by linarith
        rw [min_eq_left ‹2 * a ≤ 2 * b›, min_eq_left ‹2 * a ≤ a + b - d›]; ring
      · rw [min_eq_right h1, max_eq_right h2]
        have : 2 * b ≤ 2 * a := by linarith
        have : 2 * b ≤ a + b - d := by linarith
        rw [min_eq_right ‹2 * b ≤ 2 * a›, min_eq_left ‹2 * b ≤ a + b - d›]; ring
      · rw [min_eq_right h1, max_eq_left h2]
        have hdeq : d = 0 := by linarith
        have hab : a = b := by linarith
        rw [hdeq, hab]; simp; linarith
    rw [hlen d₁ hd₁, hlen d₂ hd₂]
    exact min_le_min_left _ (by linarith)
  · have hemp : ∀ d : ℝ, (fun x => (x, y)) ⁻¹' (disk (0 : Pt) r₁ ∩ disk (d, 0) r₂) = ∅ := fun d => by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, disk, sqDist, Set.mem_setOf_eq,
        Prod.fst_zero, Prod.snd_zero, sub_zero, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact hy ⟨by nlinarith [sq_nonneg x], by nlinarith [sq_nonneg (x - d)]⟩
    rw [hemp d₁, hemp d₂]

lemma diskInterArea_le_min_disk {d r₁ r₂ : ℝ} (hd : 0 ≤ d) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    diskInterArea d r₁ r₂ ≤ Real.pi * (min r₁ r₂) ^ 2 := by
  have h1 := diskInterArea_antitone_d hr₁ hr₂ le_rfl hd
  refine h1.trans ?_
  unfold diskInterArea
  split_ifs with h0 hle
  · positivity
  · exact le_rfl
  · exact absurd (abs_nonneg (r₁ - r₂)) hle

/-! ## Elementary Lower Bounds on `vol(B(v, ρ) \ ⋃_{u ∈ S} B(p u, r))` -/

/-- If `p u ∈ disk c rad` for all `u`, then
`⋃ u, disk (p u) r ⊆ disk c (r + rad)`, hence
`volume (disk v ρ \ ⋃ u, disk (p u) r) ≥ π ρ² - diskInterArea (euclidDist v c) ρ (r + rad)`. -/
lemma volume_disk_sdiff_union_ge_circumdisk {k : ℕ} (p : Fin k → Pt) (c v : Pt)
    {r rad ρ : ℝ} (hr : 0 ≤ r) (hrad : 0 ≤ rad) (hρ : 0 ≤ ρ)
    (henc : ∀ u : Fin k, euclidDist (p u) c ≤ rad) :
    ENNReal.ofReal (Real.pi * ρ ^ 2 - diskInterArea (euclidDist v c) ρ (r + rad)) ≤
      volume (disk v ρ \ ⋃ u : Fin k, disk (p u) r) := by
  have hsub : (⋃ u : Fin k, disk (p u) r) ⊆ disk c (r + rad) := by
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨u, hu⟩
    have h1 : euclidDist z (p u) ≤ r := (euclidDist_le_iff hr).mpr hu
    have h2 : euclidDist z c ≤ r + rad :=
      (euclidDist_triangle z (p u) c).trans (add_le_add h1 (henc u))
    exact (euclidDist_le_iff (add_nonneg hr hrad)).mp h2
  have hsdiff : disk v ρ \ disk c (r + rad) ⊆ disk v ρ \ ⋃ u : Fin k, disk (p u) r :=
    Set.sdiff_subset_sdiff_right hsub
  refine le_trans ?_ (measure_mono hsdiff)
  have hmeas_inter : MeasurableSet (disk v ρ ∩ disk c (r + rad)) :=
    (measurableSet_disk v ρ).inter (measurableSet_disk c (r + rad))
  have hfin : volume (disk v ρ ∩ disk c (r + rad)) ≠ ⊤ := by
    rw [volume_disk_inter v c hρ (add_nonneg hr hrad)]; exact ENNReal.ofReal_ne_top
  have heq : disk v ρ \ disk c (r + rad) = disk v ρ \ (disk v ρ ∩ disk c (r + rad)) := by
    ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [heq, measure_sdiff Set.inter_subset_left hmeas_inter.nullMeasurableSet hfin,
    volume_disk v hρ, volume_disk_inter v c hρ (add_nonneg hr hrad),
    ← ENNReal.ofReal_sub _ (diskInterArea_nonneg _ _ _)]

/-- Union bound:
`volume (disk v ρ \ ⋃ u, disk (p u) r) ≥ π ρ² - ∑ u, diskInterArea (euclidDist v (p u)) ρ r`. -/
lemma volume_disk_sdiff_union_ge_unionBound {k : ℕ} (p : Fin k → Pt) (v : Pt)
    {r ρ : ℝ} (hr : 0 ≤ r) (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (Real.pi * ρ ^ 2 - ∑ u : Fin k, diskInterArea (euclidDist v (p u)) ρ r) ≤
      volume (disk v ρ \ ⋃ u : Fin k, disk (p u) r) := by
  let U : Set Pt := ⋃ u : Fin k, disk (p u) r
  have hmeasU : MeasurableSet (disk v ρ ∩ U) :=
    (measurableSet_disk v ρ).inter (MeasurableSet.iUnion fun u => measurableSet_disk (p u) r)
  have hfin : volume (disk v ρ ∩ U) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [volume_disk v hρ]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_left)
  have hcov : disk v ρ ∩ U = ⋃ u : Fin k, (disk v ρ ∩ disk (p u) r) := Set.inter_iUnion _ _
  have hle_sum : volume (disk v ρ ∩ U) ≤
      ENNReal.ofReal (∑ u : Fin k, diskInterArea (euclidDist v (p u)) ρ r) := by
    rw [hcov]
    calc volume (⋃ u : Fin k, (disk v ρ ∩ disk (p u) r))
        ≤ ∑ u : Fin k, volume (disk v ρ ∩ disk (p u) r) := measure_iUnion_fintype_le _ _
      _ = ∑ u : Fin k, ENNReal.ofReal (diskInterArea (euclidDist v (p u)) ρ r) := by
            refine Finset.sum_congr rfl fun u _ => volume_disk_inter v (p u) hρ hr
      _ = ENNReal.ofReal (∑ u : Fin k, diskInterArea (euclidDist v (p u)) ρ r) :=
            (ENNReal.ofReal_sum_of_nonneg fun u _ => diskInterArea_nonneg _ _ _).symm
  have heq : disk v ρ \ U = disk v ρ \ (disk v ρ ∩ U) := by
    ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [heq, measure_sdiff Set.inter_subset_left hmeasU.nullMeasurableSet hfin, volume_disk v hρ]
  rw [ENNReal.ofReal_sub _ (Finset.sum_nonneg fun u _ => diskInterArea_nonneg _ _ _)]
  exact tsub_le_tsub_left hle_sum _

end

end BHHBounds.Geometry
