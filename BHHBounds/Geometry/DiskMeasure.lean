import BHHBounds.Defs
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Disks, planar symmetries and polar coordinates

The area `π r²` of a disk, measure-preserving rotations, reflections and scalings of the plane, and
the polar change of variables.
-/

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace BHHBounds.Geometry

noncomputable section

/-! ## Disk Volumes -/

lemma volume_disk (a : Pt) {r : ℝ} (hr : 0 ≤ r) :
    volume (disk a r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' (disk a r) =
      Metric.closedBall (⟨a.1, a.2⟩ : ℂ) r := by
    ext w
    simp only [Set.mem_preimage, Complex.measurableEquivRealProd_apply, disk, sqDist,
      Set.mem_setOf_eq, Metric.mem_closedBall, Complex.dist_eq]
    rw [← sq_le_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    constructor <;> intro h <;> nlinarith [h]
  rw [← Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, hpre,
    Complex.volume_closedBall, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

lemma volume_disk_one (a : Pt) : volume (disk a 1) = ENNReal.ofReal Real.pi := by
  rw [volume_disk a zero_le_one, one_pow, mul_one]

lemma volume_openDisk (a : Pt) {r : ℝ} (hr : 0 ≤ r) :
    volume {z : Pt | sqDist z a < r ^ 2} = ENNReal.ofReal (Real.pi * r ^ 2) := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' {z : Pt | sqDist z a < r ^ 2} =
      Metric.ball (⟨a.1, a.2⟩ : ℂ) r := by
    ext w
    simp only [Set.mem_preimage, Complex.measurableEquivRealProd_apply, sqDist,
      Set.mem_setOf_eq, Metric.mem_ball, Complex.dist_eq]
    constructor
    · intro h
      have hsq : ‖w - (⟨a.1, a.2⟩ : ℂ)‖ ^ 2 < r ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im]
        nlinarith [h]
      exact (sq_lt_sq₀ (norm_nonneg _) hr).mp hsq
    · intro h
      have hsq : ‖w - (⟨a.1, a.2⟩ : ℂ)‖ ^ 2 < r ^ 2 := (sq_lt_sq₀ (norm_nonneg _) hr).mpr h
      rw [Complex.sq_norm, Complex.normSq_apply] at hsq
      simp only [Complex.sub_re, Complex.sub_im] at hsq
      nlinarith [hsq]
  rw [← Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, hpre,
    Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

lemma volume_line_zero {a b c : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    volume {z : Pt | a * z.1 + b * z.2 = c} = 0 := by
  rw [Measure.volume_eq_prod]
  have hmeas : MeasurableSet {z : Pt | a * z.1 + b * z.2 = c} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rcases hab with ha | hb
  · rw [Measure.prod_apply_symm hmeas]
    have hzero : ∀ y : ℝ, volume {x : ℝ | a * x + b * y = c} = 0 := by
      intro y
      have hsub : {x : ℝ | a * x + b * y = c} ⊆ {(c - b * y) / a} := by
        intro x hx
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
        field_simp [ha]; linarith
      exact measure_mono_null hsub Real.volume_singleton
    simp [hzero]
  · rw [Measure.prod_apply hmeas]
    have hzero : ∀ x : ℝ, volume {y : ℝ | a * x + b * y = c} = 0 := by
      intro x
      have hsub : {y : ℝ | a * x + b * y = c} ⊆ {(c - a * x) / b} := by
        intro y hy
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hy ⊢
        field_simp [hb]; linarith
      exact measure_mono_null hsub Real.volume_singleton
    simp [hzero]

/-! ## Measure-Preserving Planar Symmetries & Scaling -/

/-- Orthogonal rotation `(x, y) ↦ (c x + s y, -s x + c y)` with `c² + s² = 1`. -/
def rotLinearEquiv (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : Pt ≃ₗ[ℝ] Pt where
  toFun p := (c * p.1 + s * p.2, -s * p.1 + c * p.2)
  invFun p := (c * p.1 - s * p.2, s * p.1 + c * p.2)
  left_inv p := by
    ext
    · dsimp; linear_combination p.1 * hcs
    · dsimp; linear_combination p.2 * hcs
  right_inv p := by
    ext
    · dsimp; linear_combination p.1 * hcs
    · dsimp; linear_combination p.2 * hcs
  map_add' p q := by ext <;> (dsimp; ring)
  map_smul' a p := by ext <;> (dsimp; ring)

lemma rotLinearEquiv_sqDist (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (p q : Pt) :
    sqDist (rotLinearEquiv c s hcs p) (rotLinearEquiv c s hcs q) = sqDist p q := by
  simp only [rotLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sqDist]
  have h1 : (c * p.1 + s * p.2 - (c * q.1 + s * q.2)) ^ 2 +
      (-s * p.1 + c * p.2 - (-s * q.1 + c * q.2)) ^ 2 =
      (c ^ 2 + s ^ 2) * ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) := by ring
  rw [h1, hcs, one_mul]

lemma rotLinearEquiv_det (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    LinearMap.det (rotLinearEquiv c s hcs).toLinearMap = 1 := by
  let b := Module.Basis.finTwoProd ℝ
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, rotLinearEquiv, b]
  linear_combination hcs

lemma measurePreserving_rotLinearEquiv (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    MeasurePreserving (rotLinearEquiv c s hcs) volume volume := by
  have hdet := rotLinearEquiv_det c s hcs
  have hne : LinearMap.det (rotLinearEquiv c s hcs).toLinearMap ≠ 0 := by rw [hdet]; norm_num
  refine ⟨(rotLinearEquiv c s hcs).toLinearMap.continuous_of_finiteDimensional.measurable, ?_⟩
  change Measure.map (rotLinearEquiv c s hcs).toLinearMap volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, hdet, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul]

/-- Reflection `(x, y) ↦ (x, -y)`. -/
def reflYLinearEquiv : Pt ≃ₗ[ℝ] Pt where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext; rfl; (dsimp; ring)
  map_smul' a p := by ext <;> simp

lemma measurePreserving_reflY : MeasurePreserving reflYLinearEquiv volume volume := by
  let b := Module.Basis.finTwoProd ℝ
  have hdet : LinearMap.det reflYLinearEquiv.toLinearMap = -1 := by
    rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, reflYLinearEquiv, b]
  have hne : LinearMap.det reflYLinearEquiv.toLinearMap ≠ 0 := by rw [hdet]; norm_num
  refine ⟨reflYLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable, ?_⟩
  change Measure.map reflYLinearEquiv.toLinearMap volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, hdet]
  norm_num

/-- Uniform scaling `z ↦ (r * z.1, r * z.2)` for `r ≠ 0`. -/
def scaleLinearEquiv {r : ℝ} (hr : r ≠ 0) : Pt ≃ₗ[ℝ] Pt where
  toFun p := (r * p.1, r * p.2)
  invFun p := (r⁻¹ * p.1, r⁻¹ * p.2)
  left_inv p := by ext <;> (dsimp; field_simp [hr])
  right_inv p := by ext <;> (dsimp; field_simp [hr])
  map_add' p q := by ext <;> (dsimp; ring)
  map_smul' a p := by ext <;> (dsimp; ring)

lemma scaleLinearEquiv_det {r : ℝ} (hr : r ≠ 0) :
    LinearMap.det (scaleLinearEquiv hr).toLinearMap = r ^ 2 := by
  let b := Module.Basis.finTwoProd ℝ
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, scaleLinearEquiv, b, sq]

lemma volume_preimage_scale {r : ℝ} (hr : 0 < r) {S : Set Pt} (hS : MeasurableSet S) :
    volume ((scaleLinearEquiv (ne_of_gt hr)) ⁻¹' S) = ENNReal.ofReal (r ^ 2)⁻¹ * volume S := by
  have hne : LinearMap.det (scaleLinearEquiv (ne_of_gt hr)).toLinearMap ≠ 0 := by
    rw [scaleLinearEquiv_det]; positivity
  have hmap : Measure.map (scaleLinearEquiv (ne_of_gt hr)).toLinearMap volume =
      ENNReal.ofReal |(r ^ 2)⁻¹| • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, scaleLinearEquiv_det]
  have hcont : Continuous (scaleLinearEquiv (ne_of_gt hr)).toLinearMap :=
    (scaleLinearEquiv (ne_of_gt hr)).toLinearMap.continuous_of_finiteDimensional
  have heq : volume ((scaleLinearEquiv (ne_of_gt hr)) ⁻¹' S) =
      (Measure.map (scaleLinearEquiv (ne_of_gt hr)).toLinearMap volume) S := by
    symm; exact Measure.map_apply hcont.measurable hS
  rw [heq, hmap, Measure.smul_apply, smul_eq_mul, abs_of_nonneg (by positivity)]

lemma volume_image_scale {r : ℝ} (hr : 0 < r) {S : Set Pt} (hS : MeasurableSet S) :
    volume ((scaleLinearEquiv (ne_of_gt hr)) '' S) = ENNReal.ofReal (r ^ 2) * volume S := by
  have hinv_pos : 0 < r⁻¹ := inv_pos.mpr hr
  have hpre : (scaleLinearEquiv (ne_of_gt hr)) '' S =
      (scaleLinearEquiv (ne_of_gt hinv_pos)) ⁻¹' S := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage, scaleLinearEquiv, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (r⁻¹ * (r * w.1), r⁻¹ * (r * w.2)) = w := by
        ext <;> dsimp <;> field_simp [ne_of_gt hr]
      rwa [this]
    · intro hz
      refine ⟨(r⁻¹ * z.1, r⁻¹ * z.2), hz, ?_⟩
      ext <;> dsimp <;> field_simp [ne_of_gt hr]
  rw [hpre, volume_preimage_scale hinv_pos hS]
  congr 2; field_simp [ne_of_gt hr]

lemma unionDiskArea_scale {k : ℕ} (y : Fin k → Pt) {R : ℝ} (hR : 0 < R) :
    unionDiskArea (fun i => (R * (y i).1, R * (y i).2)) R = R ^ 2 * unionDiskArea y 1 := by
  unfold unionDiskArea
  have hmeas : MeasurableSet (⋃ i : Fin k, disk (y i) 1) :=
    MeasurableSet.iUnion fun i => measurableSet_disk (y i) 1
  have himg : (⋃ i : Fin k, disk (R * (y i).1, R * (y i).2) R) =
      (scaleLinearEquiv (ne_of_gt hR)) '' (⋃ i : Fin k, disk (y i) 1) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_image, disk, sqDist, Set.mem_setOf_eq,
      scaleLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨(R⁻¹ * z.1, R⁻¹ * z.2), ⟨i, ?_⟩, ?_⟩
      · have hmul : (R⁻¹ * z.1 - (y i).1) ^ 2 + (R⁻¹ * z.2 - (y i).2) ^ 2 =
            (R ^ 2)⁻¹ * ((z.1 - R * (y i).1) ^ 2 + (z.2 - R * (y i).2) ^ 2) := by
          field_simp [ne_of_gt hR]
        rw [hmul, one_pow]
        have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
        rw [inv_mul_le_iff₀ hR2, mul_one]; exact hi
      · ext <;> dsimp <;> field_simp [ne_of_gt hR]
    · rintro ⟨w, ⟨i, hi⟩, rfl⟩
      refine ⟨i, ?_⟩
      have hmul : (R * w.1 - R * (y i).1) ^ 2 + (R * w.2 - R * (y i).2) ^ 2 =
          R ^ 2 * ((w.1 - (y i).1) ^ 2 + (w.2 - (y i).2) ^ 2) := by ring
      rw [hmul]
      nlinarith [sq_nonneg R]
  rw [himg, volume_image_scale hR hmeas, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg R)]

/-! ## Polar Coordinates on `ℝ²` -/

/-- Shifting `(-π, π)` to `(0, 2π)` preserves the `lintegral` of any `2π`-periodic function. -/
lemma lintegral_Ioo_neg_pi_pi_eq_Ioo_zero_two_pi {g : ℝ → ℝ≥0∞}
    (hper : ∀ θ, g (θ + 2 * Real.pi) = g θ) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, g θ = ∫⁻ θ in Ioo (0 : ℝ) (2 * Real.pi), g θ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsplit1 : Ioo (-Real.pi) Real.pi =ᵐ[volume]
      (Ioo (-Real.pi) (0 : ℝ) ∪ Ioo (0 : ℝ) Real.pi : Set ℝ) := by
    rw [Filter.EventuallyEq, ae_iff]
    have hsub : {θ : ℝ | ¬ (θ ∈ Ioo (-Real.pi) Real.pi ↔
        θ ∈ Ioo (-Real.pi) 0 ∪ Ioo 0 Real.pi)} ⊆ {(0 : ℝ)} := by
      intro θ hθ
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff] at hθ ⊢
      by_contra hne
      apply hθ
      constructor
      · intro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨h1, hlt⟩
        · exact Or.inr ⟨hgt, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
    exact measure_mono_null
      (fun θ hθ => hsub (by
        change ¬ ((θ ∈ Ioo (-Real.pi) Real.pi) = (θ ∈ Ioo (-Real.pi) 0 ∪ Ioo 0 Real.pi)) at hθ
        rwa [eq_iff_iff] at hθ))
      Real.volume_singleton
  have hsplit2 : Ioo (0 : ℝ) (2 * Real.pi) =ᵐ[volume]
      (Ioo (0 : ℝ) Real.pi ∪ Ioo Real.pi (2 * Real.pi) : Set ℝ) := by
    rw [Filter.EventuallyEq, ae_iff]
    have hsub : {θ : ℝ | ¬ (θ ∈ Ioo (0 : ℝ) (2 * Real.pi) ↔
        θ ∈ Ioo 0 Real.pi ∪ Ioo Real.pi (2 * Real.pi))} ⊆ {Real.pi} := by
      intro θ hθ
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff] at hθ ⊢
      by_contra hne
      apply hθ
      constructor
      · intro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨h1, hlt⟩
        · exact Or.inr ⟨hgt, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
    exact measure_mono_null
      (fun θ hθ => hsub (by
        change ¬ ((θ ∈ Ioo (0 : ℝ) (2 * Real.pi)) = (θ ∈ Ioo 0 Real.pi ∪ Ioo Real.pi (2 * Real.pi))) at hθ
        rwa [eq_iff_iff] at hθ))
      Real.volume_singleton
  have hdisj1 : Disjoint (Ioo (-Real.pi) (0 : ℝ)) (Ioo (0 : ℝ) Real.pi) :=
    Set.disjoint_left.mpr fun _ h1 h2 => by linarith [h1.2, h2.1]
  have hdisj2 : Disjoint (Ioo (0 : ℝ) Real.pi) (Ioo Real.pi (2 * Real.pi)) :=
    Set.disjoint_left.mpr fun _ h1 h2 => by linarith [h1.2, h2.1]
  rw [setLIntegral_congr hsplit1, setLIntegral_congr hsplit2,
    lintegral_union measurableSet_Ioo hdisj1,
    lintegral_union measurableSet_Ioo hdisj2]
  have hshift : ∫⁻ θ in Ioo (-Real.pi) (0 : ℝ), g θ =
      ∫⁻ θ in Ioo Real.pi (2 * Real.pi), g θ := by
    have hpre : (fun θ : ℝ => θ + 2 * Real.pi) ⁻¹' Ioo Real.pi (2 * Real.pi) =
        Ioo (-Real.pi) (0 : ℝ) := by
      ext θ; simp only [Set.mem_preimage, Set.mem_Ioo]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
    have hmp : MeasurePreserving (fun θ : ℝ => θ + 2 * Real.pi) volume volume :=
      measurePreserving_add_right volume (2 * Real.pi)
    rw [← hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (2 * Real.pi)) g
      (Ioo Real.pi (2 * Real.pi)), hpre]
    exact setLIntegral_congr_fun measurableSet_Ioo fun θ _ => (hper θ).symm
  rw [hshift, add_comm]

/-- Nonnegative polar change of variables on `ℝ²` (`θ ∈ (0, 2π)`). -/
lemma lintegral_polar_eq {f : Pt → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z : Pt, f z =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
        ∫⁻ θ in Ioo (0 : ℝ) (2 * Real.pi), f (r * Real.cos θ, r * Real.sin θ) := by
  rw [← lintegral_comp_polarCoord_symm f]
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  rw [htarget, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • f (polarCoord.symm p)) := by
    have hc : Measurable polarCoord.symm := continuous_polarCoord_symm.measurable
    exact (ENNReal.measurable_ofReal.comp measurable_fst).mul (hf.comp hc)
  rw [lintegral_prod _ hmeas.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [smul_eq_mul, polarCoord_symm_apply]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact lintegral_Ioo_neg_pi_pi_eq_Ioo_zero_two_pi fun θ => by
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Radial polar `lintegral`: `∫⁻ z, h (euclidNorm z) = ∫⁻ r ∈ (0, ∞), 2π r h(r)`. -/
lemma lintegral_radial_eq {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ z : Pt, h (euclidNorm z) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.pi * r) * h r := by
  have hf : Measurable (fun z : Pt => h (euclidNorm z)) := by
    refine hh.comp ?_
    unfold euclidNorm; fun_prop
  rw [lintegral_polar_eq hf]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 ≤ r := le_of_lt hr
  have hnorm : ∀ θ : ℝ, euclidNorm (r * Real.cos θ, r * Real.sin θ) = r := fun θ => by
    unfold euclidNorm
    have hsq : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      have hcs := Real.cos_sq_add_sin_sq θ
      nlinarith
    rw [hsq, Real.sqrt_sq hr0]
  simp_rw [hnorm]
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm (h r),
    ← mul_assoc, ← ENNReal.ofReal_mul hr0]
  congr 2; ring

/-- Radial Bochner integral for nonnegative radial functions. -/
lemma integral_radial_eq {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nn : ∀ r, 0 ≤ h r) :
    ∫ z : Pt, h (euclidNorm z) =
      ∫ r in Ioi (0 : ℝ), (2 * Real.pi * r) * h r := by
  have hf_meas : Measurable (fun z : Pt => h (euclidNorm z)) := by
    refine hh_meas.comp ?_
    unfold euclidNorm; fun_prop
  have hg_meas : Measurable (fun r : ℝ => (2 * Real.pi * r) * h r) :=
    (measurable_const.mul measurable_id).mul hh_meas
  have hlint : ∫⁻ z : Pt, ENNReal.ofReal (h (euclidNorm z)) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((2 * Real.pi * r) * h r) := by
    have h0 := lintegral_radial_eq (h := fun r => ENNReal.ofReal (h r))
      (ENNReal.measurable_ofReal.comp hh_meas)
    rw [h0]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 ≤ 2 * Real.pi * r := mul_nonneg (by positivity) (le_of_lt hr)
    rw [ENNReal.ofReal_mul hr0]
  have h1 : ∫ z : Pt, h (euclidNorm z) =
      (∫⁻ z : Pt, ENNReal.ofReal (h (euclidNorm z))).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => hh_nn _)
      hf_meas.aestronglyMeasurable
  have h2 : ∫ r in Ioi (0 : ℝ), (2 * Real.pi * r) * h r =
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((2 * Real.pi * r) * h r)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_mem measurableSet_Ioi).mono fun r hr =>
        mul_nonneg (mul_nonneg (by positivity) (le_of_lt hr)) (hh_nn r))
      hg_meas.aestronglyMeasurable
  rw [h1, h2, hlint]

end

end BHHBounds.Geometry
