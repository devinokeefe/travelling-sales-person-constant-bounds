import BHHBounds.Upper.ExpBins
import BHHBounds.Upper.Cert4Spec
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Soundness of the Exact Integer Strip Edge-Cost Table (`costFlat1..4`)

Proves `edgeCost4_sound`: every entry `edgeCost4 v gs ys` in `Cert4Spec.lean` is a
rigorous upper bound on the exact conditional expected Euclidean edge length
`E[√((∑ E_i / (11/5))^2 + (Y_v - Y_4)^2) | gap_bins = gs, height_bins = ys]`
under independent `Exp(1)` quantile-bin measures and `Unif[0, 11/5]` height-bin measures.
-/

namespace BHHBounds.Upper

open MeasureTheory Set Real Filter
open scoped ENNReal NNReal BigOperators

/-! ## Section 1: Computable Dyadic Rational Enclosure for `Real.log` -/

def atanhTruncQ (n : ℕ) (z : ℚ) : ℚ :=
  2 * ∑ k ∈ Finset.range n, z ^ (2 * k + 1) / (2 * k + 1 : ℚ)

lemma atanhTruncQ_cast (n : ℕ) (z : ℚ) :
    (atanhTruncQ n z : ℝ) = atanhTrunc n (z : ℝ) := by
  unfold atanhTruncQ atanhTrunc
  push_cast
  rfl

lemma atanhTruncQ_nonneg (n : ℕ) {z : ℚ} (hz : 0 ≤ z) : 0 ≤ atanhTruncQ n z := by
  unfold atanhTruncQ
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg (pow_nonneg hz _) (by positivity)

def coreLogBoundsQ (n : ℕ) (x : ℚ) : ℚ × ℚ :=
  let z := (x - 1) / (x + 1)
  let lo := atanhTruncQ n z
  let rem := 2 * z ^ (2 * n + 1) / ((2 * n + 1 : ℚ) * (1 - z ^ 2))
  (lo, lo + rem)

lemma coreLogBoundsQ_sound (n : ℕ) {x : ℚ} (hx : 1 ≤ x) :
    0 ≤ (coreLogBoundsQ n x).1 ∧
    ((coreLogBoundsQ n x).1 : ℝ) ≤ Real.log (x : ℝ) ∧
    Real.log (x : ℝ) ≤ ((coreLogBoundsQ n x).2 : ℝ) := by
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hzQ : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) (by linarith)
  have h := log_bounds_of_ge_one n hxR
  refine ⟨atanhTruncQ_nonneg n hzQ, ?_, ?_⟩
  · simpa [coreLogBoundsQ, atanhTruncQ_cast] using h.1
  · simpa [coreLogBoundsQ, atanhTruncQ_cast] using h.2

/-- Dyadic argument reduction: splits `x ≥ 1` into `2^k * y` (`y ∈ [1, 2]`) so `z ≤ 1/3`. -/
def logBoundsFuelQ (n : ℕ) : ℕ → ℚ → ℚ × ℚ
  | 0, x => coreLogBoundsQ n x
  | fuel + 1, x =>
    if x < 2 then coreLogBoundsQ n x
    else
      let b2 := coreLogBoundsQ n 2
      let br := logBoundsFuelQ n fuel (x / 2)
      (b2.1 + br.1, b2.2 + br.2)

lemma logBoundsFuelQ_sound (n : ℕ) :
    ∀ (fuel : ℕ) {x : ℚ}, 1 ≤ x →
      0 ≤ (logBoundsFuelQ n fuel x).1 ∧
      ((logBoundsFuelQ n fuel x).1 : ℝ) ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) ≤ ((logBoundsFuelQ n fuel x).2 : ℝ)
  | 0, x, hx => coreLogBoundsQ_sound n hx
  | fuel + 1, x, hx => by
    unfold logBoundsFuelQ
    split_ifs with hlt
    · exact coreLogBoundsQ_sound n hx
    · have hx2 : (2 : ℚ) ≤ x := le_of_not_gt hlt
      have hx_half : (1 : ℚ) ≤ x / 2 := by linarith
      have h2 := coreLogBoundsQ_sound n (x := 2) (by norm_num)
      push_cast at h2
      have hr := logBoundsFuelQ_sound n fuel hx_half
      have hxR : (x : ℝ) = 2 * ((x / 2 : ℚ) : ℝ) := by push_cast; ring
      have hlog : Real.log (x : ℝ) = Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) := by
        rw [hxR, Real.log_mul (by norm_num) (by
          have : (1 : ℝ) ≤ ((x / 2 : ℚ) : ℝ) := by exact_mod_cast hx_half
          linarith)]
      refine ⟨add_nonneg h2.1 hr.1, ?_, ?_⟩
      · push_cast; rw [hlog]; linarith [h2.2.1, hr.2.1]
      · push_cast; rw [hlog]; linarith [h2.2.2, hr.2.2]

def logBoundsQ (x : ℚ) : ℚ × ℚ := logBoundsFuelQ 14 8 x

lemma logBoundsQ_sound {x : ℚ} (hx : 1 ≤ x) :
    0 ≤ (logBoundsQ x).1 ∧
    ((logBoundsQ x).1 : ℝ) ≤ Real.log (x : ℝ) ∧
    Real.log (x : ℝ) ≤ ((logBoundsQ x).2 : ℝ) :=
  logBoundsFuelQ_sound 14 8 hx

/-- Rational upper bounds `(mean_hi, var_hi)` for `Exp(1)` quantile bin `j < n`. -/
def expBinMomentsQ (n j : ℕ) : ℚ × ℚ :=
  let a := logBoundsQ ((n : ℚ) / ((n - j : ℕ) : ℚ))
  let left : ℚ := ((n - j : ℕ) : ℚ)
  let right : ℚ := ((n - (j + 1) : ℕ) : ℚ)
  if j + 1 < n then
    let b := logBoundsQ ((n : ℚ) / right)
    let mean_lo := max 0 (left * (a.1 + 1) - right * (b.2 + 1))
    let mean_hi := left * (a.2 + 1) - right * (b.1 + 1)
    let m2_hi := left * (a.2 ^ 2 + 2 * a.2 + 2) - right * (b.1 ^ 2 + 2 * b.1 + 2)
    (mean_hi, m2_hi - mean_lo ^ 2)
  else
    let mean_lo := max 0 (a.1 + 1)
    let mean_hi := a.2 + 1
    let m2_hi := a.2 ^ 2 + 2 * a.2 + 2
    (mean_hi, m2_hi - mean_lo ^ 2)

/-! ## Section 2: Exact Quantile-Bin & Height-Bin Probability Measures -/

/-- `ℝ≥0`-valued density of `Exp(1)` conditioned on quantile bin `expBinSet n j`. -/
noncomputable def expBinDensityNN (n j : ℕ) (x : ℝ) : ℝ≥0 :=
  (expBinSet n j).indicator (fun t => Real.toNNReal ((n : ℝ) * Real.exp (-t))) x

lemma measurable_expBinDensityNN (n j : ℕ) : Measurable (expBinDensityNN n j) :=
  (Measurable.real_toNNReal (by fun_prop)).indicator (measurableSet_expBinSet n j)

/-- Exact conditional distribution of `Exp(1)` on quantile bin `expBinSet n j` (`j < n`). -/
noncomputable def expBinMeasure (n j : ℕ) : Measure ℝ :=
  volume.withDensity fun x => (expBinDensityNN n j x : ℝ≥0∞)

lemma integrableOn_exp_neg_bin (n j : ℕ) :
    IntegrableOn (fun x => Real.exp (-x)) (expBinSet n j) volume := by
  unfold expBinSet
  split_ifs
  · exact (by fun_prop : Continuous _).integrableOn_Ioc
  · exact integrableOn_exp_neg_Ioi (expCut n j)

lemma integrableOn_mul_exp_neg_bin {n j : ℕ} (hj : j < n) :
    IntegrableOn (fun x => x * Real.exp (-x)) (expBinSet n j) volume := by
  unfold expBinSet
  split_ifs
  · exact (by fun_prop : Continuous _).integrableOn_Ioc
  · exact integrableOn_mul_exp_neg_Ioi (expCut_nonneg hj)

lemma integrableOn_sq_mul_exp_neg_bin (n j : ℕ) :
    IntegrableOn (fun x => x ^ 2 * Real.exp (-x)) (expBinSet n j) volume := by
  unfold expBinSet
  split_ifs
  · exact (by fun_prop : Continuous _).integrableOn_Ioc
  · exact integrableOn_sq_mul_exp_neg_Ioi (expCut n j)

lemma expBinDensityNN_coe (n j : ℕ) (x : ℝ) :
    ((expBinDensityNN n j x : ℝ≥0) : ℝ) =
      (expBinSet n j).indicator (fun t => (n : ℝ) * Real.exp (-t)) x := by
  unfold expBinDensityNN
  by_cases hx : x ∈ expBinSet n j
  · simp [Set.indicator_of_mem hx, Real.coe_toNNReal _ (by positivity : 0 ≤ (n : ℝ) * Real.exp (-x))]
  · simp [Set.indicator_of_notMem hx]

lemma isProbabilityMeasure_expBinMeasure {n j : ℕ} (hj : j < n) :
    IsProbabilityMeasure (expBinMeasure n j) := by
  constructor
  unfold expBinMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfun : (fun x => (expBinDensityNN n j x : ℝ≥0∞)) =
      (expBinSet n j).indicator (fun t => ENNReal.ofReal ((n : ℝ) * Real.exp (-t))) := by
    funext x
    unfold expBinDensityNN
    by_cases hx : x ∈ expBinSet n j
    · simp [Set.indicator_of_mem hx, ENNReal.ofReal]
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, lintegral_indicator (measurableSet_expBinSet n j)]
  have hint : IntegrableOn (fun t => (n : ℝ) * Real.exp (-t)) (expBinSet n j) volume :=
    (integrableOn_exp_neg_bin n j).const_mul (n : ℝ)
  have hnn : ∀ t, 0 ≤ (n : ℝ) * Real.exp (-t) := fun t => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)]
  rw [integral_const_mul, setIntegral_exp_neg_bin hj]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [mul_one_div_cancel hn, ENNReal.ofReal_one]

lemma integral_expBinMeasure (n j : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(expBinMeasure n j) = (n : ℝ) * ∫ x in expBinSet n j, f x * Real.exp (-x) := by
  unfold expBinMeasure
  rw [integral_withDensity_eq_integral_smul (measurable_expBinDensityNN n j)]
  have hfun : (fun x => expBinDensityNN n j x • f x) =
      (expBinSet n j).indicator (fun x => (n : ℝ) * (f x * Real.exp (-x))) := by
    funext x
    change ((expBinDensityNN n j x : ℝ≥0) : ℝ) * f x = _
    rw [expBinDensityNN_coe]
    by_cases hx : x ∈ expBinSet n j
    · simp only [Set.indicator_of_mem hx]; ring
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, integral_indicator (measurableSet_expBinSet n j), integral_const_mul]

lemma integrable_expBinMeasure_iff {n j : ℕ} (hj : j < n) {f : ℝ → ℝ} :
    Integrable f (expBinMeasure n j) ↔
      IntegrableOn (fun x => f x * Real.exp (-x)) (expBinSet n j) volume := by
  unfold expBinMeasure
  rw [integrable_withDensity_iff_integrable_smul₀ (measurable_expBinDensityNN n j).aemeasurable]
  have hfun : (fun x => expBinDensityNN n j x • f x) =
      (expBinSet n j).indicator (fun x => (n : ℝ) * (f x * Real.exp (-x))) := by
    funext x
    change ((expBinDensityNN n j x : ℝ≥0) : ℝ) * f x = _
    rw [expBinDensityNN_coe]
    by_cases hx : x ∈ expBinSet n j
    · simp only [Set.indicator_of_mem hx]; ring
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, integrable_indicator_iff (measurableSet_expBinSet n j)]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hn) _

lemma integrable_id_expBinMeasure {n j : ℕ} (hj : j < n) :
    Integrable (fun x : ℝ => x) (expBinMeasure n j) :=
  (integrable_expBinMeasure_iff hj).mpr (integrableOn_mul_exp_neg_bin hj)

lemma integrable_sq_expBinMeasure {n j : ℕ} (hj : j < n) :
    Integrable (fun x : ℝ => x ^ 2) (expBinMeasure n j) :=
  (integrable_expBinMeasure_iff hj).mpr (integrableOn_sq_mul_exp_neg_bin n j)

lemma expBinMeasure_moments_le {n j : ℕ} (hj : j < n) :
    0 ≤ ∫ x, x ∂(expBinMeasure n j) ∧
    ∫ x, x ∂(expBinMeasure n j) ≤ ((expBinMomentsQ n j).1 : ℝ) ∧
    (∫ x, x ^ 2 ∂(expBinMeasure n j)) - (∫ x, x ∂(expBinMeasure n j)) ^ 2 ≤
      ((expBinMomentsQ n j).2 : ℝ) := by
  have hmean : ∫ x, x ∂(expBinMeasure n j) =
      if j + 1 < n then
        ((n - j : ℕ) : ℝ) * (expCut n j + 1) - ((n - (j + 1) : ℕ) : ℝ) * (expCut n (j + 1) + 1)
      else expCut n j + 1 := by
    rw [integral_expBinMeasure, setIntegral_mul_exp_neg_bin hj]
  have hm2 : ∫ x, x ^ 2 ∂(expBinMeasure n j) =
      if j + 1 < n then
        ((n - j : ℕ) : ℝ) * (expCut n j ^ 2 + 2 * expCut n j + 2) -
          ((n - (j + 1) : ℕ) : ℝ) * (expCut n (j + 1) ^ 2 + 2 * expCut n (j + 1) + 2)
      else expCut n j ^ 2 + 2 * expCut n j + 2 := by
    rw [integral_expBinMeasure, setIntegral_sq_mul_exp_neg_bin hj]
  have hmean_nn : 0 ≤ ∫ x, x ∂(expBinMeasure n j) := by
    rw [integral_expBinMeasure]
    apply mul_nonneg (Nat.cast_nonneg n)
    apply setIntegral_nonneg (measurableSet_expBinSet n j)
    intro x hx
    have hx0 : 0 ≤ x := by
      have ha := expCut_nonneg hj
      unfold expBinSet at hx
      split_ifs at hx
      · exact ha.trans (le_of_lt hx.1)
      · exact ha.trans (le_of_lt hx)
    exact mul_nonneg hx0 (le_of_lt (Real.exp_pos _))
  have ha_ge : (1 : ℚ) ≤ (n : ℚ) / ((n - j : ℕ) : ℚ) := by
    rw [one_le_div (by exact_mod_cast (by omega : 0 < n - j))]
    exact_mod_cast (Nat.sub_le n j)
  have ha_bnd := logBoundsQ_sound ha_ge
  have ha_eq : Real.log (((n : ℚ) / ((n - j : ℕ) : ℚ) : ℚ) : ℝ) = expCut n j := by
    unfold expCut; push_cast; rfl
  rw [ha_eq] at ha_bnd
  have ha_lo0 : (0 : ℝ) ≤ ((logBoundsQ ((n : ℚ) / ((n - j : ℕ) : ℚ))).1 : ℝ) := by exact_mod_cast ha_bnd.1
  have ha_nn : 0 ≤ expCut n j := expCut_nonneg hj
  refine ⟨hmean_nn, ?_, ?_⟩
  · rw [hmean]; unfold expBinMomentsQ
    split_ifs with hlt
    · have hb_ge : (1 : ℚ) ≤ (n : ℚ) / ((n - (j + 1) : ℕ) : ℚ) := by
        rw [one_le_div (by exact_mod_cast (by omega : 0 < n - (j + 1)))]
        exact_mod_cast (Nat.sub_le n (j + 1))
      have hb_bnd := logBoundsQ_sound hb_ge
      have hb_eq : Real.log (((n : ℚ) / ((n - (j + 1) : ℕ) : ℚ) : ℚ) : ℝ) = expCut n (j + 1) := by
        unfold expCut; push_cast; rfl
      rw [hb_eq] at hb_bnd
      have hleft : (0 : ℝ) ≤ ((n - j : ℕ) : ℝ) := Nat.cast_nonneg _
      have hright : (0 : ℝ) ≤ ((n - (j + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      push_cast
      nlinarith [ha_bnd.2.2, hb_bnd.2.1]
    · push_cast; linarith [ha_bnd.2.2]
  · rw [hmean, hm2]; unfold expBinMomentsQ
    split_ifs with hlt
    · simp only [hlt, ↓reduceIte] at hmean
      have hb_ge : (1 : ℚ) ≤ (n : ℚ) / ((n - (j + 1) : ℕ) : ℚ) := by
        rw [one_le_div (by exact_mod_cast (by omega : 0 < n - (j + 1)))]
        exact_mod_cast (Nat.sub_le n (j + 1))
      have hb_bnd := logBoundsQ_sound hb_ge
      have hb_eq : Real.log (((n : ℚ) / ((n - (j + 1) : ℕ) : ℚ) : ℚ) : ℝ) = expCut n (j + 1) := by
        unfold expCut; push_cast; rfl
      rw [hb_eq] at hb_bnd
      have hleft : (0 : ℝ) ≤ ((n - j : ℕ) : ℝ) := Nat.cast_nonneg _
      have hright : (0 : ℝ) ≤ ((n - (j + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      have hb_lo0 : (0 : ℝ) ≤ ((logBoundsQ ((n : ℚ) / ((n - (j + 1) : ℕ) : ℚ))).1 : ℝ) := by exact_mod_cast hb_bnd.1
      have hb_nn : 0 ≤ expCut n (j + 1) := expCut_nonneg hlt
      push_cast
      have hmlo : max (0 : ℝ) (((n - j : ℕ) : ℝ) * ((logBoundsQ ((n : ℚ) / ((n - j : ℕ) : ℚ))).1 + 1) -
          ((n - (j + 1) : ℕ) : ℝ) * ((logBoundsQ ((n : ℚ) / ((n - (j + 1) : ℕ) : ℚ))).2 + 1)) ≤
          ((n - j : ℕ) : ℝ) * (expCut n j + 1) - ((n - (j + 1) : ℕ) : ℝ) * (expCut n (j + 1) + 1) := by
        apply max_le
        · rw [← hmean]; exact hmean_nn
        · nlinarith [ha_bnd.2.1, hb_bnd.2.2]
      have hmlo0 : (0 : ℝ) ≤ max (0 : ℝ) (((n - j : ℕ) : ℝ) * ((logBoundsQ ((n : ℚ) / ((n - j : ℕ) : ℚ))).1 + 1) -
          ((n - (j + 1) : ℕ) : ℝ) * ((logBoundsQ ((n : ℚ) / ((n - (j + 1) : ℕ) : ℚ))).2 + 1)) := le_max_left _ _
      have hsq_a : expCut n j ^ 2 + 2 * expCut n j + 2 ≤
          ((logBoundsQ ((n : ℚ) / ((n - j : ℕ) : ℚ))).2 : ℝ) ^ 2 +
            2 * ((logBoundsQ ((n : ℚ) / ((n - j : ℕ) : ℚ))).2 : ℝ) + 2 := by
        nlinarith [ha_bnd.2.2]
      have hsq_b : ((logBoundsQ ((n : ℚ) / ((n - (j + 1) : ℕ) : ℚ))).1 : ℝ) ^ 2 +
            2 * ((logBoundsQ ((n : ℚ) / ((n - (j + 1) : ℕ) : ℚ))).1 : ℝ) + 2 ≤
          expCut n (j + 1) ^ 2 + 2 * expCut n (j + 1) + 2 := by
        nlinarith [hb_bnd.2.1]
      nlinarith
    · push_cast
      have hmlo : max (0 : ℝ) (((logBoundsQ ((n : ℚ) / ((n - j : ℕ) : ℚ))).1 : ℝ) + 1) ≤ expCut n j + 1 := by
        apply max_le <;> linarith [ha_bnd.2.1]
      have hmlo0 : (0 : ℝ) ≤ max (0 : ℝ) (((logBoundsQ ((n : ℚ) / ((n - j : ℕ) : ℚ))).1 : ℝ) + 1) := le_max_left _ _
      nlinarith [ha_bnd.2.1, ha_bnd.2.2]

/-- Cutpoint scaling identity `expCut (m * n) (m * j) = expCut n j`. -/
lemma expCut_mul (m n j : ℕ) (hm : 0 < m) :
    expCut (m * n) (m * j) = expCut n j := by
  unfold expCut
  have hsub : m * n - m * j = m * (n - j) := (Nat.mul_sub_left_distrib m n j).symm
  rw [hsub]
  push_cast
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [mul_div_mul_left _ _ hmR]

lemma expCut_mono_le {n a b : ℕ} (hab : a ≤ b) (hb : b < n) : expCut n a ≤ expCut n b := by
  have hd : b = a + (b - a) := by omega
  rw [hd]
  generalize hm : b - a = m
  have hlt : a + m < n := by omega
  clear hd hm hab hb
  induction m with
  | zero => simp
  | succ k ih => exact (ih (by omega)).trans (expCut_le_succ (by omega))

/-- Exact 16-way partition of `expBinSet 4 g` into `expBinSet 64 (16 * g + r)`. -/
lemma expBinSet_refine (g : Fin 4) :
    expBinSet 4 g.val = ⋃ r : Fin 16, expBinSet 64 (16 * g.val + r.val) := by
  ext x
  simp only [mem_iUnion]
  have h0 : expCut 64 (16 * g.val) = expCut 4 g.val := expCut_mul 16 4 g.val (by norm_num)
  constructor
  · intro hx
    have hgt : expCut 64 (16 * g.val) < x := by
      rw [h0]; unfold expBinSet at hx; split_ifs at hx <;> [exact hx.1; exact hx]
    have hex : ∃ r : Fin 16, expCut 64 (16 * g.val + r.val) < x := ⟨0, by simpa using hgt⟩
    classical
    let S := Finset.univ.filter fun r : Fin 16 => expCut 64 (16 * g.val + r.val) < x
    have hSne : S.Nonempty := by
      obtain ⟨r, hr⟩ := hex
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
    let rmax := S.max' hSne
    have hrmax_mem : rmax ∈ S := Finset.max'_mem S hSne
    have hrmax_lt : expCut 64 (16 * g.val + rmax.val) < x := (Finset.mem_filter.mp hrmax_mem).2
    refine ⟨rmax, ?_⟩
    unfold expBinSet
    split_ifs with hlt64
    · refine ⟨hrmax_lt, ?_⟩
      by_cases h15 : rmax.val + 1 < 16
      · let rnext : Fin 16 := ⟨rmax.val + 1, h15⟩
        have hnot : rnext ∉ S := fun h => by
          have hle := Finset.le_max' S rnext h
          exact Nat.not_lt_of_ge hle (Nat.lt_succ_self _)
        have hle' : x ≤ expCut 64 (16 * g.val + rnext.val) := by
          by_contra hgt'
          push Not at hgt'
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt'⟩)
        simpa [rnext, Nat.add_assoc] using hle'
      · have hglt : g.val + 1 < 4 := by omega
        have h16eq : 16 * g.val + rmax.val + 1 = 16 * (g.val + 1) := by omega
        rw [h16eq, expCut_mul 16 4 (g.val + 1) (by norm_num)]
        unfold expBinSet at hx
        simp only [hglt, ↓reduceIte] at hx
        exact hx.2
    · exact hrmax_lt
  · rintro ⟨r, hr⟩
    have hmono_lo : expCut 64 (16 * g.val) ≤ expCut 64 (16 * g.val + r.val) :=
      expCut_mono_le (by omega) (by have := g.isLt; have := r.isLt; omega)
    have hgt : expCut 4 g.val < x := by
      rw [← h0]
      unfold expBinSet at hr
      split_ifs at hr
      · exact lt_of_le_of_lt hmono_lo hr.1
      · exact lt_of_le_of_lt hmono_lo hr
    unfold expBinSet
    split_ifs with hlt4
    · refine ⟨hgt, ?_⟩
      have hlt64 : 16 * g.val + r.val + 1 < 64 := by have := r.isLt; omega
      unfold expBinSet at hr
      simp only [hlt64, ↓reduceIte] at hr
      have hmono_hi : expCut 64 (16 * g.val + r.val + 1) ≤ expCut 64 (16 * (g.val + 1)) :=
        expCut_mono_le (by have := r.isLt; omega) (by omega)
      rw [expCut_mul 16 4 (g.val + 1) (by norm_num)] at hmono_hi
      exact hr.2.trans hmono_hi
    · exact hgt

lemma expBinSet_pairwiseDisjoint (g : Fin 4) :
    ((Finset.univ : Finset (Fin 16)) : Set (Fin 16)).Pairwise
      (Function.onFun Disjoint (fun r : Fin 16 => expBinSet 64 (16 * g.val + r.val))) := by
  intro r1 _ r2 _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx1 hx2
  have horder : ∀ a b : Fin 16, a.val < b.val →
      x ∈ expBinSet 64 (16 * g.val + a.val) → x ∈ expBinSet 64 (16 * g.val + b.val) → False := by
    intro a b hab hxa hxb
    have hlta : 16 * g.val + a.val + 1 < 64 := by have := g.isLt; have := b.isLt; omega
    unfold expBinSet at hxa hxb
    simp only [hlta, ↓reduceIte] at hxa
    have hmono : expCut 64 (16 * g.val + a.val + 1) ≤ expCut 64 (16 * g.val + b.val) :=
      expCut_mono_le (by omega) (by have := g.isLt; have := b.isLt; omega)
    have hlt_b : expCut 64 (16 * g.val + b.val) < x := by
      split_ifs at hxb <;> [exact hxb.1; exact hxb]
    linarith [hxa.2]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact horder r1 r2 h hx1 hx2
  · exact horder r2 r1 h hx2 hx1

/-- Exact 16-way refinement of `expBinMeasure 4 g`. -/
theorem integral_expBinMeasure_refine (g : Fin 4) {f : ℝ → ℝ}
    (hf : Integrable f (expBinMeasure 4 g.val)) :
    ∫ x, f x ∂(expBinMeasure 4 g.val) =
      (1 / 16 : ℝ) * ∑ r : Fin 16, ∫ x, f x ∂(expBinMeasure 64 (16 * g.val + r.val)) := by
  have hion : IntegrableOn (fun x => f x * Real.exp (-x)) (expBinSet 4 g.val) volume :=
    (integrable_expBinMeasure_iff g.isLt).mp hf
  rw [integral_expBinMeasure]
  simp_rw [integral_expBinMeasure]
  rw [← Finset.mul_sum]
  have hpart : expBinSet 4 g.val = ⋃ r ∈ (Finset.univ : Finset (Fin 16)), expBinSet 64 (16 * g.val + r.val) := by
    rw [expBinSet_refine g]; simp
  rw [hpart, integral_biUnion_finset Finset.univ
    (fun r _ => measurableSet_expBinSet 64 (16 * g.val + r.val))
    (expBinSet_pairwiseDisjoint g)
    (fun r _ => hion.mono_set (by
      rw [expBinSet_refine g]
      exact Set.subset_iUnion (fun s : Fin 16 => expBinSet 64 (16 * g.val + s.val)) r))]
  ring

/-! ### Height-Bin Uniform Probability Measures -/

def heightBinSet (B : ℕ) (h : ℝ) (b : ℕ) : Set ℝ :=
  Ioc ((b : ℝ) * h / (B : ℝ)) (((b + 1 : ℕ) : ℝ) * h / (B : ℝ))

lemma measurableSet_heightBinSet (B : ℕ) (h : ℝ) (b : ℕ) : MeasurableSet (heightBinSet B h b) :=
  measurableSet_Ioc

noncomputable def heightBinDensityNN (B : ℕ) (h : ℝ) (b : ℕ) (y : ℝ) : ℝ≥0 :=
  (heightBinSet B h b).indicator (fun _ => Real.toNNReal ((B : ℝ) / h)) y

lemma measurable_heightBinDensityNN (B : ℕ) (h : ℝ) (b : ℕ) :
    Measurable (heightBinDensityNN B h b) :=
  measurable_const.indicator (measurableSet_heightBinSet B h b)

noncomputable def heightBinMeasure (B : ℕ) (h : ℝ) (b : ℕ) : Measure ℝ :=
  volume.withDensity fun y => (heightBinDensityNN B h b y : ℝ≥0∞)

lemma heightBinDensityNN_coe {B : ℕ} {h : ℝ} (hh : 0 < h) (b : ℕ) (y : ℝ) :
    ((heightBinDensityNN B h b y : ℝ≥0) : ℝ) =
      (heightBinSet B h b).indicator (fun _ => (B : ℝ) / h) y := by
  unfold heightBinDensityNN
  by_cases hy : y ∈ heightBinSet B h b
  · simp [Set.indicator_of_mem hy, Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg B) (le_of_lt hh))]
  · simp [Set.indicator_of_notMem hy]

lemma isProbabilityMeasure_heightBinMeasure {B : ℕ} {h : ℝ} (hB : 0 < B) (hh : 0 < h) (b : ℕ) :
    IsProbabilityMeasure (heightBinMeasure B h b) := by
  constructor
  unfold heightBinMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfun : (fun y => (heightBinDensityNN B h b y : ℝ≥0∞)) =
      (heightBinSet B h b).indicator (fun _ => ENNReal.ofReal ((B : ℝ) / h)) := by
    funext y; unfold heightBinDensityNN
    by_cases hy : y ∈ heightBinSet B h b
    · simp [Set.indicator_of_mem hy, ENNReal.ofReal]
    · simp [Set.indicator_of_notMem hy]
  rw [hfun, lintegral_indicator (measurableSet_heightBinSet B h b), lintegral_const,
      Measure.restrict_apply_univ, heightBinSet, Real.volume_Ioc]
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hlen : (((b + 1 : ℕ) : ℝ) * h / (B : ℝ)) - ((b : ℝ) * h / (B : ℝ)) = h / (B : ℝ) := by
    push_cast; ring
  rw [hlen, ← ENNReal.ofReal_mul (div_nonneg (le_of_lt hBpos) (le_of_lt hh))]
  have hmul : (B : ℝ) / h * (h / (B : ℝ)) = 1 := by field_simp [ne_of_gt hBpos, ne_of_gt hh]
  rw [hmul, ENNReal.ofReal_one]

lemma integral_heightBinMeasure {B : ℕ} {h : ℝ} (hh : 0 < h) (b : ℕ) (f : ℝ → ℝ) :
    ∫ y, f y ∂(heightBinMeasure B h b) = ((B : ℝ) / h) * ∫ y in heightBinSet B h b, f y := by
  unfold heightBinMeasure
  rw [integral_withDensity_eq_integral_smul (measurable_heightBinDensityNN B h b)]
  have hfun : (fun y => heightBinDensityNN B h b y • f y) =
      (heightBinSet B h b).indicator (fun y => ((B : ℝ) / h) * f y) := by
    funext y
    change ((heightBinDensityNN B h b y : ℝ≥0) : ℝ) * f y = _
    rw [heightBinDensityNN_coe hh]
    by_cases hy : y ∈ heightBinSet B h b
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  rw [hfun, integral_indicator (measurableSet_heightBinSet B h b), integral_const_mul]

lemma integrable_heightBinMeasure_iff {B : ℕ} {h : ℝ} (hB : 0 < B) (hh : 0 < h) (b : ℕ) {f : ℝ → ℝ} :
    Integrable f (heightBinMeasure B h b) ↔ IntegrableOn f (heightBinSet B h b) volume := by
  unfold heightBinMeasure
  have hpos : 0 < (B : ℝ) / h := div_pos (by exact_mod_cast hB) hh
  rw [integrable_withDensity_iff_integrable_smul₀ (measurable_heightBinDensityNN B h b).aemeasurable]
  have hfun : (fun y => heightBinDensityNN B h b y • f y) =
      (heightBinSet B h b).indicator (fun y => ((B : ℝ) / h) * f y) := by
    funext y
    change ((heightBinDensityNN B h b y : ℝ≥0) : ℝ) * f y = _
    rw [heightBinDensityNN_coe hh]
    by_cases hy : y ∈ heightBinSet B h b
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  rw [hfun, integrable_indicator_iff (measurableSet_heightBinSet B h b)]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt hpos)) _

lemma ae_mem_heightBinSet {B : ℕ} {h : ℝ} (b : ℕ) :
    ∀ᵐ y ∂(heightBinMeasure B h b), y ∈ heightBinSet B h b := by
  rw [ae_iff]
  unfold heightBinMeasure
  change (volume.withDensity fun y => (heightBinDensityNN B h b y : ℝ≥0∞)) (heightBinSet B h b)ᶜ = 0
  rw [withDensity_apply _ (measurableSet_heightBinSet B h b).compl]
  rw [lintegral_eq_zero_iff (Measurable.coe_nnreal_ennreal (measurable_heightBinDensityNN B h b))]
  filter_upwards [ae_restrict_mem (measurableSet_heightBinSet B h b).compl] with y hy
  simp [heightBinDensityNN, Set.indicator_of_notMem hy]

/-- Exact 4-way refinement of `heightBinMeasure 6 h b`. -/
theorem integral_heightBinMeasure_refine {h : ℝ} (hh : 0 < h) (b : ℕ) {f : ℝ → ℝ}
    (hf : Integrable f (heightBinMeasure 6 h b)) :
    ∫ y, f y ∂(heightBinMeasure 6 h b) =
      (1 / 4 : ℝ) * ∑ s : Fin 4, ∫ y, f y ∂(heightBinMeasure 24 h (4 * b + s.val)) := by
  have hion : IntegrableOn f (heightBinSet 6 h b) volume :=
    (integrable_heightBinMeasure_iff (by norm_num) hh b).mp hf
  rw [integral_heightBinMeasure hh b]
  simp_rw [integral_heightBinMeasure hh]
  rw [← Finset.mul_sum]
  have hpart : heightBinSet 6 h b =
      ⋃ s ∈ (Finset.univ : Finset (Fin 4)), heightBinSet 24 h (4 * b + s.val) := by
    ext y
    simp only [heightBinSet, mem_iUnion, exists_prop, Finset.mem_univ, true_and, mem_Ioc]
    constructor
    · rintro ⟨hy1, hy2⟩
      by_cases h1 : y ≤ ((4 * b + 1 : ℕ) : ℝ) * h / 24
      · exact ⟨0, by simp only [Fin.val_zero]; push_cast at hy1 ⊢; linarith, by simp only [Fin.val_zero]; simpa using h1⟩
      · by_cases h2 : y ≤ ((4 * b + 2 : ℕ) : ℝ) * h / 24
        · exact ⟨1, by simp only [Fin.val_one]; push_cast at h1 ⊢; linarith, by simp only [Fin.val_one]; push_cast at h2 ⊢; linarith⟩
        · by_cases h3 : y ≤ ((4 * b + 3 : ℕ) : ℝ) * h / 24
          · exact ⟨2, by simp only [Fin.val_two]; push_cast at h2 ⊢; linarith, by simp only [Fin.val_two]; push_cast at h3 ⊢; linarith⟩
          · exact ⟨3, by change ((4 * b + 3 : ℕ) : ℝ) * h / 24 < y; push_cast at h3 ⊢; linarith,
              by change y ≤ ((4 * b + 3 + 1 : ℕ) : ℝ) * h / 24; push_cast at hy2 ⊢; linarith⟩
    · rintro ⟨s, hs1, hs2⟩
      have hs0 : (0 : ℝ) ≤ (s.val : ℝ) := Nat.cast_nonneg _
      have hs3 : (s.val : ℝ) + 1 ≤ 4 := by exact_mod_cast s.isLt
      constructor
      · push_cast at hs1 ⊢; nlinarith
      · push_cast at hs2 ⊢; nlinarith
  have hdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).Pairwise
      (Function.onFun Disjoint (fun s : Fin 4 => heightBinSet 24 h (4 * b + s.val))) := by
    intro s1 _ s2 _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy1 hy2
    simp only [heightBinSet, mem_Ioc] at hy1 hy2
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have hle : (s1.val : ℝ) + 1 ≤ (s2.val : ℝ) := by exact_mod_cast hlt
      push_cast at hy1 hy2; nlinarith
    · have hle : (s2.val : ℝ) + 1 ≤ (s1.val : ℝ) := by exact_mod_cast hlt
      push_cast at hy1 hy2; nlinarith
  rw [hpart, integral_biUnion_finset Finset.univ (fun s _ => measurableSet_heightBinSet 24 h (4 * b + s.val))
    hdisj (fun s _ => hion.mono_set (by
      rw [hpart]
      exact Set.subset_biUnion_of_mem (u := fun s : Fin 4 => heightBinSet 24 h (4 * b + s.val))
        (Finset.mem_univ s)))]
  ring

lemma integrable_heightBin_diff_sq {Ba Bb : ℕ} {h : ℝ} (hBa : 0 < Ba) (hBb : 0 < Bb) (hh : 0 < h)
    (a b : ℕ) :
    Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2)
      ((heightBinMeasure Ba h a).prod (heightBinMeasure Bb h b)) := by
  haveI : IsProbabilityMeasure (heightBinMeasure Ba h a) := isProbabilityMeasure_heightBinMeasure hBa hh a
  haveI : IsProbabilityMeasure (heightBinMeasure Bb h b) := isProbabilityMeasure_heightBinMeasure hBb hh b
  have hcont : Continuous (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) := by fun_prop
  have hcomp : IsCompact (Icc ((a : ℝ) * h / Ba) (((a + 1 : ℕ) : ℝ) * h / Ba) ×ˢ
      Icc ((b : ℝ) * h / Bb) (((b + 1 : ℕ) : ℝ) * h / Bb)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont.continuousOn
  refine Integrable.mono' (integrable_const M) hcont.aestronglyMeasurable ?_
  have hsupp : ∀ᵐ q ∂((heightBinMeasure Ba h a).prod (heightBinMeasure Bb h b)),
      q.1 ∈ heightBinSet Ba h a ∧ q.2 ∈ heightBinSet Bb h b :=
    (Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_mem_heightBinSet a)).and
      (Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (ae_mem_heightBinSet b))
  filter_upwards [hsupp] with q hq
  exact hM q ⟨Ioc_subset_Icc_self hq.1, Ioc_subset_Icc_self hq.2⟩

/-- Exact 2nd moment of `(Y_1 - Y_2)^2` for independent uniform height bins `a, b`. -/
theorem integral_heightBinMeasure_diff_sq {B : ℕ} {h : ℝ} (hB : 0 < B) (hh : 0 < h) (a b : ℕ) :
    ∫ p, (p.1 - p.2) ^ 2 ∂((heightBinMeasure B h a).prod (heightBinMeasure B h b)) =
      (((a : ℝ) - (b : ℝ)) ^ 2 + 1 / 6) * (h / (B : ℝ)) ^ 2 := by
  haveI : IsProbabilityMeasure (heightBinMeasure B h a) := isProbabilityMeasure_heightBinMeasure hB hh a
  haveI : IsProbabilityMeasure (heightBinMeasure B h b) := isProbabilityMeasure_heightBinMeasure hB hh b
  rw [integral_prod _ (integrable_heightBin_diff_sq hB hB hh a b)]
  simp_rw [integral_heightBinMeasure hh]
  set w : ℝ := h / (B : ℝ)
  have hw : 0 < w := div_pos hh (by exact_mod_cast hB)
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hle_a : (a : ℝ) * h / (B : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * h / (B : ℝ) := by
    rw [mul_div_assoc, mul_div_assoc]; push_cast; nlinarith [div_pos hh hBpos]
  have hle_b : (b : ℝ) * h / (B : ℝ) ≤ ((b + 1 : ℕ) : ℝ) * h / (B : ℝ) := by
    rw [mul_div_assoc, mul_div_assoc]; push_cast; nlinarith [div_pos hh hBpos]
  have hinner : ∀ x : ℝ,
      ∫ y in heightBinSet B h b, (x - y) ^ 2 =
        w * ∫ v in (0 : ℝ)..1, (x - ((b : ℝ) * w + w * v)) ^ 2 := by
    intro x
    rw [heightBinSet, ← intervalIntegral.integral_of_le hle_b]
    have hsub := intervalIntegral.integral_comp_mul_add (f := fun y => (x - y) ^ 2)
      (a := (0 : ℝ)) (b := 1) (c := w) (d := (b : ℝ) * w) (ne_of_gt hw)
    have h1 : w * 0 + (b : ℝ) * w = (b : ℝ) * h / (B : ℝ) := by simp [w]; ring
    have h2 : w * 1 + (b : ℝ) * w = ((b + 1 : ℕ) : ℝ) * h / (B : ℝ) := by push_cast; simp [w]; ring
    rw [h1, h2] at hsub
    have hsub' : ∫ v in (0 : ℝ)..1, (x - ((b : ℝ) * w + w * v)) ^ 2 =
        w⁻¹ * ∫ y in (b : ℝ) * h / (B : ℝ)..((b + 1 : ℕ) : ℝ) * h / (B : ℝ), (x - y) ^ 2 := by
      simpa [add_comm] using hsub
    rw [hsub', ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hw), one_mul]
  simp_rw [hinner, integral_const_mul]
  rw [heightBinSet, ← intervalIntegral.integral_of_le hle_a]
  have houter := intervalIntegral.integral_comp_mul_add
    (f := fun x => ∫ v in (0 : ℝ)..1, (x - ((b : ℝ) * w + w * v)) ^ 2)
    (a := (0 : ℝ)) (b := 1) (c := w) (d := (a : ℝ) * w) (ne_of_gt hw)
  have ha1 : w * 0 + (a : ℝ) * w = (a : ℝ) * h / (B : ℝ) := by simp [w]; ring
  have ha2 : w * 1 + (a : ℝ) * w = ((a + 1 : ℕ) : ℝ) * h / (B : ℝ) := by push_cast; simp [w]; ring
  rw [ha1, ha2] at houter
  have houter' : ∫ x in (a : ℝ) * h / (B : ℝ)..((a + 1 : ℕ) : ℝ) * h / (B : ℝ),
        ∫ v in (0 : ℝ)..1, (x - ((b : ℝ) * w + w * v)) ^ 2 =
      w * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (((a : ℝ) * w + w * u) - ((b : ℝ) * w + w * v)) ^ 2 := by
    have := congrArg (w * ·) houter
    simp only [smul_eq_mul] at this
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hw), one_mul] at this
    simpa [add_comm] using this.symm
  rw [houter']
  have hfactor : ∀ u v : ℝ,
      (((a : ℝ) * w + w * u) - ((b : ℝ) * w + w * v)) ^ 2 = w ^ 2 * (((a : ℝ) - (b : ℝ)) + u - v) ^ 2 := by
    intro u v; ring
  simp_rw [hfactor, intervalIntegral.integral_const_mul]
  rw [integral_uniform_diff_sq ((a : ℝ) - (b : ℝ))]
  have hBw : ((B : ℝ) / h) * w = 1 := by simp [w]; field_simp [ne_of_gt hBpos, ne_of_gt hh]
  calc (B : ℝ) / h * ((B : ℝ) / h * (w * (w * (w ^ 2 * (((a : ℝ) - (b : ℝ)) ^ 2 + 1 / 6)))))
      = (((B : ℝ) / h * w) * ((B : ℝ) / h * w)) * ((((a : ℝ) - (b : ℝ)) ^ 2 + 1 / 6) * w ^ 2) := by ring
    _ = (((a : ℝ) - (b : ℝ)) ^ 2 + 1 / 6) * w ^ 2 := by rw [hBw]; ring

/-! ## Section 3: Independent Sum Variance & Coordinate Refinement on `Measure.pi` -/

lemma integral_comp_measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {φ : α → β} (hmp : MeasurePreserving φ μ ν)
    {f : β → ℝ} (hf : AEStronglyMeasurable f ν) :
    ∫ a, f (φ a) ∂μ = ∫ b, f b ∂ν := by
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (hmp.map_eq.symm ▸ hf)]

lemma integrable_comp_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {φ : α → β} (hmp : MeasurePreserving φ μ ν)
    {f : β → ℝ} (hf : Integrable f ν) :
    Integrable (fun a => f (φ a)) μ :=
  hmp.integrable_comp_of_integrable hf

lemma integral_pi_coord {k : ℕ} (μs : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (i : Fin k) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (μs i)) :
    ∫ xs, f (xs i) ∂(Measure.pi μs) = ∫ x, f x ∂(μs i) :=
  integral_comp_measurePreserving (measurePreserving_eval μs i) hf

lemma integrable_pi_coord {k : ℕ} (μs : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (i : Fin k) {f : ℝ → ℝ} (hf : Integrable f (μs i)) :
    Integrable (fun xs : Fin k → ℝ => f (xs i)) (Measure.pi μs) :=
  integrable_comp_mp (measurePreserving_eval μs i) hf

lemma integral_pi_mul_distinct {k : ℕ} (μs : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    {i j : Fin k} (hij : i ≠ j) {f g : ℝ → ℝ} (hf : Integrable f (μs i)) (hg : Integrable g (μs j)) :
    ∫ xs, f (xs i) * g (xs j) ∂(Measure.pi μs) = (∫ x, f x ∂(μs i)) * (∫ y, g y ∂(μs j)) := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k' =>
    have hmp := measurePreserving_piFinSuccAbove μs i
    obtain ⟨j', rfl⟩ : ∃ j' : Fin k', i.succAbove j' = j := Fin.exists_succAbove_eq hij.symm
    have hg' : Integrable (fun ys : Fin k' → ℝ => g (ys j')) (Measure.pi fun l => μs (i.succAbove l)) :=
      integrable_pi_coord (fun l => μs (i.succAbove l)) j' hg
    have hprod : Integrable (fun p : ℝ × (Fin k' → ℝ) => f p.1 * g (p.2 j'))
        ((μs i).prod (Measure.pi fun l => μs (i.succAbove l))) := hf.mul_prod hg'
    have hcomp : ∫ xs, f (xs i) * g (xs (i.succAbove j')) ∂(Measure.pi μs) =
        ∫ p : ℝ × (Fin k' → ℝ), f p.1 * g (p.2 j') ∂((μs i).prod (Measure.pi fun l => μs (i.succAbove l))) :=
      integral_comp_measurePreserving hmp hprod.aestronglyMeasurable
    rw [hcomp, integral_prod_mul f (fun ys : Fin k' → ℝ => g (ys j')),
        integral_pi_coord (fun l => μs (i.succAbove l)) j' hg.aestronglyMeasurable]

lemma integrable_pi_mul_distinct {k : ℕ} (μs : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    {i j : Fin k} (hij : i ≠ j) {f g : ℝ → ℝ} (hf : Integrable f (μs i)) (hg : Integrable g (μs j)) :
    Integrable (fun xs : Fin k → ℝ => f (xs i) * g (xs j)) (Measure.pi μs) := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k' =>
    have hmp := measurePreserving_piFinSuccAbove μs i
    obtain ⟨j', rfl⟩ : ∃ j' : Fin k', i.succAbove j' = j := Fin.exists_succAbove_eq hij.symm
    have hg' : Integrable (fun ys : Fin k' → ℝ => g (ys j')) (Measure.pi fun l => μs (i.succAbove l)) :=
      integrable_pi_coord (fun l => μs (i.succAbove l)) j' hg
    have hprod : Integrable (fun p : ℝ × (Fin k' → ℝ) => f p.1 * g (p.2 j'))
        ((μs i).prod (Measure.pi fun l => μs (i.succAbove l))) := hf.mul_prod hg'
    exact integrable_comp_mp hmp hprod

/-- Exact 2nd moment of a sum of independent real variables: `(∑ μ_i)^2 + ∑ Var_i`. -/
theorem integral_pi_sum_sq {k : ℕ} (μs : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (h1 : ∀ i, Integrable (fun x : ℝ => x) (μs i))
    (h2 : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μs i)) :
    Integrable (fun xs : Fin k → ℝ => (∑ i : Fin k, xs i) ^ 2) (Measure.pi μs) ∧
    ∫ xs, (∑ i : Fin k, xs i) ^ 2 ∂(Measure.pi μs) =
      (∑ i : Fin k, ∫ x, x ∂(μs i)) ^ 2 +
        ∑ i : Fin k, ((∫ x, x ^ 2 ∂(μs i)) - (∫ x, x ∂(μs i)) ^ 2) := by
  have hexpand : ∀ xs : Fin k → ℝ,
      (∑ i : Fin k, xs i) ^ 2 = ∑ i : Fin k, ∑ j : Fin k, xs i * xs j := by
    intro xs; rw [sq, Finset.sum_mul_sum]
  have hint_ij : ∀ i j : Fin k, Integrable (fun xs : Fin k → ℝ => xs i * xs j) (Measure.pi μs) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simpa [sq] using integrable_pi_coord μs i (h2 i)
    · exact integrable_pi_mul_distinct μs hij (h1 i) (h1 j)
  have hint_all : Integrable (fun xs : Fin k → ℝ => (∑ i : Fin k, xs i) ^ 2) (Measure.pi μs) := by
    simp_rw [hexpand]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_ij i j
  refine ⟨hint_all, ?_⟩
  simp_rw [hexpand]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_ij i j]
  have hterm : ∀ i : Fin k,
      ∫ xs, ∑ j : Fin k, xs i * xs j ∂(Measure.pi μs) =
        ∑ j : Fin k, if i = j then ∫ x, x ^ 2 ∂(μs i)
          else (∫ x, x ∂(μs i)) * (∫ y, y ∂(μs j)) := by
    intro i
    rw [integral_finsetSum _ fun j _ => hint_ij i j]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · subst hij
      have hsq := integral_pi_coord μs i (h2 i).aestronglyMeasurable
      simpa [sq] using hsq
    · exact integral_pi_mul_distinct μs hij (h1 i) (h1 j)
  simp_rw [hterm]
  have hsplit : ∀ i : Fin k,
      (∑ j : Fin k, if i = j then ∫ x, x ^ 2 ∂(μs i) else (∫ x, x ∂(μs i)) * (∫ y, y ∂(μs j))) =
        (∑ j : Fin k, (∫ x, x ∂(μs i)) * (∫ y, y ∂(μs j))) +
          ((∫ x, x ^ 2 ∂(μs i)) - (∫ x, x ∂(μs i)) ^ 2) := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase Finset.univ (fun j => (∫ x, x ∂(μs i)) * (∫ y, y ∂(μs j))) (Finset.mem_univ i)]
    simp only [↓reduceIte]
    have hrest : ∑ j ∈ Finset.univ.erase i, (if i = j then ∫ x, x ^ 2 ∂(μs i)
          else (∫ x, x ∂(μs i)) * (∫ y, y ∂(μs j))) =
        ∑ j ∈ Finset.univ.erase i, (∫ x, x ∂(μs i)) * (∫ y, y ∂(μs j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj).symm]
    rw [hrest]; ring
  simp_rw [hsplit, Finset.sum_add_distrib]

/-- Refining a single coordinate `imax` of `Measure.pi` into 16 sub-bins. -/
theorem integral_pi_refine_coord {k : ℕ} (gs : Fin (k + 1) → Fin 4) (imax : Fin (k + 1))
    {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
    {f : ((Fin (k + 1) → ℝ) × (ℝ × ℝ)) → ℝ}
    (hf : Integrable f ((Measure.pi fun i => expBinMeasure 4 (gs i).val).prod ν)) :
    ∫ p, f p ∂((Measure.pi fun i => expBinMeasure 4 (gs i).val).prod ν) =
      (1 / 16 : ℝ) * ∑ r : Fin 16,
        ∫ p, f p ∂((Measure.pi fun i =>
          if i = imax then expBinMeasure 64 (16 * (gs imax).val + r.val)
          else expBinMeasure 4 (gs i).val).prod ν) := by
  haveI : ∀ i, IsProbabilityMeasure (expBinMeasure 4 (gs i).val) :=
    fun i => isProbabilityMeasure_expBinMeasure (gs i).isLt
  haveI : ∀ (r : Fin 16) (i : Fin (k + 1)),
      IsProbabilityMeasure (if i = imax then expBinMeasure 64 (16 * (gs imax).val + r.val)
        else expBinMeasure 4 (gs i).val) := by
    intro r i; split_ifs
    · exact isProbabilityMeasure_expBinMeasure (by have := (gs imax).isLt; have := r.isLt; omega)
    · exact isProbabilityMeasure_expBinMeasure (gs i).isLt
  let restMeas : Measure (Fin k → ℝ) := Measure.pi fun l => expBinMeasure 4 (gs (imax.succAbove l)).val
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) imax
  let E : ((Fin (k + 1) → ℝ) × (ℝ × ℝ)) ≃ᵐ (ℝ × ((Fin k → ℝ) × (ℝ × ℝ))) :=
    (e.prodCongr (MeasurableEquiv.refl (ℝ × ℝ))).trans MeasurableEquiv.prodAssoc
  have hmp_base : MeasurePreserving E
      ((Measure.pi fun i => expBinMeasure 4 (gs i).val).prod ν)
      ((expBinMeasure 4 (gs imax).val).prod (restMeas.prod ν)) := by
    have h1 := (measurePreserving_piFinSuccAbove (fun i => expBinMeasure 4 (gs i).val) imax).prod
      (MeasurePreserving.id ν)
    have h2 := measurePreserving_prodAssoc (expBinMeasure 4 (gs imax).val) restMeas ν
    exact h2.comp h1
  have hsymm_base : MeasurePreserving E.symm
      ((expBinMeasure 4 (gs imax).val).prod (restMeas.prod ν))
      ((Measure.pi fun i => expBinMeasure 4 (gs i).val).prod ν) := hmp_base.symm E
  have hfφ : Integrable (fun q => f (E.symm q)) ((expBinMeasure 4 (gs imax).val).prod (restMeas.prod ν)) :=
    integrable_comp_mp hsymm_base hf
  have hlhs : ∫ p, f p ∂((Measure.pi fun i => expBinMeasure 4 (gs i).val).prod ν) =
      ∫ x, (∫ y, f (E.symm (x, y)) ∂(restMeas.prod ν)) ∂(expBinMeasure 4 (gs imax).val) := by
    rw [← integral_prod (fun q => f (E.symm q)) hfφ]
    rw [← integral_comp_measurePreserving hmp_base hfφ.aestronglyMeasurable]
    congr 1; funext p; simp
  rw [hlhs, integral_expBinMeasure_refine (gs imax) hfφ.integral_prod_left]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  let μr : Fin (k + 1) → Measure ℝ := fun i =>
    if i = imax then expBinMeasure 64 (16 * (gs imax).val + r.val)
    else expBinMeasure 4 (gs i).val
  have hrest_eq : (Measure.pi fun l : Fin k => μr (imax.succAbove l)) = restMeas := by
    congr 1; funext l; simp [μr, Fin.succAbove_ne]
  have himax_eq : μr imax = expBinMeasure 64 (16 * (gs imax).val + r.val) := by simp [μr]
  have hmp_r : MeasurePreserving E ((Measure.pi μr).prod ν)
      ((expBinMeasure 64 (16 * (gs imax).val + r.val)).prod (restMeas.prod ν)) := by
    have h1 := (measurePreserving_piFinSuccAbove μr imax).prod (MeasurePreserving.id ν)
    rw [himax_eq, hrest_eq] at h1
    exact (measurePreserving_prodAssoc _ _ _).comp h1
  haveI : IsProbabilityMeasure (expBinMeasure 64 (16 * (gs imax).val + r.val)) :=
    isProbabilityMeasure_expBinMeasure (by have := (gs imax).isLt; have := r.isLt; omega)
  have hfr : Integrable (fun q => f (E.symm q))
      ((expBinMeasure 64 (16 * (gs imax).val + r.val)).prod (restMeas.prod ν)) := by
    have hle : expBinMeasure 64 (16 * (gs imax).val + r.val) ≤ (16 : ℝ≥0∞) • expBinMeasure 4 (gs imax).val := by
      refine Measure.le_iff.mpr fun s hs => ?_
      simp only [Measure.smul_apply, smul_eq_mul, expBinMeasure, withDensity_apply _ hs]
      rw [← lintegral_const_mul' (16 : ℝ≥0∞) _ (by simp)]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ expBinSet 64 (16 * (gs imax).val + r.val)
      · have hx4 : x ∈ expBinSet 4 (gs imax).val := by
          rw [expBinSet_refine (gs imax)]
          exact Set.mem_iUnion.mpr ⟨r, hx⟩
        simp only [expBinDensityNN, Set.indicator_of_mem hx, Set.indicator_of_mem hx4]
        have h16 : (16 : ℝ≥0∞) = ((16 : ℝ≥0) : ℝ≥0∞) := rfl
        rw [h16, ← ENNReal.coe_mul]
        apply ENNReal.coe_le_coe.mpr
        rw [← NNReal.coe_le_coe]
        push_cast
        rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
        linarith
      · simp [expBinDensityNN, Set.indicator_of_notMem hx]
    have hprod_le : (expBinMeasure 64 (16 * (gs imax).val + r.val)).prod (restMeas.prod ν) ≤
        (16 : ℝ≥0∞) • ((expBinMeasure 4 (gs imax).val).prod (restMeas.prod ν)) := by
      refine Measure.le_iff.mpr fun s hs => ?_
      rw [Measure.prod_apply hs, Measure.smul_apply, Measure.prod_apply hs, smul_eq_mul]
      calc ∫⁻ x, (restMeas.prod ν) (Prod.mk x ⁻¹' s) ∂(expBinMeasure 64 (16 * (gs imax).val + r.val))
          ≤ ∫⁻ x, (restMeas.prod ν) (Prod.mk x ⁻¹' s) ∂((16 : ℝ≥0∞) • expBinMeasure 4 (gs imax).val) :=
            lintegral_mono' hle le_rfl
        _ = 16 * ∫⁻ x, (restMeas.prod ν) (Prod.mk x ⁻¹' s) ∂(expBinMeasure 4 (gs imax).val) := by
            rw [lintegral_smul_measure, smul_eq_mul]
    exact (hfφ.smul_measure (by simp : (16 : ℝ≥0∞) ≠ ⊤)).mono_measure hprod_le
  rw [← integral_prod (fun q => f (E.symm q)) hfr,
      ← integral_comp_measurePreserving hmp_r hfr.aestronglyMeasurable]
  congr 1; funext p; simp

/-! ## Section 4: Exact Integer Certificate Verification for `costFlat1..4` -/

def momentScale : ℕ := 10 ^ 12

private lemma momentScale_pos : 0 < momentScale := by decide

def ceilQNat (q : ℚ) : ℕ :=
  let num := q.num * (momentScale : ℤ)
  let den := (q.den : ℤ)
  if num ≤ 0 then 0 else ((num + den - 1) / den).toNat

lemma le_ceilQNat (q : ℚ) : (q : ℝ) ≤ (ceilQNat q : ℝ) / (momentScale : ℝ) := by
  unfold ceilQNat
  dsimp only
  have hM : (0 : ℝ) < (momentScale : ℝ) := by exact_mod_cast momentScale_pos
  have hMZ : (0 : ℤ) < (momentScale : ℤ) := by exact_mod_cast momentScale_pos
  have hden : (0 : ℤ) < (q.den : ℤ) := Int.natCast_pos.mpr q.pos
  have hdenR : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  rw [Rat.cast_def]
  split_ifs with hle
  · have hq0 : (q.num : ℝ) ≤ 0 := by
      have : q.num ≤ 0 := by nlinarith
      exact_mod_cast this
    simp only [Nat.cast_zero, zero_div]
    exact div_nonpos_of_nonpos_of_nonneg hq0 (le_of_lt hdenR)
  · push Not at hle
    have hnonneg : 0 ≤ (q.num * (momentScale : ℤ) + (q.den : ℤ) - 1) / (q.den : ℤ) :=
      Int.ediv_nonneg (by omega) (le_of_lt hden)
    have hceil : q.num * (momentScale : ℤ) ≤
        ((q.num * (momentScale : ℤ) + (q.den : ℤ) - 1) / (q.den : ℤ)) * (q.den : ℤ) := by
      set A : ℤ := q.num * (momentScale : ℤ)
      set D : ℤ := (q.den : ℤ)
      have hdm := Int.mul_ediv_add_emod (A + D - 1) D
      have hmlt := Int.emod_lt_of_pos (A + D - 1) hden
      have hm0 := Int.emod_nonneg (A + D - 1) (ne_of_gt hden)
      nlinarith
    have htoNat : (((q.num * (momentScale : ℤ) + (q.den : ℤ) - 1) / (q.den : ℤ)).toNat : ℤ) =
        (q.num * (momentScale : ℤ) + (q.den : ℤ) - 1) / (q.den : ℤ) := Int.toNat_of_nonneg hnonneg
    have hceilR : (q.num : ℝ) * (momentScale : ℝ) ≤
        ((((q.num * (momentScale : ℤ) + (q.den : ℤ) - 1) / (q.den : ℤ)).toNat : ℕ) : ℝ) * (q.den : ℝ) := by
      rw [← htoNat] at hceil
      exact_mod_cast hceil
    rw [div_le_div_iff₀ hdenR hM]
    linarith

def coarseMomInt : Array (ℕ × ℕ) :=
  (List.range 4).toArray.map fun j =>
    let p := expBinMomentsQ 4 j
    (ceilQNat p.1, ceilQNat p.2)

def fineMomInt : Array (ℕ × ℕ) :=
  (List.range 64).toArray.map fun j =>
    let p := expBinMomentsQ 64 j
    (ceilQNat p.1, ceilQNat p.2)

/-- Integer ceiling of `√(target / D)`. -/
def ceilSqrtDiv (target D : ℕ) : ℕ :=
  let q := (target + D - 1) / D
  let r := Nat.sqrt q
  if r * r < q then r + 1 else r

lemma sqrt_div_le_ceilSqrtDiv (target D : ℕ) (hD : 0 < D) :
    Real.sqrt ((target : ℝ) / (D : ℝ)) ≤ (ceilSqrtDiv target D : ℝ) := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [Real.sqrt_le_left (Nat.cast_nonneg _), div_le_iff₀ hDR]
  unfold ceilSqrtDiv
  set q := (target + D - 1) / D
  have hq : target ≤ q * D := by
    have hdm := Nat.div_add_mod (target + D - 1) D
    have hm := Nat.mod_lt (target + D - 1) hD
    have h1 : D * q + (target + D - 1) % D = target + D - 1 := hdm
    have h2 : target + D - 1 + 1 = target + D := by omega
    nlinarith
  have hr : q ≤ (if Nat.sqrt q * Nat.sqrt q < q then Nat.sqrt q + 1 else Nat.sqrt q) ^ 2 := by
    split_ifs with hlt
    · have := Nat.lt_succ_sqrt q; nlinarith
    · push Not at hlt; nlinarith
  have hnat : target ≤ (if Nat.sqrt q * Nat.sqrt q < q then Nat.sqrt q + 1 else Nat.sqrt q) ^ 2 * D :=
    hq.trans (Nat.mul_le_mul_right D hr)
  exact_mod_cast hnat

def costDenom : ℕ := 121 * 86400 * momentScale * momentScale

def certCellWith (fArr : Array (ℕ × ℕ)) (sm sv c dy r s1 s2 : ℕ) : ℕ :=
  let fm := (fArr[16 * c + r]!).1
  let fv := (fArr[16 * c + r]!).2
  let ex_num := ((sm + fm) * (sm + fm) + (sv + fv) * momentScale) * 25
  let diff : ℕ := if dy * 4 + s1 ≥ s2 then dy * 4 + s1 - s2 else s2 - (dy * 4 + s1)
  let ey_term := (diff * diff * 6 + 1) * 121 * 121 * momentScale * momentScale
  let num := ex_num * 86400 + ey_term
  ceilSqrtDiv (num * (costScale * costScale)) costDenom

def certCostBoundWith (fArr : Array (ℕ × ℕ)) (sm sv c dy : ℕ) : ℕ :=
  let total := (List.range 16).foldl (fun acc r =>
    (List.range 4).foldl (fun acc1 s1 =>
      (List.range 4).foldl (fun acc2 s2 =>
        acc2 + certCellWith fArr sm sv c dy r s1 s2) acc1) acc) 0
  (total + 255) / 256

/-- Certifies a single `(gs, dy, tableVal)` entry with largest gap index `imax`. -/
def certCostBound (sm sv c dy : ℕ) : ℕ := certCostBoundWith fineMomInt sm sv c dy

def checkCostFlat1 : Bool :=
  (List.finRange 4).all fun g0 =>
    (List.finRange 6).all fun dy =>
      decide ((certCostBound 0 0 g0.val dy.val : ℤ) ≤ costFlat1[g0.val * 6 + dy.val]!)

def checkCostFlat2 : Bool :=
  (List.finRange 4).all fun g0 =>
    (List.finRange 4).all fun g1 =>
      let c := max g0.val g1.val
      let o := min g0.val g1.val
      let sm := (coarseMomInt[o]!).1
      let sv := (coarseMomInt[o]!).2
      (List.finRange 6).all fun dy =>
        decide ((certCostBound sm sv c dy.val : ℤ) ≤ costFlat2[(g0.val * 4 + g1.val) * 6 + dy.val]!)

def checkCostFlat3 : Bool :=
  (List.finRange 4).all fun g0 =>
    (List.finRange 4).all fun g1 =>
      (List.finRange 4).all fun g2 =>
        let c := max g0.val (max g1.val g2.val)
        let sm := (coarseMomInt[g0.val]!).1 + (coarseMomInt[g1.val]!).1 + (coarseMomInt[g2.val]!).1 - (coarseMomInt[c]!).1
        let sv := (coarseMomInt[g0.val]!).2 + (coarseMomInt[g1.val]!).2 + (coarseMomInt[g2.val]!).2 - (coarseMomInt[c]!).2
        (List.finRange 6).all fun dy =>
          decide ((certCostBound sm sv c dy.val : ℤ) ≤
            costFlat3[((g0.val * 4 + g1.val) * 4 + g2.val) * 6 + dy.val]!)

def checkCostFlat4 : Bool :=
  (List.finRange 4).all fun g0 =>
    (List.finRange 4).all fun g1 =>
      (List.finRange 4).all fun g2 =>
        (List.finRange 4).all fun g3 =>
          let c := max (max g0.val g1.val) (max g2.val g3.val)
          let sm := (coarseMomInt[g0.val]!).1 + (coarseMomInt[g1.val]!).1 +
              (coarseMomInt[g2.val]!).1 + (coarseMomInt[g3.val]!).1 - (coarseMomInt[c]!).1
          let sv := (coarseMomInt[g0.val]!).2 + (coarseMomInt[g1.val]!).2 +
              (coarseMomInt[g2.val]!).2 + (coarseMomInt[g3.val]!).2 - (coarseMomInt[c]!).2
          (List.finRange 6).all fun dy =>
            decide ((certCostBound sm sv c dy.val : ℤ) ≤
              costFlat4[(((g0.val * 4 + g1.val) * 4 + g2.val) * 4 + g3.val) * 6 + dy.val]!)

theorem costFlat1_checked : checkCostFlat1 = true := by native_decide
theorem costFlat2_checked : checkCostFlat2 = true := by native_decide
theorem costFlat3_checked : checkCostFlat3 = true := by native_decide
theorem costFlat4_checked : checkCostFlat4 = true := by native_decide

/-! ## Section 5: Conditional Expectation Bound `edgeCost4_sound` -/

private lemma foldl_add_range (n : ℕ) (f : ℕ → ℕ) (init : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) init = init + ∑ i : Fin n, f i.val := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, Fin.sum_univ_castSucc]
    simp [Nat.add_assoc]

private lemma certCostBoundWith_eq_sum (fArr : Array (ℕ × ℕ)) (sm sv c dy : ℕ) :
    certCostBoundWith fArr sm sv c dy =
      ((∑ r : Fin 16, ∑ s1 : Fin 4, ∑ s2 : Fin 4,
          certCellWith fArr sm sv c dy r.val s1.val s2.val) + 255) / 256 := by
  unfold certCostBoundWith
  dsimp only
  apply congrArg (fun t => (t + 255) / 256)
  have h1 : ∀ (r s1 acc1 : ℕ),
      (List.range 4).foldl (fun acc2 s2 => acc2 + certCellWith fArr sm sv c dy r s1 s2) acc1 =
        acc1 + ∑ s2 : Fin 4, certCellWith fArr sm sv c dy r s1 s2.val :=
    fun r s1 acc1 => foldl_add_range 4 _ acc1
  have h2 : ∀ (r acc : ℕ),
      (List.range 4).foldl (fun acc1 s1 =>
        (List.range 4).foldl (fun acc2 s2 => acc2 + certCellWith fArr sm sv c dy r s1 s2) acc1) acc =
        acc + ∑ s1 : Fin 4, ∑ s2 : Fin 4, certCellWith fArr sm sv c dy r s1.val s2.val := by
    intro r acc
    simp_rw [h1]
    exact foldl_add_range 4 _ acc
  simp_rw [h2]
  simpa using foldl_add_range 16 _ 0

private lemma coarseMomInt_ge {g : Fin 4} :
    0 ≤ ∫ x, x ∂(expBinMeasure 4 g.val) ∧
    ∫ x, x ∂(expBinMeasure 4 g.val) ≤ ((coarseMomInt[g.val]!).1 : ℝ) / (momentScale : ℝ) ∧
    (∫ x, x ^ 2 ∂(expBinMeasure 4 g.val)) - (∫ x, x ∂(expBinMeasure 4 g.val)) ^ 2 ≤
      ((coarseMomInt[g.val]!).2 : ℝ) / (momentScale : ℝ) := by
  have h := expBinMeasure_moments_le g.isLt
  have hget : coarseMomInt[g.val]! = (ceilQNat (expBinMomentsQ 4 g.val).1, ceilQNat (expBinMomentsQ 4 g.val).2) := by
    unfold coarseMomInt
    have hsz : g.val < ((List.range 4).toArray.map fun j =>
        let p := expBinMomentsQ 4 j; (ceilQNat p.1, ceilQNat p.2)).size := by simp [g.isLt]
    rw [getElem!_pos _ g.val hsz]
    simp
  rw [hget]
  exact ⟨h.1, h.2.1.trans (le_ceilQNat _), h.2.2.trans (le_ceilQNat _)⟩

private lemma fineMomInt_ge {j : ℕ} (hj : j < 64) :
    0 ≤ ∫ x, x ∂(expBinMeasure 64 j) ∧
    ∫ x, x ∂(expBinMeasure 64 j) ≤ ((fineMomInt[j]!).1 : ℝ) / (momentScale : ℝ) ∧
    (∫ x, x ^ 2 ∂(expBinMeasure 64 j)) - (∫ x, x ∂(expBinMeasure 64 j)) ^ 2 ≤
      ((fineMomInt[j]!).2 : ℝ) / (momentScale : ℝ) := by
  have h := expBinMeasure_moments_le hj
  have hget : fineMomInt[j]! = (ceilQNat (expBinMomentsQ 64 j).1, ceilQNat (expBinMomentsQ 64 j).2) := by
    unfold fineMomInt
    have hsz : j < ((List.range 64).toArray.map fun j =>
        let p := expBinMomentsQ 64 j; (ceilQNat p.1, ceilQNat p.2)).size := by simp [hj]
    rw [getElem!_pos _ j hsz]
    simp
  rw [hget]
  exact ⟨h.1, h.2.1.trans (le_ceilQNat _), h.2.2.trans (le_ceilQNat _)⟩

private lemma diff_sq_eq (ya yb : Fin 6) (s1 s2 : Fin 4) :
    let dy := if ya.val ≤ yb.val then yb.val - ya.val else ya.val - yb.val
    let s1' := if ya.val ≤ yb.val then s2 else s1
    let s2' := if ya.val ≤ yb.val then s1 else s2
    let diff : ℕ := if dy * 4 + s1'.val ≥ s2'.val then dy * 4 + s1'.val - s2'.val else s2'.val - (dy * 4 + s1'.val)
    ((((4 * ya.val + s1.val : ℕ) : ℝ) - ((4 * yb.val + s2.val : ℕ) : ℝ)) ^ 2) = (diff : ℝ) ^ 2 := by
  intro dy s1' s2' diff
  have hZ : (((4 * ya.val + s1.val : ℕ) : ℤ) - ((4 * yb.val + s2.val : ℕ) : ℤ)) ^ 2 = (diff : ℤ) ^ 2 := by
    dsimp only [diff, s1', s2', dy]
    split_ifs with h1 h2 h3
    · have hsub1 : ((yb.val - ya.val : ℕ) : ℤ) = (yb.val : ℤ) - (ya.val : ℤ) := Nat.cast_sub h1
      have hsub2 : (((yb.val - ya.val) * 4 + s2.val - s1.val : ℕ) : ℤ) =
          (((yb.val - ya.val) * 4 + s2.val : ℕ) : ℤ) - (s1.val : ℤ) := Nat.cast_sub h2
      rw [hsub2]; push_cast; rw [hsub1]; ring
    · have hsub1 : ((yb.val - ya.val : ℕ) : ℤ) = (yb.val : ℤ) - (ya.val : ℤ) := Nat.cast_sub h1
      have hsub2 : ((s1.val - ((yb.val - ya.val) * 4 + s2.val) : ℕ) : ℤ) =
          (s1.val : ℤ) - (((yb.val - ya.val) * 4 + s2.val : ℕ) : ℤ) := Nat.cast_sub (by omega)
      rw [hsub2]; push_cast; rw [hsub1]; ring
    · have hsub1 : ((ya.val - yb.val : ℕ) : ℤ) = (ya.val : ℤ) - (yb.val : ℤ) := Nat.cast_sub (by omega)
      have hsub2 : (((ya.val - yb.val) * 4 + s1.val - s2.val : ℕ) : ℤ) =
          (((ya.val - yb.val) * 4 + s1.val : ℕ) : ℤ) - (s2.val : ℤ) := Nat.cast_sub h3
      rw [hsub2]; push_cast; rw [hsub1]; ring
    · have hsub1 : ((ya.val - yb.val : ℕ) : ℤ) = (ya.val : ℤ) - (yb.val : ℤ) := Nat.cast_sub (by omega)
      have hsub2 : ((s2.val - ((ya.val - yb.val) * 4 + s1.val) : ℕ) : ℤ) =
          (s2.val : ℤ) - (((ya.val - yb.val) * 4 + s1.val : ℕ) : ℤ) := Nat.cast_sub (by omega)
      rw [hsub2]; push_cast; rw [hsub1]; ring
  exact_mod_cast hZ

private lemma subcell_alg_identity (M sm fm sv fv diff : ℕ) (hM : (0 : ℝ) < (M : ℝ)) :
    ((((sm + fm : ℕ) : ℝ) / (M : ℝ)) ^ 2 + ((sv + fv : ℕ) : ℝ) / (M : ℝ)) / (11 / 5 : ℝ) ^ 2 +
      ((diff : ℝ) ^ 2 + 1 / 6) * ((11 / 5 : ℝ) / 24) ^ 2 =
    (((((sm + fm) * (sm + fm) + (sv + fv) * M) * 25) * 86400 +
        (diff * diff * 6 + 1) * 121 * 121 * M * M : ℕ) : ℝ) /
      ((121 * 86400 * M * M : ℕ) : ℝ) := by
  push_cast
  field_simp [ne_of_gt hM]
  ring

private lemma edgeBin_integrable_gen {k : ℕ} (μs : Fin (k + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] (Ba Bb a b : ℕ) (hBa : 0 < Ba) (hBb : 0 < Bb)
    (h1 : ∀ i, Integrable (fun x : ℝ => x) (μs i))
    (h2 : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μs i)) :
    let Z : ((Fin (k + 1) → ℝ) × (ℝ × ℝ)) → ℝ :=
      fun p => ((∑ i : Fin (k + 1), p.1 i) / (11 / 5 : ℝ)) ^ 2 + (p.2.1 - p.2.2) ^ 2
    Integrable Z ((Measure.pi μs).prod
      ((heightBinMeasure Ba (11 / 5) a).prod (heightBinMeasure Bb (11 / 5) b))) ∧
    Integrable (fun p => Real.sqrt (Z p)) ((Measure.pi μs).prod
      ((heightBinMeasure Ba (11 / 5) a).prod (heightBinMeasure Bb (11 / 5) b))) := by
  intro Z
  have hh : (0 : ℝ) < 11 / 5 := by norm_num
  haveI : IsProbabilityMeasure (heightBinMeasure Ba (11 / 5) a) :=
    isProbabilityMeasure_heightBinMeasure hBa hh a
  haveI : IsProbabilityMeasure (heightBinMeasure Bb (11 / 5) b) :=
    isProbabilityMeasure_heightBinMeasure hBb hh b
  have hZ1 : Integrable (fun p : (Fin (k + 1) → ℝ) × (ℝ × ℝ) =>
      ((∑ i : Fin (k + 1), p.1 i) / (11 / 5 : ℝ)) ^ 2)
      ((Measure.pi μs).prod ((heightBinMeasure Ba (11 / 5) a).prod (heightBinMeasure Bb (11 / 5) b))) := by
    have hsq := (integral_pi_sum_sq μs h1 h2).1
    have hdiv : Integrable (fun xs : Fin (k + 1) → ℝ =>
        ((∑ i : Fin (k + 1), xs i) / (11 / 5 : ℝ)) ^ 2) (Measure.pi μs) := by
      have : (fun xs : Fin (k + 1) → ℝ => ((∑ i : Fin (k + 1), xs i) / (11 / 5 : ℝ)) ^ 2) =
          fun xs => (∑ i : Fin (k + 1), xs i) ^ 2 / (11 / 5 : ℝ) ^ 2 := by funext xs; ring
      rw [this]; exact hsq.div_const _
    exact integrable_comp_mp measurePreserving_fst hdiv
  have hZ2 : Integrable (fun p : (Fin (k + 1) → ℝ) × (ℝ × ℝ) => (p.2.1 - p.2.2) ^ 2)
      ((Measure.pi μs).prod ((heightBinMeasure Ba (11 / 5) a).prod (heightBinMeasure Bb (11 / 5) b))) :=
    integrable_comp_mp measurePreserving_snd (integrable_heightBin_diff_sq hBa hBb hh a b)
  have hZ : Integrable Z ((Measure.pi μs).prod
      ((heightBinMeasure Ba (11 / 5) a).prod (heightBinMeasure Bb (11 / 5) b))) := hZ1.add hZ2
  refine ⟨hZ, ?_⟩
  have hZcont : Continuous Z := by unfold Z; fun_prop
  refine Integrable.mono' (hZ.add (integrable_const 1)) (Real.continuous_sqrt.comp hZcont).aestronglyMeasurable ?_
  filter_upwards with p
  have hZp0 : 0 ≤ Z p := by unfold Z; positivity
  have hsr0 : 0 ≤ Real.sqrt (Z p) := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hsr0]
  have hsq := sq_nonneg (Real.sqrt (Z p) - 1)
  rw [sub_sq, Real.sq_sqrt hZp0] at hsq
  change Real.sqrt (Z p) ≤ Z p + 1
  linarith

/-- General upper bound parameterized over opaque moment arrays `cArr`, `fArr` (prevents kernel
unfolding of `coarseMomInt` / `fineMomInt` during typechecking). -/
theorem edgeBin_integral_le_cert_gen (cArr fArr : Array (ℕ × ℕ))
    (hcArr : ∀ g : Fin 4,
      0 ≤ ∫ x, x ∂(expBinMeasure 4 g.val) ∧
      ∫ x, x ∂(expBinMeasure 4 g.val) ≤ ((cArr[g.val]!).1 : ℝ) / (momentScale : ℝ) ∧
      (∫ x, x ^ 2 ∂(expBinMeasure 4 g.val)) - (∫ x, x ∂(expBinMeasure 4 g.val)) ^ 2 ≤
        ((cArr[g.val]!).2 : ℝ) / (momentScale : ℝ))
    (hfArr : ∀ j : ℕ, j < 64 →
      0 ≤ ∫ x, x ∂(expBinMeasure 64 j) ∧
      ∫ x, x ∂(expBinMeasure 64 j) ≤ ((fArr[j]!).1 : ℝ) / (momentScale : ℝ) ∧
      (∫ x, x ^ 2 ∂(expBinMeasure 64 j)) - (∫ x, x ∂(expBinMeasure 64 j)) ^ 2 ≤
        ((fArr[j]!).2 : ℝ) / (momentScale : ℝ))
    {k : ℕ} (gs : Fin (k + 1) → Fin 4) (imax : Fin (k + 1)) (ya yb : Fin 6) :
    let sm := ∑ i ∈ Finset.univ.erase imax, (cArr[(gs i).val]!).1
    let sv := ∑ i ∈ Finset.univ.erase imax, (cArr[(gs i).val]!).2
    let dy := if ya.val ≤ yb.val then yb.val - ya.val else ya.val - yb.val
    ∫ p, Real.sqrt (((∑ i : Fin (k + 1), p.1 i) / (11 / 5 : ℝ)) ^ 2 + (p.2.1 - p.2.2) ^ 2)
      ∂((Measure.pi fun i => expBinMeasure 4 (gs i).val).prod
        ((heightBinMeasure 6 (11 / 5) ya.val).prod (heightBinMeasure 6 (11 / 5) yb.val))) ≤
      (certCostBoundWith fArr sm sv (gs imax).val dy : ℝ) / (costScale : ℝ) := by
  intro sm sv dy
  have hh : (0 : ℝ) < 11 / 5 := by norm_num
  haveI : ∀ i, IsProbabilityMeasure (expBinMeasure 4 (gs i).val) :=
    fun i => isProbabilityMeasure_expBinMeasure (gs i).isLt
  haveI : IsProbabilityMeasure (heightBinMeasure 6 (11 / 5) ya.val) :=
    isProbabilityMeasure_heightBinMeasure (by norm_num) hh ya.val
  haveI : IsProbabilityMeasure (heightBinMeasure 6 (11 / 5) yb.val) :=
    isProbabilityMeasure_heightBinMeasure (by norm_num) hh yb.val
  set ν := (heightBinMeasure 6 (11 / 5) ya.val).prod (heightBinMeasure 6 (11 / 5) yb.val)
  set Z : ((Fin (k + 1) → ℝ) × (ℝ × ℝ)) → ℝ :=
    fun p => ((∑ i : Fin (k + 1), p.1 i) / (11 / 5 : ℝ)) ^ 2 + (p.2.1 - p.2.2) ^ 2
  have hbase_int := edgeBin_integrable_gen (fun i => expBinMeasure 4 (gs i).val) 6 6 ya.val yb.val
    (by norm_num) (by norm_num)
    (fun i => integrable_id_expBinMeasure (gs i).isLt)
    (fun i => integrable_sq_expBinMeasure (gs i).isLt)
  rw [integral_pi_refine_coord gs imax hbase_int.2]
  have hD_nat_pos : 0 < costDenom := by unfold costDenom; have := momentScale_pos; positivity
  have hMpos : (0 : ℝ) < (momentScale : ℝ) := by exact_mod_cast momentScale_pos
  have hDpos : (0 : ℝ) < (costDenom : ℝ) := by exact_mod_cast hD_nat_pos
  have hsc_pos : (0 : ℝ) < (costScale : ℝ) := by norm_num [costScale]
  let cellInt : Fin 16 → Fin 4 → Fin 4 → ℕ := fun r s1 s2 =>
    certCellWith fArr sm sv (gs imax).val dy r.val s1.val s2.val
  have hsub_bound : ∀ r : Fin 16,
      ∫ p, Real.sqrt (Z p) ∂((Measure.pi fun i =>
        if i = imax then expBinMeasure 64 (16 * (gs imax).val + r.val)
        else expBinMeasure 4 (gs i).val).prod ν) ≤
      (1 / 16 : ℝ) * ∑ s1 : Fin 4, ∑ s2 : Fin 4, (cellInt r s1 s2 : ℝ) / (costScale : ℝ) := by
    intro r
    let μr : Fin (k + 1) → Measure ℝ := fun i =>
      if i = imax then expBinMeasure 64 (16 * (gs imax).val + r.val)
      else expBinMeasure 4 (gs i).val
    have hlt_r : 16 * (gs imax).val + r.val < 64 := by have := (gs imax).isLt; have := r.isLt; omega
    haveI : ∀ i, IsProbabilityMeasure (μr i) := fun i => by
      dsimp only [μr]; split_ifs
      · exact isProbabilityMeasure_expBinMeasure hlt_r
      · exact isProbabilityMeasure_expBinMeasure (gs i).isLt
    have h1r : ∀ i, Integrable (fun x : ℝ => x) (μr i) := fun i => by
      dsimp only [μr]; split_ifs
      · exact integrable_id_expBinMeasure hlt_r
      · exact integrable_id_expBinMeasure (gs i).isLt
    have h2r : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μr i) := fun i => by
      dsimp only [μr]; split_ifs
      · exact integrable_sq_expBinMeasure hlt_r
      · exact integrable_sq_expBinMeasure (gs i).isLt
    have hr_int := edgeBin_integrable_gen μr 6 6 ya.val yb.val (by norm_num) (by norm_num) h1r h2r
    rw [integral_prod_symm _ hr_int.2]
    have hinner_int : Integrable (fun q : ℝ × ℝ => ∫ xs, Real.sqrt (Z (xs, q)) ∂(Measure.pi μr)) ν :=
      hr_int.2.integral_prod_right
    rw [integral_prod _ hinner_int, integral_heightBinMeasure_refine hh ya.val hinner_int.integral_prod_left]
    have hrefine_b : ∀ s1 : Fin 4,
        ∫ u, (∫ v, (∫ xs, Real.sqrt (Z (xs, (u, v))) ∂(Measure.pi μr)) ∂(heightBinMeasure 6 (11 / 5) yb.val))
          ∂(heightBinMeasure 24 (11 / 5) (4 * ya.val + s1.val)) =
        (1 / 4 : ℝ) * ∑ s2 : Fin 4,
          ∫ p, Real.sqrt (Z p) ∂((Measure.pi μr).prod
            ((heightBinMeasure 24 (11 / 5) (4 * ya.val + s1.val)).prod
             (heightBinMeasure 24 (11 / 5) (4 * yb.val + s2.val)))) := by
      intro s1
      haveI : IsProbabilityMeasure (heightBinMeasure 24 (11 / 5) (4 * ya.val + s1.val)) :=
        isProbabilityMeasure_heightBinMeasure (by norm_num) hh _
      have hs1_int := edgeBin_integrable_gen μr 24 6 (4 * ya.val + s1.val) yb.val (by norm_num) (by norm_num) h1r h2r
      have hq_int : Integrable (fun q : ℝ × ℝ => ∫ xs, Real.sqrt (Z (xs, q)) ∂(Measure.pi μr))
          ((heightBinMeasure 24 (11 / 5) (4 * ya.val + s1.val)).prod (heightBinMeasure 6 (11 / 5) yb.val)) :=
        hs1_int.2.integral_prod_right
      rw [← integral_prod _ hq_int, integral_prod_symm _ hq_int,
          integral_heightBinMeasure_refine hh yb.val hq_int.integral_prod_right]
      congr 1
      apply Finset.sum_congr rfl
      intro s2 _
      haveI : IsProbabilityMeasure (heightBinMeasure 24 (11 / 5) (4 * yb.val + s2.val)) :=
        isProbabilityMeasure_heightBinMeasure (by norm_num) hh _
      have hs12_int := edgeBin_integrable_gen μr 24 24 (4 * ya.val + s1.val) (4 * yb.val + s2.val)
        (by norm_num) (by norm_num) h1r h2r
      have hq12 : Integrable (fun q : ℝ × ℝ => ∫ xs, Real.sqrt (Z (xs, q)) ∂(Measure.pi μr))
          ((heightBinMeasure 24 (11 / 5) (4 * ya.val + s1.val)).prod
           (heightBinMeasure 24 (11 / 5) (4 * yb.val + s2.val))) :=
        hs12_int.2.integral_prod_right
      rw [← integral_prod_symm _ hq12, ← integral_prod_symm _ hs12_int.2]
    simp_rw [hrefine_b, ← Finset.mul_sum, ← mul_assoc]
    have h16 : (1 / 4 : ℝ) * (1 / 4 : ℝ) = 1 / 16 := by norm_num
    rw [h16]
    have hcell : ∀ s1 s2 : Fin 4,
        ∫ p, Real.sqrt (Z p) ∂((Measure.pi μr).prod
          ((heightBinMeasure 24 (11 / 5) (4 * ya.val + s1.val)).prod
           (heightBinMeasure 24 (11 / 5) (4 * yb.val + s2.val)))) ≤
        (cellInt r (if ya.val ≤ yb.val then s2 else s1) (if ya.val ≤ yb.val then s1 else s2) : ℝ) / (costScale : ℝ) := by
      intro s1 s2
      haveI : IsProbabilityMeasure (heightBinMeasure 24 (11 / 5) (4 * ya.val + s1.val)) :=
        isProbabilityMeasure_heightBinMeasure (by norm_num) hh _
      haveI : IsProbabilityMeasure (heightBinMeasure 24 (11 / 5) (4 * yb.val + s2.val)) :=
        isProbabilityMeasure_heightBinMeasure (by norm_num) hh _
      have hs12_int := edgeBin_integrable_gen μr 24 24 (4 * ya.val + s1.val) (4 * yb.val + s2.val)
        (by norm_num) (by norm_num) h1r h2r
      set μsub := (Measure.pi μr).prod
        ((heightBinMeasure 24 (11 / 5) (4 * ya.val + s1.val)).prod
         (heightBinMeasure 24 (11 / 5) (4 * yb.val + s2.val)))
      have hZ_eq : ∫ p, Z p ∂μsub =
          ((∑ i : Fin (k + 1), ∫ x, x ∂(μr i)) ^ 2 +
            ∑ i : Fin (k + 1), ((∫ x, x ^ 2 ∂(μr i)) - (∫ x, x ∂(μr i)) ^ 2)) / (11 / 5 : ℝ) ^ 2 +
          ((((4 * ya.val + s1.val : ℕ) : ℝ) - ((4 * yb.val + s2.val : ℕ) : ℝ)) ^ 2 + 1 / 6) *
            ((11 / 5 : ℝ) / 24) ^ 2 := by
        have hdiv : Integrable (fun xs : Fin (k + 1) → ℝ =>
            ((∑ i : Fin (k + 1), xs i) / (11 / 5 : ℝ)) ^ 2) (Measure.pi μr) := by
          have : (fun xs : Fin (k + 1) → ℝ => ((∑ i : Fin (k + 1), xs i) / (11 / 5 : ℝ)) ^ 2) =
              fun xs => (∑ i : Fin (k + 1), xs i) ^ 2 / (11 / 5 : ℝ) ^ 2 := by funext xs; ring
          rw [this]; exact (integral_pi_sum_sq μr h1r h2r).1.div_const _
        have hZ1_int : Integrable (fun p : (Fin (k + 1) → ℝ) × (ℝ × ℝ) =>
            ((∑ i : Fin (k + 1), p.1 i) / (11 / 5 : ℝ)) ^ 2) μsub :=
          integrable_comp_mp measurePreserving_fst hdiv
        have hy_int := integrable_heightBin_diff_sq (Ba := 24) (Bb := 24) (h := 11 / 5)
          (by norm_num) (by norm_num) hh (4 * ya.val + s1.val) (4 * yb.val + s2.val)
        have hZ2_int : Integrable (fun p : (Fin (k + 1) → ℝ) × (ℝ × ℝ) => (p.2.1 - p.2.2) ^ 2) μsub :=
          integrable_comp_mp measurePreserving_snd hy_int
        show ∫ p, (((∑ i : Fin (k + 1), p.1 i) / (11 / 5 : ℝ)) ^ 2 + (p.2.1 - p.2.2) ^ 2) ∂μsub = _
        rw [integral_add hZ1_int hZ2_int]
        have h1eq : ∫ p, ((∑ i : Fin (k + 1), p.1 i) / (11 / 5 : ℝ)) ^ 2 ∂μsub =
            (∫ xs, (∑ i : Fin (k + 1), xs i) ^ 2 ∂(Measure.pi μr)) / (11 / 5 : ℝ) ^ 2 := by
          rw [integral_comp_measurePreserving measurePreserving_fst hdiv.aestronglyMeasurable]
          have : (fun xs : Fin (k + 1) → ℝ => ((∑ i : Fin (k + 1), xs i) / (11 / 5 : ℝ)) ^ 2) =
              fun xs => (∑ i : Fin (k + 1), xs i) ^ 2 / (11 / 5 : ℝ) ^ 2 := by funext xs; ring
          rw [this, integral_div]
        have h2eq : ∫ p, (p.2.1 - p.2.2) ^ 2 ∂μsub =
            ((((4 * ya.val + s1.val : ℕ) : ℝ) - ((4 * yb.val + s2.val : ℕ) : ℝ)) ^ 2 + 1 / 6) *
              ((11 / 5 : ℝ) / 24) ^ 2 := by
          rw [integral_comp_measurePreserving measurePreserving_snd hy_int.aestronglyMeasurable]
          simpa using integral_heightBinMeasure_diff_sq (B := 24) (h := 11 / 5) (by norm_num) hh
            (4 * ya.val + s1.val) (4 * yb.val + s2.val)
        rw [h1eq, h2eq, (integral_pi_sum_sq μr h1r h2r).2]
      let s1' := if ya.val ≤ yb.val then s2 else s1
      let s2' := if ya.val ≤ yb.val then s1 else s2
      let fm := (fArr[16 * (gs imax).val + r.val]!).1
      let fv := (fArr[16 * (gs imax).val + r.val]!).2
      let ex_num := ((sm + fm) * (sm + fm) + (sv + fv) * momentScale) * 25
      let diff : ℕ := if dy * 4 + s1'.val ≥ s2'.val then dy * 4 + s1'.val - s2'.val else s2'.val - (dy * 4 + s1'.val)
      let ey_term := (diff * diff * 6 + 1) * 121 * 121 * momentScale * momentScale
      let num := ex_num * 86400 + ey_term
      have hdiff_sq := diff_sq_eq ya yb s1 s2
      have hmean_sum_nn : 0 ≤ ∑ i : Fin (k + 1), ∫ x, x ∂(μr i) := by
        apply Finset.sum_nonneg; intro i _
        dsimp only [μr]; split_ifs
        · exact (hfArr _ hlt_r).1
        · exact (hcArr (gs i)).1
      have hmean_sum_le : ∑ i : Fin (k + 1), ∫ x, x ∂(μr i) ≤ ((sm + fm : ℕ) : ℝ) / (momentScale : ℝ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ imax)]
        have himax_le : ∫ x, x ∂(μr imax) ≤ (fm : ℝ) / (momentScale : ℝ) := by
          simpa [μr, fm] using (hfArr _ hlt_r).2.1
        have hrest_le : ∑ i ∈ Finset.univ.erase imax, ∫ x, x ∂(μr i) ≤ (sm : ℝ) / (momentScale : ℝ) := by
          have hsum_le : ∑ i ∈ Finset.univ.erase imax, ∫ x, x ∂(μr i) ≤
              ∑ i ∈ Finset.univ.erase imax, ((cArr[(gs i).val]!).1 : ℝ) / (momentScale : ℝ) := by
            apply Finset.sum_le_sum; intro i hi
            have hne : i ≠ imax := Finset.ne_of_mem_erase hi
            simpa [μr, hne] using (hcArr (gs i)).2.1
          rw [← Finset.sum_div] at hsum_le
          simpa [sm] using hsum_le
        push_cast; rw [add_div]; linarith
      have hvar_sum_le : ∑ i : Fin (k + 1), ((∫ x, x ^ 2 ∂(μr i)) - (∫ x, x ∂(μr i)) ^ 2) ≤
          ((sv + fv : ℕ) : ℝ) / (momentScale : ℝ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ imax)]
        have himax_le : (∫ x, x ^ 2 ∂(μr imax)) - (∫ x, x ∂(μr imax)) ^ 2 ≤ (fv : ℝ) / (momentScale : ℝ) := by
          simpa [μr, fv] using (hfArr _ hlt_r).2.2
        have hrest_le : ∑ i ∈ Finset.univ.erase imax,
            ((∫ x, x ^ 2 ∂(μr i)) - (∫ x, x ∂(μr i)) ^ 2) ≤ (sv : ℝ) / (momentScale : ℝ) := by
          have hsum_le : ∑ i ∈ Finset.univ.erase imax, ((∫ x, x ^ 2 ∂(μr i)) - (∫ x, x ∂(μr i)) ^ 2) ≤
              ∑ i ∈ Finset.univ.erase imax, ((cArr[(gs i).val]!).2 : ℝ) / (momentScale : ℝ) := by
            apply Finset.sum_le_sum; intro i hi
            have hne : i ≠ imax := Finset.ne_of_mem_erase hi
            simpa [μr, hne] using (hcArr (gs i)).2.2
          rw [← Finset.sum_div] at hsum_le
          simpa [sv] using hsum_le
        push_cast; rw [add_div]; linarith
      have hZ_le : ∫ p, Z p ∂μsub ≤ (num : ℝ) / (costDenom : ℝ) := by
        rw [hZ_eq, hdiff_sq]
        have hsq_le : (∑ i : Fin (k + 1), ∫ x, x ∂(μr i)) ^ 2 ≤ (((sm + fm : ℕ) : ℝ) / (momentScale : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hmean_sum_nn hmean_sum_le 2
        have halg : ((((sm + fm : ℕ) : ℝ) / (momentScale : ℝ)) ^ 2 + ((sv + fv : ℕ) : ℝ) / (momentScale : ℝ)) /
              (11 / 5 : ℝ) ^ 2 +
            ((diff : ℝ) ^ 2 + 1 / 6) * ((11 / 5 : ℝ) / 24) ^ 2 = (num : ℝ) / (costDenom : ℝ) :=
          subcell_alg_identity momentScale sm fm sv fv diff hMpos
        linarith [div_le_div_of_nonneg_right (add_le_add hsq_le hvar_sum_le) (by positivity : (0 : ℝ) ≤ (11 / 5 : ℝ) ^ 2)]
      have hnum_pos : (0 : ℝ) < (num : ℝ) / (costDenom : ℝ) := by
        have hMp : 0 < momentScale := momentScale_pos
        have hey_pos : 0 < ey_term := by
          dsimp only [ey_term]
          exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (by decide)) (by decide)) hMp) hMp
        have hnum_p : 0 < num := Nat.add_pos_right _ hey_pos
        exact div_pos (Nat.cast_pos.mpr hnum_p) hDpos
      have hjensen := integral_sqrt_le_sqrt_of_le (μ := μsub)
        (fun p => by positivity) hs12_int.1 hs12_int.2 hnum_pos hZ_le
      have hsqrt_le : Real.sqrt ((num : ℝ) / (costDenom : ℝ)) ≤
          (ceilSqrtDiv (num * (costScale * costScale)) costDenom : ℝ) / (costScale : ℝ) := by
        rw [le_div_iff₀ hsc_pos, ← Real.sqrt_sq (le_of_lt hsc_pos), ← Real.sqrt_mul (le_of_lt hnum_pos)]
        have hmul : (num : ℝ) / (costDenom : ℝ) * (costScale : ℝ) ^ 2 =
            ((num * (costScale * costScale) : ℕ) : ℝ) / (costDenom : ℝ) := by push_cast; ring
        rw [hmul]
        exact sqrt_div_le_ceilSqrtDiv _ costDenom hD_nat_pos
      have hcell_eq : certCellWith fArr sm sv (gs imax).val dy r.val s1'.val s2'.val =
          ceilSqrtDiv (num * (costScale * costScale)) costDenom := rfl
      show ∫ p, Real.sqrt (Z p) ∂μsub ≤
        (certCellWith fArr sm sv (gs imax).val dy r.val s1'.val s2'.val : ℝ) / (costScale : ℝ)
      rw [hcell_eq]
      exact hjensen.trans hsqrt_le
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    by_cases hle : ya.val ≤ yb.val
    · have hsum_le := Finset.sum_le_sum fun s1 (_ : s1 ∈ Finset.univ) =>
        Finset.sum_le_sum fun s2 (_ : s2 ∈ Finset.univ) => hcell s1 s2
      simp only [hle, ↓reduceIte] at hsum_le
      exact hsum_le.trans_eq Finset.sum_comm
    · have hsum_le := Finset.sum_le_sum fun s1 (_ : s1 ∈ Finset.univ) =>
        Finset.sum_le_sum fun s2 (_ : s2 ∈ Finset.univ) => hcell s1 s2
      simpa [hle] using hsum_le
  have hcomb : (1 / 16 : ℝ) * ∑ r : Fin 16,
      ∫ p, Real.sqrt (Z p) ∂((Measure.pi fun i =>
        if i = imax then expBinMeasure 64 (16 * (gs imax).val + r.val)
        else expBinMeasure 4 (gs i).val).prod ν) ≤
      ((∑ r : Fin 16, ∑ s1 : Fin 4, ∑ s2 : Fin 4,
          certCellWith fArr sm sv (gs imax).val dy r.val s1.val s2.val : ℕ) : ℝ) / (256 * (costScale : ℝ)) := by
    have hsum := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hsub_bound r
    have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 16)
    refine hmul.trans_eq ?_
    simp_rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [← Finset.sum_div]
    push_cast
    ring
  refine hcomb.trans ?_
  rw [certCostBoundWith_eq_sum]
  generalize ∑ r : Fin 16, ∑ s1 : Fin 4, ∑ s2 : Fin 4,
      certCellWith fArr sm sv (gs imax).val dy r.val s1.val s2.val = T
  have hceil : T ≤ ((T + 255) / 256) * 256 := by omega
  have hceilR : (T : ℝ) ≤ (((T + 255) / 256 : ℕ) : ℝ) * 256 := by exact_mod_cast hceil
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hsc_pos) hsc_pos]
  nlinarith

/-- General upper bound for any `k + 1` gap bins `gs`, designated refined coordinate `imax`,
and two height bins `ya, yb` with `dy = |ya - yb|`. -/
theorem edgeBin_integral_le_cert {k : ℕ} (gs : Fin (k + 1) → Fin 4) (imax : Fin (k + 1))
    (ya yb : Fin 6) :
    let sm := ∑ i ∈ Finset.univ.erase imax, (coarseMomInt[(gs i).val]!).1
    let sv := ∑ i ∈ Finset.univ.erase imax, (coarseMomInt[(gs i).val]!).2
    let dy := if ya.val ≤ yb.val then yb.val - ya.val else ya.val - yb.val
    ∫ p, Real.sqrt (((∑ i : Fin (k + 1), p.1 i) / (11 / 5 : ℝ)) ^ 2 + (p.2.1 - p.2.2) ^ 2)
      ∂((Measure.pi fun i => expBinMeasure 4 (gs i).val).prod
        ((heightBinMeasure 6 (11 / 5) ya.val).prod (heightBinMeasure 6 (11 / 5) yb.val))) ≤
      (certCostBound sm sv (gs imax).val dy : ℝ) / (costScale : ℝ) :=
  edgeBin_integral_le_cert_gen coarseMomInt fineMomInt (fun _ => coarseMomInt_ge)
    (fun _ hj => fineMomInt_ge hj) gs imax ya yb

/-- Every entry `edgeCost4 v gs ys` upper-bounds the exact
conditional expected Euclidean edge length for the corresponding `4 - v` exponential gaps and
endpoint heights `Y_v, Y_4`. -/
theorem edgeCost4_sound (v : Fin 4) (gs : Fin 4 → Fin 4) (ys : Fin 5 → Fin 6) :
    ∫ p, Real.sqrt (((∑ i : Fin (4 - v.val), p.1 i) / (11 / 5 : ℝ)) ^ 2 + (p.2.1 - p.2.2) ^ 2)
      ∂((Measure.pi fun i : Fin (4 - v.val) => expBinMeasure 4 (gs ⟨v.val + i.val, by omega⟩).val).prod
        ((heightBinMeasure 6 (11 / 5) (ys v.castSucc).val).prod
         (heightBinMeasure 6 (11 / 5) (ys (Fin.last 4)).val))) ≤
      edgeCost4 v gs ys := by
  let dy : Fin 6 := ⟨if (ys v.castSucc).val ≤ (ys (Fin.last 4)).val
    then (ys (Fin.last 4)).val - (ys v.castSucc).val
    else (ys v.castSucc).val - (ys (Fin.last 4)).val, by
      have h1 := (ys v.castSucc).isLt; have h2 := (ys (Fin.last 4)).isLt; split_ifs <;> omega⟩
  have hsc : (0 : ℝ) < (costScale : ℝ) := by norm_num [costScale]
  fin_cases v
  · let gs4 : Fin 4 → Fin 4 := fun i => gs ⟨0 + i.val, by omega⟩
    have hmax : ∃ imax : Fin 4, (gs4 imax).val = max (max (gs 0).val (gs 1).val) (max (gs 2).val (gs 3).val) := by
      rcases max_choice (max (gs 0).val (gs 1).val) (max (gs 2).val (gs 3).val) with hm | hm
      · rcases max_choice (gs 0).val (gs 1).val with hm1 | hm1
        · exact ⟨0, by change (gs 0).val = _; rw [hm, hm1]⟩
        · exact ⟨1, by change (gs 1).val = _; rw [hm, hm1]⟩
      · rcases max_choice (gs 2).val (gs 3).val with hm2 | hm2
        · exact ⟨2, by change (gs 2).val = _; rw [hm, hm2]⟩
        · exact ⟨3, by change (gs 3).val = _; rw [hm, hm2]⟩
    obtain ⟨imax, himax⟩ := hmax
    have hcert := edgeBin_integral_le_cert (k := 3) gs4 imax (ys (0 : Fin 4).castSucc) (ys (Fin.last 4))
    refine hcert.trans ?_
    unfold edgeCost4 edgeCostInt4
    dsimp only [Fin.val_zero]
    apply div_le_div_of_nonneg_right _ (le_of_lt hsc)
    have hchk := List.all_eq_true.mp costFlat4_checked (gs 0) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk (gs 1) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk (gs 2) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk (gs 3) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk dy (List.mem_finRange _)
    rw [decide_eq_true_eq] at hchk
    have hsm : ∑ i ∈ Finset.univ.erase imax, (coarseMomInt[(gs4 i).val]!).1 =
        (coarseMomInt[(gs 0).val]!).1 + (coarseMomInt[(gs 1).val]!).1 +
          (coarseMomInt[(gs 2).val]!).1 + (coarseMomInt[(gs 3).val]!).1 -
          (coarseMomInt[max (max (gs 0).val (gs 1).val) (max (gs 2).val (gs 3).val)]!).1 := by
      have htot := Finset.add_sum_erase Finset.univ (fun i : Fin 4 => (coarseMomInt[(gs4 i).val]!).1) (Finset.mem_univ imax)
      rw [Fin.sum_univ_four] at htot
      rw [← himax]; change _ = (coarseMomInt[(gs4 0).val]!).1 + (coarseMomInt[(gs4 1).val]!).1 +
        (coarseMomInt[(gs4 2).val]!).1 + (coarseMomInt[(gs4 3).val]!).1 - (coarseMomInt[(gs4 imax).val]!).1
      omega
    have hsv : ∑ i ∈ Finset.univ.erase imax, (coarseMomInt[(gs4 i).val]!).2 =
        (coarseMomInt[(gs 0).val]!).2 + (coarseMomInt[(gs 1).val]!).2 +
          (coarseMomInt[(gs 2).val]!).2 + (coarseMomInt[(gs 3).val]!).2 -
          (coarseMomInt[max (max (gs 0).val (gs 1).val) (max (gs 2).val (gs 3).val)]!).2 := by
      have htot := Finset.add_sum_erase Finset.univ (fun i : Fin 4 => (coarseMomInt[(gs4 i).val]!).2) (Finset.mem_univ imax)
      rw [Fin.sum_univ_four] at htot
      rw [← himax]; change _ = (coarseMomInt[(gs4 0).val]!).2 + (coarseMomInt[(gs4 1).val]!).2 +
        (coarseMomInt[(gs4 2).val]!).2 + (coarseMomInt[(gs4 3).val]!).2 - (coarseMomInt[(gs4 imax).val]!).2
      omega
    rw [hsm, hsv, himax]
    exact_mod_cast hchk
  · let gs3 : Fin 3 → Fin 4 := fun i => gs ⟨1 + i.val, by omega⟩
    have hmax : ∃ imax : Fin 3, (gs3 imax).val = max (gs 1).val (max (gs 2).val (gs 3).val) := by
      rcases max_choice (gs 1).val (max (gs 2).val (gs 3).val) with hm | hm
      · exact ⟨0, by change (gs 1).val = _; rw [hm]⟩
      · rcases max_choice (gs 2).val (gs 3).val with hm2 | hm2
        · exact ⟨1, by change (gs 2).val = _; rw [hm, hm2]⟩
        · exact ⟨2, by change (gs 3).val = _; rw [hm, hm2]⟩
    obtain ⟨imax, himax⟩ := hmax
    have hcert := edgeBin_integral_le_cert (k := 2) gs3 imax (ys (1 : Fin 4).castSucc) (ys (Fin.last 4))
    refine hcert.trans ?_
    unfold edgeCost4 edgeCostInt4
    dsimp only [Fin.val_one]
    apply div_le_div_of_nonneg_right _ (le_of_lt hsc)
    have hchk := List.all_eq_true.mp costFlat3_checked (gs 1) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk (gs 2) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk (gs 3) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk dy (List.mem_finRange _)
    rw [decide_eq_true_eq] at hchk
    have hsm : ∑ i ∈ Finset.univ.erase imax, (coarseMomInt[(gs3 i).val]!).1 =
        (coarseMomInt[(gs 1).val]!).1 + (coarseMomInt[(gs 2).val]!).1 +
          (coarseMomInt[(gs 3).val]!).1 -
          (coarseMomInt[max (gs 1).val (max (gs 2).val (gs 3).val)]!).1 := by
      have htot := Finset.add_sum_erase Finset.univ (fun i : Fin 3 => (coarseMomInt[(gs3 i).val]!).1) (Finset.mem_univ imax)
      rw [Fin.sum_univ_three] at htot
      rw [← himax]; change _ = (coarseMomInt[(gs3 0).val]!).1 + (coarseMomInt[(gs3 1).val]!).1 +
        (coarseMomInt[(gs3 2).val]!).1 - (coarseMomInt[(gs3 imax).val]!).1
      omega
    have hsv : ∑ i ∈ Finset.univ.erase imax, (coarseMomInt[(gs3 i).val]!).2 =
        (coarseMomInt[(gs 1).val]!).2 + (coarseMomInt[(gs 2).val]!).2 +
          (coarseMomInt[(gs 3).val]!).2 -
          (coarseMomInt[max (gs 1).val (max (gs 2).val (gs 3).val)]!).2 := by
      have htot := Finset.add_sum_erase Finset.univ (fun i : Fin 3 => (coarseMomInt[(gs3 i).val]!).2) (Finset.mem_univ imax)
      rw [Fin.sum_univ_three] at htot
      rw [← himax]; change _ = (coarseMomInt[(gs3 0).val]!).2 + (coarseMomInt[(gs3 1).val]!).2 +
        (coarseMomInt[(gs3 2).val]!).2 - (coarseMomInt[(gs3 imax).val]!).2
      omega
    rw [hsm, hsv, himax]
    exact_mod_cast hchk
  · let gs2 : Fin 2 → Fin 4 := fun i => gs ⟨2 + i.val, by omega⟩
    have hmax : ∃ imax : Fin 2, (gs2 imax).val = max (gs 2).val (gs 3).val := by
      rcases max_choice (gs 2).val (gs 3).val with hm | hm
      · exact ⟨0, by change (gs 2).val = _; rw [hm]⟩
      · exact ⟨1, by change (gs 3).val = _; rw [hm]⟩
    obtain ⟨imax, himax⟩ := hmax
    have hcert := edgeBin_integral_le_cert (k := 1) gs2 imax (ys (2 : Fin 4).castSucc) (ys (Fin.last 4))
    refine hcert.trans ?_
    unfold edgeCost4 edgeCostInt4
    dsimp only [Fin.val_two]
    apply div_le_div_of_nonneg_right _ (le_of_lt hsc)
    have hchk := List.all_eq_true.mp costFlat2_checked (gs 2) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk (gs 3) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk dy (List.mem_finRange _)
    rw [decide_eq_true_eq] at hchk
    have hsm : ∑ i ∈ Finset.univ.erase imax, (coarseMomInt[(gs2 i).val]!).1 =
        (coarseMomInt[min (gs 2).val (gs 3).val]!).1 := by
      have htot := Finset.add_sum_erase Finset.univ (fun i : Fin 2 => (coarseMomInt[(gs2 i).val]!).1) (Finset.mem_univ imax)
      rw [Fin.sum_univ_two] at htot
      rcases Fin.eq_zero_or_eq_succ imax with rfl | ⟨j, rfl⟩
      · have hle : (gs 3).val ≤ (gs 2).val := by change (gs 2).val = _ at himax; omega
        rw [min_eq_right hle]; change _ = (coarseMomInt[(gs2 1).val]!).1; omega
      · have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        have hle : (gs 2).val ≤ (gs 3).val := by change (gs 3).val = _ at himax; omega
        rw [min_eq_left hle]
        have h1eq : (0 : Fin 1).succ = (1 : Fin 2) := rfl
        rw [h1eq] at htot ⊢
        change _ = (coarseMomInt[(gs2 0).val]!).1; omega
    have hsv : ∑ i ∈ Finset.univ.erase imax, (coarseMomInt[(gs2 i).val]!).2 =
        (coarseMomInt[min (gs 2).val (gs 3).val]!).2 := by
      have htot := Finset.add_sum_erase Finset.univ (fun i : Fin 2 => (coarseMomInt[(gs2 i).val]!).2) (Finset.mem_univ imax)
      rw [Fin.sum_univ_two] at htot
      rcases Fin.eq_zero_or_eq_succ imax with rfl | ⟨j, rfl⟩
      · have hle : (gs 3).val ≤ (gs 2).val := by change (gs 2).val = _ at himax; omega
        rw [min_eq_right hle]; change _ = (coarseMomInt[(gs2 1).val]!).2; omega
      · have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        have hle : (gs 2).val ≤ (gs 3).val := by change (gs 3).val = _ at himax; omega
        rw [min_eq_left hle]
        have h1eq : (0 : Fin 1).succ = (1 : Fin 2) := rfl
        rw [h1eq] at htot ⊢
        change _ = (coarseMomInt[(gs2 0).val]!).2; omega
    rw [hsm, hsv, himax]
    exact_mod_cast hchk
  · let gs1 : Fin 1 → Fin 4 := fun i => gs ⟨3 + i.val, by omega⟩
    have hcert := edgeBin_integral_le_cert (k := 0) gs1 0 (ys (3 : Fin 4).castSucc) (ys (Fin.last 4))
    refine hcert.trans ?_
    unfold edgeCost4 edgeCostInt4
    change (certCostBound _ _ (gs 3).val _ : ℝ) / (costScale : ℝ) ≤ (costFlat1[(gs 3).val * 6 + dy.val]! : ℝ) / (costScale : ℝ)
    apply div_le_div_of_nonneg_right _ (le_of_lt hsc)
    have hchk := List.all_eq_true.mp costFlat1_checked (gs 3) (List.mem_finRange _)
    have hchk := List.all_eq_true.mp hchk dy (List.mem_finRange _)
    rw [decide_eq_true_eq] at hchk
    have hsm : ∑ i ∈ Finset.univ.erase (0 : Fin 1), (coarseMomInt[(gs1 i).val]!).1 = 0 := by simp
    have hsv : ∑ i ∈ Finset.univ.erase (0 : Fin 1), (coarseMomInt[(gs1 i).val]!).2 = 0 := by simp
    rw [hsm, hsv]
    exact_mod_cast hchk

end BHHBounds.Upper
