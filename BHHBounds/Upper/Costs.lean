import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Analytic lemmas for the edge-cost table

Rational enclosures of `Real.log` from the `atanh` series, moments of `Exp(1)` on an interval, the
second moment of a difference of independent uniform variables, and `∫ √Z ≤ √M` when `∫ Z ≤ M` on a
probability space.
-/

namespace BHHBounds.Upper

open MeasureTheory Set Real

/-- Finite geometric sum identity `∑_{k=0}^{n-1} r^k = (1 - r^n) / (1 - r)`. -/
lemma geom_sum_real {r : ℝ} (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, r ^ k = (1 - r ^ n) / (1 - r) := by
  rw [eq_div_iff (sub_ne_zero.mpr hr.symm)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

/-- Truncated odd series `2 ∑_{k=0}^{n-1} z^(2k+1) / (2k+1)`. -/
noncomputable def atanhTrunc (n : ℕ) (z : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.range n, z ^ (2 * k + 1) / (2 * k + 1 : ℝ)

lemma hasDerivAt_atanhTrunc (n : ℕ) (t : ℝ) :
    HasDerivAt (atanhTrunc n) (2 * ∑ k ∈ Finset.range n, t ^ (2 * k)) t := by
  unfold atanhTrunc
  have hsum : HasDerivAt (fun x => ∑ k ∈ Finset.range n, x ^ (2 * k + 1) / (2 * k + 1 : ℝ))
      (∑ k ∈ Finset.range n, t ^ (2 * k)) t := by
    refine HasDerivAt.fun_sum (u := Finset.range n)
      (A := fun k x => x ^ (2 * k + 1) / (2 * k + 1 : ℝ))
      (A' := fun k => t ^ (2 * k)) fun k _ => ?_
    refine ((hasDerivAt_pow (2 * k + 1) t).div_const (2 * k + 1 : ℝ)).congr_deriv ?_
    have hne : (2 * k + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hne]
  exact hsum.const_mul 2

lemma hasDerivAt_log_ratio {t : ℝ} (ht1 : -1 < t) (ht2 : t < 1) :
    HasDerivAt (fun x => Real.log ((1 + x) / (1 - x))) (2 / (1 - t ^ 2)) t := by
  have h1 : 0 < 1 + t := by linarith
  have h2 : 0 < 1 - t := by linarith
  have hdiv : HasDerivAt (fun x => (1 + x) / (1 - x)) (2 / (1 - t) ^ 2) t := by
    have ha : HasDerivAt (fun x => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
    have hb : HasDerivAt (fun x => 1 - x) (-1) t := (hasDerivAt_id t).const_sub 1
    refine (ha.fun_div hb (ne_of_gt h2)).congr_deriv ?_
    ring
  refine (hdiv.log (ne_of_gt (div_pos h1 h2))).congr_deriv ?_
  have hne1 : 1 + t ≠ 0 := ne_of_gt h1
  have hne2 : 1 - t ≠ 0 := ne_of_gt h2
  have hne3 : 1 - t ^ 2 ≠ 0 := by nlinarith
  field_simp [hne1, hne2, hne3]
  ring

/-- Lower and upper rational series bounds on `Real.log ((1 + z) / (1 - z))` for `0 ≤ z < 1`. -/
theorem log_atanh_bounds (n : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    atanhTrunc n z ≤ Real.log ((1 + z) / (1 - z)) ∧
    Real.log ((1 + z) / (1 - z)) ≤
      atanhTrunc n z + 2 * z ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (1 - z ^ 2)) := by
  have hz2_lt : z ^ 2 < 1 := by nlinarith
  have h1z2 : 0 < 1 - z ^ 2 := by linarith
  let f : ℝ → ℝ := fun t => Real.log ((1 + t) / (1 - t)) - atanhTrunc n t
  have hf0 : f 0 = 0 := by simp [f, atanhTrunc]
  have hf_deriv : ∀ t ∈ Icc (0 : ℝ) z,
      HasDerivAt f (2 * t ^ (2 * n) / (1 - t ^ 2)) t := by
    intro t ht
    have ht1 : -1 < t := by linarith [ht.1]
    have ht2 : t < 1 := lt_of_le_of_lt ht.2 hz1
    have ht2_ne : t ^ 2 ≠ 1 := by nlinarith [ht.1, ht2]
    refine ((hasDerivAt_log_ratio ht1 ht2).fun_sub (hasDerivAt_atanhTrunc n t)).congr_deriv ?_
    have hsum_eq : ∑ k ∈ Finset.range n, t ^ (2 * k) = ∑ k ∈ Finset.range n, (t ^ 2) ^ k :=
      Finset.sum_congr rfl fun k _ => by rw [pow_mul]
    rw [hsum_eq, geom_sum_real ht2_ne n, ← pow_mul]
    have hne : 1 - t ^ 2 ≠ 0 := sub_ne_zero.mpr ht2_ne.symm
    field_simp [hne]
    ring
  have hf_cont : ContinuousOn f (Icc 0 z) := fun t ht => (hf_deriv t ht).continuousAt.continuousWithinAt
  constructor
  · have hmono : MonotoneOn f (Icc 0 z) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z) hf_cont
      · exact fun t ht => (hf_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hf_deriv t (interior_subset ht)).deriv]
        rw [interior_Icc] at ht
        have ht0 : 0 ≤ t := le_of_lt ht.1
        have ht2 : t < 1 := lt_of_lt_of_le ht.2 (le_of_lt hz1)
        have hden : 0 < 1 - t ^ 2 := by nlinarith
        exact div_nonneg (by positivity) (le_of_lt hden)
    have := hmono (left_mem_Icc.mpr hz0) (right_mem_Icc.mpr hz0) hz0
    simp only [f, hf0] at this
    linarith
  · let g : ℝ → ℝ := fun t => f t - 2 * t ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (1 - z ^ 2))
    have hg0 : g 0 = 0 := by simp [g, hf0]
    have hg_deriv : ∀ t ∈ Icc (0 : ℝ) z,
        HasDerivAt g (2 * t ^ (2 * n) / (1 - t ^ 2) - 2 * t ^ (2 * n) / (1 - z ^ 2)) t := by
      intro t ht
      have hterm : HasDerivAt (fun x => 2 * x ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (1 - z ^ 2)))
          (2 * t ^ (2 * n) / (1 - z ^ 2)) t := by
        refine (((hasDerivAt_pow (2 * n + 1) t).const_mul 2).div_const
          ((2 * n + 1 : ℝ) * (1 - z ^ 2))).congr_deriv ?_
        have hne1 : (2 * n + 1 : ℝ) ≠ 0 := by positivity
        have hne2 : 1 - z ^ 2 ≠ 0 := ne_of_gt h1z2
        push_cast
        field_simp [hne1, hne2]
      exact (hf_deriv t ht).fun_sub hterm
    have hg_cont : ContinuousOn g (Icc 0 z) := fun t ht => (hg_deriv t ht).continuousAt.continuousWithinAt
    have hanti : AntitoneOn g (Icc 0 z) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 z) hg_cont
      · exact fun t ht => (hg_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hg_deriv t (interior_subset ht)).deriv]
        rw [interior_Icc] at ht
        have ht0 : 0 ≤ t := le_of_lt ht.1
        have hden_t : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2, hz1]
        have hle : 1 - z ^ 2 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
        have hdiv : 1 / (1 - t ^ 2) ≤ 1 / (1 - z ^ 2) := one_div_le_one_div_of_le h1z2 hle
        have hpos : 0 ≤ 2 * t ^ (2 * n) := by positivity
        have := mul_le_mul_of_nonneg_left hdiv hpos
        simpa [div_eq_mul_inv] using sub_nonpos.mpr this
    have := hanti (left_mem_Icc.mpr hz0) (right_mem_Icc.mpr hz0) hz0
    simp only [g, f, hg0] at this
    linarith

/-- Convenient wrapper for `x ≥ 1`: apply `log_atanh_bounds` with `z = (x - 1) / (x + 1)`. -/
theorem log_bounds_of_ge_one (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    atanhTrunc n ((x - 1) / (x + 1)) ≤ Real.log x ∧
    Real.log x ≤
      atanhTrunc n ((x - 1) / (x + 1)) +
        2 * ((x - 1) / (x + 1)) ^ (2 * n + 1) /
          ((2 * n + 1 : ℝ) * (1 - ((x - 1) / (x + 1)) ^ 2)) := by
  have hxpos : 0 < x + 1 := by linarith
  have hz0 : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) (le_of_lt hxpos)
  have hz1 : (x - 1) / (x + 1) < 1 := by
    rw [div_lt_one hxpos]; linarith
  have hratio : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
    have hne : x + 1 ≠ 0 := ne_of_gt hxpos
    field_simp [hne]
    ring
  simpa [hratio] using log_atanh_bounds n hz0 hz1

/-- Exact integrals for `Exp(1)` on `[a, b]`: mass, 1st moment, and 2nd moment. -/
lemma hasDerivAt_exp_neg (x : ℝ) :
    HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-x)) x := by
  refine ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).congr_deriv ?_
  ring

lemma integral_exp_neg (a b : ℝ) :
    ∫ x in a..b, Real.exp (-x) = Real.exp (-a) - Real.exp (-b) := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-x)) x := by
    intro x _
    exact (hasDerivAt_exp_neg x).fun_neg.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  ring

lemma integral_mul_exp_neg (a b : ℝ) :
    ∫ x in a..b, x * Real.exp (-x) = (a + 1) * Real.exp (-a) - (b + 1) * Real.exp (-b) := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun t => -(t + 1) * Real.exp (-t)) (x * Real.exp (-x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -(t + 1)) (-1) x := ((hasDerivAt_id x).add_const 1).fun_neg
    exact (h1.fun_mul (hasDerivAt_exp_neg x)).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  ring

lemma integral_sq_mul_exp_neg (a b : ℝ) :
    ∫ x in a..b, x ^ 2 * Real.exp (-x) =
      (a ^ 2 + 2 * a + 2) * Real.exp (-a) - (b ^ 2 + 2 * b + 2) * Real.exp (-b) := by
  have hd : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t => -(t ^ 2 + 2 * t + 2) * Real.exp (-t)) (x ^ 2 * Real.exp (-x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -(t ^ 2 + 2 * t + 2)) (-(2 * x + 2)) x := by
      have ha : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hb : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
        simpa using (hasDerivAt_id x).const_mul 2
      exact ((ha.fun_add hb).add_const 2).fun_neg
    exact (h1.fun_mul (hasDerivAt_exp_neg x)).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  ring

/-- Exact 2nd moment of `(δ + u - v)^2` for independent `u, v ∈ [0, 1]`: equals `δ^2 + 1/6`. -/
lemma integral_uniform_diff_sq (δ : ℝ) :
    ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (δ + u - v) ^ 2 = δ ^ 2 + 1 / 6 := by
  have hinner : ∀ u : ℝ, ∫ v in (0 : ℝ)..1, (δ + u - v) ^ 2 = (δ + u) ^ 2 - (δ + u) + 1 / 3 := by
    intro u
    have hd : ∀ v ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t => -((δ + u - t) ^ 3) / 3) ((δ + u - v) ^ 2) v := by
      intro v _
      have h1 : HasDerivAt (fun t => δ + u - t) (-1) v := (hasDerivAt_id v).const_sub (δ + u)
      have h2 := (hasDerivAt_pow 3 (δ + u - v)).comp v h1
      exact ((h2.fun_neg).div_const 3).congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous _).intervalIntegrable _ _)]
    ring
  simp_rw [hinner]
  have hd2 : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => (δ + t) ^ 3 / 3 - (δ + t) ^ 2 / 2 + t / 3)
        ((δ + u) ^ 2 - (δ + u) + 1 / 3) u := by
    intro u _
    have h0 : HasDerivAt (fun t => δ + t) 1 u := (hasDerivAt_id u).const_add δ
    have h1 := ((hasDerivAt_pow 3 (δ + u)).comp u h0).div_const 3
    have h2 := ((hasDerivAt_pow 2 (δ + u)).comp u h0).div_const 2
    have h3 := (hasDerivAt_id u).div_const 3
    exact ((h1.fun_sub h2).fun_add h3).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  ring

/-- Elementary Jensen / Cauchy–Schwarz bound for `√`: on any probability measure `μ`,
if `Z ≥ 0` is integrable with `∫ Z dμ ≤ M` (`M > 0`), then `∫ √Z dμ ≤ √M`. -/
theorem integral_sqrt_le_sqrt_of_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ0 : ∀ ω, 0 ≤ Z ω) (hZi : Integrable Z μ)
    (hZsq : Integrable (fun ω => √(Z ω)) μ) {M : ℝ} (hM : 0 < M) (hle : ∫ ω, Z ω ∂μ ≤ M) :
    ∫ ω, √(Z ω) ∂μ ≤ √M := by
  have hsM : 0 < √M := Real.sqrt_pos.mpr hM
  have hpw : ∀ ω, √(Z ω) ≤ (Z ω + M) / (2 * √M) := by
    intro ω
    have h1 := sq_nonneg (√(Z ω) - √M)
    have h2 : √(Z ω) ^ 2 = Z ω := Real.sq_sqrt (hZ0 ω)
    have h3 : √M ^ 2 = M := Real.sq_sqrt (le_of_lt hM)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hint_rhs : Integrable (fun ω => (Z ω + M) / (2 * √M)) μ :=
    (hZi.add (integrable_const M)).div_const (2 * √M)
  have hmono := integral_mono hZsq hint_rhs hpw
  have hrhs : ∫ ω, (Z ω + M) / (2 * √M) ∂μ = ((∫ ω, Z ω ∂μ) + M) / (2 * √M) := by
    rw [integral_div, integral_add hZi (integrable_const M), integral_const]
    simp
  rw [hrhs] at hmono
  have hbound : ((∫ ω, Z ω ∂μ) + M) / (2 * √M) ≤ √M := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : √M * √M = M := Real.mul_self_sqrt (le_of_lt hM)
    nlinarith
  exact hmono.trans hbound

end BHHBounds.Upper
