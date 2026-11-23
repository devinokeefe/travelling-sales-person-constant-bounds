import BHHBounds.Upper.Costs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Quantile bins of `Exp(1)`

Tail integrals of `x ^ m * exp (-x)` for `m ≤ 2`, the cutpoints `expCut n j = log (n / (n - j))`,
and the mass and first two moments of `exp (-x)` on each bin `expBinSet n j`.
-/

namespace BHHBounds.Upper

open MeasureTheory Set Real Filter
open scoped ENNReal

/-- `t^m * exp(-t) → 0` as `t → +∞` for `m = 0, 1, 2`. -/
lemma tendsto_exp_neg_atTop : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero

lemma tendsto_mul_exp_neg_atTop : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (nhds 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  simpa using h

lemma tendsto_sq_mul_exp_neg_atTop : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-t)) atTop (nhds 0) :=
  Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2

/-- Improper integral `∫_{a}^{∞} exp(-x) dx = exp(-a)`. -/
lemma integrableOn_exp_neg_Ioi (a : ℝ) : IntegrableOn (fun x => Real.exp (-x)) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg
    (g := fun t => -Real.exp (-t)) (g' := fun t => Real.exp (-t)) (l := 0)
  · fun_prop
  · intro x _; exact (hasDerivAt_exp_neg x).fun_neg.congr_deriv (by ring)
  · intro x _; exact le_of_lt (Real.exp_pos _)
  · simpa using tendsto_exp_neg_atTop.neg

lemma integral_Ioi_exp_neg (a : ℝ) : ∫ x in Ioi a, Real.exp (-x) = Real.exp (-a) := by
  have ht := intervalIntegral_tendsto_integral_Ioi a (integrableOn_exp_neg_Ioi a) tendsto_id
  dsimp only [id_eq] at ht
  have hval : Tendsto (fun b => Real.exp (-a) - Real.exp (-b)) atTop (nhds (Real.exp (-a) - 0)) :=
    tendsto_const_nhds.sub tendsto_exp_neg_atTop
  have heq : (fun b => ∫ x in a..b, Real.exp (-x)) = (fun b => Real.exp (-a) - Real.exp (-b)) :=
    funext fun b => integral_exp_neg a b
  rw [heq] at ht
  simpa using tendsto_nhds_unique ht hval

/-- Improper integral `∫_{a}^{∞} x * exp(-x) dx = (a + 1) * exp(-a)` for `a ≥ 0`. -/
lemma integrableOn_mul_exp_neg_Ioi {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x => x * Real.exp (-x)) (Ioi a) volume := by
  have htend : Tendsto (fun t : ℝ => -(t + 1) * Real.exp (-t)) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => -(t * Real.exp (-t) + Real.exp (-t))) atTop (nhds (-(0 + 0))) :=
      (tendsto_mul_exp_neg_atTop.add tendsto_exp_neg_atTop).neg
    convert h1 using 1
    · funext t; ring
    · congr 1; ring
  apply integrableOn_Ioi_deriv_of_nonneg
    (g := fun t => -(t + 1) * Real.exp (-t)) (g' := fun t => t * Real.exp (-t)) (l := 0)
  · fun_prop
  · intro x _
    have h1 : HasDerivAt (fun t => -(t + 1)) (-1) x := ((hasDerivAt_id x).add_const 1).fun_neg
    exact (h1.fun_mul (hasDerivAt_exp_neg x)).congr_deriv (by ring)
  · intro x hx
    exact mul_nonneg (ha.trans (le_of_lt hx)) (le_of_lt (Real.exp_pos _))
  · exact htend

lemma integral_Ioi_mul_exp_neg {a : ℝ} (ha : 0 ≤ a) :
    ∫ x in Ioi a, x * Real.exp (-x) = (a + 1) * Real.exp (-a) := by
  have ht := intervalIntegral_tendsto_integral_Ioi a (integrableOn_mul_exp_neg_Ioi ha) tendsto_id
  dsimp only [id_eq] at ht
  have ht0 : Tendsto (fun b : ℝ => (b + 1) * Real.exp (-b)) atTop (nhds 0) := by
    have h1 : Tendsto (fun b : ℝ => b * Real.exp (-b) + Real.exp (-b)) atTop (nhds (0 + 0)) :=
      tendsto_mul_exp_neg_atTop.add tendsto_exp_neg_atTop
    convert h1 using 1
    · funext b; ring
    · congr 1; ring
  have hval : Tendsto (fun b => (a + 1) * Real.exp (-a) - (b + 1) * Real.exp (-b)) atTop
      (nhds ((a + 1) * Real.exp (-a) - 0)) := tendsto_const_nhds.sub ht0
  have heq : (fun b => ∫ x in a..b, x * Real.exp (-x)) =
      (fun b => (a + 1) * Real.exp (-a) - (b + 1) * Real.exp (-b)) :=
    funext fun b => integral_mul_exp_neg a b
  rw [heq] at ht
  simpa using tendsto_nhds_unique ht hval

/-- Improper integral `∫_{a}^{∞} x^2 * exp(-x) dx = (a^2 + 2a + 2) * exp(-a)`. -/
lemma integrableOn_sq_mul_exp_neg_Ioi (a : ℝ) :
    IntegrableOn (fun x => x ^ 2 * Real.exp (-x)) (Ioi a) volume := by
  have htend : Tendsto (fun t : ℝ => -(t ^ 2 + 2 * t + 2) * Real.exp (-t)) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => -(t ^ 2 * Real.exp (-t) + 2 * (t * Real.exp (-t)) + 2 * Real.exp (-t)))
        atTop (nhds (-(0 + 2 * 0 + 2 * 0))) :=
      ((tendsto_sq_mul_exp_neg_atTop.add (tendsto_mul_exp_neg_atTop.const_mul 2)).add
        (tendsto_exp_neg_atTop.const_mul 2)).neg
    convert h1 using 1
    · funext t; ring
    · congr 1; ring
  apply integrableOn_Ioi_deriv_of_nonneg
    (g := fun t => -(t ^ 2 + 2 * t + 2) * Real.exp (-t)) (g' := fun t => t ^ 2 * Real.exp (-t)) (l := 0)
  · fun_prop
  · intro x _
    have h1 : HasDerivAt (fun t => -(t ^ 2 + 2 * t + 2)) (-(2 * x + 2)) x := by
      have ha' : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      have hb' : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
      exact ((ha'.fun_add hb').add_const 2).fun_neg
    exact (h1.fun_mul (hasDerivAt_exp_neg x)).congr_deriv (by ring)
  · intro x _
    exact mul_nonneg (sq_nonneg x) (le_of_lt (Real.exp_pos _))
  · exact htend

lemma integral_Ioi_sq_mul_exp_neg (a : ℝ) :
    ∫ x in Ioi a, x ^ 2 * Real.exp (-x) = (a ^ 2 + 2 * a + 2) * Real.exp (-a) := by
  have ht := intervalIntegral_tendsto_integral_Ioi a (integrableOn_sq_mul_exp_neg_Ioi a) tendsto_id
  dsimp only [id_eq] at ht
  have ht0 : Tendsto (fun b : ℝ => (b ^ 2 + 2 * b + 2) * Real.exp (-b)) atTop (nhds 0) := by
    have h1 : Tendsto (fun b : ℝ => b ^ 2 * Real.exp (-b) + 2 * (b * Real.exp (-b)) + 2 * Real.exp (-b))
        atTop (nhds (0 + 2 * 0 + 2 * 0)) :=
      (tendsto_sq_mul_exp_neg_atTop.add (tendsto_mul_exp_neg_atTop.const_mul 2)).add
        (tendsto_exp_neg_atTop.const_mul 2)
    convert h1 using 1
    · funext b; ring
    · congr 1; ring
  have hval : Tendsto (fun b => (a ^ 2 + 2 * a + 2) * Real.exp (-a) - (b ^ 2 + 2 * b + 2) * Real.exp (-b))
      atTop (nhds ((a ^ 2 + 2 * a + 2) * Real.exp (-a) - 0)) := tendsto_const_nhds.sub ht0
  have heq : (fun b => ∫ x in a..b, x ^ 2 * Real.exp (-x)) =
      (fun b => (a ^ 2 + 2 * a + 2) * Real.exp (-a) - (b ^ 2 + 2 * b + 2) * Real.exp (-b)) :=
    funext fun b => integral_sq_mul_exp_neg a b
  rw [heq] at ht
  simpa using tendsto_nhds_unique ht hval

/-- Quantile cutpoint `a(n, j) = log(n / (n - j))` for `j < n`. -/
noncomputable def expCut (n j : ℕ) : ℝ :=
  Real.log ((n : ℝ) / ((n - j : ℕ) : ℝ))

lemma expCut_nonneg {n j : ℕ} (hj : j < n) : 0 ≤ expCut n j := by
  unfold expCut
  apply Real.log_nonneg
  rw [one_le_div (by exact_mod_cast Nat.sub_pos_of_lt hj)]
  exact_mod_cast Nat.sub_le n j

lemma exp_neg_expCut {n j : ℕ} (hj : j < n) :
    Real.exp (-expCut n j) = ((n - j : ℕ) : ℝ) / (n : ℝ) := by
  unfold expCut
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  have hnj : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  rw [Real.exp_neg, Real.exp_log (div_pos hn hnj), inv_div]

lemma expCut_le_succ {n j : ℕ} (hj : j + 1 < n) : expCut n j ≤ expCut n (j + 1) := by
  unfold expCut
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1 : (0 : ℝ) < ((n - (j + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - (j + 1))
  have h2 : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - j)
  apply Real.log_le_log (div_pos hn h2)
  apply div_le_div_of_nonneg_left (le_of_lt hn) h1
  exact_mod_cast (by omega : n - (j + 1) ≤ n - j)

/-- Quantile bin `j < n` of `Exp(1)`: `(expCut n j, expCut n (j+1)]` for `j + 1 < n`,
and `(expCut n j, ∞)` for `j + 1 = n`. -/
def expBinSet (n j : ℕ) : Set ℝ :=
  if j + 1 < n then Ioc (expCut n j) (expCut n (j + 1)) else Ioi (expCut n j)

lemma measurableSet_expBinSet (n j : ℕ) : MeasurableSet (expBinSet n j) := by
  unfold expBinSet; split_ifs <;> [exact measurableSet_Ioc; exact measurableSet_Ioi]

/-- Exact mass of `exp(-x)` on `expBinSet n j`: equals `1 / n` for every `j < n`. -/
theorem setIntegral_exp_neg_bin {n j : ℕ} (hj : j < n) :
    ∫ x in expBinSet n j, Real.exp (-x) = 1 / (n : ℝ) := by
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  unfold expBinSet
  split_ifs with hlt
  · rw [← intervalIntegral.integral_of_le (expCut_le_succ hlt), integral_exp_neg,
        exp_neg_expCut hj, exp_neg_expCut hlt]
    have hsub : ((n - j : ℕ) : ℝ) - ((n - (j + 1) : ℕ) : ℝ) = 1 := by
      have : n - j = (n - (j + 1)) + 1 := by omega
      rw [this]; push_cast; ring
    rw [← sub_div, hsub]
  · rw [integral_Ioi_exp_neg, exp_neg_expCut hj]
    have : n - j = 1 := by omega
    simp [this]

/-- Exact 1st moment `n * ∫_{bin} x exp(-x) dx`. -/
theorem setIntegral_mul_exp_neg_bin {n j : ℕ} (hj : j < n) :
    (n : ℝ) * ∫ x in expBinSet n j, x * Real.exp (-x) =
      if j + 1 < n then
        ((n - j : ℕ) : ℝ) * (expCut n j + 1) - ((n - (j + 1) : ℕ) : ℝ) * (expCut n (j + 1) + 1)
      else
        expCut n j + 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold expBinSet
  split_ifs with hlt
  · rw [← intervalIntegral.integral_of_le (expCut_le_succ hlt), integral_mul_exp_neg,
        exp_neg_expCut hj, exp_neg_expCut hlt]
    field_simp [hn]
  · rw [integral_Ioi_mul_exp_neg (expCut_nonneg hj), exp_neg_expCut hj]
    have : n - j = 1 := by omega
    rw [this]; push_cast; field_simp [hn]

/-- Exact 2nd moment `n * ∫_{bin} x^2 exp(-x) dx`. -/
theorem setIntegral_sq_mul_exp_neg_bin {n j : ℕ} (hj : j < n) :
    (n : ℝ) * ∫ x in expBinSet n j, x ^ 2 * Real.exp (-x) =
      if j + 1 < n then
        ((n - j : ℕ) : ℝ) * (expCut n j ^ 2 + 2 * expCut n j + 2) -
          ((n - (j + 1) : ℕ) : ℝ) * (expCut n (j + 1) ^ 2 + 2 * expCut n (j + 1) + 2)
      else
        expCut n j ^ 2 + 2 * expCut n j + 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold expBinSet
  split_ifs with hlt
  · rw [← intervalIntegral.integral_of_le (expCut_le_succ hlt), integral_sq_mul_exp_neg,
        exp_neg_expCut hj, exp_neg_expCut hlt]
    field_simp [hn]
  · rw [integral_Ioi_sq_mul_exp_neg (expCut n j), exp_neg_expCut hj]
    have : n - j = 1 := by omega
    rw [this]; push_cast; field_simp [hn]

end BHHBounds.Upper
