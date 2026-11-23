import BHHBounds.Dual.FiniteN

/-!
# Conditional Triangle Expectation and Poisson Convergence

Provides the conditional-expectation layer for matched isolated triangles in `[0, 1]²`:
1. `finExtSurvProb` and `triCondVal`: exact finite-`n` external survival probability and canonical
   conditional expectation given a matched triangle shape `(L, pt)`.
2. `cond_integral_Z_eq_triCondVal`: exact evaluation of the `(n - 3)`-fold conditional integral
   over the remaining `n - 3` points `Z : Fin (n - 3) → Pt` for a fixed matched triple `Y`.
3. `measurable_triCondVal`, `triCondVal_bound`, and `tendsto_triCondVal`: joint measurability,
   uniform envelope on `boxRegion b`, and dominated-convergence limit as `n → ∞`.
-/

open MeasureTheory Set Real Filter Finset
open scoped ENNReal Classical
open BHHBounds.Geometry
open BHHBounds.Cert

namespace BHHBounds.Dual

noncomputable section

/-! ## Section 1: Definitions and Elementary Bounds -/

/-- Finite-`n` external survival probability for `k`-th step radius at point `v` outside `triUnion`. -/
def finExtSurvProb (n : ℕ) (m : ℕ) (A V : ℝ) : ℝ :=
  if m ≥ 2 then 0
  else if m = 1 then (1 - (A + V) / (n : ℝ)) ^ (n - 4)
  else (1 - (A + V) / (n : ℝ)) ^ (n - 4) +
    ((n - 4 : ℕ) : ℝ) * (V / (n : ℝ)) * (1 - (A + V) / (n : ℝ)) ^ (n - 5)

/-- Finite-`n` canonical conditional expectation given a matched triangle `(L, pt)`. -/
def triCondVal (rho w : Array Int) (yPrev rj yj : Int) (n : ℕ) (L : ℝ) (pt : Pt) : ℝ :=
  let P := triVerts L pt
  let A := unionDiskArea P (toR rj)
  2 * (toR yj - toR yPrev) * (1 - A / (n : ℝ)) ^ (n - 3) -
  (((n - 3 : ℕ) : ℝ) / (n : ℝ)) *
    ∫ v in (triUnion P (toR rj))ᶜ,
      ∑ u : Fin 3, ∑ k : Fin rho.size,
        triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj) (euclidDist v (P u)) k.val *
        finExtSurvProb n (triHitCount P v (toR (rho.getD k.val 0))) A
          (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal

private def triCondIntegrand (rho w : Array Int) (yPrev rj yj : Int) (n : ℕ) (L : ℝ) (pt v : Pt) : ℝ :=
  ∑ u : Fin 3, ∑ k : Fin rho.size,
    triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
      (euclidDist v (triVerts L pt u)) k.val *
    finExtSurvProb n (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
      (unionDiskArea (triVerts L pt) (toR rj))
      (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal

private lemma toR_lt_toR {a b : Int} (h : a < b) : toR a < toR b :=
  div_lt_div_of_pos_right (by exact_mod_cast h) S_pos

private lemma mem_disk_iff {a c : Pt} {r : ℝ} (hr : 0 ≤ r) :
    a ∈ disk c r ↔ euclidDist a c ≤ r :=
  (euclidDist_le_iff hr).symm

private lemma triCrossCoeff_nonneg {rho w : Array Int} (hpot : ValidStepPot rho w)
    {p yPrev yj d : ℝ} (hy : yPrev ≤ yj) (k : Fin rho.size) :
    0 ≤ triCrossCoeff w p yPrev yj d k.val := by
  unfold triCrossCoeff
  have hdw := stepPot_dw_nonneg hpot k
  have hle : toR (wPrev w k.val) ≤ toR (w.getD k.val 0) := by linarith
  have hmono : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
      max 0 (p + yj + t₁ - d) - max 0 (p + yPrev + t₁ - d) ≤
      max 0 (p + yj + t₂ - d) - max 0 (p + yPrev + t₂ - d) := by
    intro t₁ t₂ ht
    rcases le_total 0 (p + yj + t₁ - d) with h1 | h1 <;>
    rcases le_total 0 (p + yPrev + t₂ - d) with h2 | h2
    · rw [max_eq_right h1, max_eq_right (show 0 ≤ p + yj + t₂ - d by linarith), max_eq_right h2]
      linarith [le_max_right (0 : ℝ) (p + yPrev + t₁ - d)]
    · rw [max_eq_right h1, max_eq_right (show 0 ≤ p + yj + t₂ - d by linarith), max_eq_left h2]
      linarith [le_max_left (0 : ℝ) (p + yPrev + t₁ - d)]
    · rw [max_eq_left h1, max_eq_left (show p + yPrev + t₁ - d ≤ 0 by linarith), sub_self]
      exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))
    · rw [max_eq_left h1, max_eq_left (show p + yPrev + t₁ - d ≤ 0 by linarith), sub_self]
      exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))
  linarith [hmono (toR (wPrev w k.val)) (toR (w.getD k.val 0)) hle]

private lemma triCrossCoeff_le {p yPrev yj d : ℝ} (hy : yPrev ≤ yj) (w : Array Int) (k : Nat) :
    triCrossCoeff w p yPrev yj d k ≤ yj - yPrev := by
  unfold triCrossCoeff
  have h1 : max 0 (p + yj + toR (w.getD k 0) - d) -
      max 0 (p + yPrev + toR (w.getD k 0) - d) ≤ yj - yPrev := by
    rcases le_total 0 (p + yj + toR (w.getD k 0) - d) with h | h
    · rw [max_eq_right h]
      linarith [le_max_right (0 : ℝ) (p + yPrev + toR (w.getD k 0) - d)]
    · rw [max_eq_left h]
      linarith [le_max_left (0 : ℝ) (p + yPrev + toR (w.getD k 0) - d)]
  have h2 : 0 ≤ max 0 (p + yj + toR (wPrev w k) - d) -
      max 0 (p + yPrev + toR (wPrev w k) - d) :=
    sub_nonneg.mpr (max_le_max_left 0 (by linarith))
  linarith

private lemma triCrossCoeff_eq_zero_of_le {rho w : Array Int} (hpot : ValidStepPot rho w)
    {p yPrev yj d : ℝ} (hy : yPrev ≤ yj) (k : Fin rho.size)
    (hd : p + yj + toR (w.getD k.val 0) ≤ d) :
    triCrossCoeff w p yPrev yj d k.val = 0 := by
  unfold triCrossCoeff
  have hdw := stepPot_dw_nonneg hpot k
  rw [max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

private lemma finExtSurvProb_nonneg {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {A V : ℝ}
    (hV : 0 ≤ V) (hAV : A + V ≤ (n : ℝ)) :
    0 ≤ finExtSurvProb n m A V := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : 0 ≤ 1 - (A + V) / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn_pos]; exact hAV
  unfold finExtSurvProb
  split_ifs
  · exact le_rfl
  · exact pow_nonneg h1 _
  · exact add_nonneg (pow_nonneg h1 _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hV (le_of_lt hn_pos))) (pow_nonneg h1 _))

private lemma finExtSurvProb_le {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {A V : ℝ}
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hAV : A + V ≤ (n : ℝ)) :
    finExtSurvProb n m A V ≤ 1 + V := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1_nn : 0 ≤ 1 - (A + V) / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn_pos]; exact hAV
  have h1_le : 1 - (A + V) / (n : ℝ) ≤ 1 := by
    have : 0 ≤ (A + V) / (n : ℝ) := div_nonneg (by linarith) (le_of_lt hn_pos)
    linarith
  have hpow4 : (1 - (A + V) / (n : ℝ)) ^ (n - 4) ≤ 1 := pow_le_one₀ h1_nn h1_le
  have hpow5 : (1 - (A + V) / (n : ℝ)) ^ (n - 5) ≤ 1 := pow_le_one₀ h1_nn h1_le
  have hfrac : ((n - 4 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn_pos]; exact_mod_cast Nat.sub_le n 4
  unfold finExtSurvProb
  split_ifs
  · linarith
  · linarith
  · have hterm2 : ((n - 4 : ℕ) : ℝ) * (V / (n : ℝ)) * (1 - (A + V) / (n : ℝ)) ^ (n - 5) ≤ V := by
      have heq : ((n - 4 : ℕ) : ℝ) * (V / (n : ℝ)) = (((n - 4 : ℕ) : ℝ) / (n : ℝ)) * V := by ring
      rw [heq]
      have hcoef_nn : 0 ≤ (((n - 4 : ℕ) : ℝ) / (n : ℝ)) * V :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos)) hV
      calc (((n - 4 : ℕ) : ℝ) / (n : ℝ)) * V * (1 - (A + V) / (n : ℝ)) ^ (n - 5)
          ≤ (((n - 4 : ℕ) : ℝ) / (n : ℝ)) * V * 1 := mul_le_mul_of_nonneg_left hpow5 hcoef_nn
        _ = (((n - 4 : ℕ) : ℝ) / (n : ℝ)) * V := mul_one _
        _ ≤ 1 * V := mul_le_mul_of_nonneg_right hfrac hV
        _ = V := one_mul V
    linarith

private lemma tendsto_finExtSurvProb (m : ℕ) (A V : ℝ) :
    Tendsto (fun n : ℕ => finExtSurvProb n m A V) atTop
      (nhds (Real.exp (-A) * extSurvProb m V)) := by
  unfold finExtSurvProb extSurvProb
  split_ifs with h2 h1
  · simp
  · have h := tendsto_one_sub_div_pow (A + V) 4
    have hexp : Real.exp (-(A + V)) = Real.exp (-A) * Real.exp (-V) := by
      rw [← Real.exp_add]; congr 1; ring
    rwa [hexp] at h
  · have h0 := tendsto_one_sub_div_pow (A + V) 4
    have hbin := tendsto_binom_one (A + V) V 4
    have hbin' : Tendsto (fun n : ℕ =>
        ((n - 4 : ℕ) : ℝ) * (V / (n : ℝ)) * (1 - (A + V) / (n : ℝ)) ^ (n - 5))
        atTop (nhds (V * Real.exp (-(A + V)))) := by
      refine hbin.congr fun n => ?_
      rw [Nat.sub_sub]
    have hsum := h0.add hbin'
    have hexp : Real.exp (-(A + V)) + V * Real.exp (-(A + V)) =
        Real.exp (-A) * ((1 + V) * Real.exp (-V)) := by
      have : Real.exp (-(A + V)) = Real.exp (-A) * Real.exp (-V) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring
    rwa [hexp] at hsum

private lemma triVerts_dist_zero_le {rho w : Array Int} {b : BoxCert} (hb : ValidBox rho w b)
    {L : ℝ} {pt : Pt} (hmem : (L, pt) ∈ boxRegion b) (u : Fin 3) :
    euclidDist (triVerts L pt u) (0, 0) ≤ toR b.l1 := by
  have hql := boxRegion_mem_quarterLens hb hmem
  have hL_lt : L < toR b.l1 := hmem.2.1
  fin_cases u
  · simp only [Fin.zero_eta, triVerts, Matrix.cons_val_zero, euclidDist_self]
    exact le_of_lt (hql.1.trans hL_lt)
  · simp only [Fin.mk_one, triVerts, Matrix.cons_val_one, Matrix.cons_val_zero, euclidDist, sqDist]
    have hsq : (L - 0) ^ 2 + ((0 : ℝ) - 0) ^ 2 = L ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (le_of_lt hql.1)]
    exact le_of_lt hL_lt
  · change euclidDist (L * pt.1, L * pt.2) (0, 0) ≤ toR b.l1
    unfold euclidDist sqDist
    have hsq : (L * pt.1 - 0) ^ 2 + (L * pt.2 - 0) ^ 2 = L ^ 2 * (pt.1 ^ 2 + pt.2 ^ 2) := by ring
    dsimp only
    rw [hsq, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq (le_of_lt hql.1)]
    have hnorm : euclidNorm pt < 1 := quarterLens_euclidNorm_lt_one hql.2
    unfold euclidNorm at hnorm
    have hmul : L * Real.sqrt (pt.1 ^ 2 + pt.2 ^ 2) < L := by nlinarith [hql.1]
    linarith

private lemma unionDiskArea_triVerts_le (P : Fin 3 → Pt) {r : ℝ} (hr : 0 ≤ r) :
    unionDiskArea P r ≤ 3 * Real.pi * r ^ 2 := by
  unfold unionDiskArea
  have hvol : volume (⋃ u : Fin 3, disk (P u) r) ≤ ENNReal.ofReal (3 * Real.pi * r ^ 2) := by
    calc volume (⋃ u : Fin 3, disk (P u) r)
        ≤ ∑ u : Fin 3, volume (disk (P u) r) := measure_iUnion_fintype_le volume _
      _ = ∑ _u : Fin 3, ENNReal.ofReal (Real.pi * r ^ 2) := by
          refine Finset.sum_congr rfl fun u _ => volume_disk (P u) hr
      _ = 3 * ENNReal.ofReal (Real.pi * r ^ 2) := by simp
      _ = ENNReal.ofReal (3 * Real.pi * r ^ 2) := by
          rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), mul_assoc]
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  rwa [ENNReal.toReal_ofReal (by positivity)] at hle

private lemma disk_sdiff_volume_le (v : Pt) (U : Set Pt) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume (disk v ρ \ U)).toReal ≤ Real.pi * ρ ^ 2 := by
  have hvol : volume (disk v ρ \ U) ≤ ENNReal.ofReal (Real.pi * ρ ^ 2) :=
    (measure_mono Set.sdiff_subset).trans_eq (volume_disk v hρ)
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  rwa [ENNReal.toReal_ofReal (by positivity)] at hle

/-! ## Section 2: `triEmbed` Integral Change of Variables and `unitSquarePi` Peeling -/

private lemma measurable_triEmbed (x₀ : Pt) (c s : ℝ) (refl : Bool) (invSqrtN : ℝ) :
    Measurable (triEmbed x₀ c s refl invSqrtN) := by
  unfold triEmbed
  cases refl <;> simp only [↓reduceIte, Bool.false_eq_true] <;> fun_prop

private lemma surjective_triEmbed (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (refl : Bool)
    {invSqrtN : ℝ} (hpos : 0 < invSqrtN) :
    Function.Surjective (triEmbed x₀ c s refl invSqrtN) := by
  intro q
  let dx := (q.1 - x₀.1) / invSqrtN
  let dy := (q.2 - x₀.2) / invSqrtN
  let u : Pt := (c * dx + s * dy, -s * dx + c * dy)
  refine ⟨if refl then (u.1, -u.2) else u, ?_⟩
  have hne : invSqrtN ≠ 0 := ne_of_gt hpos
  unfold triEmbed
  cases refl <;> simp only [↓reduceIte, Bool.false_eq_true, u, dx, dy] <;> apply Prod.ext
  · have h : x₀.1 + invSqrtN * (c * (c * ((q.1 - x₀.1) / invSqrtN) + s * ((q.2 - x₀.2) / invSqrtN)) -
        s * (-s * ((q.1 - x₀.1) / invSqrtN) + c * ((q.2 - x₀.2) / invSqrtN))) - q.1 =
        (c ^ 2 + s ^ 2 - 1) * (q.1 - x₀.1) := by field_simp [hne]; ring
    linear_combination h + (q.1 - x₀.1) * hcs
  · have h : x₀.2 + invSqrtN * (s * (c * ((q.1 - x₀.1) / invSqrtN) + s * ((q.2 - x₀.2) / invSqrtN)) +
        c * (-s * ((q.1 - x₀.1) / invSqrtN) + c * ((q.2 - x₀.2) / invSqrtN))) - q.2 =
        (c ^ 2 + s ^ 2 - 1) * (q.2 - x₀.2) := by field_simp [hne]; ring
    linear_combination h + (q.2 - x₀.2) * hcs
  · have h : x₀.1 + invSqrtN * (c * (c * ((q.1 - x₀.1) / invSqrtN) + s * ((q.2 - x₀.2) / invSqrtN)) -
        s * -(-(-s * ((q.1 - x₀.1) / invSqrtN) + c * ((q.2 - x₀.2) / invSqrtN)))) - q.1 =
        (c ^ 2 + s ^ 2 - 1) * (q.1 - x₀.1) := by field_simp [hne]; ring
    linear_combination h + (q.1 - x₀.1) * hcs
  · have h : x₀.2 + invSqrtN * (s * (c * ((q.1 - x₀.1) / invSqrtN) + s * ((q.2 - x₀.2) / invSqrtN)) +
        c * -(-(-s * ((q.1 - x₀.1) / invSqrtN) + c * ((q.2 - x₀.2) / invSqrtN)))) - q.2 =
        (c ^ 2 + s ^ 2 - 1) * (q.2 - x₀.2) := by field_simp [hne]; ring
    linear_combination h + (q.2 - x₀.2) * hcs

private lemma injective_triEmbed (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (refl : Bool)
    {invSqrtN : ℝ} (hpos : 0 < invSqrtN) :
    Function.Injective (triEmbed x₀ c s refl invSqrtN) := by
  intro u v huv
  have hsq := triEmbed_sqDist x₀ hcs refl invSqrtN u v
  rw [huv, sqDist_self] at hsq
  have hsq0 : sqDist u v = 0 := by
    have hpos2 : 0 < invSqrtN ^ 2 := sq_pos_of_pos hpos
    nlinarith
  unfold sqDist at hsq0
  apply Prod.ext <;> nlinarith [sq_nonneg (u.1 - v.1), sq_nonneg (u.2 - v.2)]

/-- Integral change of variables along `triEmbed`: `∫ q, f q = invSqrtN² * ∫ v, f (triEmbed ... v)`. -/
private lemma integral_triEmbed (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (refl : Bool)
    {invSqrtN : ℝ} (hpos : 0 < invSqrtN) {f : Pt → ℝ} (hf : Measurable f) :
    ∫ q : Pt, f q ∂volume = invSqrtN ^ 2 * ∫ v : Pt, f (triEmbed x₀ c s refl invSqrtN v) ∂volume := by
  have hmeas := measurable_triEmbed x₀ c s refl invSqrtN
  have hsurj := surjective_triEmbed x₀ hcs refl hpos
  have hmap : Measure.map (triEmbed x₀ c s refl invSqrtN) (ENNReal.ofReal (invSqrtN ^ 2) • volume) =
      volume := by
    refine Measure.ext fun T hT => ?_
    rw [Measure.map_apply hmeas hT, Measure.smul_apply, smul_eq_mul,
        ← volume_image_triEmbed x₀ hcs refl hpos (hT.preimage hmeas),
        Set.image_preimage_eq T hsurj]
  conv_lhs => rw [← hmap]
  rw [integral_map hmeas.aemeasurable (by rw [hmap]; exact hf.aestronglyMeasurable),
      integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

/-- Peel off coordinate `0` from `Fin k → Pt` (`1 ≤ k`). -/
private def peelFirst {k : ℕ} (hk : 1 ≤ k) : (Fin k → Pt) ≃ Pt × (Fin (k - 1) → Pt) where
  toFun Z := (Z ⟨0, by omega⟩, fun i => Z ⟨i.val + 1, by omega⟩)
  invFun p i := if hi : i.val = 0 then p.1 else p.2 ⟨i.val - 1, by omega⟩
  left_inv Z := by
    funext i
    dsimp only
    split_ifs with hi
    · congr 1; exact Fin.ext hi.symm
    · congr 1; exact Fin.ext (by dsimp only; omega)
  right_inv p := by
    apply Prod.ext
    · simp
    · funext i; simp

private lemma measurable_peelFirst_symm {k : ℕ} (hk : 1 ≤ k) :
    Measurable (peelFirst hk).symm := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i.val = 0
  · have heq : (fun p : Pt × (Fin (k - 1) → Pt) => (peelFirst hk).symm p i) = fun p => p.1 := by
      funext p; simp [peelFirst, hi]
    rw [heq]; exact measurable_fst
  · have heq : (fun p : Pt × (Fin (k - 1) → Pt) => (peelFirst hk).symm p i) =
        fun p => p.2 ⟨i.val - 1, by omega⟩ := by
      funext p; simp [peelFirst, hi]
    rw [heq]; exact (measurable_pi_apply _).comp measurable_snd

private lemma measurePreserving_peelFirst_symm {k : ℕ} (hk : 1 ≤ k) :
    MeasurePreserving (peelFirst hk).symm (unitSquareMeasure.prod (unitSquarePi (k - 1)))
      (unitSquarePi k) := by
  refine ⟨measurable_peelFirst_symm hk, ?_⟩
  symm
  unfold unitSquarePi
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_peelFirst_symm hk) (MeasurableSet.univ_pi hs)]
  have hpre : (peelFirst hk).symm ⁻¹' Set.pi Set.univ s =
      s ⟨0, by omega⟩ ×ˢ Set.pi Set.univ (fun i : Fin (k - 1) => s ⟨i.val + 1, by omega⟩) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa [peelFirst] using h ⟨0, by omega⟩, fun i => ?_⟩
      simpa [peelFirst] using h ⟨i.val + 1, by omega⟩
    · rintro ⟨h0, hrest⟩ i
      simp only [peelFirst, Equiv.coe_fn_symm_mk]
      split_ifs with hi
      · convert h0 using 2; exact Fin.ext hi
      · convert hrest ⟨i.val - 1, by omega⟩ using 2; exact Fin.ext (by dsimp only; omega)
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hcast : k = (k - 1) + 1 := by omega
  let e : Fin ((k - 1) + 1) ≃ Fin k := finCongr hcast.symm
  rw [← Fintype.prod_equiv e (fun j => unitSquareMeasure (s (e j))) (fun i => unitSquareMeasure (s i))
        (fun _ => rfl), Fin.prod_univ_succ]
  congr 1

/-! ## Section 3: Joint Measurability of `triCondVal` -/

private lemma measurable_triVerts (u : Fin 3) :
    Measurable (fun p : ℝ × Pt => triVerts p.1 p.2 u) := by
  fin_cases u
  · change Measurable (fun _ : ℝ × Pt => ((0 : ℝ), (0 : ℝ))); exact measurable_const
  · change Measurable (fun p : ℝ × Pt => (p.1, (0 : ℝ))); fun_prop
  · change Measurable (fun p : ℝ × Pt => (p.1 * p.2.1, p.1 * p.2.2)); fun_prop

private lemma measurableSet_triUnion_prod (r : ℝ) :
    MeasurableSet {q : (ℝ × Pt) × Pt | q.2 ∈ triUnion (triVerts q.1.1 q.1.2) r} := by
  have heq : {q : (ℝ × Pt) × Pt | q.2 ∈ triUnion (triVerts q.1.1 q.1.2) r} =
      ⋃ u : Fin 3, {q : (ℝ × Pt) × Pt | sqDist q.2 (triVerts q.1.1 q.1.2 u) ≤ r ^ 2} := by
    ext q; simp [triUnion, disk]
  rw [heq]
  refine MeasurableSet.iUnion fun u => measurableSet_le ?_ measurable_const
  have hvu : Measurable (fun q : (ℝ × Pt) × Pt => triVerts q.1.1 q.1.2 u) :=
    (measurable_triVerts u).comp measurable_fst
  unfold sqDist
  exact (((measurable_fst.comp measurable_snd).sub (measurable_fst.comp hvu)).pow_const 2).add
    (((measurable_snd.comp measurable_snd).sub (measurable_snd.comp hvu)).pow_const 2)

private lemma measurable_unionDiskArea_triVerts (r : ℝ) :
    Measurable (fun p : ℝ × Pt => unionDiskArea (triVerts p.1 p.2) r) := by
  have hmeas_ind : Measurable (fun q : (ℝ × Pt) × Pt =>
      if q.2 ∈ triUnion (triVerts q.1.1 q.1.2) r then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_triUnion_prod r) measurable_const measurable_const
  have hlint : Measurable (fun p : ℝ × Pt =>
      ∫⁻ v : Pt, (if v ∈ triUnion (triVerts p.1 p.2) r then (1 : ℝ≥0∞) else 0) ∂volume) :=
    hmeas_ind.lintegral_prod_right'
  have heq : (fun p : ℝ × Pt => unionDiskArea (triVerts p.1 p.2) r) =
      fun p => (∫⁻ v : Pt, (if v ∈ triUnion (triVerts p.1 p.2) r then (1 : ℝ≥0∞) else 0) ∂volume).toReal := by
    funext p
    unfold unionDiskArea
    congr 1
    change volume (triUnion (triVerts p.1 p.2) r) = _
    have hm : MeasurableSet (triUnion (triVerts p.1 p.2) r) :=
      MeasurableSet.iUnion fun u => measurableSet_disk _ _
    rw [← lintegral_indicator_one hm]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ triUnion (triVerts p.1 p.2) r <;> simp [Set.indicator, hv]
  rw [heq]
  exact ENNReal.measurable_toReal.comp hlint

private lemma measurable_diskSdiffTriUnion_toReal (ρ r : ℝ) :
    Measurable (fun q : (ℝ × Pt) × Pt =>
      (volume (disk q.2 ρ \ triUnion (triVerts q.1.1 q.1.2) r)).toReal) := by
  let S : Set (((ℝ × Pt) × Pt) × Pt) :=
    {x | x.2 ∈ disk x.1.2 ρ ∧ x.2 ∉ triUnion (triVerts x.1.1.1 x.1.1.2) r}
  have hS1 : MeasurableSet {x : ((ℝ × Pt) × Pt) × Pt | x.2 ∈ disk x.1.2 ρ} := by
    change MeasurableSet {x : ((ℝ × Pt) × Pt) × Pt | sqDist x.2 x.1.2 ≤ ρ ^ 2}
    unfold sqDist
    refine measurableSet_le ?_ measurable_const
    exact (((measurable_fst.comp measurable_snd).sub
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).pow_const 2).add
      (((measurable_snd.comp measurable_snd).sub
        (measurable_snd.comp (measurable_snd.comp measurable_fst))).pow_const 2)
  have hS2 : MeasurableSet {x : ((ℝ × Pt) × Pt) × Pt |
      x.2 ∉ triUnion (triVerts x.1.1.1 x.1.1.2) r} := by
    have hpre : {x : ((ℝ × Pt) × Pt) × Pt | x.2 ∈ triUnion (triVerts x.1.1.1 x.1.1.2) r} =
        (fun x : ((ℝ × Pt) × Pt) × Pt => (x.1.1, x.2)) ⁻¹'
          {q : (ℝ × Pt) × Pt | q.2 ∈ triUnion (triVerts q.1.1 q.1.2) r} := rfl
    exact (hpre ▸ (measurableSet_triUnion_prod r).preimage
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).compl
  have hS : MeasurableSet S := hS1.inter hS2
  have hmeas_ind : Measurable (fun x : ((ℝ × Pt) × Pt) × Pt => if x ∈ S then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite hS measurable_const measurable_const
  have hlint : Measurable (fun q : (ℝ × Pt) × Pt =>
      ∫⁻ z : Pt, (if (q, z) ∈ S then (1 : ℝ≥0∞) else 0) ∂volume) :=
    hmeas_ind.lintegral_prod_right'
  have heq : (fun q : (ℝ × Pt) × Pt =>
      (volume (disk q.2 ρ \ triUnion (triVerts q.1.1 q.1.2) r)).toReal) =
      fun q => (∫⁻ z : Pt, (if (q, z) ∈ S then (1 : ℝ≥0∞) else 0) ∂volume).toReal := by
    funext q
    congr 1
    have hm : MeasurableSet (disk q.2 ρ \ triUnion (triVerts q.1.1 q.1.2) r) :=
      (measurableSet_disk _ _).diff (MeasurableSet.iUnion fun u => measurableSet_disk _ _)
    rw [← lintegral_indicator_one hm]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ disk q.2 ρ ∧ z ∉ triUnion (triVerts q.1.1 q.1.2) r
    · have hz1 : z ∈ disk q.2 ρ \ triUnion (triVerts q.1.1 q.1.2) r := hz
      have hz2 : (q, z) ∈ S := hz
      rw [Set.indicator_of_mem hz1, if_pos hz2]; rfl
    · have hz1 : z ∉ disk q.2 ρ \ triUnion (triVerts q.1.1 q.1.2) r := hz
      have hz2 : (q, z) ∉ S := hz
      rw [Set.indicator_of_notMem hz1, if_neg hz2]
  rw [heq]
  exact ENNReal.measurable_toReal.comp hlint

private lemma measurable_stepPot (rho w : Array Int) :
    Measurable (stepPot rho w) := by
  unfold stepPot
  refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const

private lemma measurable_triVertPot (rho w : Array Int) (u : Fin 3) :
    Measurable (fun p : ℝ × Pt => triVertPot rho w p.1 p.2 u) := by
  fin_cases u
  · exact (measurable_stepPot rho w).comp measurable_fst
  · exact (measurable_stepPot rho w).comp measurable_fst
  · change Measurable (fun p : ℝ × Pt => stepPot rho w (p.1 * euclidNorm (1 - p.2.1, p.2.2)))
    refine (measurable_stepPot rho w).comp (measurable_fst.mul ?_)
    unfold euclidNorm
    fun_prop

private lemma measurable_triHitCount_prod (ρ : ℝ) :
    Measurable (fun q : (ℝ × Pt) × Pt => triHitCount (triVerts q.1.1 q.1.2) q.2 ρ) := by
  have heq : (fun q : (ℝ × Pt) × Pt => triHitCount (triVerts q.1.1 q.1.2) q.2 ρ) =
      fun q => ∑ u : Fin 3, if euclidDist q.2 (triVerts q.1.1 q.1.2 u) ≤ ρ then 1 else 0 := by
    funext q; unfold triHitCount; rw [Finset.card_filter]
  rw [heq]
  refine Finset.measurable_sum _ fun u _ => ?_
  have hdist : Measurable (fun q : (ℝ × Pt) × Pt => euclidDist q.2 (triVerts q.1.1 q.1.2 u)) :=
    measurable_euclidDist.comp (measurable_snd.prodMk ((measurable_triVerts u).comp measurable_fst))
  exact Measurable.ite (measurableSet_le hdist measurable_const) measurable_const measurable_const

private lemma measurable_finExtSurvProb (n : ℕ) :
    Measurable (fun x : ℕ × ℝ × ℝ => finExtSurvProb n x.1 x.2.1 x.2.2) := by
  unfold finExtSurvProb
  have hm1 : MeasurableSet {x : ℕ × ℝ × ℝ | x.1 ≥ 2} :=
    (MeasurableSet.of_discrete (s := {m : ℕ | m ≥ 2})).preimage measurable_fst
  have hm2 : MeasurableSet {x : ℕ × ℝ × ℝ | x.1 = 1} :=
    (MeasurableSet.of_discrete (s := {m : ℕ | m = 1})).preimage measurable_fst
  refine Measurable.ite hm1 measurable_const (Measurable.ite hm2 ?_ ?_)
  · fun_prop
  · fun_prop

private lemma measurable_triCondIntegrand_raw (rho w : Array Int) (yPrev rj yj : Int) (n : ℕ) :
    Measurable (fun q : (ℝ × Pt) × Pt =>
      triCondIntegrand rho w yPrev rj yj n q.1.1 q.1.2 q.2) := by
  unfold triCondIntegrand
  refine Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · unfold triCrossCoeff
    have hp : Measurable (fun q : (ℝ × Pt) × Pt => triVertPot rho w q.1.1 q.1.2 u) :=
      (measurable_triVertPot rho w u).comp measurable_fst
    have hd : Measurable (fun q : (ℝ × Pt) × Pt => euclidDist q.2 (triVerts q.1.1 q.1.2 u)) :=
      measurable_euclidDist.comp (measurable_snd.prodMk ((measurable_triVerts u).comp measurable_fst))
    have h1 : Measurable (fun q : (ℝ × Pt) × Pt =>
        max 0 (triVertPot rho w q.1.1 q.1.2 u + toR yj + toR (w.getD k.val 0) -
          euclidDist q.2 (triVerts q.1.1 q.1.2 u))) :=
      measurable_const.max (((hp.add measurable_const).add measurable_const).sub hd)
    have h2 : Measurable (fun q : (ℝ × Pt) × Pt =>
        max 0 (triVertPot rho w q.1.1 q.1.2 u + toR yPrev + toR (w.getD k.val 0) -
          euclidDist q.2 (triVerts q.1.1 q.1.2 u))) :=
      measurable_const.max (((hp.add measurable_const).add measurable_const).sub hd)
    have h3 : Measurable (fun q : (ℝ × Pt) × Pt =>
        max 0 (triVertPot rho w q.1.1 q.1.2 u + toR yj + toR (wPrev w k.val) -
          euclidDist q.2 (triVerts q.1.1 q.1.2 u))) :=
      measurable_const.max (((hp.add measurable_const).add measurable_const).sub hd)
    have h4 : Measurable (fun q : (ℝ × Pt) × Pt =>
        max 0 (triVertPot rho w q.1.1 q.1.2 u + toR yPrev + toR (wPrev w k.val) -
          euclidDist q.2 (triVerts q.1.1 q.1.2 u))) :=
      measurable_const.max (((hp.add measurable_const).add measurable_const).sub hd)
    exact (h1.sub h2).sub (h3.sub h4)
  · exact (measurable_finExtSurvProb n).comp
      ((measurable_triHitCount_prod (toR (rho.getD k.val 0))).prodMk
        (((measurable_unionDiskArea_triVerts (toR rj)).comp measurable_fst).prodMk
          (measurable_diskSdiffTriUnion_toReal (toR (rho.getD k.val 0)) (toR rj))))

private lemma measurable_triCondIntegrand_v (rho w : Array Int) (yPrev rj yj : Int) (n : ℕ)
    (L : ℝ) (pt : Pt) :
    Measurable (triCondIntegrand rho w yPrev rj yj n L pt) := by
  have h := (measurable_triCondIntegrand_raw rho w yPrev rj yj n).comp
    ((measurable_const (a := (L, pt))).prodMk measurable_id)
  simpa only [Function.comp_def, id_eq] using h

lemma measurable_triCondVal (rho w : Array Int) (yPrev rj yj : Int) (n : ℕ) :
    Measurable (fun p : ℝ × Pt => triCondVal rho w yPrev rj yj n p.1 p.2) := by
  have hA : Measurable (fun p : ℝ × Pt => unionDiskArea (triVerts p.1 p.2) (toR rj)) :=
    measurable_unionDiskArea_triVerts (toR rj)
  have h1 : Measurable (fun p : ℝ × Pt =>
      2 * (toR yj - toR yPrev) * (1 - unionDiskArea (triVerts p.1 p.2) (toR rj) / (n : ℝ)) ^ (n - 3)) :=
    measurable_const.mul ((measurable_const.sub (hA.div_const _)).pow_const _)
  have hint_eq : (fun p : ℝ × Pt =>
      ∫ v in (triUnion (triVerts p.1 p.2) (toR rj))ᶜ,
        triCondIntegrand rho w yPrev rj yj n p.1 p.2 v) =
      fun p => ∫ v : Pt,
        (if v ∉ triUnion (triVerts p.1 p.2) (toR rj) then
          triCondIntegrand rho w yPrev rj yj n p.1 p.2 v
        else 0) ∂volume := by
    funext p
    have hm : MeasurableSet (triUnion (triVerts p.1 p.2) (toR rj))ᶜ :=
      (MeasurableSet.iUnion fun u => measurableSet_disk _ _).compl
    rw [← integral_indicator hm]
    congr 1; funext v
    by_cases hv : v ∉ triUnion (triVerts p.1 p.2) (toR rj)
    · rw [Set.indicator_of_mem hv, if_pos hv]
    · rw [Set.indicator_of_notMem hv, if_neg hv]
  have hmeas_ind : Measurable (fun q : (ℝ × Pt) × Pt =>
      if q.2 ∉ triUnion (triVerts q.1.1 q.1.2) (toR rj) then
        triCondIntegrand rho w yPrev rj yj n q.1.1 q.1.2 q.2
      else 0) :=
    Measurable.ite (measurableSet_triUnion_prod (toR rj)).compl
      (measurable_triCondIntegrand_raw rho w yPrev rj yj n) measurable_const
  have h2 : Measurable (fun p : ℝ × Pt =>
      ∫ v in (triUnion (triVerts p.1 p.2) (toR rj))ᶜ,
        triCondIntegrand rho w yPrev rj yj n p.1 p.2 v) := by
    rw [hint_eq]
    exact (hmeas_ind.stronglyMeasurable.integral_prod_right).measurable
  change Measurable (fun p : ℝ × Pt =>
    2 * (toR yj - toR yPrev) * (1 - unionDiskArea (triVerts p.1 p.2) (toR rj) / (n : ℝ)) ^ (n - 3) -
    (((n - 3 : ℕ) : ℝ) / (n : ℝ)) *
      ∫ v in (triUnion (triVerts p.1 p.2) (toR rj))ᶜ,
        triCondIntegrand rho w yPrev rj yj n p.1 p.2 v)
  exact h1.sub (measurable_const.mul h2)

/-! ## Section 4: Exact Conditional `Z`-Integral (`cond_integral_Z_eq_triCondVal`) -/

/-- Generic exchangeability + Fubini + exact hit-count evaluation of the `(n - 3)`-term crossing
sum over `unitSquarePi (n - 3)`. -/
private lemma integral_termJ_eq {n : ℕ} (hn : 5 ≤ n) {m : ℕ}
    {U_phys : Set Pt} (hU_meas : MeasurableSet U_phys)
    {mHit : Fin m → Pt → ℕ} (hmHit : ∀ k, Measurable (mHit k))
    (rDisk : Fin m → ℝ)
    {coeff : Fin 3 → Fin m → Pt → ℝ}
    (hcoeff_meas : ∀ u k, Measurable (coeff u k))
    {B : ℝ} (hB : 0 ≤ B)
    (hcoeff_nn : ∀ u k q, 0 ≤ coeff u k q)
    (hcoeff_le : ∀ u k q, coeff u k q ≤ B) :
    let D_phys : Fin m → Pt → Set Pt := fun k q => disk q (rDisk k) \ U_phys
    let termJ : Fin (n - 3) → (Fin (n - 3) → Pt) → ℝ := fun j Z =>
      if hitCount Z U_phys = 0 then
        ∑ u : Fin 3, ∑ k : Fin m, coeff u k (Z j) *
          (if mHit k (Z j) +
              ((Finset.univ.erase j).filter fun j' : Fin (n - 3) => Z j' ∈ D_phys k (Z j)).card ≤ 1
            then (1 : ℝ) else 0)
      else 0
    (∀ j, Integrable (termJ j) (unitSquarePi (n - 3))) ∧
    ∑ j : Fin (n - 3), ∫ Z : Fin (n - 3) → Pt, termJ j Z ∂(unitSquarePi (n - 3)) =
      ((n - 3 : ℕ) : ℝ) *
        ∫ q : Pt,
          (if q ∉ U_phys then
            ∑ u : Fin 3, ∑ k : Fin m, coeff u k q *
              (if mHit k q ≥ 2 then 0
               else if mHit k q = 1 then
                 (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 4)
               else
                 (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 4) +
                   ((n - 4 : ℕ) : ℝ) * (unitSquareMeasure (D_phys k q)).toReal *
                     (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 5))
          else 0) ∂unitSquareMeasure := by
  intro D_phys termJ
  have hmeas_hcU : Measurable (fun Z : Fin (n - 3) → Pt => hitCount Z U_phys) := by
    have heq : (fun Z : Fin (n - 3) → Pt => hitCount Z U_phys) =
        fun Z => ∑ i : Fin (n - 3), if Z i ∈ U_phys then 1 else 0 := by
      funext Z; unfold hitCount; rw [Finset.card_filter]
    rw [heq]
    exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (hU_meas.preimage (measurable_pi_apply i)) measurable_const measurable_const
  have hmeas_termJ : ∀ j : Fin (n - 3), Measurable (termJ j) := by
    intro j
    dsimp only [termJ]
    refine Measurable.ite (hmeas_hcU (MeasurableSet.singleton 0)) ?_ measurable_const
    refine Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
    · exact (hcoeff_meas u k).comp (measurable_pi_apply j)
    · have hm1 : Measurable (fun Z : Fin (n - 3) → Pt => mHit k (Z j)) :=
        (hmHit k).comp (measurable_pi_apply j)
      have hm2 : Measurable (fun Z : Fin (n - 3) → Pt =>
          ((Finset.univ.erase j).filter fun j' : Fin (n - 3) => Z j' ∈ D_phys k (Z j)).card) := by
        have heq : (fun Z : Fin (n - 3) → Pt =>
            ((Finset.univ.erase j).filter fun j' : Fin (n - 3) => Z j' ∈ D_phys k (Z j)).card) =
            fun Z => ∑ j' ∈ Finset.univ.erase j, if Z j' ∈ D_phys k (Z j) then 1 else 0 := by
          funext Z; rw [Finset.card_filter]
        rw [heq]
        refine Finset.measurable_sum _ fun j' _ => ?_
        have hS1 : MeasurableSet {Z : Fin (n - 3) → Pt | sqDist (Z j') (Z j) ≤ (rDisk k) ^ 2} := by
          unfold sqDist
          refine measurableSet_le ?_ measurable_const
          exact (((measurable_fst.comp (measurable_pi_apply j')).sub
            (measurable_fst.comp (measurable_pi_apply j))).pow_const 2).add
            (((measurable_snd.comp (measurable_pi_apply j')).sub
              (measurable_snd.comp (measurable_pi_apply j))).pow_const 2)
        have hS2 : MeasurableSet {Z : Fin (n - 3) → Pt | Z j' ∉ U_phys} :=
          hU_meas.compl.preimage (measurable_pi_apply j')
        exact Measurable.ite (hS1.inter hS2) measurable_const measurable_const
      exact Measurable.ite (measurableSet_le (hm1.add hm2) measurable_const)
        measurable_const measurable_const
  have hint_termJ : ∀ j : Fin (n - 3), Integrable (termJ j) (unitSquarePi (n - 3)) := by
    intro j
    refine Integrable.of_bound (hmeas_termJ j).aestronglyMeasurable
      (3 * (m : ℝ) * B) (Filter.Eventually.of_forall fun Z => ?_)
    dsimp only [termJ]
    split_ifs with hZ0
    · have hnn : 0 ≤ ∑ u : Fin 3, ∑ k : Fin m, coeff u k (Z j) *
          (if mHit k (Z j) +
              ((Finset.univ.erase j).filter fun j' : Fin (n - 3) => Z j' ∈ D_phys k (Z j)).card ≤ 1
            then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun k _ =>
          mul_nonneg (hcoeff_nn u k (Z j)) (by split_ifs <;> norm_num)
      rw [Real.norm_of_nonneg hnn]
      calc ∑ u : Fin 3, ∑ k : Fin m, coeff u k (Z j) *
            (if mHit k (Z j) +
                ((Finset.univ.erase j).filter fun j' : Fin (n - 3) => Z j' ∈ D_phys k (Z j)).card ≤ 1
              then (1 : ℝ) else 0)
          ≤ ∑ _u : Fin 3, ∑ _k : Fin m, B := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun k _ => ?_
            have h1 := hcoeff_le u k (Z j)
            have h2 := hcoeff_nn u k (Z j)
            split_ifs <;> linarith
        _ = 3 * (m : ℝ) * B := by
            simp [Finset.sum_const, nsmul_eq_mul]; ring
    · rw [norm_zero]; positivity
  refine ⟨hint_termJ, ?_⟩
  let j0 : Fin (n - 3) := ⟨0, by omega⟩
  have hexch : ∀ j : Fin (n - 3),
      ∫ Z : Fin (n - 3) → Pt, termJ j Z ∂(unitSquarePi (n - 3)) =
      ∫ Z : Fin (n - 3) → Pt, termJ j0 Z ∂(unitSquarePi (n - 3)) := by
    intro j
    let σ : Equiv.Perm (Fin (n - 3)) := Equiv.swap j0 j
    have hmp := measurePreserving_perm_pi (n - 3) σ
    conv_rhs => rw [← hmp.map_eq]
    rw [integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact (hmeas_termJ j0).aestronglyMeasurable)]
    congr 1; funext Z
    have hhc_perm : hitCount (Z ∘ σ) U_phys = hitCount Z U_phys := by
      unfold hitCount
      refine Finset.card_bij (fun i _ => σ i) (fun i hi => ?_) (fun a _ b _ h => σ.injective h) (fun b hb => ?_)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      · refine ⟨σ.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, σ.apply_symm_apply b⟩
        simpa [Function.comp] using (Finset.mem_filter.mp hb).2
    have h0_eq : (Z ∘ σ) j0 = Z j := by simp [Function.comp, σ]
    dsimp only [termJ]
    rw [hhc_perm, h0_eq]
    split_ifs with hZ0
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have hcard_perm : ((Finset.univ.erase j0).filter fun j' => (Z ∘ σ) j' ∈ D_phys k (Z j)).card =
          ((Finset.univ.erase j).filter fun j' => Z j' ∈ D_phys k (Z j)).card := by
        refine Finset.card_bij (fun i _ => σ i) (fun i hi => ?_)
          (fun a _ b _ h => σ.injective h) (fun b hb => ?_)
        · rcases Finset.mem_filter.mp hi with ⟨hi_er, hi_D⟩
          have hne : σ i ≠ j := by
            intro he; exact (Finset.ne_of_mem_erase hi_er) (σ.injective (he.trans (Equiv.swap_apply_left j0 j).symm))
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩, hi_D⟩
        · rcases Finset.mem_filter.mp hb with ⟨hb_er, hb_D⟩
          have hne : σ.symm b ≠ j0 := by
            intro he
            have : b = σ j0 := by rw [← he, σ.apply_symm_apply]
            rw [Equiv.swap_apply_left] at this
            exact Finset.ne_of_mem_erase hb_er this
          refine ⟨σ.symm b, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩, ?_⟩,
            σ.apply_symm_apply b⟩
          simpa [Function.comp] using hb_D
      rw [hcard_perm]
    · rfl
  rw [Finset.sum_congr rfl fun j _ => hexch j, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  congr 1
  have hk_ge : 1 ≤ n - 3 := by omega
  have hpeel := measurePreserving_peelFirst_symm hk_ge
  have hsub_eq : n - 3 - 1 = n - 4 := by omega
  have h_peel_int : ∫ Z : Fin (n - 3) → Pt, termJ j0 Z ∂(unitSquarePi (n - 3)) =
      ∫ p : Pt × (Fin (n - 3 - 1) → Pt), termJ j0 ((peelFirst hk_ge).symm p)
        ∂(unitSquareMeasure.prod (unitSquarePi (n - 3 - 1))) := by
    rw [← hpeel.map_eq, integral_map (measurable_peelFirst_symm hk_ge).aemeasurable
        (by rw [hpeel.map_eq]; exact (hmeas_termJ j0).aestronglyMeasurable)]
  rw [h_peel_int]
  let F_prod : Pt × (Fin (n - 3 - 1) → Pt) → ℝ := fun p =>
    if p.1 ∉ U_phys then
      ∑ u : Fin 3, ∑ k : Fin m, coeff u k p.1 *
        (if hitCount p.2 U_phys = 0 ∧ mHit k p.1 + hitCount p.2 (D_phys k p.1) ≤ 1
          then (1 : ℝ) else 0)
    else 0
  have hF_prod_eq : ∀ p : Pt × (Fin (n - 3 - 1) → Pt),
      termJ j0 ((peelFirst hk_ge).symm p) = F_prod p := by
    intro ⟨q, Zr⟩
    have h0 : (peelFirst hk_ge).symm (q, Zr) j0 = q := by simp [peelFirst, j0]
    have hhc_iff : hitCount ((peelFirst hk_ge).symm (q, Zr)) U_phys = 0 ↔
        q ∉ U_phys ∧ hitCount Zr U_phys = 0 := by
      simp only [hitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
        forall_true_left]
      constructor
      · intro h
        refine ⟨by simpa [h0] using @h j0, fun i => ?_⟩
        simpa [peelFirst] using @h ⟨i.val + 1, by omega⟩
      · rintro ⟨hq, hZr⟩ i
        simp only [peelFirst, Equiv.coe_fn_symm_mk]
        split_ifs with hi
        · exact hq
        · exact @hZr ⟨i.val - 1, by omega⟩
    have hcard_D : ∀ k : Fin m,
        ((Finset.univ.erase j0).filter fun j' =>
          (peelFirst hk_ge).symm (q, Zr) j' ∈ D_phys k q).card =
        hitCount Zr (D_phys k q) := by
      intro k
      unfold hitCount
      refine Finset.card_bij (fun j' hj' => ⟨j'.val - 1, by
          have hne := Finset.ne_of_mem_erase (Finset.mem_filter.mp hj').1
          have : j'.val ≠ 0 := fun h => hne (Fin.ext h)
          omega⟩) (fun j' hj' => ?_) (fun a ha b hb he => ?_) (fun i hi => ?_)
      · rcases Finset.mem_filter.mp hj' with ⟨hja, hjD⟩
        have hne : j'.val ≠ 0 := fun h => Finset.ne_of_mem_erase hja (Fin.ext h)
        simp only [peelFirst, Equiv.coe_fn_symm_mk, hne, ↓reduceDIte] at hjD
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hjD
      · have hna : a.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp ha).1 (Fin.ext h)
        have hnb : b.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp hb).1 (Fin.ext h)
        have hval := congrArg Fin.val he
        dsimp only at hval
        exact Fin.ext (by omega)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        refine ⟨⟨i.val + 1, by omega⟩, ?_, Fin.ext (by simp)⟩
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
        refine ⟨by intro h; simp [j0] at h, ?_⟩
        simpa [peelFirst] using hi
    dsimp only [termJ, F_prod]
    rw [h0]
    by_cases hq : q ∉ U_phys
    · rw [if_pos hq]
      by_cases hZr : hitCount Zr U_phys = 0
      · rw [if_pos (hhc_iff.mpr ⟨hq, hZr⟩)]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun k _ => ?_
        rw [hcard_D k]
        congr 1
        exact if_congr (by simp only [hZr, true_and]) rfl rfl
      · rw [if_neg (fun h => hZr (hhc_iff.mp h).2)]
        symm
        exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun k _ => by
          rw [if_neg (fun h => hZr h.1), mul_zero]
    · rw [if_neg hq, if_neg (fun h => hq (hhc_iff.mp h).1)]
  simp_rw [hF_prod_eq]
  have hF_int : Integrable F_prod (unitSquareMeasure.prod (unitSquarePi (n - 3 - 1))) := by
    have heq : F_prod = fun p => termJ j0 ((peelFirst hk_ge).symm p) :=
      funext fun p => (hF_prod_eq p).symm
    rw [heq]
    exact (hpeel.integrable_comp (hmeas_termJ j0).aestronglyMeasurable).mpr (hint_termJ j0)
  rw [MeasureTheory.integral_prod F_prod hF_int]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only [F_prod]
  by_cases hq : q ∉ U_phys
  · simp only [if_pos hq]
    have hmeas_hcS : ∀ {S : Set Pt}, MeasurableSet S →
        Measurable (fun Zr : Fin (n - 3 - 1) → Pt => hitCount Zr S) := by
      intro S hS
      have heq : (fun Zr : Fin (n - 3 - 1) → Pt => hitCount Zr S) =
          fun Zr => ∑ i : Fin (n - 3 - 1), if Zr i ∈ S then 1 else 0 := by
        funext Zr; unfold hitCount; rw [Finset.card_filter]
      rw [heq]
      exact Finset.measurable_sum _ fun i _ =>
        Measurable.ite (hS.preimage (measurable_pi_apply i)) measurable_const measurable_const
    have hD_meas : ∀ k : Fin m, MeasurableSet (D_phys k q) := fun k =>
      (measurableSet_disk _ _).diff hU_meas
    have hint_uk : ∀ (u : Fin 3) (k : Fin m),
        Integrable (fun Zr : Fin (n - 3 - 1) → Pt =>
          coeff u k q *
          (if hitCount Zr U_phys = 0 ∧ mHit k q + hitCount Zr (D_phys k q) ≤ 1
            then (1 : ℝ) else 0)) (unitSquarePi (n - 3 - 1)) := by
      intro u k
      have hpred : MeasurableSet {Zr : Fin (n - 3 - 1) → Pt |
          hitCount Zr U_phys = 0 ∧ mHit k q + hitCount Zr (D_phys k q) ≤ 1} :=
        ((hmeas_hcS hU_meas) (MeasurableSet.singleton 0)).inter
          (measurableSet_le (measurable_const.add (hmeas_hcS (hD_meas k))) measurable_const)
      refine Integrable.of_bound
        (measurable_const.mul (Measurable.ite hpred measurable_const measurable_const)).aestronglyMeasurable
        B (Filter.Eventually.of_forall fun Zr => ?_)
      split_ifs
      · rw [mul_one, Real.norm_of_nonneg (hcoeff_nn u k q)]; exact hcoeff_le u k q
      · rw [mul_zero, norm_zero]; exact hB
    rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun k _ => hint_uk u k]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_finsetSum _ fun k _ => hint_uk u k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    have hdisj : Disjoint U_phys (D_phys k q) := disjoint_sdiff_self_right
    split_ifs with hm2 hm1
    · have h0 : ∀ Zr : Fin (n - 3 - 1) → Pt,
          (if hitCount Zr U_phys = 0 ∧ mHit k q + hitCount Zr (D_phys k q) ≤ 1
            then (1 : ℝ) else 0) = 0 := fun Zr => if_neg (by omega)
      simp [h0]
    · have heq : (fun Zr : Fin (n - 3 - 1) → Pt =>
          if hitCount Zr U_phys = 0 ∧ mHit k q + hitCount Zr (D_phys k q) ≤ 1
            then (1 : ℝ) else 0) =
          fun Zr => if hitCount Zr (U_phys ∪ D_phys k q) = 0 then (1 : ℝ) else 0 := by
        funext Zr
        have hiff : (hitCount Zr U_phys = 0 ∧ mHit k q + hitCount Zr (D_phys k q) ≤ 1) ↔
            hitCount Zr (U_phys ∪ D_phys k q) = 0 := by
          have hUD0 : hitCount Zr (U_phys ∪ D_phys k q) = 0 ↔
              hitCount Zr U_phys = 0 ∧ hitCount Zr (D_phys k q) = 0 := by
            simp only [hitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
              forall_true_left, Set.mem_union, not_or, forall_and]
          rw [hUD0]; omega
        exact if_congr hiff rfl rfl
      rw [heq, prob_hitCount_eq_zero (n - 3 - 1) (hU_meas.union (hD_meas k)), hsub_eq]
    · have hm0 : mHit k q = 0 := by omega
      have heq : (fun Zr : Fin (n - 3 - 1) → Pt =>
          if hitCount Zr U_phys = 0 ∧ mHit k q + hitCount Zr (D_phys k q) ≤ 1
            then (1 : ℝ) else 0) =
          fun Zr => if hitCount Zr U_phys = 0 ∧ hitCount Zr (D_phys k q) ≤ 1
            then (1 : ℝ) else 0 := by
        funext Zr; simp [hm0]
      rw [heq, prob_disjoint_zero_le_one (n - 3 - 1) hU_meas (hD_meas k) hdisj, hsub_eq,
          show n - 4 - 1 = n - 5 by omega]
  · simp only [if_neg hq, integral_zero]

theorem cond_integral_Z_eq_triCondVal {n : ℕ} (hn : 5 ≤ n)
    {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) {yPrev rj yj : Int}
    (hyPrev_nn : 0 ≤ yPrev) (hy : yPrev < yj) (hrj_l1 : b.l1 < rj)
    (hhalf : 2 * (evalStepPot rho w b.l1 + yj) ≤ rj)
    {Rbuf : ℝ} (hRbuf_pos : 0 ≤ Rbuf)
    (hRbuf_r : toR b.l1 + toR rj ≤ Rbuf)
    (hRbuf_ext : ∀ i < rho.size,
      toR b.l1 + 2 * toR (w.getD (rho.size - 1) 0) + toR yj + toR (rho.getD i 0) ≤ Rbuf)
    (Y : Fin 3 → Pt)
    (hY0 : Y 0 ∈ interiorBox (Rbuf / Real.sqrt (n : ℝ)))
    (hYbox : canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
      (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
      (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2) ∈ boxRegion b) :
    let sh := canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
      (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
      (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2)
    let join : (Fin (n - 3) → Pt) → (Fin n → Pt) := fun Z i =>
      (splitFinEquiv 3 (n - 3)).symm (Y, Z) (Fin.cast (by omega) i)
    ∫ Z : Fin (n - 3) → Pt,
      (if ∀ x ∈ ({(⟨0, by omega⟩ : Fin n), ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)),
          ∀ z ∉ ({(⟨0, by omega⟩ : Fin n), ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)),
            toR rj < rescaledDist (join Z) x z then
        2 * (toR yj - toR yPrev) -
          ∑ x ∈ ({(⟨0, by omega⟩ : Fin n), ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)),
            ∑ z ∈ Finset.univ \ ({(⟨0, by omega⟩ : Fin n), ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)),
              (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yj +
                  stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z) -
               max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yPrev +
                  stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z))
      else 0) ∂(unitSquarePi (n - 3)) =
    triCondVal rho w yPrev rj yj n sh.1 sh.2 := by
  intro sh join
  -- Basic positivity & scaling constants
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let sqN : ℝ := Real.sqrt (n : ℝ)
  have hsqN_pos : 0 < sqN := Real.sqrt_pos.mpr hn_pos
  have hsqN_ne : sqN ≠ 0 := ne_of_gt hsqN_pos
  have hsqN_sq : sqN ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
  let invSqN : ℝ := 1 / sqN
  have hinvSqN_pos : 0 < invSqN := one_div_pos.mpr hsqN_pos
  have hinvSqN_sq : invSqN ^ 2 = 1 / (n : ℝ) := by
    dsimp only [invSqN]; rw [div_pow, one_pow, hsqN_sq]
  -- Canonical shape geometry
  have hn3 : 3 ≤ n := by omega
  have hu_lt : ∀ u : Fin 3, u.val < n := fun u => lt_of_lt_of_le u.isLt hn3
  have h3j_lt : ∀ j : Fin (n - 3), 3 + j.val < n := fun j => Nat.add_lt_of_lt_sub' j.isLt
  let Ys : Fin 3 → Pt := fun u => (sqN * (Y u).1, sqN * (Y u).2)
  let L : ℝ := sh.1
  let pt : Pt := sh.2
  have hql : 0 < L ∧ pt ∈ quarterLens := boxRegion_mem_quarterLens hb hYbox
  have hL_pos : 0 < L := hql.1
  have hL_lt_l1 : L < toR b.l1 := hYbox.2.1
  have hl1_pos : 0 < toR b.l1 := hL_pos.trans hL_lt_l1
  have hrj_gt_l1 : toR b.l1 < toR rj := toR_lt_toR hrj_l1
  have hrj_pos : 0 < toR rj := hl1_pos.trans hrj_gt_l1
  have hrj_nn : 0 ≤ toR rj := le_of_lt hrj_pos
  have hy_lt : toR yPrev < toR yj := toR_lt_toR hy
  have hy_le : toR yPrev ≤ toR yj := le_of_lt hy_lt
  have hyPrev_r_nn : 0 ≤ toR yPrev := toR_nonneg hyPrev_nn
  let P : Fin 3 → Pt := triVerts L pt
  -- Rigid embedding `Φ = triEmbed (Y 0) c s refl invSqN` mapping `P u ↦ Y u`
  let c : ℝ := ((Ys 1).1 - (Ys 0).1) / L
  let s : ℝ := ((Ys 1).2 - (Ys 0).2) / L
  let refl : Bool := decide (-((Ys 2).1 - (Ys 0).1) * ((Ys 1).2 - (Ys 0).2) +
    ((Ys 2).2 - (Ys 0).2) * ((Ys 1).1 - (Ys 0).1) < 0)
  have hemb_s : c ^ 2 + s ^ 2 = 1 ∧
      triEmbed (Ys 0) c s refl 1 (P 0) = Ys 0 ∧
      triEmbed (Ys 0) c s refl 1 (P 1) = Ys 1 ∧
      triEmbed (Ys 0) c s refl 1 (P 2) = Ys 2 :=
    triEmbed_canonShape (p₀ := Ys 0) (p₁ := Ys 1) (p₂ := Ys 2) hL_pos
  have hcs : c ^ 2 + s ^ 2 = 1 := hemb_s.1
  let Φ : Pt → Pt := triEmbed (Y 0) c s refl invSqN
  have hΦ_P : ∀ u : Fin 3, Φ (P u) = Y u := by
    intro u
    have hscaled : triEmbed (Ys 0) c s refl 1 (P u) = Ys u := by
      fin_cases u
      · exact hemb_s.2.1
      · exact hemb_s.2.2.1
      · exact hemb_s.2.2.2
    have h1 := congrArg Prod.fst hscaled
    have h2 := congrArg Prod.snd hscaled
    dsimp only [triEmbed, Ys] at h1 h2
    apply Prod.ext
    · dsimp only [Φ, triEmbed, invSqN]
      have : sqN * (Y u).1 = sqN * (Y 0).1 +
          (c * (if refl then ((P u).1, -(P u).2) else P u).1 -
           s * (if refl then ((P u).1, -(P u).2) else P u).2) := by
        simpa [one_mul] using h1.symm
      field_simp [hsqN_ne]; linarith
    · dsimp only [Φ, triEmbed, invSqN]
      have : sqN * (Y u).2 = sqN * (Y 0).2 +
          (s * (if refl then ((P u).1, -(P u).2) else P u).1 +
           c * (if refl then ((P u).1, -(P u).2) else P u).2) := by
        simpa [one_mul] using h2.symm
      field_simp [hsqN_ne]; linarith
  have hΦ_dist : ∀ v w : Pt, sqN * euclidDist (Φ v) (Φ w) = euclidDist v w := by
    intro v w
    rw [triEmbed_euclidDist (Y 0) hcs refl (le_of_lt hinvSqN_pos) v w]
    dsimp only [invSqN]; field_simp [hsqN_ne]
  have hΦ_dist_P : ∀ (v : Pt) (u : Fin 3), sqN * euclidDist (Φ v) (Y u) = euclidDist v (P u) := by
    intro v u; rw [← hΦ_P u, hΦ_dist]
  have hΦ_surj := surjective_triEmbed (Y 0) hcs refl hinvSqN_pos
  have hΦ_inj := injective_triEmbed (Y 0) hcs refl hinvSqN_pos
  have hΦ_meas := measurable_triEmbed (Y 0) c s refl invSqN
  -- `join Z` coordinate evaluations
  have hjoin_Y : ∀ (Z : Fin (n - 3) → Pt) (u : Fin 3), join Z ⟨u.val, by omega⟩ = Y u := by
    intro Z u
    dsimp only [join]
    have hcast : Fin.cast (by omega : n = 3 + (n - 3)) ⟨u.val, by omega⟩ = Fin.castAdd (n - 3) u :=
      Fin.ext rfl
    rw [hcast]; exact Fin.append_left Y Z u
  have hjoin_Z : ∀ (Z : Fin (n - 3) → Pt) (j : Fin (n - 3)),
      join Z ⟨3 + j.val, by omega⟩ = Z j := by
    intro Z j
    dsimp only [join]
    have hcast : Fin.cast (by omega : n = 3 + (n - 3)) ⟨3 + j.val, by omega⟩ = Fin.natAdd 3 j :=
      Fin.ext rfl
    rw [hcast]; exact Fin.append_right Y Z j
  -- Index sets `S₃` and `Finset.univ \ S₃`
  let S₃ : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hS₃_mem : ∀ i : Fin n, i ∈ S₃ ↔ i.val < 3 := by
    intro i; simp only [S₃, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega
  have hS₃_eq_img : S₃ = Finset.univ.image (fun u : Fin 3 => (⟨u.val, by omega⟩ : Fin n)) := by
    ext i; simp only [hS₃_mem, Finset.mem_image, Finset.mem_univ, true_and, Fin.ext_iff]
    constructor
    · intro hi; exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨u, hu⟩; omega
  have hS₃_compl_img : Finset.univ \ S₃ =
      Finset.univ.image (fun j : Fin (n - 3) => (⟨3 + j.val, by omega⟩ : Fin n)) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hS₃_mem, not_lt,
      Finset.mem_image, Fin.ext_iff]
    constructor
    · intro hi; exact ⟨⟨i.val - 3, by omega⟩, by dsimp only; omega⟩
    · rintro ⟨j, hj⟩; omega
  -- Physical union of clearance disks `U_phys`
  let U_phys : Set Pt := ⋃ u : Fin 3, disk (Y u) (toR rj / sqN)
  have hU_meas : MeasurableSet U_phys := MeasurableSet.iUnion fun u => measurableSet_disk _ _
  have hU_img : U_phys = Φ '' triUnion P (toR rj) := by
    ext q
    obtain ⟨v, rfl⟩ := hΦ_surj q
    simp only [U_phys, triUnion, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨v, ⟨u, ?_⟩, rfl⟩
      rw [mem_disk_iff hrj_nn, ← hΦ_dist_P v u]
      have h1 : euclidDist (Φ v) (Y u) ≤ toR rj / sqN :=
        (mem_disk_iff (div_nonneg hrj_nn (le_of_lt hsqN_pos))).mp hu
      exact (le_div_iff₀' hsqN_pos).mp h1
    · rintro ⟨v', ⟨u, hu⟩, hv'⟩
      have hveq : v' = v := hΦ_inj hv'
      subst hveq
      refine ⟨u, ?_⟩
      rw [mem_disk_iff (div_nonneg hrj_nn (le_of_lt hsqN_pos)), le_div_iff₀' hsqN_pos,
          hΦ_dist_P v' u]
      exact (mem_disk_iff hrj_nn).mp hu
  have hU_sub : U_phys ⊆ unitSquare := by
    intro q hq
    rcases Set.mem_iUnion.mp hq with ⟨u, hu⟩
    have h1 : euclidDist q (Y u) ≤ toR rj / sqN :=
      (mem_disk_iff (div_nonneg hrj_nn (le_of_lt hsqN_pos))).mp hu
    have h2 : euclidDist (Y u) (Y 0) ≤ toR b.l1 / sqN := by
      rw [le_div_iff₀' hsqN_pos, ← hΦ_P u, ← hΦ_P 0, hΦ_dist]
      exact triVerts_dist_zero_le hb hYbox u
    have h3 : euclidDist q (Y 0) ≤ Rbuf / sqN := by
      calc euclidDist q (Y 0)
          ≤ euclidDist q (Y u) + euclidDist (Y u) (Y 0) := euclidDist_triangle _ _ _
        _ ≤ toR rj / sqN + toR b.l1 / sqN := add_le_add h1 h2
        _ = (toR b.l1 + toR rj) / sqN := by ring
        _ ≤ Rbuf / sqN := div_le_div_of_nonneg_right hRbuf_r (le_of_lt hsqN_pos)
    exact disk_subset_unitSquare hY0 (div_nonneg hRbuf_pos (le_of_lt hsqN_pos)) le_rfl
      ((mem_disk_iff (div_nonneg hRbuf_pos (le_of_lt hsqN_pos))).mpr h3)
  have hU_area : (unitSquareMeasure U_phys).toReal = unionDiskArea P (toR rj) / (n : ℝ) := by
    have hm_tri : MeasurableSet (triUnion P (toR rj)) :=
      MeasurableSet.iUnion fun u => measurableSet_disk _ _
    rw [unitSquareMeasure_eq_volume_of_subset hU_sub, hU_img,
        volume_image_triEmbed (Y 0) hcs refl hinvSqN_pos hm_tri,
        hinvSqN_sq, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    unfold unionDiskArea triUnion
    ring
  -- Clearance predicate equivalence: `∀ x ∈ S₃, ∀ z ∉ S₃, toR rj < d x z ↔ hitCount Z U_phys = 0`
  have hclear_iff : ∀ Z : Fin (n - 3) → Pt,
      (∀ x ∈ S₃, ∀ z ∉ S₃, toR rj < rescaledDist (join Z) x z) ↔ hitCount Z U_phys = 0 := by
    intro Z
    simp only [hitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
      forall_true_left, U_phys, Set.mem_iUnion, not_exists]
    constructor
    · intro h j u hj
      have hlt := h ⟨u.val, by omega⟩ ((hS₃_mem _).mpr u.isLt)
        ⟨3 + j.val, by omega⟩ (by simp only [hS₃_mem]; omega)
      unfold rescaledDist at hlt
      rw [hjoin_Y, hjoin_Z, euclidDist_symm] at hlt
      have hle : euclidDist (Z j) (Y u) ≤ toR rj / sqN :=
        (mem_disk_iff (div_nonneg hrj_nn (le_of_lt hsqN_pos))).mp hj
      have hle' : sqN * euclidDist (Z j) (Y u) ≤ toR rj := (le_div_iff₀' hsqN_pos).mp hle
      linarith
    · intro h x hx z hz
      have hxv : x.val < 3 := (hS₃_mem x).mp hx
      have hzv : ¬ z.val < 3 := fun hl => hz ((hS₃_mem z).mpr hl)
      have hz_lt : z.val < n := z.isLt
      have hxj : join Z x = Y ⟨x.val, hxv⟩ := by
        convert hjoin_Y Z ⟨x.val, hxv⟩ using 2
      have hzj : join Z z = Z ⟨z.val - 3, by omega⟩ := by
        convert hjoin_Z Z ⟨z.val - 3, by omega⟩ using 2
        exact Fin.ext (by dsimp only; omega)
      unfold rescaledDist
      rw [hxj, hzj, euclidDist_symm]
      have hnot : Z ⟨z.val - 3, by omega⟩ ∉ disk (Y ⟨x.val, hxv⟩) (toR rj / sqN) :=
        @h ⟨z.val - 3, by omega⟩ ⟨x.val, hxv⟩
      rw [mem_disk_iff (div_nonneg hrj_nn (le_of_lt hsqN_pos)), not_le] at hnot
      exact (div_lt_iff₀' hsqN_pos).mp hnot
  -- Edge lengths of `Y` (rescaled) and vertex potentials when cleared
  have hY_edges : sqN * euclidDist (Y 0) (Y 1) = L ∧
      sqN * euclidDist (Y 0) (Y 2) = L * euclidNorm pt ∧
      sqN * euclidDist (Y 1) (Y 2) = L * euclidNorm (1 - pt.1, pt.2) := by
    have hed := canonShape_edge_dists (p₀ := Ys 0) (p₁ := Ys 1) (p₂ := Ys 2) hL_pos
    have hYs_dist : ∀ u v : Fin 3, euclidDist (Ys u) (Ys v) = sqN * euclidDist (Y u) (Y v) := by
      intro u v
      unfold Ys euclidDist sqDist
      have hsq : (sqN * (Y u).1 - sqN * (Y v).1) ^ 2 + (sqN * (Y u).2 - sqN * (Y v).2) ^ 2 =
          sqN ^ 2 * (((Y u).1 - (Y v).1) ^ 2 + ((Y u).2 - (Y v).2) ^ 2) := by ring
      dsimp only; rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hsqN_pos)]
    exact ⟨by rw [← hYs_dist]; exact hed.1, by rw [← hYs_dist]; exact hed.2.1,
      by rw [← hYs_dist]; exact hed.2.2⟩
  have hY_strict : sqN * euclidDist (Y 0) (Y 2) < sqN * euclidDist (Y 1) (Y 2) ∧
      sqN * euclidDist (Y 1) (Y 2) < sqN * euclidDist (Y 0) (Y 1) := by
    have hst := canonShape_strict_edges (p₀ := Ys 0) (p₁ := Ys 1) (p₂ := Ys 2) hL_pos hql.2
    have hYs_dist : ∀ u v : Fin 3, euclidDist (Ys u) (Ys v) = sqN * euclidDist (Y u) (Y v) := by
      intro u v
      unfold Ys euclidDist sqDist
      have hsq : (sqN * (Y u).1 - sqN * (Y v).1) ^ 2 + (sqN * (Y u).2 - sqN * (Y v).2) ^ 2 =
          sqN ^ 2 * (((Y u).1 - (Y v).1) ^ 2 + ((Y u).2 - (Y v).2) ^ 2) := by ring
      dsimp only; rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hsqN_pos)]
    rwa [hYs_dist, hYs_dist, hYs_dist] at hst
  have hpot_iso : ∀ (Z : Fin (n - 3) → Pt), hitCount Z U_phys = 0 →
      ∀ u : Fin 3, stepPot rho w (nn2 hn3 (rescaledDist (join Z)) ⟨u.val, hu_lt u⟩) =
        triVertPot rho w L pt u := by
    intro Z hZ0 u
    have hclear := (hclear_iff Z).mpr hZ0
    have hiso : IsIsolated (rescaledDist (join Z)) S₃ := by
      intro x hx a ha z hz
      have hxz := hclear x hx z hz
      have hxv : x.val < 3 := (hS₃_mem x).mp hx
      have hav : a.val < 3 := (hS₃_mem a).mp ha
      have hxa : rescaledDist (join Z) x a ≤ L := by
        unfold rescaledDist
        have hxj : join Z x = Y ⟨x.val, hxv⟩ := by convert hjoin_Y Z ⟨x.val, hxv⟩ using 2
        have haj : join Z a = Y ⟨a.val, hav⟩ := by convert hjoin_Y Z ⟨a.val, hav⟩ using 2
        rw [hxj, haj]
        generalize (⟨x.val, hxv⟩ : Fin 3) = ux
        generalize (⟨a.val, hav⟩ : Fin 3) = ua
        fin_cases ux <;> fin_cases ua <;> simp only [euclidDist_self, mul_zero]
        · exact le_of_lt hL_pos
        · exact le_of_eq hY_edges.1
        · change sqN * euclidDist (Y 0) (Y 2) ≤ L
          linarith only [hY_strict.1, hY_strict.2, hY_edges.1]
        · rw [euclidDist_symm]; exact le_of_eq hY_edges.1
        · exact le_of_lt hL_pos
        · change sqN * euclidDist (Y 1) (Y 2) ≤ L
          linarith only [hY_strict.2, hY_edges.1]
        · change sqN * euclidDist (Y 2) (Y 0) ≤ L
          rw [euclidDist_symm]; linarith only [hY_strict.1, hY_strict.2, hY_edges.1]
        · change sqN * euclidDist (Y 2) (Y 1) ≤ L
          rw [euclidDist_symm]; linarith only [hY_strict.2, hY_edges.1]
        · exact le_of_lt hL_pos
      linarith only [hxa, hL_lt_l1, hrj_gt_l1, hxz]
    have hjY0 : join Z ⟨0, hu_lt 0⟩ = Y 0 := hjoin_Y Z 0
    have hjY1 : join Z ⟨1, hu_lt 1⟩ = Y 1 := hjoin_Y Z 1
    have hjY2 : join Z ⟨2, hu_lt 2⟩ = Y 2 := hjoin_Y Z 2
    have hS₃_eq1 : ({(⟨1, hu_lt 1⟩ : Fin n), ⟨0, hu_lt 0⟩, ⟨2, hu_lt 2⟩} : Finset (Fin n)) = S₃ := by
      ext q; simp only [S₃, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun h => by rcases h with rfl | rfl | rfl <;> simp,
             fun h => by rcases h with rfl | rfl | rfl <;> simp⟩
    have hS₃_eq2 : ({(⟨2, hu_lt 2⟩ : Fin n), ⟨0, hu_lt 0⟩, ⟨1, hu_lt 1⟩} : Finset (Fin n)) = S₃ := by
      ext q; simp only [S₃, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun h => by rcases h with rfl | rfl | rfl <;> simp,
             fun h => by rcases h with rfl | rfl | rfl <;> simp⟩
    fin_cases u
    · have hnn : nn2 hn3 (rescaledDist (join Z)) ⟨0, hu_lt 0⟩ = L := by
        rw [nn2_isolated_triple hn3 (Fin.ne_of_val_ne (by simp))
          (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) hiso]
        unfold rescaledDist
        rw [hjY0, hjY1, hjY2]
        change max (sqN * euclidDist (Y 0) (Y 1)) (sqN * euclidDist (Y 0) (Y 2)) = L
        rw [max_eq_left (by linarith only [hY_strict.1, hY_strict.2]), hY_edges.1]
      rw [hnn]; rfl
    · have hiso1 : IsIsolated (rescaledDist (join Z))
          ({(⟨1, hu_lt 1⟩ : Fin n), ⟨0, hu_lt 0⟩, ⟨2, hu_lt 2⟩} : Finset (Fin n)) :=
        hS₃_eq1.symm ▸ hiso
      have hnn : nn2 hn3 (rescaledDist (join Z)) ⟨1, hu_lt 1⟩ = L := by
        rw [nn2_isolated_triple hn3 (Fin.ne_of_val_ne (by simp))
          (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) hiso1]
        unfold rescaledDist
        rw [hjY1, hjY0, hjY2, euclidDist_symm (Y 1) (Y 0)]
        change max (sqN * euclidDist (Y 0) (Y 1)) (sqN * euclidDist (Y 1) (Y 2)) = L
        rw [max_eq_left (by linarith only [hY_strict.2]), hY_edges.1]
      rw [hnn]; rfl
    · have hiso2 : IsIsolated (rescaledDist (join Z))
          ({(⟨2, hu_lt 2⟩ : Fin n), ⟨0, hu_lt 0⟩, ⟨1, hu_lt 1⟩} : Finset (Fin n)) :=
        hS₃_eq2.symm ▸ hiso
      have hnn : nn2 hn3 (rescaledDist (join Z)) ⟨2, hu_lt 2⟩ =
          L * euclidNorm (1 - pt.1, pt.2) := by
        rw [nn2_isolated_triple hn3 (Fin.ne_of_val_ne (by simp))
          (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) hiso2]
        unfold rescaledDist
        rw [hjY2, hjY0, hjY1, euclidDist_symm (Y 2) (Y 0), euclidDist_symm (Y 2) (Y 1)]
        change max (sqN * euclidDist (Y 0) (Y 2)) (sqN * euclidDist (Y 1) (Y 2)) =
          L * euclidNorm (1 - pt.1, pt.2)
        rw [max_eq_right (le_of_lt hY_strict.1), hY_edges.2.2]
      rw [hnn]; rfl
  -- Bound `triVertPot rho w L pt u ≤ toR (evalStepPot rho w b.l1)`
  have htriVertPot_le_ev : ∀ u : Fin 3, triVertPot rho w L pt u ≤ toR (evalStepPot rho w b.l1) := by
    intro u
    fin_cases u
    · exact stepPot_le_evalStepPot hpot (le_of_lt hL_lt_l1)
    · exact stepPot_le_evalStepPot hpot (le_of_lt hL_lt_l1)
    · refine stepPot_le_evalStepPot hpot ?_
      have hn1 : euclidNorm (1 - pt.1, pt.2) < 1 := quarterLens_euclidNorm_sub_lt_one hql.2
      have : L * euclidNorm (1 - pt.1, pt.2) < L := by nlinarith [hL_pos]
      linarith
  have hhalf_r : 2 * (toR (evalStepPot rho w b.l1) + toR yj) ≤ toR rj := by
    have htmp := toR_le_toR hhalf
    unfold toR at htmp ⊢; push_cast at htmp ⊢
    rw [← add_div, ← mul_div_assoc]; exact htmp
  -- Auxiliary functions for rewriting the crossing penalty in terms of `Z`
  let mHit : Fin rho.size → Pt → ℕ := fun k q =>
    (Finset.univ.filter fun u : Fin 3 => sqN * euclidDist q (Y u) ≤ toR (rho.getD k.val 0)).card
  let D_phys : Fin rho.size → Pt → Set Pt := fun k q =>
    disk q (toR (rho.getD k.val 0) / sqN) \ U_phys
  let termJ : Fin (n - 3) → (Fin (n - 3) → Pt) → ℝ := fun j Z =>
    if hitCount Z U_phys = 0 then
      ∑ u : Fin 3, ∑ k : Fin rho.size,
        triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
          (sqN * euclidDist (Z j) (Y u)) k.val *
        (if mHit k (Z j) +
            ((Finset.univ.erase j).filter fun j' : Fin (n - 3) => Z j' ∈ D_phys k (Z j)).card ≤ 1
          then (1 : ℝ) else 0)
    else 0
  -- Pointwise rewrite of the entire `Z`-integrand!
  have hptwise : ∀ Z : Fin (n - 3) → Pt,
      (if ∀ x ∈ S₃, ∀ z ∉ S₃, toR rj < rescaledDist (join Z) x z then
        2 * (toR yj - toR yPrev) -
          ∑ x ∈ S₃, ∑ z ∈ Finset.univ \ S₃,
            (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yj +
                stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z) -
             max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yPrev +
                stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z))
      else 0) =
      (if hitCount Z U_phys = 0 then 2 * (toR yj - toR yPrev) else 0) -
        ∑ j : Fin (n - 3), termJ j Z := by
    intro Z
    by_cases hZ0 : hitCount Z U_phys = 0
    · have hcl := (hclear_iff Z).mpr hZ0
      rw [if_pos hcl, if_pos hZ0]
      congr 1
      -- Reindex `∑ x ∈ S₃, ∑ z ∈ univ \ S₃` to `∑ j : Fin (n - 3), ∑ u : Fin 3`
      let gEdge : Fin n → Fin n → ℝ := fun x z =>
        max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yj +
            stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z) -
        max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yPrev +
            stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z)
      change ∑ x ∈ S₃, ∑ z ∈ Finset.univ \ S₃, gEdge x z = _
      rw [hS₃_compl_img, hS₃_eq_img,
          Finset.sum_image (by intro a _ b _ h; exact Fin.ext (by simpa using h))]
      have hinner_img : ∀ u : Fin 3,
          (∑ z ∈ Finset.univ.image (fun j : Fin (n - 3) => (⟨3 + j.val, by omega⟩ : Fin n)),
            gEdge ⟨u.val, by omega⟩ z) =
          ∑ j : Fin (n - 3), gEdge ⟨u.val, by omega⟩ ⟨3 + j.val, by omega⟩ := fun u =>
        Finset.sum_image (by intro a _ b _ h; exact Fin.ext (by simp at h; omega))
      simp_rw [hinner_img]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [termJ]
      rw [if_pos hZ0]
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only [gEdge]
      -- Evaluate `pot x = triVertPot`, apply 1D Abel summation in `nn2 z`, and rewrite `lt_nn2_iff`
      have hpu := hpot_iso Z hZ0 u
      have hduz : rescaledDist (join Z) ⟨u.val, hu_lt u⟩ ⟨3 + j.val, h3j_lt j⟩ =
          sqN * euclidDist (Z j) (Y u) := by
        unfold rescaledDist
        rw [hjoin_Y Z u, hjoin_Z Z j, euclidDist_symm]
      rw [hpu, hduz]
      have hgt_rj : toR rj < sqN * euclidDist (Z j) (Y u) := by
        rw [← hduz]
        exact hcl ⟨u.val, hu_lt u⟩ ((hS₃_mem _).mpr u.isLt)
          ⟨3 + j.val, h3j_lt j⟩ (fun hm => Nat.not_lt.mpr (Nat.le_add_right 3 j.val) ((hS₃_mem _).mp hm))
      have hp_nn : 0 ≤ triVertPot rho w L pt u := by
        fin_cases u <;> exact stepPot_nonneg hpot _
      have hclear_u : triVertPot rho w L pt u + toR yj < sqN * euclidDist (Z j) (Y u) := by
        have h1 := htriVertPot_le_ev u
        have h2 : 0 ≤ toR (evalStepPot rho w b.l1) := hp_nn.trans h1
        have h3 : 0 ≤ toR yj := hyPrev_r_nn.trans hy_le
        linarith only [h1, h2, h3, hhalf_r, hgt_rj]
      let f : ℝ → ℝ := fun t =>
        max 0 (triVertPot rho w L pt u + toR yj + t - sqN * euclidDist (Z j) (Y u)) -
        max 0 (triVertPot rho w L pt u + toR yPrev + t - sqN * euclidDist (Z j) (Y u))
      have hf0 : f 0 = 0 := by
        dsimp only [f]
        rw [add_zero, add_zero, max_eq_left (by linarith only [hclear_u]),
            max_eq_left (by linarith only [hclear_u, hy_le]), sub_self]
      have habel := stepPot_abel_1d hpot f hf0 (nn2 hn3 (rescaledDist (join Z)) ⟨3 + j.val, h3j_lt j⟩)
      dsimp only [f] at habel
      rw [habel]
      refine Finset.sum_congr rfl fun k _ => ?_
      change triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
          (sqN * euclidDist (Z j) (Y u)) k.val *
        (if toR (rho.getD k.val 0) < nn2 hn3 (rescaledDist (join Z)) ⟨3 + j.val, h3j_lt j⟩
          then 1 else 0) = _
      congr 1
      -- Rewrite `toR ρ_k < nn2 ... ⟨3 + j, _⟩` via `lt_nn2_iff` and partition `univ.erase z` by `S₃`
      refine if_congr ((lt_nn2_iff hn3 (rescaledDist (join Z)) ⟨3 + j.val, h3j_lt j⟩
        (toR (rho.getD k.val 0))).trans ?_) rfl rfl
      have hcard_eq : ((Finset.univ.erase (⟨3 + j.val, h3j_lt j⟩ : Fin n)).filter
            fun i => rescaledDist (join Z) ⟨3 + j.val, h3j_lt j⟩ i ≤ toR (rho.getD k.val 0)).card =
          mHit k (Z j) +
            ((Finset.univ.erase j).filter fun j' : Fin (n - 3) => Z j' ∈ D_phys k (Z j)).card := by
        let Fset := (Finset.univ.erase (⟨3 + j.val, h3j_lt j⟩ : Fin n)).filter
          fun i => rescaledDist (join Z) ⟨3 + j.val, h3j_lt j⟩ i ≤ toR (rho.getD k.val 0)
        rw [← Finset.card_filter_add_card_filter_not (s := Fset) (p := fun i => i ∈ S₃)]
        congr 1
        · -- `Fset.filter (· ∈ S₃)` bijects with `Finset.univ.filter (fun u : Fin 3 => ...)`
          have himg : Fset.filter (fun i => i ∈ S₃) =
              (Finset.univ.filter fun u' : Fin 3 =>
                sqN * euclidDist (Z j) (Y u') ≤ toR (rho.getD k.val 0)).image
                (fun u' : Fin 3 => (⟨u'.val, hu_lt u'⟩ : Fin n)) := by
            ext i
            simp only [Fset, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
              true_and, hS₃_mem, Finset.mem_image, Fin.ext_iff]
            constructor
            · rintro ⟨⟨hne, hle⟩, hi3⟩
              refine ⟨⟨i.val, hi3⟩, ?_, rfl⟩
              unfold rescaledDist at hle
              have hij : join Z i = Y ⟨i.val, hi3⟩ := by convert hjoin_Y Z ⟨i.val, hi3⟩ using 2
              rw [hjoin_Z, hij] at hle; exact hle
            · rintro ⟨u', hu', hiu⟩
              have hi_eq : i = ⟨u'.val, hu_lt u'⟩ := Fin.ext hiu.symm
              subst hi_eq
              refine ⟨⟨Fin.ne_of_val_ne (Nat.ne_of_lt (lt_of_lt_of_le u'.isLt (Nat.le_add_right 3 j.val))),
                ?_⟩, u'.isLt⟩
              unfold rescaledDist
              rw [hjoin_Z, hjoin_Y]; exact hu'
          rw [himg, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]
        · -- `Fset.filter (· ∉ S₃)` bijects with `(Finset.univ.erase j).filter (fun j' => Z j' ∈ D_phys k (Z j))`
          have hρ_nn : 0 ≤ toR (rho.getD k.val 0) := toR_nonneg (hpot.rho_nonneg k.isLt)
          have hZ_notU : ∀ j' : Fin (n - 3), Z j' ∉ U_phys := by
            intro j' hj'
            have hpos : 0 < hitCount Z U_phys :=
              Finset.card_pos.mpr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩⟩
            exact Nat.ne_of_gt hpos hZ0
          have himg : Fset.filter (fun i => i ∉ S₃) =
              ((Finset.univ.erase j).filter fun j' : Fin (n - 3) => Z j' ∈ D_phys k (Z j)).image
                (fun j' : Fin (n - 3) => (⟨3 + j'.val, h3j_lt j'⟩ : Fin n)) := by
            ext i
            simp only [Fset, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
              hS₃_mem, not_lt, Finset.mem_image, Fin.ext_iff]
            constructor
            · rintro ⟨⟨hne, hle⟩, hi3⟩
              have hi_sub : i.val - 3 < n - 3 := Nat.sub_lt_sub_right hi3 i.isLt
              refine ⟨⟨i.val - 3, hi_sub⟩,
                ⟨fun he => hne (Fin.ext (by
                    have hv : i.val - 3 = j.val := congrArg Fin.val he
                    change i.val = 3 + j.val; rw [← hv, Nat.add_sub_of_le hi3])), ?_⟩,
                Nat.add_sub_of_le hi3⟩
              refine ⟨?_, hZ_notU _⟩
              rw [mem_disk_iff (div_nonneg hρ_nn (le_of_lt hsqN_pos)), le_div_iff₀' hsqN_pos,
                  euclidDist_symm]
              unfold rescaledDist at hle
              have hij : join Z i = Z ⟨i.val - 3, hi_sub⟩ := by
                convert hjoin_Z Z ⟨i.val - 3, hi_sub⟩ using 2
                exact Fin.ext (Nat.add_sub_of_le hi3).symm
              rw [hjoin_Z, hij] at hle; exact hle
            · rintro ⟨j', ⟨hjne, hjD⟩, hij⟩
              have hi_eq : i = ⟨3 + j'.val, h3j_lt j'⟩ := Fin.ext hij.symm
              subst hi_eq
              refine ⟨⟨fun he => hjne (Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))), ?_⟩,
                Nat.le_add_right 3 j'.val⟩
              unfold rescaledDist
              rw [hjoin_Z, hjoin_Z, euclidDist_symm]
              have hle := (mem_disk_iff (div_nonneg hρ_nn (le_of_lt hsqN_pos))).mp hjD.1
              exact (le_div_iff₀' hsqN_pos).mp hle
          rw [himg, Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))]
      rw [hcard_eq]
    · have hncl : ¬ (∀ x ∈ S₃, ∀ z ∉ S₃, toR rj < rescaledDist (join Z) x z) :=
        fun h => hZ0 ((hclear_iff Z).mp h)
      rw [if_neg hncl, if_neg hZ0]
      have hsum0 : ∑ j : Fin (n - 3), termJ j Z = 0 :=
        Finset.sum_eq_zero fun j _ => by dsimp only [termJ]; rw [if_neg hZ0]
      rw [hsum0, sub_zero]
  have hptwise_int : ∫ Z : Fin (n - 3) → Pt,
      (if ∀ x ∈ S₃, ∀ z ∉ S₃, toR rj < rescaledDist (join Z) x z then
        2 * (toR yj - toR yPrev) -
          ∑ x ∈ S₃, ∑ z ∈ Finset.univ \ S₃,
            (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yj +
                stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z) -
             max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yPrev +
                stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z))
      else 0) ∂(unitSquarePi (n - 3)) =
      ∫ Z : Fin (n - 3) → Pt,
        ((if hitCount Z U_phys = 0 then 2 * (toR yj - toR yPrev) else 0) -
          ∑ j : Fin (n - 3), termJ j Z) ∂(unitSquarePi (n - 3)) :=
    congrArg (fun f => ∫ Z : Fin (n - 3) → Pt, f Z ∂(unitSquarePi (n - 3))) (funext hptwise)
  change ∫ Z : Fin (n - 3) → Pt,
      (if ∀ x ∈ S₃, ∀ z ∉ S₃, toR rj < rescaledDist (join Z) x z then
        2 * (toR yj - toR yPrev) -
          ∑ x ∈ S₃, ∑ z ∈ Finset.univ \ S₃,
            (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yj +
                stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z) -
             max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) x) + toR yPrev +
                stepPot rho w (nn2 (by omega) (rescaledDist (join Z)) z) - rescaledDist (join Z) x z))
      else 0) ∂(unitSquarePi (n - 3)) = _
  rw [hptwise_int]
  -- Integrability of the two parts on `unitSquarePi (n - 3)`
  have hmeas_hcU : Measurable (fun Z : Fin (n - 3) → Pt => hitCount Z U_phys) := by
    have heq : (fun Z : Fin (n - 3) → Pt => hitCount Z U_phys) =
        fun Z => ∑ i : Fin (n - 3), if Z i ∈ U_phys then 1 else 0 := by
      funext Z; unfold hitCount; rw [Finset.card_filter]
    rw [heq]
    exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (hU_meas.preimage (measurable_pi_apply i)) measurable_const measurable_const
  have hint_const : Integrable (fun Z : Fin (n - 3) → Pt =>
      if hitCount Z U_phys = 0 then 2 * (toR yj - toR yPrev) else 0) (unitSquarePi (n - 3)) := by
    refine Integrable.of_bound
      (Measurable.ite (hmeas_hcU (MeasurableSet.singleton 0)) measurable_const measurable_const).aestronglyMeasurable
      (2 * (toR yj - toR yPrev)) (Filter.Eventually.of_forall fun Z => ?_)
    have h2dy_nn : 0 ≤ 2 * (toR yj - toR yPrev) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hy_le)
    split_ifs
    · rw [Real.norm_of_nonneg h2dy_nn]
    · rw [norm_zero]; exact h2dy_nn
  -- Apply `integral_termJ_eq` for integrability, exchangeability, Fubini, and inner survival probs!
  let coeffQ : Fin 3 → Fin rho.size → Pt → ℝ := fun u k q =>
    triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
      (sqN * euclidDist q (Y u)) k.val
  have hmHit_meas : ∀ k : Fin rho.size, Measurable (mHit k) := by
    intro k
    have heq : mHit k = fun q => ∑ u' : Fin 3,
        if sqN * euclidDist q (Y u') ≤ toR (rho.getD k.val 0) then 1 else 0 := by
      funext q; dsimp only [mHit]; rw [Finset.card_filter]
    rw [heq]
    refine Finset.measurable_sum _ fun u' _ => ?_
    have hd' : Measurable (fun q : Pt => sqN * euclidDist q (Y u')) :=
      measurable_const.mul (measurable_euclidDist.comp (measurable_id.prodMk measurable_const))
    exact Measurable.ite (measurableSet_le hd' measurable_const) measurable_const measurable_const
  have hcoeffQ_meas : ∀ (u : Fin 3) (k : Fin rho.size), Measurable (coeffQ u k) := by
    intro u k
    dsimp only [coeffQ]; unfold triCrossCoeff
    have hd : Measurable (fun q : Pt => sqN * euclidDist q (Y u)) :=
      measurable_const.mul (measurable_euclidDist.comp (measurable_id.prodMk measurable_const))
    exact ((measurable_const.max (measurable_const.sub hd)).sub
      (measurable_const.max (measurable_const.sub hd))).sub
      ((measurable_const.max (measurable_const.sub hd)).sub
        (measurable_const.max (measurable_const.sub hd)))
  have htermJ_eval := integral_termJ_eq hn hU_meas hmHit_meas
    (fun k : Fin rho.size => toR (rho.getD k.val 0) / sqN) hcoeffQ_meas
    (sub_nonneg.mpr hy_le)
    (fun u k q => triCrossCoeff_nonneg hpot hy_le k)
    (fun u k q => triCrossCoeff_le hy_le w k.val)
  rw [integral_sub hint_const (integrable_finsetSum _ fun j _ => htermJ_eval.1 j),
      integral_finsetSum _ fun j _ => htermJ_eval.1 j]
  -- Evaluate Term 1
  have hterm1 : ∫ Z : Fin (n - 3) → Pt,
      (if hitCount Z U_phys = 0 then 2 * (toR yj - toR yPrev) else 0) ∂(unitSquarePi (n - 3)) =
      2 * (toR yj - toR yPrev) * (1 - unionDiskArea P (toR rj) / (n : ℝ)) ^ (n - 3) := by
    have hmul : (fun Z : Fin (n - 3) → Pt =>
        if hitCount Z U_phys = 0 then 2 * (toR yj - toR yPrev) else 0) =
        fun Z => (2 * (toR yj - toR yPrev)) * (if hitCount Z U_phys = 0 then (1 : ℝ) else 0) := by
      funext Z; split_ifs <;> ring
    rw [hmul, integral_const_mul, prob_hitCount_eq_zero (n - 3) hU_meas, hU_area]
  rw [hterm1, htermJ_eval.2]
  dsimp only [coeffQ]
  -- Define the canonical integrand on `Pt` in physical coordinates `q` (via `Φ⁻¹ q`!)
  -- Using `hRbuf_ext`, whenever `triCrossCoeff ≠ 0`, `D_phys k q ⊆ unitSquare` and `q ∈ unitSquare`!
  let Φinv : Pt → Pt := fun q =>
    let dx := (q.1 - (Y 0).1) / invSqN
    let dy := (q.2 - (Y 0).2) / invSqN
    let u : Pt := (c * dx + s * dy, -s * dx + c * dy)
    if refl then (u.1, -u.2) else u
  have hΦ_Φinv : ∀ q : Pt, Φ (Φinv q) = q := by
    intro q
    have hne : invSqN ≠ 0 := ne_of_gt hinvSqN_pos
    dsimp only [Φ, triEmbed, Φinv]
    cases refl <;> simp only [↓reduceIte, Bool.false_eq_true] <;> apply Prod.ext
    · have h : (Y 0).1 + invSqN * (c * (c * ((q.1 - (Y 0).1) / invSqN) + s * ((q.2 - (Y 0).2) / invSqN)) -
          s * (-s * ((q.1 - (Y 0).1) / invSqN) + c * ((q.2 - (Y 0).2) / invSqN))) - q.1 =
          (c ^ 2 + s ^ 2 - 1) * (q.1 - (Y 0).1) := by field_simp [hne]; ring
      linear_combination h + (q.1 - (Y 0).1) * hcs
    · have h : (Y 0).2 + invSqN * (s * (c * ((q.1 - (Y 0).1) / invSqN) + s * ((q.2 - (Y 0).2) / invSqN)) +
          c * (-s * ((q.1 - (Y 0).1) / invSqN) + c * ((q.2 - (Y 0).2) / invSqN))) - q.2 =
          (c ^ 2 + s ^ 2 - 1) * (q.2 - (Y 0).2) := by field_simp [hne]; ring
      linear_combination h + (q.2 - (Y 0).2) * hcs
    · have h : (Y 0).1 + invSqN * (c * (c * ((q.1 - (Y 0).1) / invSqN) + s * ((q.2 - (Y 0).2) / invSqN)) -
          s * -(-(-s * ((q.1 - (Y 0).1) / invSqN) + c * ((q.2 - (Y 0).2) / invSqN)))) - q.1 =
          (c ^ 2 + s ^ 2 - 1) * (q.1 - (Y 0).1) := by field_simp [hne]; ring
      linear_combination h + (q.1 - (Y 0).1) * hcs
    · have h : (Y 0).2 + invSqN * (s * (c * ((q.1 - (Y 0).1) / invSqN) + s * ((q.2 - (Y 0).2) / invSqN)) +
          c * -(-(-s * ((q.1 - (Y 0).1) / invSqN) + c * ((q.2 - (Y 0).2) / invSqN)))) - q.2 =
          (c ^ 2 + s ^ 2 - 1) * (q.2 - (Y 0).2) := by field_simp [hne]; ring
      linear_combination h + (q.2 - (Y 0).2) * hcs
  have hΦinv_Φ : ∀ v : Pt, Φinv (Φ v) = v := fun v => hΦ_inj (hΦ_Φinv (Φ v))
  have hΦinv_meas : Measurable Φinv := by
    dsimp only [Φinv]; cases refl <;> simp only [↓reduceIte, Bool.false_eq_true] <;> fun_prop
  -- Canonical integrand in `q`
  let G_canon : Pt → ℝ := fun q =>
    if Φinv q ∉ triUnion P (toR rj) then
      triCondIntegrand rho w yPrev rj yj n L pt (Φinv q)
    else 0
  -- Support lemma: whenever `triCrossCoeff ≠ 0`, `disk q (ρ_k / sqN) ⊆ unitSquare` and `q ∈ unitSquare`
  have hsupp_disk : ∀ (q : Pt) (u : Fin 3) (k : Fin rho.size),
      triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
        (sqN * euclidDist q (Y u)) k.val ≠ 0 →
      disk q (toR (rho.getD k.val 0) / sqN) ⊆ unitSquare ∧ q ∈ unitSquare := by
    intro q u k hne
    have hlt : sqN * euclidDist q (Y u) <
        triVertPot rho w L pt u + toR yj + toR (w.getD k.val 0) := by
      by_contra hge; push Not at hge
      exact hne (triCrossCoeff_eq_zero_of_le hpot hy_le k hge)
    have hpu_le : triVertPot rho w L pt u ≤ toR (w.getD (rho.size - 1) 0) := by
      fin_cases u <;> exact stepPot_le_wMax hpot _
    have hwk_le : toR (w.getD k.val 0) ≤ toR (w.getD (rho.size - 1) 0) :=
      toR_le_toR (hpot.w_le_of_le (Nat.le_sub_one_of_lt k.isLt) (Nat.sub_lt hpot.size_pos Nat.one_pos))
    have hYu0 : sqN * euclidDist (Y u) (Y 0) ≤ toR b.l1 := by
      rw [← hΦ_P u, ← hΦ_P 0, hΦ_dist]
      exact triVerts_dist_zero_le hb hYbox u
    have hq0 : sqN * euclidDist q (Y 0) ≤
        toR b.l1 + 2 * toR (w.getD (rho.size - 1) 0) + toR yj := by
      have htri := euclidDist_triangle q (Y u) (Y 0)
      have hmul : sqN * euclidDist q (Y 0) ≤ sqN * euclidDist q (Y u) + sqN * euclidDist (Y u) (Y 0) := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left htri (le_of_lt hsqN_pos)
      linarith only [hmul, hlt, hpu_le, hwk_le, hYu0]
    have hρ_nn : 0 ≤ toR (rho.getD k.val 0) := toR_nonneg (hpot.rho_nonneg k.isLt)
    have hsub : disk q (toR (rho.getD k.val 0) / sqN) ⊆ unitSquare := by
      intro x hx
      have hxq : sqN * euclidDist x q ≤ toR (rho.getD k.val 0) :=
        (le_div_iff₀' hsqN_pos).mp ((mem_disk_iff (div_nonneg hρ_nn (le_of_lt hsqN_pos))).mp hx)
      have hx0 : sqN * euclidDist x (Y 0) ≤ Rbuf := by
        have htri := euclidDist_triangle x q (Y 0)
        have hmul : sqN * euclidDist x (Y 0) ≤ sqN * euclidDist x q + sqN * euclidDist q (Y 0) := by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left htri (le_of_lt hsqN_pos)
        linarith only [hmul, hxq, hq0, hRbuf_ext k.val k.isLt]
      exact disk_subset_unitSquare hY0 (div_nonneg hRbuf_pos (le_of_lt hsqN_pos)) le_rfl
        ((mem_disk_iff (div_nonneg hRbuf_pos (le_of_lt hsqN_pos))).mpr
          ((le_div_iff₀' hsqN_pos).mpr hx0))
    refine ⟨hsub, hsub ?_⟩
    change sqDist q q ≤ (toR (rho.getD k.val 0) / sqN) ^ 2
    rw [sqDist_self]; positivity
  -- Pointwise equality of inner-integral expression and `G_canon` for ALL `q : Pt`!
  have hG_eq : ∀ q : Pt,
      (if q ∉ U_phys then
        ∑ u : Fin 3, ∑ k : Fin rho.size,
          triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (sqN * euclidDist q (Y u)) k.val *
          (if mHit k q ≥ 2 then 0
           else if mHit k q = 1 then
             (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 4)
           else
             (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 4) +
               ((n - 4 : ℕ) : ℝ) * (unitSquareMeasure (D_phys k q)).toReal *
                 (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 5))
      else 0) = G_canon q := by
    intro q
    have hq_mem_U : q ∈ U_phys ↔ Φinv q ∈ triUnion P (toR rj) := by
      rw [hU_img]
      constructor
      · rintro ⟨v, hv, hqv⟩; rwa [← hqv, hΦinv_Φ]
      · intro hv; exact ⟨Φinv q, hv, hΦ_Φinv q⟩
    dsimp only [G_canon]
    by_cases hq : q ∉ U_phys
    · have hq' : Φinv q ∉ triUnion P (toR rj) := fun h => hq (hq_mem_U.mpr h)
      rw [if_pos hq, if_pos hq']
      unfold triCondIntegrand
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun k _ => ?_
      have hdist_eq : sqN * euclidDist q (Y u) = euclidDist (Φinv q) (P u) := by
        conv_lhs => rw [← hΦ_Φinv q, hΦ_dist_P]
      rw [hdist_eq]
      by_cases hc0 : triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
          (euclidDist (Φinv q) (P u)) k.val = 0
      · rw [hc0, zero_mul, zero_mul]
      · congr 1
        have hD_sub_sq : disk q (toR (rho.getD k.val 0) / sqN) ⊆ unitSquare :=
          (hsupp_disk q u k (by rwa [hdist_eq])).1
        have hD_sub : D_phys k q ⊆ unitSquare := Set.sdiff_subset.trans hD_sub_sq
        have hρ_nn : 0 ≤ toR (rho.getD k.val 0) := toR_nonneg (hpot.rho_nonneg k.isLt)
        have hD_img : D_phys k q = Φ '' (disk (Φinv q) (toR (rho.getD k.val 0)) \ triUnion P (toR rj)) := by
          ext x
          obtain ⟨v, rfl⟩ := hΦ_surj x
          simp only [D_phys, Set.mem_sdiff, Set.mem_image]
          constructor
          · rintro ⟨hxD, hxU⟩
            refine ⟨v, ⟨?_, fun hvU => hxU (hU_img ▸ ⟨v, hvU, rfl⟩)⟩, rfl⟩
            rw [mem_disk_iff hρ_nn, ← hΦ_dist v (Φinv q), hΦ_Φinv q]
            exact (le_div_iff₀' hsqN_pos).mp
              ((mem_disk_iff (div_nonneg hρ_nn (le_of_lt hsqN_pos))).mp hxD)
          · rintro ⟨v', ⟨hvD, hvU⟩, hvv'⟩
            have hveq : v' = v := hΦ_inj hvv'
            subst hveq
            refine ⟨?_, fun hxU => hvU (by rcases hU_img ▸ hxU with ⟨w', hw', hweq⟩; rwa [← hΦ_inj hweq])⟩
            rw [mem_disk_iff (div_nonneg hρ_nn (le_of_lt hsqN_pos)), le_div_iff₀' hsqN_pos,
                ← hΦ_Φinv q, hΦ_dist]
            exact (mem_disk_iff hρ_nn).mp hvD
        have hm_D : MeasurableSet (disk (Φinv q) (toR (rho.getD k.val 0)) \ triUnion P (toR rj)) :=
          (measurableSet_disk _ _).diff (MeasurableSet.iUnion fun u' => measurableSet_disk _ _)
        have hD_area : (unitSquareMeasure (D_phys k q)).toReal =
            (volume (disk (Φinv q) (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal / (n : ℝ) := by
          rw [unitSquareMeasure_eq_volume_of_subset hD_sub, hD_img,
              volume_image_triEmbed (Y 0) hcs refl hinvSqN_pos hm_D,
              hinvSqN_sq, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
          ring
        have hUD_area : (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal =
            (unionDiskArea P (toR rj) +
              (volume (disk (Φinv q) (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal) / (n : ℝ) := by
          have hdisj : Disjoint U_phys (D_phys k q) := disjoint_sdiff_self_right
          have hm_Dp : MeasurableSet (D_phys k q) := (measurableSet_disk _ _).diff hU_meas
          rw [measure_union hdisj hm_Dp,
              ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
              hU_area, hD_area, add_div]
        have hmHit_eq : mHit k q = triHitCount P (Φinv q) (toR (rho.getD k.val 0)) := by
          unfold triHitCount
          dsimp only [mHit]
          congr 1; ext u'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          conv_lhs => rw [← hΦ_Φinv q, hΦ_dist_P]
        rw [hmHit_eq, hD_area, hUD_area]
        rfl
    · have hq' : ¬ (Φinv q ∉ triUnion P (toR rj)) := fun h => h (hq_mem_U.mp (not_not.mp hq))
      rw [if_neg hq, if_neg hq']
  have hG_int_eq : (∫ q : Pt,
      (if q ∉ U_phys then
        ∑ u : Fin 3, ∑ k : Fin rho.size,
          triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (sqN * euclidDist q (Y u)) k.val *
          (if mHit k q ≥ 2 then 0
           else if mHit k q = 1 then
             (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 4)
           else
             (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 4) +
               ((n - 4 : ℕ) : ℝ) * (unitSquareMeasure (D_phys k q)).toReal *
                 (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 5))
      else 0) ∂unitSquareMeasure) = ∫ q : Pt, G_canon q ∂unitSquareMeasure :=
    congrArg (fun f => ∫ q : Pt, f q ∂unitSquareMeasure) (funext hG_eq)
  change 2 * (toR yj - toR yPrev) * (1 - unionDiskArea P (toR rj) / (n : ℝ)) ^ (n - 3) -
      ((n - 3 : ℕ) : ℝ) *
        (∫ q : Pt,
          (if q ∉ U_phys then
            ∑ u : Fin 3, ∑ k : Fin rho.size,
              triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
                (sqN * euclidDist q (Y u)) k.val *
              (if mHit k q ≥ 2 then 0
               else if mHit k q = 1 then
                 (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 4)
               else
                 (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 4) +
                   ((n - 4 : ℕ) : ℝ) * (unitSquareMeasure (D_phys k q)).toReal *
                     (1 - (unitSquareMeasure (U_phys ∪ D_phys k q)).toReal) ^ (n - 5))
          else 0) ∂unitSquareMeasure) = _
  rw [hG_int_eq]
  -- `G_canon q = 0` for all `q ∉ unitSquare`, so `∫ q, G_canon q ∂unitSquareMeasure = ∫ q, G_canon q ∂volume`
  have hG_supp : ∀ q : Pt, q ∉ unitSquare → G_canon q = 0 := by
    intro q hq_out
    dsimp only [G_canon]
    split_ifs with hq
    · rfl
    · unfold triCondIntegrand
      refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun k _ => ?_
      have hc0 : triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
          (euclidDist (Φinv q) (P u)) k.val = 0 := by
        by_contra hne
        have hdist_eq : sqN * euclidDist q (Y u) = euclidDist (Φinv q) (P u) := by
          conv_lhs => rw [← hΦ_Φinv q, hΦ_dist_P]
        exact hq_out (hsupp_disk q u k (by rwa [hdist_eq])).2
      rw [hc0, zero_mul]
  have hG_meas : Measurable G_canon := by
    have hm_tri_c : MeasurableSet (triUnion P (toR rj))ᶜ :=
      (MeasurableSet.iUnion fun u => measurableSet_disk _ _).compl
    have hcomp := (measurable_triCondIntegrand_v rho w yPrev rj yj n L pt).comp hΦinv_meas
    rw [Function.comp_def] at hcomp
    exact Measurable.ite (hm_tri_c.preimage hΦinv_meas) hcomp measurable_const
  have h_us_eq_vol : ∫ q : Pt, G_canon q ∂unitSquareMeasure = ∫ q : Pt, G_canon q ∂volume := by
    have hm_us : MeasurableSet unitSquare := measurableSet_Icc.prod measurableSet_Icc
    rw [← restrict_unitSquare_eq, ← integral_indicator hm_us]
    congr 1; funext q
    by_cases hq : q ∈ unitSquare
    · exact Set.indicator_of_mem hq G_canon
    · rw [Set.indicator_of_notMem hq, hG_supp q hq]
  rw [h_us_eq_vol, integral_triEmbed (Y 0) hcs refl hinvSqN_pos hG_meas, hinvSqN_sq]
  have hG_Φ : ∀ v : Pt, G_canon (triEmbed (Y 0) c s refl invSqN v) =
      ((triUnion P (toR rj))ᶜ).indicator (triCondIntegrand rho w yPrev rj yj n L pt) v := by
    intro v
    change (if Φinv (Φ v) ∉ triUnion P (toR rj) then
        triCondIntegrand rho w yPrev rj yj n L pt (Φinv (Φ v)) else 0) = _
    rw [hΦinv_Φ v]
    by_cases hv : v ∉ triUnion P (toR rj)
    · rw [Set.indicator_of_mem hv, if_pos hv]
    · rw [Set.indicator_of_notMem hv, if_neg hv]
  simp_rw [hG_Φ]
  have hm_compl : MeasurableSet (triUnion P (toR rj))ᶜ :=
    (MeasurableSet.iUnion fun u => measurableSet_disk _ _).compl
  rw [integral_indicator hm_compl]
  change 2 * (toR yj - toR yPrev) * (1 - unionDiskArea P (toR rj) / (n : ℝ)) ^ (n - 3) -
      ((n - 3 : ℕ) : ℝ) * (1 / (n : ℝ) *
        ∫ v in (triUnion P (toR rj))ᶜ, triCondIntegrand rho w yPrev rj yj n L pt v) =
      2 * (toR yj - toR yPrev) * (1 - unionDiskArea P (toR rj) / (n : ℝ)) ^ (n - 3) -
      (((n - 3 : ℕ) : ℝ) / (n : ℝ)) *
        ∫ v in (triUnion P (toR rj))ᶜ, triCondIntegrand rho w yPrev rj yj n L pt v
  ring

/-! ## Section 5: Uniform Bound and Pointwise Convergence (`triCondVal_bound`, `tendsto_triCondVal`) -/

private def triSuppRad (rho w : Array Int) (b : BoxCert) (yj : Int) : ℝ :=
  toR b.l1 + 2 * toR (w.getD (rho.size - 1) 0) + toR yj

private def triDomConst (rho : Array Int) (yPrev yj : Int) : ℝ :=
  3 * (rho.size : ℝ) * (toR yj - toR yPrev) *
    (1 + Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2)

private def triMinN (rho : Array Int) (rj : Int) : ℕ :=
  max 5 (Nat.ceil (3 * Real.pi * (toR rj) ^ 2 +
    Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2) + 1)

private lemma triCondIntegrand_dom {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) {yPrev rj yj : Int}
    (hyPrev_nn : 0 ≤ yPrev) (hy : yPrev < yj) (hrj_l1 : b.l1 < rj)
    {n : ℕ} (hn : triMinN rho rj ≤ n)
    {L : ℝ} {pt : Pt} (hmem : (L, pt) ∈ boxRegion b) (v : Pt) :
    0 ≤ triCondIntegrand rho w yPrev rj yj n L pt v ∧
    triCondIntegrand rho w yPrev rj yj n L pt v ≤
      (disk (0, 0) (triSuppRad rho w b yj)).indicator (fun _ => triDomConst rho yPrev yj) v := by
  have hsize := hpot.size_pos
  have hwMax_nn : 0 ≤ toR (w.getD (rho.size - 1) 0) := toR_nonneg (hpot.w_nonneg (by omega))
  have hrhoMax_nn : 0 ≤ toR (rho.getD (rho.size - 1) 0) := toR_nonneg (hpot.rho_nonneg (by omega))
  have hl1_pos : 0 < toR b.l1 := by
    simpa [toR_zero] using toR_lt_toR (lt_trans hb.l0_pos hb.l0_lt_l1)
  have hrj_nn : 0 ≤ toR rj := le_of_lt (hl1_pos.trans (toR_lt_toR hrj_l1))
  have hy_le : toR yPrev ≤ toR yj := toR_le_toR (le_of_lt hy)
  have hyj_nn : 0 ≤ toR yj := (toR_nonneg hyPrev_nn).trans hy_le
  have hR_nn : 0 ≤ triSuppRad rho w b yj := by unfold triSuppRad; linarith
  have hn1 : 1 ≤ n := by unfold triMinN at hn; omega
  have hM_le_n : 3 * Real.pi * (toR rj) ^ 2 +
      Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2 ≤ (n : ℝ) := by
    have h1 : Nat.ceil (3 * Real.pi * (toR rj) ^ 2 +
        Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2) ≤ n := by
      unfold triMinN at hn; omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hA_nn : 0 ≤ unionDiskArea (triVerts L pt) (toR rj) := ENNReal.toReal_nonneg
  have hA_le : unionDiskArea (triVerts L pt) (toR rj) ≤ 3 * Real.pi * (toR rj) ^ 2 :=
    unionDiskArea_triVerts_le (triVerts L pt) hrj_nn
  have hV_le : ∀ k : Fin rho.size,
      (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal ≤
        Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2 := fun k => by
    have hρk_nn : 0 ≤ toR (rho.getD k.val 0) := toR_nonneg (hpot.rho_nonneg k.isLt)
    have hρk_le : toR (rho.getD k.val 0) ≤ toR (rho.getD (rho.size - 1) 0) :=
      toR_le_toR (hpot.rho_le_of_le (by omega) (by omega))
    have h1 := disk_sdiff_volume_le v (triUnion (triVerts L pt) (toR rj)) hρk_nn
    have hsq : toR (rho.getD k.val 0) ^ 2 ≤ (toR (rho.getD (rho.size - 1) 0)) ^ 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hAV_le : ∀ k : Fin rho.size,
      unionDiskArea (triVerts L pt) (toR rj) +
        (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal ≤
        (n : ℝ) := fun k => by linarith [hA_le, hV_le k, hM_le_n]
  unfold triCondIntegrand
  constructor
  · refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (triCrossCoeff_nonneg hpot hy_le k)
        (finExtSurvProb_nonneg hn1 _ ENNReal.toReal_nonneg (hAV_le k))
  · by_cases hv : v ∈ disk (0, 0) (triSuppRad rho w b yj)
    · rw [Set.indicator_of_mem hv]
      calc ∑ u : Fin 3, ∑ k : Fin rho.size,
            triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
              (euclidDist v (triVerts L pt u)) k.val *
            finExtSurvProb n (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
              (unionDiskArea (triVerts L pt) (toR rj))
              (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal
          ≤ ∑ _u : Fin 3, ∑ _k : Fin rho.size,
              (toR yj - toR yPrev) * (1 + Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2) := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun k _ => ?_
            refine mul_le_mul (triCrossCoeff_le hy_le w k.val)
              ((finExtSurvProb_le hn1 _ hA_nn ENNReal.toReal_nonneg (hAV_le k)).trans
                (by linarith [hV_le k]))
              (finExtSurvProb_nonneg hn1 _ ENNReal.toReal_nonneg (hAV_le k))
              (by linarith)
        _ = triDomConst rho yPrev yj := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              triDomConst]
            ring
    · rw [Set.indicator_of_notMem hv]
      have hgt : triSuppRad rho w b yj < euclidDist v (0, 0) := by
        rw [mem_disk_iff hR_nn] at hv; exact not_le.mp hv
      have hsum0 : ∑ u : Fin 3, ∑ k : Fin rho.size,
          triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val *
          finExtSurvProb n (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
            (unionDiskArea (triVerts L pt) (toR rj))
            (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal = 0 := by
        refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun k _ => ?_
        have hpu_le : triVertPot rho w L pt u ≤ toR (w.getD (rho.size - 1) 0) := by
          fin_cases u <;> exact stepPot_le_wMax hpot _
        have hwk_le : toR (w.getD k.val 0) ≤ toR (w.getD (rho.size - 1) 0) :=
          toR_le_toR (hpot.w_le_of_le (by omega) (by omega))
        have hP0 : euclidDist (triVerts L pt u) (0, 0) ≤ toR b.l1 :=
          triVerts_dist_zero_le hb hmem u
        have htri := euclidDist_triangle v (triVerts L pt u) (0, 0)
        have hd_ge : triVertPot rho w L pt u + toR yj + toR (w.getD k.val 0) ≤
            euclidDist v (triVerts L pt u) := by
          unfold triSuppRad at hgt; linarith
        rw [triCrossCoeff_eq_zero_of_le hpot hy_le k hd_ge, zero_mul]
      rw [hsum0]

lemma triCondVal_bound {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) {yPrev rj yj : Int}
    (hyPrev_nn : 0 ≤ yPrev) (hy : yPrev < yj) (hrj_l1 : b.l1 < rj)
    (_hhalf : 2 * (evalStepPot rho w b.l1 + yj) ≤ rj) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ L pt, (L, pt) ∈ boxRegion b →
      ‖triCondVal rho w yPrev rj yj n L pt‖ ≤ C := by
  have hsize := hpot.size_pos
  have hwMax_nn : 0 ≤ toR (w.getD (rho.size - 1) 0) := toR_nonneg (hpot.w_nonneg (by omega))
  have hl1_pos : 0 < toR b.l1 := by
    simpa [toR_zero] using toR_lt_toR (lt_trans hb.l0_pos hb.l0_lt_l1)
  have hrj_nn : 0 ≤ toR rj := le_of_lt (hl1_pos.trans (toR_lt_toR hrj_l1))
  have hy_le : toR yPrev ≤ toR yj := toR_le_toR (le_of_lt hy)
  have hyj_nn : 0 ≤ toR yj := (toR_nonneg hyPrev_nn).trans hy_le
  have hR_nn : 0 ≤ triSuppRad rho w b yj := by unfold triSuppRad; linarith
  have hB_nn : 0 ≤ triDomConst rho yPrev yj := by unfold triDomConst; positivity
  let C : ℝ := 2 * (toR yj - toR yPrev) +
    triDomConst rho yPrev yj * (Real.pi * (triSuppRad rho w b yj) ^ 2)
  refine ⟨C, by dsimp only [C]; positivity, triMinN rho rj, fun n hn L pt hmem => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 5 ≤ n := le_trans (le_max_left _ _) hn
    exact_mod_cast (by omega : 0 < n)
  have hA_nn : 0 ≤ unionDiskArea (triVerts L pt) (toR rj) := ENNReal.toReal_nonneg
  have hA_le_n : unionDiskArea (triVerts L pt) (toR rj) ≤ (n : ℝ) := by
    have h1 := unionDiskArea_triVerts_le (triVerts L pt) hrj_nn
    have hM_le : 3 * Real.pi * (toR rj) ^ 2 +
        Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2 ≤ (n : ℝ) := by
      have hc : Nat.ceil (3 * Real.pi * (toR rj) ^ 2 +
          Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2) ≤ n := by
        unfold triMinN at hn; omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast hc)
    have h2 : 0 ≤ Real.pi * (toR (rho.getD (rho.size - 1) 0)) ^ 2 := by positivity
    linarith
  have hpow_nn : 0 ≤ (1 - unionDiskArea (triVerts L pt) (toR rj) / (n : ℝ)) ^ (n - 3) :=
    pow_nonneg (by rw [sub_nonneg, div_le_one hn_pos]; exact hA_le_n) _
  have hpow_le : (1 - unionDiskArea (triVerts L pt) (toR rj) / (n : ℝ)) ^ (n - 3) ≤ 1 :=
    pow_le_one₀ (by rw [sub_nonneg, div_le_one hn_pos]; exact hA_le_n)
      (by have : 0 ≤ unionDiskArea (triVerts L pt) (toR rj) / (n : ℝ) :=
            div_nonneg hA_nn (le_of_lt hn_pos); linarith)
  have hterm1_norm :
      ‖2 * (toR yj - toR yPrev) * (1 - unionDiskArea (triVerts L pt) (toR rj) / (n : ℝ)) ^ (n - 3)‖ ≤
      2 * (toR yj - toR yPrev) := by
    rw [Real.norm_of_nonneg (mul_nonneg (by linarith) hpow_nn)]
    nlinarith
  have hfrac_nn : 0 ≤ ((n - 3 : ℕ) : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos)
  have hfrac_le : ((n - 3 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn_pos]; exact_mod_cast Nat.sub_le n 3
  let g_dom : Pt → ℝ :=
    (disk (0, 0) (triSuppRad rho w b yj)).indicator (fun _ => triDomConst rho yPrev yj)
  have hvol_disk_lt : volume (disk (0, 0) (triSuppRad rho w b yj)) < ⊤ := by
    rw [volume_disk (0, 0) hR_nn]; exact ENNReal.ofReal_lt_top
  have hg_int_vol : Integrable g_dom volume :=
    (integrableOn_const (hs := hvol_disk_lt.ne)).integrable_indicator (measurableSet_disk _ _)
  have hg_integral : ∫ v : Pt, g_dom v ∂volume =
      triDomConst rho yPrev yj * (Real.pi * (triSuppRad rho w b yj) ^ 2) := by
    dsimp only [g_dom]
    rw [integral_indicator_const _ (measurableSet_disk _ _), smul_eq_mul,
        Measure.real, volume_disk (0, 0) hR_nn, ENNReal.toReal_ofReal (by positivity), mul_comm]
  have hH_nn : ∀ v : Pt, 0 ≤ triCondIntegrand rho w yPrev rj yj n L pt v := fun v =>
    (triCondIntegrand_dom hpot hb hyPrev_nn hy hrj_l1 hn hmem v).1
  have hH_le : ∀ v : Pt, triCondIntegrand rho w yPrev rj yj n L pt v ≤ g_dom v := fun v =>
    (triCondIntegrand_dom hpot hb hyPrev_nn hy hrj_l1 hn hmem v).2
  have hH_int : IntegrableOn (triCondIntegrand rho w yPrev rj yj n L pt)
      (triUnion (triVerts L pt) (toR rj))ᶜ volume := by
    refine Integrable.mono' hg_int_vol.restrict
      (measurable_triCondIntegrand_v rho w yPrev rj yj n L pt).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (hH_nn v)]
    exact hH_le v
  have hI_nn : 0 ≤ ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
      triCondIntegrand rho w yPrev rj yj n L pt v :=
    integral_nonneg hH_nn
  have hI_le : ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
      triCondIntegrand rho w yPrev rj yj n L pt v ≤
      triDomConst rho yPrev yj * (Real.pi * (triSuppRad rho w b yj) ^ 2) := by
    calc ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
          triCondIntegrand rho w yPrev rj yj n L pt v
        ≤ ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ, g_dom v :=
          integral_mono hH_int hg_int_vol.restrict hH_le
      _ ≤ ∫ v : Pt, g_dom v ∂volume :=
          setIntegral_le_integral hg_int_vol
            (Filter.Eventually.of_forall fun v => Set.indicator_nonneg (fun _ _ => hB_nn) v)
      _ = triDomConst rho yPrev yj * (Real.pi * (triSuppRad rho w b yj) ^ 2) := hg_integral
  have hterm2_norm :
      ‖(((n - 3 : ℕ) : ℝ) / (n : ℝ)) *
        ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
          triCondIntegrand rho w yPrev rj yj n L pt v‖ ≤
      triDomConst rho yPrev yj * (Real.pi * (triSuppRad rho w b yj) ^ 2) := by
    rw [Real.norm_of_nonneg (mul_nonneg hfrac_nn hI_nn)]
    calc (((n - 3 : ℕ) : ℝ) / (n : ℝ)) *
            ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
              triCondIntegrand rho w yPrev rj yj n L pt v
        ≤ 1 * (triDomConst rho yPrev yj * (Real.pi * (triSuppRad rho w b yj) ^ 2)) :=
          mul_le_mul hfrac_le hI_le hI_nn zero_le_one
      _ = triDomConst rho yPrev yj * (Real.pi * (triSuppRad rho w b yj) ^ 2) := one_mul _
  change ‖2 * (toR yj - toR yPrev) * (1 - unionDiskArea (triVerts L pt) (toR rj) / (n : ℝ)) ^ (n - 3) -
      (((n - 3 : ℕ) : ℝ) / (n : ℝ)) *
        ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
          triCondIntegrand rho w yPrev rj yj n L pt v‖ ≤ C
  calc ‖2 * (toR yj - toR yPrev) * (1 - unionDiskArea (triVerts L pt) (toR rj) / (n : ℝ)) ^ (n - 3) -
        (((n - 3 : ℕ) : ℝ) / (n : ℝ)) *
          ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
            triCondIntegrand rho w yPrev rj yj n L pt v‖
      ≤ ‖2 * (toR yj - toR yPrev) * (1 - unionDiskArea (triVerts L pt) (toR rj) / (n : ℝ)) ^ (n - 3)‖ +
        ‖(((n - 3 : ℕ) : ℝ) / (n : ℝ)) *
          ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
            triCondIntegrand rho w yPrev rj yj n L pt v‖ := norm_sub_le _ _
    _ ≤ C := by dsimp only [C]; linarith

theorem tendsto_triCondVal {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) {yPrev rj yj : Int}
    (hyPrev_nn : 0 ≤ yPrev) (hy : yPrev < yj) (hrj_l1 : b.l1 < rj)
    (_hhalf : 2 * (evalStepPot rho w b.l1 + yj) ≤ rj)
    {L : ℝ} {pt : Pt} (hmem : (L, pt) ∈ boxRegion b) :
    Tendsto (fun n : ℕ => triCondVal rho w yPrev rj yj n L pt) atTop
      (nhds (Real.exp (-unionDiskArea (triVerts L pt) (toR rj)) *
        (2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L pt))) := by
  have hsize := hpot.size_pos
  have hwMax_nn : 0 ≤ toR (w.getD (rho.size - 1) 0) := toR_nonneg (hpot.w_nonneg (by omega))
  have hl1_pos : 0 < toR b.l1 := by
    simpa [toR_zero] using toR_lt_toR (lt_trans hb.l0_pos hb.l0_lt_l1)
  have hy_le : toR yPrev ≤ toR yj := toR_le_toR (le_of_lt hy)
  have hyj_nn : 0 ≤ toR yj := (toR_nonneg hyPrev_nn).trans hy_le
  have hR_nn : 0 ≤ triSuppRad rho w b yj := by unfold triSuppRad; linarith
  -- First term converges to `2 * (yj - yPrev) * exp (-A)`
  have ht1 : Tendsto (fun n : ℕ =>
        2 * (toR yj - toR yPrev) * (1 - unionDiskArea (triVerts L pt) (toR rj) / (n : ℝ)) ^ (n - 3))
      atTop (nhds (2 * (toR yj - toR yPrev) * Real.exp (-unionDiskArea (triVerts L pt) (toR rj)))) :=
    tendsto_const_nhds.mul (tendsto_one_sub_div_pow (unionDiskArea (triVerts L pt) (toR rj)) 3)
  -- Prefactor `(n - 3) / n → 1`
  have ht_pref : Tendsto (fun n : ℕ => ((n - 3 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) :=
    tendsto_nat_sub_div_self 3
  -- Integral term converges by DCT on `volume.restrict (triUnion (triVerts L pt) (toR rj))ᶜ`
  let μ : Measure Pt := volume.restrict (triUnion (triVerts L pt) (toR rj))ᶜ
  let H_lim : Pt → ℝ := fun v =>
    ∑ u : Fin 3, ∑ k : Fin rho.size,
      triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
        (euclidDist v (triVerts L pt u)) k.val *
      (Real.exp (-unionDiskArea (triVerts L pt) (toR rj)) *
        extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
          (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal)
  let g_dom : Pt → ℝ :=
    (disk (0, 0) (triSuppRad rho w b yj)).indicator (fun _ => triDomConst rho yPrev yj)
  have hvol_disk_lt : volume (disk (0, 0) (triSuppRad rho w b yj)) < ⊤ := by
    rw [volume_disk (0, 0) hR_nn]; exact ENNReal.ofReal_lt_top
  have hg_int : Integrable g_dom μ :=
    ((integrableOn_const (hs := hvol_disk_lt.ne)).integrable_indicator
      (measurableSet_disk _ _)).restrict
  have hH_aem : ∀ n : ℕ, AEStronglyMeasurable (triCondIntegrand rho w yPrev rj yj n L pt) μ := fun n =>
    (measurable_triCondIntegrand_v rho w yPrev rj yj n L pt).aestronglyMeasurable
  let N : ℕ := triMinN rho rj
  have ht_int_shift : Tendsto
      (fun m : ℕ => ∫ v : Pt, triCondIntegrand rho w yPrev rj yj (m + N) L pt v ∂μ)
      atTop (nhds (∫ v : Pt, H_lim v ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence g_dom (fun m => hH_aem (m + N)) hg_int ?_ ?_
    · intro m
      refine Filter.Eventually.of_forall fun v => ?_
      have hbounds := triCondIntegrand_dom hpot hb hyPrev_nn hy hrj_l1 (Nat.le_add_left N m) hmem v
      rw [Real.norm_of_nonneg hbounds.1]
      exact hbounds.2
    · refine Filter.Eventually.of_forall fun v => ?_
      unfold triCondIntegrand
      dsimp only [H_lim]
      refine tendsto_finsetSum _ fun u _ => tendsto_finsetSum _ fun k _ => ?_
      refine tendsto_const_nhds.mul ?_
      exact (tendsto_finExtSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
        (unionDiskArea (triVerts L pt) (toR rj))
        (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal).comp
        (tendsto_add_atTop_nat N)
  have ht_int : Tendsto
      (fun n : ℕ => ∫ v : Pt, triCondIntegrand rho w yPrev rj yj n L pt v ∂μ)
      atTop (nhds (∫ v : Pt, H_lim v ∂μ)) :=
    (tendsto_add_atTop_iff_nat N).mp ht_int_shift
  have hH_lim_eq : ∫ v : Pt, H_lim v ∂μ =
      Real.exp (-unionDiskArea (triVerts L pt) (toR rj)) * levelCrossPen rho w yPrev rj yj L pt := by
    have hfac : ∀ v : Pt, H_lim v = Real.exp (-unionDiskArea (triVerts L pt) (toR rj)) *
        ∑ u : Fin 3, ∑ k : Fin rho.size,
          triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val *
          extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
            (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal := by
      intro v
      dsimp only [H_lim]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hfac, integral_const_mul]
    rfl
  rw [hH_lim_eq] at ht_int
  have hfull := ht1.sub (ht_pref.mul ht_int)
  have hlim_eq : 2 * (toR yj - toR yPrev) * Real.exp (-unionDiskArea (triVerts L pt) (toR rj)) -
      1 * (Real.exp (-unionDiskArea (triVerts L pt) (toR rj)) *
        levelCrossPen rho w yPrev rj yj L pt) =
      Real.exp (-unionDiskArea (triVerts L pt) (toR rj)) *
        (2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L pt) := by
    ring
  rw [hlim_eq] at hfull
  exact hfull

end

end BHHBounds.Dual
