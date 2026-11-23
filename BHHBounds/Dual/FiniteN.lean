import BHHBounds.Asymptotics
import BHHBounds.Dual.TwoFactorMoat
import BHHBounds.Dual.PoissonIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-`n` Probability, Geometry, and Pointwise Dual Infrastructure

Provides all finite-`n` building blocks for `BHHBounds/Dual/Expectation.lean`:
1. Elementary binomial-to-Poisson convergence limits (`tendsto_one_sub_div_pow`,
   `tendsto_binom_one`, `tendsto_binom_two`, `tendsto_one_sub_inv_sqrt_sq`).
2. `unitSquarePi` splitting (`measurePreserving_splitFinEquiv`), exchangeability
   (`measurePreserving_perm_pi`), product expectation (`integral_prod_unitSquarePi`), and exact
   i.i.d. hit-count expectations (`prob_hitCount_eq_zero`, `prob_hitCount_eq_one`,
   `prob_hitCount_le_one`, `prob_twoSet_joint`, `prob_tri_ext_surv`).
3. Interior buffer `interiorBox`, `disk_subset_unitSquare`, and exact rigid-motion/scaling
   area identities for disks and triangle disk unions inside `[0, 1]²`.
4. Second-nearest-neighbor distance `nn2`, canonical triangle coordinates `canonShape`,
   uniqueness of canonical ordering, and the deterministic pointwise dual lower bound
   `pointwise_dual_lower_bound` for `n ≥ 4`.
-/

open MeasureTheory Set Real Filter Finset
open scoped ENNReal Classical
open BHHBounds.Geometry
open BHHBounds.Cert

namespace BHHBounds.Dual

noncomputable section

/-! ## Section 1: Elementary Binomial-to-Poisson Limits -/

/-- `(1 - a / n) ^ n → exp (-a)` as `n → ∞`, proved directly from `Real.hasDerivAt_log`. -/
lemma tendsto_one_sub_div_pow_self (a : ℝ) :
    Tendsto (fun n : ℕ => (1 - a / (n : ℝ)) ^ n) atTop (nhds (Real.exp (-a))) := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hdiv : Tendsto (fun n : ℕ => -a / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hlog_deriv : Tendsto (fun h : ℝ => (Real.log (1 + h) - Real.log 1) / h) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
      have h := (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero
      simpa [smul_eq_mul, div_eq_inv_mul] using h
    have hne : ∀ᶠ n : ℕ in atTop, -a / (n : ℝ) ∈ ({0}ᶜ : Set ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact div_ne_zero (neg_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr (by omega))
    have hcomp : Tendsto (fun n : ℕ => (Real.log (1 + (-a / (n : ℝ))) - Real.log 1) / (-a / (n : ℝ)))
        atTop (nhds 1) :=
      hlog_deriv.comp (tendsto_nhdsWithin_iff.mpr ⟨hdiv, hne⟩)
    have hmul : Tendsto (fun n : ℕ => (-a) * ((Real.log (1 + (-a / (n : ℝ))) - Real.log 1) / (-a / (n : ℝ))))
        atTop (nhds ((-a) * 1)) := tendsto_const_nhds.mul hcomp
    rw [mul_one] at hmul
    have hexp : Tendsto (fun n : ℕ => Real.exp ((-a) * ((Real.log (1 + (-a / (n : ℝ))) - Real.log 1) / (-a / (n : ℝ)))))
        atTop (nhds (Real.exp (-a))) := (Real.continuous_exp.tendsto (-a)).comp hmul
    refine hexp.congr' ?_
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < 1 - a / (n : ℝ) := by
      have h1 : Tendsto (fun n : ℕ => 1 - a / (n : ℝ)) atTop (nhds 1) := by
        simpa using tendsto_const_nhds.sub ((tendsto_const_nhds (x := a)).div_atTop tendsto_natCast_atTop_atTop)
      exact h1.eventually (Ioi_mem_nhds zero_lt_one)
    filter_upwards [Filter.eventually_ge_atTop 1, hpos] with n hn h1p
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1eq : 1 + (-a / (n : ℝ)) = 1 - a / (n : ℝ) := by ring
    rw [h1eq, Real.log_one, sub_zero]
    have hsimp : (-a) * (Real.log (1 - a / (n : ℝ)) / (-a / (n : ℝ))) = Real.log (1 - a / (n : ℝ)) * (n : ℝ) := by
      field_simp [ha, hn0]
    rw [hsimp, ← Real.rpow_def_of_pos h1p, Real.rpow_natCast]

/-- `(1 - a / n) ^ (n - c) → exp (-a)` as `n → ∞` for any fixed shift `c : ℕ`. -/
lemma tendsto_one_sub_div_pow (a : ℝ) (c : ℕ) :
    Tendsto (fun n : ℕ => (1 - a / (n : ℝ)) ^ (n - c)) atTop (nhds (Real.exp (-a))) := by
  have h1 := tendsto_one_sub_div_pow_self a
  have hdiv : Tendsto (fun n : ℕ => a / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun n : ℕ => 1 - a / (n : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hdiv
  have hpowc : Tendsto (fun n : ℕ => (1 - a / (n : ℝ)) ^ c) atTop (nhds 1) := by
    simpa using hbase.pow c
  have hquot : Tendsto (fun n : ℕ => (1 - a / (n : ℝ)) ^ n / (1 - a / (n : ℝ)) ^ c)
      atTop (nhds (Real.exp (-a) / 1)) := h1.div hpowc one_ne_zero
  rw [div_one] at hquot
  refine hquot.congr' ?_
  have hne : ∀ᶠ n : ℕ in atTop, 1 - a / (n : ℝ) ≠ 0 :=
    hbase.eventually (isOpen_ne.mem_nhds one_ne_zero)
  filter_upwards [Filter.eventually_ge_atTop c, hne] with n hnc hnz
  have hpow : (1 - a / (n : ℝ)) ^ n = (1 - a / (n : ℝ)) ^ (n - c) * (1 - a / (n : ℝ)) ^ c := by
    rw [← pow_add, Nat.sub_add_cancel hnc]
  rw [hpow, mul_div_cancel_right₀ _ (pow_ne_zero c hnz)]

lemma tendsto_nat_sub_div_self (c : ℕ) :
    Tendsto (fun n : ℕ => ((n - c : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) := by
  have h0 : Tendsto (fun n : ℕ => (c : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => 1 - (c : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub h0
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (max c 1)] with n hn
  have hnc : c ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := le_trans (le_max_right c 1) hn; omega)
  rw [Nat.cast_sub hnc, sub_div, div_self hn0]

lemma tendsto_binom_one (a b : ℝ) (c : ℕ) :
    Tendsto (fun n : ℕ => ((n - c : ℕ) : ℝ) * (b / (n : ℝ)) * (1 - a / (n : ℝ)) ^ (n - c - 1))
      atTop (nhds (b * Real.exp (-a))) := by
  have h1 := tendsto_nat_sub_div_self c
  have h2 := tendsto_one_sub_div_pow a (c + 1)
  have hprod : Tendsto (fun n : ℕ => (((n - c : ℕ) : ℝ) / (n : ℝ)) * b * (1 - a / (n : ℝ)) ^ (n - (c + 1)))
      atTop (nhds (1 * b * Real.exp (-a))) := (h1.mul tendsto_const_nhds).mul h2
  rw [one_mul] at hprod
  refine hprod.congr fun n => ?_
  rw [Nat.sub_sub]; ring

lemma tendsto_binom_two (a b u : ℝ) (c : ℕ) :
    Tendsto (fun n : ℕ => ((n - c : ℕ) : ℝ) * ((n - (c + 1) : ℕ) : ℝ) *
        (a / (n : ℝ)) * (b / (n : ℝ)) * (1 - u / (n : ℝ)) ^ (n - (c + 2)))
      atTop (nhds (a * b * Real.exp (-u))) := by
  have h1 := tendsto_nat_sub_div_self c
  have h2 := tendsto_nat_sub_div_self (c + 1)
  have h3 := tendsto_one_sub_div_pow u (c + 2)
  have hprod : Tendsto (fun n : ℕ =>
      (((n - c : ℕ) : ℝ) / (n : ℝ)) * (((n - (c + 1) : ℕ) : ℝ) / (n : ℝ)) * (a * b) *
        (1 - u / (n : ℝ)) ^ (n - (c + 2)))
      atTop (nhds (1 * 1 * (a * b) * Real.exp (-u))) :=
    ((h1.mul h2).mul tendsto_const_nhds).mul h3
  simp only [one_mul] at hprod
  refine hprod.congr fun n => ?_; ring

lemma tendsto_one_sub_inv_sqrt_sq (R : ℝ) :
    Tendsto (fun n : ℕ => (1 - 2 * R / Real.sqrt (n : ℝ)) ^ 2) atTop (nhds 1) := by
  have hsq : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => 2 * R / Real.sqrt (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsq
  have hsub : Tendsto (fun n : ℕ => 1 - 2 * R / Real.sqrt (n : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hdiv
  simpa using hsub.pow 2

/-! ## Section 2: `unitSquarePi` Splitting, Exchangeability, and Hit-Count Expectations -/

lemma measurePreserving_perm_pi (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun X : Fin n → Pt => X ∘ σ) (unitSquarePi n) (unitSquarePi n) := by
  unfold unitSquarePi
  have h := MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin n => unitSquareMeasure) σ.symm
  refine ⟨by fun_prop, ?_⟩
  have hfun : (fun X : Fin n → Pt => X ∘ σ) = MeasurableEquiv.piCongrLeft (fun _ => Pt) σ.symm := by
    funext X i; simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  rw [hfun]; exact h.map_eq

/-- Splitting `Fin (k + m) → Pt` into `(Fin k → Pt) × (Fin m → Pt)` preserves `unitSquarePi`. -/
def splitFinEquiv (k m : ℕ) : (Fin (k + m) → Pt) ≃ (Fin k → Pt) × (Fin m → Pt) where
  toFun X := (fun i => X (Fin.castAdd m i), fun j => X (Fin.natAdd k j))
  invFun p := Fin.append p.1 p.2
  left_inv X := by
    funext t
    dsimp only
    by_cases ht : t.val < k
    · have he : t = Fin.castAdd m ⟨t.val, ht⟩ := Fin.ext rfl
      rw [he, Fin.append_left]
    · have he : t = Fin.natAdd k ⟨t.val - k, by omega⟩ := Fin.ext (by simp; omega)
      rw [he, Fin.append_right]
  right_inv p := by
    apply Prod.ext
    · funext i; exact Fin.append_left p.1 p.2 i
    · funext j; exact Fin.append_right p.1 p.2 j

lemma measurable_splitFinEquiv (k m : ℕ) : Measurable (splitFinEquiv k m) :=
  (measurable_pi_lambda _ fun i => measurable_pi_apply (Fin.castAdd m i)).prodMk
    (measurable_pi_lambda _ fun j => measurable_pi_apply (Fin.natAdd k j))

lemma measurable_splitFinEquiv_symm (k m : ℕ) : Measurable (splitFinEquiv k m).symm := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases ht : t.val < k
  · have heq : (fun p : (Fin k → Pt) × (Fin m → Pt) => (splitFinEquiv k m).symm p t) =
        fun p => p.1 ⟨t.val, ht⟩ := by
      funext p
      have he : t = Fin.castAdd m ⟨t.val, ht⟩ := Fin.ext rfl
      conv_lhs => rw [he]
      exact Fin.append_left p.1 p.2 ⟨t.val, ht⟩
    rw [heq]; exact (measurable_pi_apply _).comp measurable_fst
  · have heq : (fun p : (Fin k → Pt) × (Fin m → Pt) => (splitFinEquiv k m).symm p t) =
        fun p => p.2 ⟨t.val - k, by omega⟩ := by
      funext p
      have he : t = Fin.natAdd k ⟨t.val - k, by omega⟩ := Fin.ext (by simp; omega)
      conv_lhs => rw [he]
      exact Fin.append_right p.1 p.2 ⟨t.val - k, by omega⟩
    rw [heq]; exact (measurable_pi_apply _).comp measurable_snd

lemma measurePreserving_splitFinEquiv_symm (k m : ℕ) :
    MeasurePreserving (splitFinEquiv k m).symm ((unitSquarePi k).prod (unitSquarePi m))
      (unitSquarePi (k + m)) := by
  refine ⟨measurable_splitFinEquiv_symm k m, ?_⟩
  symm
  unfold unitSquarePi
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_splitFinEquiv_symm k m) (MeasurableSet.univ_pi hs)]
  have hpre : (splitFinEquiv k m).symm ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ fun i : Fin k => s (Fin.castAdd m i)) ×ˢ
        (Set.pi Set.univ fun j : Fin m => s (Fin.natAdd k j)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun j => ?_⟩
      · have hi := h (Fin.castAdd m i); rwa [show (splitFinEquiv k m).symm p (Fin.castAdd m i) = p.1 i from Fin.append_left p.1 p.2 i] at hi
      · have hj := h (Fin.natAdd k j); rwa [show (splitFinEquiv k m).symm p (Fin.natAdd k j) = p.2 j from Fin.append_right p.1 p.2 j] at hj
    · rintro ⟨h1, h2⟩ t
      by_cases ht : t.val < k
      · have he : t = Fin.castAdd m ⟨t.val, ht⟩ := Fin.ext rfl
        rw [he, show (splitFinEquiv k m).symm p (Fin.castAdd m ⟨t.val, ht⟩) = p.1 ⟨t.val, ht⟩ from Fin.append_left p.1 p.2 _]
        exact h1 ⟨t.val, ht⟩
      · have he : t = Fin.natAdd k ⟨t.val - k, by omega⟩ := Fin.ext (by simp; omega)
        rw [he, show (splitFinEquiv k m).symm p (Fin.natAdd k ⟨t.val - k, by omega⟩) = p.2 ⟨t.val - k, by omega⟩ from Fin.append_right p.1 p.2 _]
        exact h2 ⟨t.val - k, by omega⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

lemma measurePreserving_splitFinEquiv (k m : ℕ) :
    MeasurePreserving (splitFinEquiv k m) (unitSquarePi (k + m))
      ((unitSquarePi k).prod (unitSquarePi m)) := by
  refine ⟨measurable_splitFinEquiv k m, ?_⟩
  rw [← (measurePreserving_splitFinEquiv_symm k m).map_eq,
      Measure.map_map (measurable_splitFinEquiv k m) (measurable_splitFinEquiv_symm k m)]
  have hcomp : (splitFinEquiv k m ∘ (splitFinEquiv k m).symm) = id := by
    ext p : 1; exact (splitFinEquiv k m).apply_symm_apply p
  rw [hcomp, Measure.map_id]

/-- Exact factorization of product integrals on `unitSquarePi m`. -/
lemma integral_prod_unitSquarePi : ∀ (m : ℕ) (f : Fin m → Pt → ℝ),
    (∀ i, Integrable (f i) unitSquareMeasure) →
    ∫ Z : Fin m → Pt, (∏ i : Fin m, f i (Z i)) ∂(unitSquarePi m) =
      ∏ i : Fin m, ∫ x : Pt, f i x ∂unitSquareMeasure := by
  intro m
  induction m with
  | zero =>
    intro f _
    simp [Measure.real]
  | succ k ih =>
    intro f hf
    have hmp := measurePreserving_splitFinEquiv_symm k 1
    rw [← hmp.map_eq, integral_map (measurable_splitFinEquiv_symm k 1).aemeasurable]
    · have hcongr : (fun p : (Fin k → Pt) × (Fin 1 → Pt) =>
          ∏ i : Fin (k + 1), f i ((splitFinEquiv k 1).symm p i)) =
          fun p => (∏ i : Fin k, f (Fin.castAdd 1 i) (p.1 i)) * f (Fin.natAdd k 0) (p.2 0) := by
        ext p
        rw [Fin.prod_univ_add, Fin.prod_univ_one]
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          simp [splitFinEquiv, Fin.append_left]
        · simp [splitFinEquiv, Fin.append_right]
      rw [hcongr, MeasureTheory.integral_prod_mul (f := fun x : Fin k → Pt => ∏ i : Fin k, f (Fin.castAdd 1 i) (x i))
          (g := fun y : Fin 1 → Pt => f (Fin.natAdd k 0) (y 0)), ih _ fun i => hf (Fin.castAdd 1 i)]
      have h1 : ∫ q : Fin 1 → Pt, f (Fin.natAdd k 0) (q 0) ∂(unitSquarePi 1) =
          ∫ x : Pt, f (Fin.natAdd k 0) x ∂unitSquareMeasure := by
        have heq : MeasurePreserving (fun q : Fin 1 → Pt => q 0) (unitSquarePi 1) unitSquareMeasure :=
          MeasureTheory.measurePreserving_eval (fun _ : Fin 1 => unitSquareMeasure) 0
        rw [← heq.map_eq, integral_map (measurable_pi_apply 0).aemeasurable
          (by rw [heq.map_eq]; exact (hf (Fin.natAdd k 0)).aestronglyMeasurable)]
      rw [h1, Fin.prod_univ_add, Fin.prod_univ_one]
    · rw [hmp.map_eq]
      have hmeas : ∀ i : Fin (k + 1), AEStronglyMeasurable (fun Z : Fin (k + 1) → Pt => f i (Z i))
          (unitSquarePi (k + 1)) := fun i =>
        (hf i).aestronglyMeasurable.comp_measurePreserving
          (show MeasurePreserving (fun Z : Fin (k + 1) → Pt => Z i) (unitSquarePi (k + 1)) unitSquareMeasure from
            MeasureTheory.measurePreserving_eval (fun _ : Fin (k + 1) => unitSquareMeasure) i)
      exact Finset.aestronglyMeasurable_fun_prod _ fun i _ => hmeas i

/-- Indicator integrability on `unitSquareMeasure`. -/
lemma integrable_indicator_one_unitSquare {A : Set Pt} [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    Integrable (fun x : Pt => if x ∈ A then (1 : ℝ) else 0) unitSquareMeasure := by
  have heq : (fun x : Pt => if x ∈ A then (1 : ℝ) else 0) = A.indicator (fun _ => (1 : ℝ)) := by
    ext x; by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  rw [heq]; exact (integrable_const (1 : ℝ)).indicator hA

lemma integral_indicator_one_unitSquare {A : Set Pt} [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    ∫ x : Pt, (if x ∈ A then (1 : ℝ) else 0) ∂unitSquareMeasure = (unitSquareMeasure A).toReal := by
  have heq : (fun x : Pt => if x ∈ A then (1 : ℝ) else 0) = A.indicator (fun _ => (1 : ℝ)) := by
    ext x; by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  rw [heq, integral_indicator_const _ hA, smul_eq_mul, mul_one, Measure.real]

lemma unitSquareMeasure_compl_toReal {A : Set Pt} (hA : MeasurableSet A) :
    (unitSquareMeasure Aᶜ).toReal = 1 - (unitSquareMeasure A).toReal := by
  rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le (prob_le_one) ENNReal.one_ne_top, ENNReal.toReal_one]

/-- Count of points among `Z : Fin m → Pt` falling into `A`. -/
def hitCount {m : ℕ} (Z : Fin m → Pt) (A : Set Pt) : ℕ :=
  (Finset.univ.filter fun i : Fin m => Z i ∈ A).card

/-- Exact probability that `hitCount Z A = 0` for `m` i.i.d. uniform points in `[0, 1]²`. -/
lemma prob_hitCount_eq_zero (m : ℕ) {A : Set Pt} (hA : MeasurableSet A) :
    ∫ Z : Fin m → Pt, (if hitCount Z A = 0 then (1 : ℝ) else 0) ∂(unitSquarePi m) =
      (1 - (unitSquareMeasure A).toReal) ^ m := by
  have heq : (fun Z : Fin m → Pt => if hitCount Z A = 0 then (1 : ℝ) else 0) =
      fun Z => ∏ i : Fin m, if Z i ∈ Aᶜ then (1 : ℝ) else 0 := by
    ext Z
    by_cases h0 : hitCount Z A = 0
    · rw [if_pos h0]
      have hall : ∀ i : Fin m, Z i ∈ Aᶜ := by
        intro i hi
        have hpos : 0 < hitCount Z A := Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        omega
      simp [hall]
    · rw [if_neg h0]
      have hex : ∃ i : Fin m, Z i ∈ A := by
        obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
        exact ⟨i, (Finset.mem_filter.mp hi).2⟩
      obtain ⟨i, hi⟩ := hex
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
  rw [heq, integral_prod_unitSquarePi m (fun _ x => if x ∈ Aᶜ then (1 : ℝ) else 0)
      (fun _ => integrable_indicator_one_unitSquare hA.compl)]
  simp_rw [integral_indicator_one_unitSquare hA.compl, unitSquareMeasure_compl_toReal hA]
  simp

/-- Exact probability that `hitCount Z A = 1` for `m` i.i.d. uniform points in `[0, 1]²`. -/
lemma prob_hitCount_eq_one (m : ℕ) {A : Set Pt} (hA : MeasurableSet A) :
    ∫ Z : Fin m → Pt, (if hitCount Z A = 1 then (1 : ℝ) else 0) ∂(unitSquarePi m) =
      (m : ℝ) * (unitSquareMeasure A).toReal * (1 - (unitSquareMeasure A).toReal) ^ (m - 1) := by
  have heq : (fun Z : Fin m → Pt => if hitCount Z A = 1 then (1 : ℝ) else 0) =
      fun Z => ∑ i₀ : Fin m, ∏ i : Fin m,
        if i = i₀ then (if Z i ∈ A then (1 : ℝ) else 0) else (if Z i ∈ Aᶜ then (1 : ℝ) else 0) := by
    ext Z
    by_cases h1 : hitCount Z A = 1
    · rw [if_pos h1]
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
      have hmem : ∀ i : Fin m, Z i ∈ A ↔ i = i₀ := by
        intro i; constructor
        · intro hi
          have : i ∈ ({i₀} : Finset (Fin m)) := hi₀ ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
          exact Finset.mem_singleton.mp this
        · rintro rfl
          have : i ∈ Finset.univ.filter (fun j : Fin m => Z j ∈ A) := hi₀.symm ▸ Finset.mem_singleton_self i
          exact (Finset.mem_filter.mp this).2
      rw [Finset.sum_eq_single i₀]
      · refine (Finset.prod_eq_one fun i _ => ?_).symm
        by_cases hi : i = i₀
        · subst hi; simp [(hmem i).mpr rfl]
        · simp [hi, mt (hmem i).mp hi]
      · intro j _ hj
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [mt (hmem j).mp hj])
      · intro h; exact absurd (Finset.mem_univ i₀) h
    · rw [if_neg h1]
      symm
      refine Finset.sum_eq_zero fun i₀ _ => ?_
      by_cases hi₀ : Z i₀ ∈ A
      · have hne : ∃ j : Fin m, j ≠ i₀ ∧ Z j ∈ A := by
          by_contra hall; push Not at hall
          have hcard : Finset.univ.filter (fun j : Fin m => Z j ∈ A) = {i₀} := by
            ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            exact ⟨fun hj => by_contra fun hne => hall j hne hj, fun h => h ▸ hi₀⟩
          exact h1 (by unfold hitCount; rw [hcard, Finset.card_singleton])
        obtain ⟨j, hjne, hjA⟩ := hne
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjne, hjA])
      · exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
  rw [heq]
  have hint : ∀ i₀ : Fin m, Integrable (fun Z : Fin m → Pt => ∏ i : Fin m,
      if i = i₀ then (if Z i ∈ A then (1 : ℝ) else 0) else (if Z i ∈ Aᶜ then (1 : ℝ) else 0)) (unitSquarePi m) := by
    intro i₀
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun Z => ?_)
    · refine Finset.aestronglyMeasurable_fun_prod _ fun i _ => ?_
      by_cases hi : i = i₀
      · simp only [hi, ↓reduceIte]
        exact (Measurable.ite (hA.preimage (measurable_pi_apply i₀)) measurable_const measurable_const).aestronglyMeasurable
      · simp only [hi, ↓reduceIte]
        exact (Measurable.ite (hA.compl.preimage (measurable_pi_apply i)) measurable_const measurable_const).aestronglyMeasurable
    · have hprod_nn : 0 ≤ ∏ i : Fin m,
          if i = i₀ then (if Z i ∈ A then (1 : ℝ) else 0) else (if Z i ∈ Aᶜ then (1 : ℝ) else 0) :=
        Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
      rw [Real.norm_of_nonneg hprod_nn]
      exact Finset.prod_le_one (fun i _ => by split_ifs <;> norm_num) (fun i _ => by split_ifs <;> norm_num)
  rw [integral_finsetSum _ fun i₀ _ => hint i₀]
  have hterm : ∀ i₀ : Fin m,
      ∫ Z : Fin m → Pt, (∏ i : Fin m,
        if i = i₀ then (if Z i ∈ A then (1 : ℝ) else 0) else (if Z i ∈ Aᶜ then (1 : ℝ) else 0)) ∂(unitSquarePi m) =
      (unitSquareMeasure A).toReal * (1 - (unitSquareMeasure A).toReal) ^ (m - 1) := by
    intro i₀
    rw [integral_prod_unitSquarePi m
      (fun i x => if i = i₀ then (if x ∈ A then (1 : ℝ) else 0) else (if x ∈ Aᶜ then (1 : ℝ) else 0))
      (fun i => by by_cases hi : i = i₀
                   · simp only [hi, ↓reduceIte]; exact integrable_indicator_one_unitSquare hA
                   · simp only [hi, ↓reduceIte]; exact integrable_indicator_one_unitSquare hA.compl)]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    simp only [↓reduceIte, integral_indicator_one_unitSquare hA]
    congr 1
    have hrest : ∀ i ∈ Finset.univ.erase i₀,
        (∫ x : Pt, (if i = i₀ then (if x ∈ A then (1 : ℝ) else 0) else (if x ∈ Aᶜ then (1 : ℝ) else 0)) ∂unitSquareMeasure) =
        1 - (unitSquareMeasure A).toReal := fun i hi => by
      have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
      simp only [hne, ↓reduceIte]
      rw [integral_indicator_one_unitSquare hA.compl, unitSquareMeasure_compl_toReal hA]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
        Finset.card_univ, Fintype.card_fin]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- Exact probability that `hitCount Z A ≤ 1` for `m` i.i.d. uniform points in `[0, 1]²`. -/
lemma prob_hitCount_le_one (m : ℕ) {A : Set Pt} (hA : MeasurableSet A) :
    ∫ Z : Fin m → Pt, (if hitCount Z A ≤ 1 then (1 : ℝ) else 0) ∂(unitSquarePi m) =
      (1 - (unitSquareMeasure A).toReal) ^ m +
        (m : ℝ) * (unitSquareMeasure A).toReal * (1 - (unitSquareMeasure A).toReal) ^ (m - 1) := by
  have heq : (fun Z : Fin m → Pt => if hitCount Z A ≤ 1 then (1 : ℝ) else 0) =
      fun Z => (if hitCount Z A = 0 then (1 : ℝ) else 0) + (if hitCount Z A = 1 then (1 : ℝ) else 0) := by
    ext Z; by_cases h0 : hitCount Z A = 0
    · simp [h0]
    · by_cases h1 : hitCount Z A = 1
      · simp [h1]
      · have h2 : ¬ hitCount Z A ≤ 1 := by omega
        simp [h0, h1, h2]
  have hint_c : ∀ k : ℕ, Integrable (fun Z : Fin m → Pt => if hitCount Z A = k then (1 : ℝ) else 0) (unitSquarePi m) := by
    intro k
    have hmeas : Measurable (fun Z : Fin m → Pt => hitCount Z A) := by
      have : (fun Z : Fin m → Pt => hitCount Z A) = fun Z => ∑ i : Fin m, if Z i ∈ A then 1 else 0 := by
        ext Z; unfold hitCount; rw [Finset.card_filter]
      rw [this]
      exact Finset.measurable_sum _ fun i _ =>
        Measurable.ite (hA.preimage (measurable_pi_apply i)) measurable_const measurable_const
    refine Integrable.of_bound
      (Measurable.ite (hmeas (MeasurableSet.singleton k)) measurable_const measurable_const).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun Z => by split_ifs <;> norm_num)
  rw [heq, integral_add (hint_c 0) (hint_c 1), prob_hitCount_eq_zero m hA, prob_hitCount_eq_one m hA]

/-- Exact probability of `hitCount Z U = 0 ∧ hitCount Z D = 1` for disjoint measurable `U, D`. -/
lemma prob_disjoint_zero_one (m : ℕ) {U D : Set Pt} (hU : MeasurableSet U) (hD : MeasurableSet D)
    (hdisj : Disjoint U D) :
    ∫ Z : Fin m → Pt, (if hitCount Z U = 0 ∧ hitCount Z D = 1 then (1 : ℝ) else 0) ∂(unitSquarePi m) =
      (m : ℝ) * (unitSquareMeasure D).toReal * (1 - (unitSquareMeasure (U ∪ D)).toReal) ^ (m - 1) := by
  have heq : (fun Z : Fin m → Pt => if hitCount Z U = 0 ∧ hitCount Z D = 1 then (1 : ℝ) else 0) =
      fun Z => ∑ i₀ : Fin m, ∏ i : Fin m,
        if i = i₀ then (if Z i ∈ D then (1 : ℝ) else 0) else (if Z i ∈ (U ∪ D)ᶜ then (1 : ℝ) else 0) := by
    ext Z
    by_cases h : hitCount Z U = 0 ∧ hitCount Z D = 1
    · rw [if_pos h]
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h.2
      have hU0 : ∀ i : Fin m, Z i ∉ U := fun i hi => by
        have : 0 < hitCount Z U := Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        omega
      have hD1 : ∀ i : Fin m, Z i ∈ D ↔ i = i₀ := by
        intro i; constructor
        · intro hi
          exact Finset.mem_singleton.mp (hi₀ ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · rintro rfl
          have hmem : i ∈ Finset.univ.filter (fun j : Fin m => Z j ∈ D) := by rw [hi₀]; exact Finset.mem_singleton_self i
          exact (Finset.mem_filter.mp hmem).2
      rw [Finset.sum_eq_single i₀]
      · refine (Finset.prod_eq_one fun i _ => ?_).symm
        by_cases hi : i = i₀
        · subst hi; simp [(hD1 i).mpr rfl]
        · simp [hi, hU0 i, mt (hD1 i).mp hi]
      · intro j _ hj
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [mt (hD1 j).mp hj])
      · intro hm; exact absurd (Finset.mem_univ i₀) hm
    · rw [if_neg h]; symm
      refine Finset.sum_eq_zero fun i₀ _ => ?_
      by_cases hi₀ : Z i₀ ∈ D
      · have hnotU : Z i₀ ∉ U := fun hu => Set.disjoint_left.mp hdisj hu hi₀
        by_cases hU0 : hitCount Z U = 0
        · have hDne1 : hitCount Z D ≠ 1 := fun h1 => h ⟨hU0, h1⟩
          have hex : ∃ j : Fin m, j ≠ i₀ ∧ Z j ∈ D := by
            by_contra hall; push Not at hall
            have hcard : Finset.univ.filter (fun j : Fin m => Z j ∈ D) = {i₀} := by
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
              exact ⟨fun hj => by_contra fun hne => hall j hne hj, fun hx => hx ▸ hi₀⟩
            exact hDne1 (by unfold hitCount; rw [hcard, Finset.card_singleton])
          obtain ⟨j, hjne, hjD⟩ := hex
          exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjne, hjD])
        · obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hU0)
          have hjU : Z j ∈ U := (Finset.mem_filter.mp hj).2
          have hjne : j ≠ i₀ := fun he => hnotU (he ▸ hjU)
          exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjne, hjU])
      · exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
  rw [heq]
  have hint : ∀ i₀ : Fin m, Integrable (fun Z : Fin m → Pt => ∏ i : Fin m,
      if i = i₀ then (if Z i ∈ D then (1 : ℝ) else 0) else (if Z i ∈ (U ∪ D)ᶜ then (1 : ℝ) else 0)) (unitSquarePi m) := by
    intro i₀
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun Z => ?_)
    · refine Finset.aestronglyMeasurable_fun_prod _ fun i _ => ?_
      by_cases hi : i = i₀
      · simp only [hi, ↓reduceIte]
        exact (Measurable.ite (hD.preimage (measurable_pi_apply i₀)) measurable_const measurable_const).aestronglyMeasurable
      · simp only [hi, ↓reduceIte]
        exact (Measurable.ite ((hU.union hD).compl.preimage (measurable_pi_apply i)) measurable_const measurable_const).aestronglyMeasurable
    · have hnn : 0 ≤ ∏ i : Fin m,
          if i = i₀ then (if Z i ∈ D then (1 : ℝ) else 0) else (if Z i ∈ (U ∪ D)ᶜ then (1 : ℝ) else 0) :=
        Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
      rw [Real.norm_of_nonneg hnn]
      exact Finset.prod_le_one (fun i _ => by split_ifs <;> norm_num) (fun i _ => by split_ifs <;> norm_num)
  rw [integral_finsetSum _ fun i₀ _ => hint i₀]
  have hterm : ∀ i₀ : Fin m,
      ∫ Z : Fin m → Pt, (∏ i : Fin m,
        if i = i₀ then (if Z i ∈ D then (1 : ℝ) else 0) else (if Z i ∈ (U ∪ D)ᶜ then (1 : ℝ) else 0)) ∂(unitSquarePi m) =
      (unitSquareMeasure D).toReal * (1 - (unitSquareMeasure (U ∪ D)).toReal) ^ (m - 1) := by
    intro i₀
    rw [integral_prod_unitSquarePi m
      (fun i x => if i = i₀ then (if x ∈ D then (1 : ℝ) else 0) else (if x ∈ (U ∪ D)ᶜ then (1 : ℝ) else 0))
      (fun i => by by_cases hi : i = i₀
                   · simp only [hi, ↓reduceIte]; exact integrable_indicator_one_unitSquare hD
                   · simp only [hi, ↓reduceIte]; exact integrable_indicator_one_unitSquare (hU.union hD).compl)]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    simp only [↓reduceIte, integral_indicator_one_unitSquare hD]
    congr 1
    have hrest : ∀ i ∈ Finset.univ.erase i₀,
        (∫ x : Pt, (if i = i₀ then (if x ∈ D then (1 : ℝ) else 0) else (if x ∈ (U ∪ D)ᶜ then (1 : ℝ) else 0)) ∂unitSquareMeasure) =
        1 - (unitSquareMeasure (U ∪ D)).toReal := fun i hi => by
      have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
      simp only [hne, ↓reduceIte]
      rw [integral_indicator_one_unitSquare (hU.union hD).compl, unitSquareMeasure_compl_toReal (hU.union hD)]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
        Finset.card_univ, Fintype.card_fin]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- Exact probability of `hitCount Z U = 0 ∧ hitCount Z D ≤ 1` for disjoint measurable `U, D`. -/
lemma prob_disjoint_zero_le_one (m : ℕ) {U D : Set Pt} (hU : MeasurableSet U) (hD : MeasurableSet D)
    (hdisj : Disjoint U D) :
    ∫ Z : Fin m → Pt, (if hitCount Z U = 0 ∧ hitCount Z D ≤ 1 then (1 : ℝ) else 0) ∂(unitSquarePi m) =
      (1 - (unitSquareMeasure (U ∪ D)).toReal) ^ m +
        (m : ℝ) * (unitSquareMeasure D).toReal * (1 - (unitSquareMeasure (U ∪ D)).toReal) ^ (m - 1) := by
  have hmeas_hc : ∀ {S : Set Pt}, MeasurableSet S → Measurable (fun Z : Fin m → Pt => hitCount Z S) := by
    intro S hS
    have : (fun Z : Fin m → Pt => hitCount Z S) = fun Z => ∑ i : Fin m, if Z i ∈ S then 1 else 0 := by
      ext Z; unfold hitCount; rw [Finset.card_filter]
    rw [this]
    exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (hS.preimage (measurable_pi_apply i)) measurable_const measurable_const
  have heq : (fun Z : Fin m → Pt => if hitCount Z U = 0 ∧ hitCount Z D ≤ 1 then (1 : ℝ) else 0) =
      fun Z => (if hitCount Z (U ∪ D) = 0 then (1 : ℝ) else 0) +
        (if hitCount Z U = 0 ∧ hitCount Z D = 1 then (1 : ℝ) else 0) := by
    ext Z
    have hUD0 : hitCount Z (U ∪ D) = 0 ↔ hitCount Z U = 0 ∧ hitCount Z D = 0 := by
      simp only [hitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
        forall_true_left, Set.mem_union, not_or, forall_and]
    by_cases hU0 : hitCount Z U = 0
    · by_cases hD0 : hitCount Z D = 0
      · simp [hUD0, hU0, hD0]
      · by_cases hD1 : hitCount Z D = 1
        · simp [hUD0, hU0, hD1]
        · have hge2 : ¬ hitCount Z D ≤ 1 := by omega
          simp [hUD0, hU0, hD0, hD1, hge2]
    · simp [hUD0, hU0]
  have hint1 : Integrable (fun Z : Fin m → Pt => if hitCount Z (U ∪ D) = 0 then (1 : ℝ) else 0) (unitSquarePi m) :=
    Integrable.of_bound (Measurable.ite ((hmeas_hc (hU.union hD)) (MeasurableSet.singleton 0))
      measurable_const measurable_const).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun Z => by split_ifs <;> norm_num)
  have hint2 : Integrable (fun Z : Fin m → Pt => if hitCount Z U = 0 ∧ hitCount Z D = 1 then (1 : ℝ) else 0) (unitSquarePi m) :=
    Integrable.of_bound (Measurable.ite (((hmeas_hc hU) (MeasurableSet.singleton 0)).inter
      ((hmeas_hc hD) (MeasurableSet.singleton 1))) measurable_const measurable_const).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun Z => by split_ifs <;> norm_num)
  rw [heq, integral_add hint1 hint2, prob_hitCount_eq_zero m (hU.union hD), prob_disjoint_zero_one m hU hD hdisj]

/-- Exact probability of `hitCount Z A = 1 ∧ hitCount Z B = 1 ∧ hitCount Z C = 0` for pairwise disjoint `A, B, C`. -/
lemma prob_disjoint_one_one_zero (m : ℕ) {A B C : Set Pt}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    ∫ Z : Fin m → Pt, (if hitCount Z A = 1 ∧ hitCount Z B = 1 ∧ hitCount Z C = 0 then (1 : ℝ) else 0) ∂(unitSquarePi m) =
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (unitSquareMeasure A).toReal * (unitSquareMeasure B).toReal *
        (1 - (unitSquareMeasure (A ∪ B ∪ C)).toReal) ^ (m - 2) := by
  let pairs : Finset (Fin m × Fin m) := Finset.univ.filter fun p => p.1 ≠ p.2
  have heq : (fun Z : Fin m → Pt => if hitCount Z A = 1 ∧ hitCount Z B = 1 ∧ hitCount Z C = 0 then (1 : ℝ) else 0) =
      fun Z => ∑ p ∈ pairs, ∏ i : Fin m,
        if i = p.1 then (if Z i ∈ A then (1 : ℝ) else 0)
        else if i = p.2 then (if Z i ∈ B then (1 : ℝ) else 0)
        else (if Z i ∈ (A ∪ B ∪ C)ᶜ then (1 : ℝ) else 0) := by
    ext Z
    by_cases h : hitCount Z A = 1 ∧ hitCount Z B = 1 ∧ hitCount Z C = 0
    · rw [if_pos h]
      obtain ⟨iA, hiA⟩ := Finset.card_eq_one.mp h.1
      obtain ⟨iB, hiB⟩ := Finset.card_eq_one.mp h.2.1
      have hA_iff : ∀ i, Z i ∈ A ↔ i = iA := fun i => by
        constructor
        · intro hi; exact Finset.mem_singleton.mp (hiA ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · rintro rfl
          have hmem : i ∈ Finset.univ.filter (fun j : Fin m => Z j ∈ A) := by rw [hiA]; exact Finset.mem_singleton_self i
          exact (Finset.mem_filter.mp hmem).2
      have hB_iff : ∀ i, Z i ∈ B ↔ i = iB := fun i => by
        constructor
        · intro hi; exact Finset.mem_singleton.mp (hiB ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · rintro rfl
          have hmem : i ∈ Finset.univ.filter (fun j : Fin m => Z j ∈ B) := by rw [hiB]; exact Finset.mem_singleton_self i
          exact (Finset.mem_filter.mp hmem).2
      have hC0 : ∀ i, Z i ∉ C := fun i hi => by
        have : 0 < hitCount Z C := Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        omega
      have hne_AB : iA ≠ iB := fun he => Set.disjoint_left.mp hAB ((hA_iff iA).mpr rfl) (he ▸ (hB_iff iB).mpr rfl)
      have hp_mem : (iA, iB) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne_AB⟩
      rw [Finset.sum_eq_single (iA, iB)]
      · refine (Finset.prod_eq_one fun i _ => ?_).symm
        by_cases h1 : i = iA
        · subst h1; simp [(hA_iff i).mpr rfl]
        · by_cases h2 : i = iB
          · subst h2; simp [h1, (hB_iff i).mpr rfl]
          · simp [h1, h2, mt (hA_iff i).mp h1, mt (hB_iff i).mp h2, hC0 i]
      · rintro ⟨p1, p2⟩ hp hne
        have hp_ne : p1 ≠ p2 := (Finset.mem_filter.mp hp).2
        by_cases h1 : p1 = iA
        · have h2 : p2 ≠ iB := fun he => hne (Prod.ext h1 he)
          exact Finset.prod_eq_zero (Finset.mem_univ p2) (by simp [hp_ne.symm, mt (hB_iff p2).mp h2])
        · exact Finset.prod_eq_zero (Finset.mem_univ p1) (by simp [mt (hA_iff p1).mp h1])
      · intro hm; exact absurd hp_mem hm
    · rw [if_neg h]; symm
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp_ne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      by_cases hA1 : Z p.1 ∈ A
      · by_cases hB1 : Z p.2 ∈ B
        · by_cases hC0 : hitCount Z C = 0
          · have hbad : ¬ (hitCount Z A = 1 ∧ hitCount Z B = 1) := fun h1 => h ⟨h1.1, h1.2, hC0⟩
            by_cases hA_eq : hitCount Z A = 1
            · have hB_ne : hitCount Z B ≠ 1 := fun hb => hbad ⟨hA_eq, hb⟩
              have hex : ∃ j, j ≠ p.2 ∧ Z j ∈ B := by
                by_contra hall; push Not at hall
                have hc : Finset.univ.filter (fun j : Fin m => Z j ∈ B) = {p.2} := by
                  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  exact ⟨fun hj => by_contra fun hn => hall j hn hj, fun hx => hx ▸ hB1⟩
                exact hB_ne (by unfold hitCount; rw [hc, Finset.card_singleton])
              obtain ⟨j, hjne, hjB⟩ := hex
              have hjne1 : j ≠ p.1 := fun he => Set.disjoint_left.mp hAB (he ▸ hA1) hjB
              exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjne1, hjne, hjB])
            · have hex : ∃ j, j ≠ p.1 ∧ Z j ∈ A := by
                by_contra hall; push Not at hall
                have hc : Finset.univ.filter (fun j : Fin m => Z j ∈ A) = {p.1} := by
                  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  exact ⟨fun hj => by_contra fun hn => hall j hn hj, fun hx => hx ▸ hA1⟩
                exact hA_eq (by unfold hitCount; rw [hc, Finset.card_singleton])
              obtain ⟨j, hjne, hjA⟩ := hex
              have hjne2 : j ≠ p.2 := fun he => Set.disjoint_left.mp hAB hjA (he ▸ hB1)
              exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjne, hjne2, hjA])
          · obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hC0)
            have hjC : Z j ∈ C := (Finset.mem_filter.mp hj).2
            have hj1 : j ≠ p.1 := fun he => Set.disjoint_left.mp hAC (he ▸ hA1) hjC
            have hj2 : j ≠ p.2 := fun he => Set.disjoint_left.mp hBC (he ▸ hB1) hjC
            exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj1, hj2, hjC])
        · exact Finset.prod_eq_zero (Finset.mem_univ p.2) (by simp [hp_ne.symm, hB1])
      · exact Finset.prod_eq_zero (Finset.mem_univ p.1) (by simp [hA1])
  rw [heq]
  have hABC : MeasurableSet (A ∪ B ∪ C) := (hA.union hB).union hC
  have hint : ∀ p ∈ pairs, Integrable (fun Z : Fin m → Pt => ∏ i : Fin m,
      if i = p.1 then (if Z i ∈ A then (1 : ℝ) else 0)
      else if i = p.2 then (if Z i ∈ B then (1 : ℝ) else 0)
      else (if Z i ∈ (A ∪ B ∪ C)ᶜ then (1 : ℝ) else 0)) (unitSquarePi m) := by
    intro p _
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun Z => ?_)
    · refine Finset.aestronglyMeasurable_fun_prod _ fun i _ => ?_
      by_cases h1 : i = p.1
      · simp only [h1, ↓reduceIte]
        exact (Measurable.ite (hA.preimage (measurable_pi_apply p.1)) measurable_const measurable_const).aestronglyMeasurable
      · by_cases h2 : i = p.2
        · simp only [h1, ↓reduceIte]
          simp only [h2, ↓reduceIte]
          exact (Measurable.ite (hB.preimage (measurable_pi_apply p.2)) measurable_const measurable_const).aestronglyMeasurable
        · simp only [h1, h2, ↓reduceIte]
          exact (Measurable.ite (hABC.compl.preimage (measurable_pi_apply i)) measurable_const measurable_const).aestronglyMeasurable
    · have hnn : 0 ≤ ∏ i : Fin m,
          if i = p.1 then (if Z i ∈ A then (1 : ℝ) else 0)
          else if i = p.2 then (if Z i ∈ B then (1 : ℝ) else 0)
          else (if Z i ∈ (A ∪ B ∪ C)ᶜ then (1 : ℝ) else 0) :=
        Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
      rw [Real.norm_of_nonneg hnn]
      exact Finset.prod_le_one (fun i _ => by split_ifs <;> norm_num) (fun i _ => by split_ifs <;> norm_num)
  rw [integral_finsetSum _ hint]
  have hterm : ∀ p ∈ pairs,
      ∫ Z : Fin m → Pt, (∏ i : Fin m,
        if i = p.1 then (if Z i ∈ A then (1 : ℝ) else 0)
        else if i = p.2 then (if Z i ∈ B then (1 : ℝ) else 0)
        else (if Z i ∈ (A ∪ B ∪ C)ᶜ then (1 : ℝ) else 0)) ∂(unitSquarePi m) =
      (unitSquareMeasure A).toReal * (unitSquareMeasure B).toReal *
        (1 - (unitSquareMeasure (A ∪ B ∪ C)).toReal) ^ (m - 2) := by
    intro p hp
    have hp_ne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    rw [integral_prod_unitSquarePi m
      (fun i x => if i = p.1 then (if x ∈ A then (1 : ℝ) else 0)
        else if i = p.2 then (if x ∈ B then (1 : ℝ) else 0)
        else (if x ∈ (A ∪ B ∪ C)ᶜ then (1 : ℝ) else 0))
      (fun i => by by_cases h1 : i = p.1
                   · simp only [h1, ↓reduceIte]; exact integrable_indicator_one_unitSquare hA
                   · by_cases h2 : i = p.2
                     · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact integrable_indicator_one_unitSquare hB
                     · simp only [h1, h2, ↓reduceIte]; exact integrable_indicator_one_unitSquare hABC.compl)]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p.1)]
    have hp2_mem : p.2 ∈ Finset.univ.erase p.1 := Finset.mem_erase.mpr ⟨hp_ne.symm, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase p.1) _ hp2_mem]
    simp only [↓reduceIte, hp_ne.symm, integral_indicator_one_unitSquare hA, integral_indicator_one_unitSquare hB]
    rw [← mul_assoc]
    congr 1
    have hrest : ∀ i ∈ (Finset.univ.erase p.1).erase p.2,
        (∫ x : Pt, (if i = p.1 then (if x ∈ A then (1 : ℝ) else 0)
          else if i = p.2 then (if x ∈ B then (1 : ℝ) else 0)
          else (if x ∈ (A ∪ B ∪ C)ᶜ then (1 : ℝ) else 0)) ∂unitSquareMeasure) =
        1 - (unitSquareMeasure (A ∪ B ∪ C)).toReal := fun i hi => by
      have hi2 : i ≠ p.2 := Finset.ne_of_mem_erase hi
      have hi1 : i ≠ p.1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      simp only [hi1, hi2, ↓reduceIte]
      rw [integral_indicator_one_unitSquare hABC.compl, unitSquareMeasure_compl_toReal hABC]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const, Finset.card_erase_of_mem hp2_mem,
        Finset.card_erase_of_mem (Finset.mem_univ p.1), Finset.card_univ, Fintype.card_fin, Nat.sub_sub]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hcard_pairs : pairs.card = m * (m - 1) := by
    have : pairs = Finset.univ.biUnion (fun i : Fin m => (Finset.univ.erase i).image fun j => (i, j)) := by
      ext ⟨i, j⟩
      simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_erase, Prod.mk.injEq]
      constructor
      · intro h; exact ⟨i, j, ⟨h.symm, trivial⟩, rfl, rfl⟩
      · rintro ⟨a, b, ⟨hba, _⟩, rfl, rfl⟩; exact hba.symm
    rw [this, Finset.card_biUnion]
    · simp_rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      simp [Finset.sum_const]
    · intro a _ b _ hab
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, he⟩
      exact hab (Prod.mk.inj he).1.symm
  rw [hcard_pairs, Nat.cast_mul]; ring

/-- Exact probability of `hitCount Z A ≤ 1 ∧ hitCount Z B ≤ 1` for measurable sets `A, B`. -/
lemma prob_twoSet_le_one (m : ℕ) {A B : Set Pt} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ Z : Fin m → Pt, (if hitCount Z A ≤ 1 ∧ hitCount Z B ≤ 1 then (1 : ℝ) else 0) ∂(unitSquarePi m) =
      (1 - (unitSquareMeasure (A ∪ B)).toReal) ^ m +
      (m : ℝ) * (unitSquareMeasure (A ∪ B)).toReal * (1 - (unitSquareMeasure (A ∪ B)).toReal) ^ (m - 1) +
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (unitSquareMeasure (A \ B)).toReal * (unitSquareMeasure (B \ A)).toReal *
        (1 - (unitSquareMeasure (A ∪ B)).toReal) ^ (m - 2) := by
  let S1 := A \ B
  let S2 := B \ A
  let S3 := A ∩ B
  have hS1 : MeasurableSet S1 := hA.diff hB
  have hS2 : MeasurableSet S2 := hB.diff hA
  have hS3 : MeasurableSet S3 := hA.inter hB
  have hU_eq : S1 ∪ S2 ∪ S3 = A ∪ B := by
    ext x; simp only [S1, S2, S3, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]; tauto
  have hS12 : Disjoint S1 S2 := Set.disjoint_left.mpr fun _ h1 h2 => h1.2 h2.1
  have hS13 : Disjoint S1 S3 := Set.disjoint_left.mpr fun _ h1 h3 => h1.2 h3.2
  have hS23 : Disjoint S2 S3 := Set.disjoint_left.mpr fun _ h2 h3 => h2.2 h3.1
  have hhcA : ∀ Z : Fin m → Pt, hitCount Z A = hitCount Z S1 + hitCount Z S3 := fun Z => by
    simp only [hitCount, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : Z i ∈ A <;> by_cases h2 : Z i ∈ B <;> simp [S1, S3, h1, h2]
  have hhcB : ∀ Z : Fin m → Pt, hitCount Z B = hitCount Z S2 + hitCount Z S3 := fun Z => by
    simp only [hitCount, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : Z i ∈ A <;> by_cases h2 : Z i ∈ B <;> simp [S2, S3, h1, h2]
  have hhcU : ∀ Z : Fin m → Pt, hitCount Z (A ∪ B) = hitCount Z S1 + hitCount Z S2 + hitCount Z S3 := fun Z => by
    simp only [hitCount, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : Z i ∈ A <;> by_cases h2 : Z i ∈ B <;> simp [S1, S2, S3, h1, h2]
  have heq : (fun Z : Fin m → Pt => if hitCount Z A ≤ 1 ∧ hitCount Z B ≤ 1 then (1 : ℝ) else 0) =
      fun Z => (if hitCount Z (A ∪ B) ≤ 1 then (1 : ℝ) else 0) +
        (if hitCount Z S1 = 1 ∧ hitCount Z S2 = 1 ∧ hitCount Z S3 = 0 then (1 : ℝ) else 0) := by
    ext Z
    have hA' := hhcA Z; have hB' := hhcB Z; have hU' := hhcU Z
    by_cases h1 : hitCount Z (A ∪ B) ≤ 1
    · have h2 : hitCount Z A ≤ 1 ∧ hitCount Z B ≤ 1 := by omega
      have h3 : ¬ (hitCount Z S1 = 1 ∧ hitCount Z S2 = 1 ∧ hitCount Z S3 = 0) := by omega
      simp [h1, h2, h3]
    · by_cases h3 : hitCount Z S1 = 1 ∧ hitCount Z S2 = 1 ∧ hitCount Z S3 = 0
      · have h2 : hitCount Z A ≤ 1 ∧ hitCount Z B ≤ 1 := by omega
        simp [h1, h2, h3]
      · have h2 : ¬ (hitCount Z A ≤ 1 ∧ hitCount Z B ≤ 1) := by omega
        simp [h1, h2, h3]
  have hmeas_hc : ∀ {S : Set Pt}, MeasurableSet S → Measurable (fun Z : Fin m → Pt => hitCount Z S) := by
    intro S hS
    have : (fun Z : Fin m → Pt => hitCount Z S) = fun Z => ∑ i : Fin m, if Z i ∈ S then 1 else 0 := by
      ext Z; unfold hitCount; rw [Finset.card_filter]
    rw [this]
    exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (hS.preimage (measurable_pi_apply i)) measurable_const measurable_const
  have hint1 : Integrable (fun Z : Fin m → Pt => if hitCount Z (A ∪ B) ≤ 1 then (1 : ℝ) else 0) (unitSquarePi m) :=
    Integrable.of_bound (Measurable.ite (measurableSet_le (hmeas_hc (hA.union hB)) measurable_const)
      measurable_const measurable_const).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun Z => by split_ifs <;> norm_num)
  have hint2 : Integrable (fun Z : Fin m → Pt => if hitCount Z S1 = 1 ∧ hitCount Z S2 = 1 ∧ hitCount Z S3 = 0 then (1 : ℝ) else 0) (unitSquarePi m) :=
    Integrable.of_bound (Measurable.ite (((hmeas_hc hS1) (MeasurableSet.singleton 1)).inter
      (((hmeas_hc hS2) (MeasurableSet.singleton 1)).inter ((hmeas_hc hS3) (MeasurableSet.singleton 0))))
      measurable_const measurable_const).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun Z => by split_ifs <;> norm_num)
  rw [heq, integral_add hint1 hint2, prob_hitCount_le_one m (hA.union hB),
      prob_disjoint_one_one_zero m hS1 hS2 hS3 hS12 hS13 hS23, hU_eq]

/-! ## Section 3: Interior Buffer & Exact Euclidean Areas Inside `[0, 1]²` -/

/-- Interior buffer square `[r, 1 - r]²`. -/
def interiorBox (r : ℝ) : Set Pt := Icc r (1 - r) ×ˢ Icc r (1 - r)

lemma measurableSet_interiorBox (r : ℝ) : MeasurableSet (interiorBox r) :=
  measurableSet_Icc.prod measurableSet_Icc

lemma interiorBox_subset_unitSquare {r : ℝ} (hr : 0 ≤ r) : interiorBox r ⊆ unitSquare := by
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma unitSquareMeasure_eq_volume_of_subset {A : Set Pt} (hA : A ⊆ unitSquare) :
    unitSquareMeasure A = volume A := by
  have hm : MeasurableSet unitSquare := measurableSet_Icc.prod measurableSet_Icc
  rw [← restrict_unitSquare_eq, Measure.restrict_apply' hm, Set.inter_eq_left.mpr hA]

lemma unitSquareMeasure_interiorBox {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    (unitSquareMeasure (interiorBox r)).toReal = (1 - 2 * r) ^ 2 := by
  rw [unitSquareMeasure_eq_volume_of_subset (interiorBox_subset_unitSquare hr0)]
  unfold interiorBox
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), sq]
  ring

lemma disk_subset_unitSquare {x : Pt} {r ρ : ℝ} (hx : x ∈ interiorBox r) (hρ : 0 ≤ ρ) (hρr : ρ ≤ r) :
    disk x ρ ⊆ unitSquare := by
  intro z hz
  have hdx : (z.1 - x.1) ^ 2 ≤ ρ ^ 2 := by
    have : sqDist z x ≤ ρ ^ 2 := hz
    unfold sqDist at this; nlinarith [sq_nonneg (z.2 - x.2)]
  have hdy : (z.2 - x.2) ^ 2 ≤ ρ ^ 2 := by
    have : sqDist z x ≤ ρ ^ 2 := hz
    unfold sqDist at this; nlinarith [sq_nonneg (z.1 - x.1)]
  have hax : |z.1 - x.1| ≤ ρ := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hρ]; exact Real.sqrt_le_sqrt hdx
  have hay : |z.2 - x.2| ≤ ρ := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hρ]; exact Real.sqrt_le_sqrt hdy
  rw [abs_le] at hax hay
  exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩⟩

lemma unitSquareMeasure_le_volume (A : Set Pt) : unitSquareMeasure A ≤ volume A := by
  rw [← restrict_unitSquare_eq]; exact Measure.restrict_le_self A

lemma unitSquareMeasure_disk_of_mem_interiorBox {x : Pt} {r ρ : ℝ}
    (hx : x ∈ interiorBox r) (hρ : 0 ≤ ρ) (hρr : ρ ≤ r) :
    (unitSquareMeasure (disk x ρ)).toReal = Real.pi * ρ ^ 2 := by
  rw [unitSquareMeasure_eq_volume_of_subset (disk_subset_unitSquare hx hρ hρr),
      volume_disk x hρ, ENNReal.toReal_ofReal (by positivity)]

/-- Rigid motion (rotation by angle `θ`, optional y-reflection `sgn ∈ {true, false}`,
scaling by `1 / √n`, and translation by `x₀`) maps a canonical triangle to a physical triangle. -/
def triEmbed (x₀ : Pt) (c s : ℝ) (refl : Bool) (invSqrtN : ℝ) (v : Pt) : Pt :=
  let v' : Pt := if refl then (v.1, -v.2) else v
  (x₀.1 + invSqrtN * (c * v'.1 - s * v'.2), x₀.2 + invSqrtN * (s * v'.1 + c * v'.2))

lemma triEmbed_sqDist (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (refl : Bool)
    (invSqrtN : ℝ) (u v : Pt) :
    sqDist (triEmbed x₀ c s refl invSqrtN u) (triEmbed x₀ c s refl invSqrtN v) =
      invSqrtN ^ 2 * sqDist u v := by
  unfold triEmbed sqDist
  cases refl <;> dsimp only
  · calc (x₀.1 + invSqrtN * (c * u.1 - s * u.2) - (x₀.1 + invSqrtN * (c * v.1 - s * v.2))) ^ 2 +
        (x₀.2 + invSqrtN * (s * u.1 + c * u.2) - (x₀.2 + invSqrtN * (s * v.1 + c * v.2))) ^ 2
        = invSqrtN ^ 2 * (c ^ 2 + s ^ 2) * ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2) := by ring
      _ = invSqrtN ^ 2 * ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2) := by rw [hcs, mul_one]
  · calc (x₀.1 + invSqrtN * (c * u.1 - s * (-u.2)) - (x₀.1 + invSqrtN * (c * v.1 - s * (-v.2)))) ^ 2 +
        (x₀.2 + invSqrtN * (s * u.1 + c * (-u.2)) - (x₀.2 + invSqrtN * (s * v.1 + c * (-v.2)))) ^ 2
        = invSqrtN ^ 2 * (c ^ 2 + s ^ 2) * ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2) := by ring
      _ = invSqrtN ^ 2 * ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2) := by rw [hcs, mul_one]

lemma triEmbed_euclidDist (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (refl : Bool)
    {invSqrtN : ℝ} (hpos : 0 ≤ invSqrtN) (u v : Pt) :
    euclidDist (triEmbed x₀ c s refl invSqrtN u) (triEmbed x₀ c s refl invSqrtN v) =
      invSqrtN * euclidDist u v := by
  unfold euclidDist
  rw [triEmbed_sqDist x₀ hcs refl invSqrtN u v, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos]

/-- `triEmbed` scales Lebesgue volume by `invSqrtN ^ 2`. -/
lemma volume_image_triEmbed (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (refl : Bool)
    {invSqrtN : ℝ} (hpos : 0 < invSqrtN) {S : Set Pt} (hS : MeasurableSet S) :
    volume (triEmbed x₀ c s refl invSqrtN '' S) = ENNReal.ofReal (invSqrtN ^ 2) * volume S := by
  have equiv_img : ∀ (e : Pt ≃ₗ[ℝ] Pt) (T : Set Pt), (e : Pt → Pt) '' T = (e.symm : Pt → Pt) ⁻¹' T := fun e T => by
    ext b; constructor
    · rintro ⟨a, ha, rfl⟩; simpa using ha
    · intro hb; exact ⟨e.symm b, hb, e.apply_symm_apply b⟩
  let rot := rotLinearEquiv c (-s) (by nlinarith)
  let sc := scaleLinearEquiv (ne_of_gt hpos)
  let f1 : Pt → Pt := if refl then reflYLinearEquiv else id
  have hf1_vol : ∀ {T : Set Pt}, MeasurableSet T → volume (f1 '' T) = volume T := by
    intro T hT
    cases refl
    · simp [f1]
    · dsimp only [f1]; rw [if_pos rfl]
      have hmp := measurePreserving_reflY
      have hsym : (reflYLinearEquiv.symm : Pt → Pt) = reflYLinearEquiv := by
        funext ⟨a, b⟩; rfl
      rw [equiv_img reflYLinearEquiv T, hsym, hmp.measure_preimage hT.nullMeasurableSet]
  have hf1_meas : MeasurableSet (f1 '' S) := by
    cases refl
    · simpa [f1] using hS
    · dsimp only [f1]; rw [if_pos rfl]
      rw [equiv_img reflYLinearEquiv S]
      exact hS.preimage reflYLinearEquiv.symm.toLinearMap.continuous_of_finiteDimensional.measurable
  have hrot_vol : volume (rot '' (f1 '' S)) = volume (f1 '' S) := by
    rw [equiv_img rot]
    have hmp := measurePreserving_rotLinearEquiv c s hcs
    have hsym : (rot.symm : Pt → Pt) = rotLinearEquiv c s hcs := by
      funext ⟨a, b⟩; apply Prod.ext <;> simp [rot, rotLinearEquiv]
    rw [hsym]
    exact hmp.measure_preimage hf1_meas.nullMeasurableSet
  have hrot_meas : MeasurableSet (rot '' (f1 '' S)) := by
    rw [equiv_img rot]
    exact hf1_meas.preimage rot.symm.toLinearMap.continuous_of_finiteDimensional.measurable
  have hsc_vol : volume (sc '' (rot '' (f1 '' S))) =
      ENNReal.ofReal (invSqrtN ^ 2) * volume (rot '' (f1 '' S)) := by
    have h := volume_image_scale hpos hrot_meas
    simpa [sc, scaleLinearEquiv] using h
  have himg : triEmbed x₀ c s refl invSqrtN '' S =
      (fun p : Pt => (x₀.1 + p.1, x₀.2 + p.2)) '' (sc '' (rot '' (f1 '' S))) := by
    ext q
    simp only [Set.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨sc (rot (f1 v)), ⟨rot (f1 v), ⟨f1 v, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      cases refl <;> apply Prod.ext <;> simp only [triEmbed, sc, scaleLinearEquiv, rot, rotLinearEquiv, f1, reflYLinearEquiv,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, id_eq, ↓reduceIte, Bool.false_eq_true] <;> ring
    · rintro ⟨_, ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      refine ⟨v, hv, ?_⟩
      cases refl <;> apply Prod.ext <;> simp only [triEmbed, sc, scaleLinearEquiv, rot, rotLinearEquiv, f1, reflYLinearEquiv,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, id_eq, ↓reduceIte, Bool.false_eq_true] <;> ring
  rw [himg]
  have htrans : volume ((fun p : Pt => (x₀.1 + p.1, x₀.2 + p.2)) '' (sc '' (rot '' (f1 '' S)))) =
      volume (sc '' (rot '' (f1 '' S))) := by
    let T := sc '' (rot '' (f1 '' S))
    have himg2 : (fun p : Pt => (x₀.1 + p.1, x₀.2 + p.2)) '' T =
        (fun q : Pt => (q.1 - x₀.1, q.2 - x₀.2)) ⁻¹' T := by
      ext ⟨a, b⟩
      simp only [Set.mem_image, Set.mem_preimage, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨u, v⟩, huv, rfl, rfl⟩
        simpa using huv
      · intro h
        exact ⟨(a - x₀.1, b - x₀.2), h, by ring, by ring⟩
    have hT_meas : MeasurableSet T := by
      dsimp only [T, sc]
      rw [equiv_img (scaleLinearEquiv (ne_of_gt hpos))]
      exact hrot_meas.preimage (scaleLinearEquiv (ne_of_gt hpos)).symm.toLinearMap.continuous_of_finiteDimensional.measurable
    have hshift_meas : Measurable (fun q : Pt => (q.1 - x₀.1, q.2 - x₀.2)) :=
      (measurable_fst.sub measurable_const).prodMk (measurable_snd.sub measurable_const)
    rw [himg2, ← lintegral_indicator_one (hT_meas.preimage hshift_meas), ← lintegral_indicator_one hT_meas]
    rw [show (volume : Measure Pt) = volume.prod volume from rfl]
    rw [MeasureTheory.lintegral_prod (fun z : Pt => ((fun q : Pt => (q.1 - x₀.1, q.2 - x₀.2)) ⁻¹' T).indicator (1 : Pt → ENNReal) z)
          (measurable_const.indicator (hT_meas.preimage hshift_meas)).aemeasurable,
        MeasureTheory.lintegral_prod (fun z : Pt => T.indicator (1 : Pt → ENNReal) z)
          (measurable_const.indicator hT_meas).aemeasurable]
    rw [← MeasureTheory.lintegral_sub_right_eq_self (fun x => ∫⁻ y : ℝ, T.indicator 1 (x, y)) x₀.1]
    refine lintegral_congr fun x => ?_
    rw [← MeasureTheory.lintegral_sub_right_eq_self (fun y => T.indicator 1 (x - x₀.1, y)) x₀.2]
    refine lintegral_congr fun y => ?_
    by_cases h : (x - x₀.1, y - x₀.2) ∈ T
    · have h' : (x, y) ∈ (fun q : Pt => (q.1 - x₀.1, q.2 - x₀.2)) ⁻¹' T := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]; rfl
    · have h' : (x, y) ∉ (fun q : Pt => (q.1 - x₀.1, q.2 - x₀.2)) ⁻¹' T := h
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  rw [htrans, hsc_vol, hrot_vol, hf1_vol hS]

/-! ## Section 4: Second-Nearest Neighbor, Canonical Triangle Shape, and Pointwise Dual -/

/-- Rescaled pairwise Euclidean distance `√n * ‖X i - X j‖`. -/
def rescaledDist {n : ℕ} (X : Fin n → Pt) (i j : Fin n) : ℝ :=
  Real.sqrt (n : ℝ) * euclidDist (X i) (X j)

lemma rescaledDist_symm {n : ℕ} (X : Fin n → Pt) (i j : Fin n) :
    rescaledDist X i j = rescaledDist X j i := by
  unfold rescaledDist; rw [euclidDist_symm]

lemma rescaledDist_nonneg {n : ℕ} (X : Fin n → Pt) (i j : Fin n) :
    0 ≤ rescaledDist X i j :=
  mul_nonneg (Real.sqrt_nonneg _) (euclidDist_nonneg _ _)

/-- Nonempty set of ordered distinct pairs of neighbors of `i` in `Fin n` (for `n ≥ 3`). -/
def neighborPairs {n : ℕ} (i : Fin n) : Finset (Fin n × Fin n) :=
  ((Finset.univ.erase i) ×ˢ (Finset.univ.erase i)).filter fun p => p.1 ≠ p.2

lemma neighborPairs_nonempty {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : (neighborPairs i).Nonempty := by
  have hcard : 2 ≤ (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.erase i).card)
  exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩⟩

/-- Second-nearest-neighbor distance of vertex `i` with respect to distance matrix `d` (for `n ≥ 3`). -/
def nn2 {n : ℕ} (hn : 3 ≤ n) (d : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  (neighborPairs i).inf' (neighborPairs_nonempty hn i) fun p => max (d i p.1) (d i p.2)

/-- Exact threshold characterization of `nn2`: `r < nn2 hn d i` iff at most 1 other vertex lies within `r`. -/
lemma lt_nn2_iff {n : ℕ} (hn : 3 ≤ n) (d : Fin n → Fin n → ℝ) (i : Fin n) (r : ℝ) :
    r < nn2 hn d i ↔ ((Finset.univ.erase i).filter fun j => d i j ≤ r).card ≤ 1 := by
  unfold nn2
  rw [Finset.lt_inf'_iff]
  constructor
  · intro h
    rw [Finset.card_le_one]
    intro a ha b hb
    rcases Finset.mem_filter.mp ha with ⟨ha_er, ha_le⟩
    rcases Finset.mem_filter.mp hb with ⟨hb_er, hb_le⟩
    by_contra hne
    have hlt := h (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha_er, hb_er⟩, hne⟩)
    exact not_lt_of_ge (max_le ha_le hb_le) hlt
  · intro hcard p hp
    rcases Finset.mem_filter.mp hp with ⟨hprod, hne⟩
    rcases Finset.mem_product.mp hprod with ⟨hp1, hp2⟩
    by_contra hle; push Not at hle
    have h1 : p.1 ∈ (Finset.univ.erase i).filter fun j => d i j ≤ r :=
      Finset.mem_filter.mpr ⟨hp1, (le_max_left _ _).trans hle⟩
    have h2 : p.2 ∈ (Finset.univ.erase i).filter fun j => d i j ≤ r :=
      Finset.mem_filter.mpr ⟨hp2, (le_max_right _ _).trans hle⟩
    exact hne (Finset.card_le_one.mp hcard p.1 h1 p.2 h2)

/-- For an isolated triple `{u, a, b}`, `nn2` of `u` is `max (d u a) (d u b)`. -/
lemma nn2_isolated_triple {n : ℕ} (hn : 3 ≤ n) {d : Fin n → Fin n → ℝ}
    {u a b : Fin n} (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b)
    (hiso : IsIsolated d ({u, a, b} : Finset (Fin n))) :
    nn2 hn d u = max (d u a) (d u b) := by
  unfold nn2
  have hmem : (a, b) ∈ neighborPairs u :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hua.symm, Finset.mem_univ _⟩,
      Finset.mem_erase.mpr ⟨hub.symm, Finset.mem_univ _⟩⟩, hab⟩
  apply le_antisymm
  · exact Finset.inf'_le _ hmem
  · rw [Finset.le_inf'_iff]
    rintro ⟨p1, p2⟩ hp
    rcases Finset.mem_filter.mp hp with ⟨hprod, hpne⟩
    rcases Finset.mem_product.mp hprod with ⟨hp1, hp2⟩
    have h1u : p1 ≠ u := Finset.ne_of_mem_erase hp1
    have h2u : p2 ≠ u := Finset.ne_of_mem_erase hp2
    by_cases h1S : p1 ∈ ({u, a, b} : Finset (Fin n))
    · by_cases h2S : p2 ∈ ({u, a, b} : Finset (Fin n))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h1S h2S
        rcases h1S with rfl | rfl | rfl
        · exact absurd rfl h1u
        · rcases h2S with rfl | rfl | rfl
          · exact absurd rfl h2u
          · exact absurd rfl hpne
          · exact le_rfl
        · rcases h2S with rfl | rfl | rfl
          · exact absurd rfl h2u
          · rw [max_comm]
          · exact absurd rfl hpne
      · have hlt1 := hiso u (by simp) a (by simp) p2 h2S
        have hlt2 := hiso u (by simp) b (by simp) p2 h2S
        exact (max_le (le_of_lt hlt1) (le_of_lt hlt2)).trans (le_max_right _ _)
    · have hlt1 := hiso u (by simp) a (by simp) p1 h1S
      have hlt2 := hiso u (by simp) b (by simp) p1 h1S
      exact (max_le (le_of_lt hlt1) (le_of_lt hlt2)).trans (le_max_left _ _)

/-- Canonical triangle shape `(L, (wx, wy))` of an ordered triple `(p₀, p₁, p₂)`. -/
def canonShape (p₀ p₁ p₂ : Pt) : ℝ × Pt :=
  let L := euclidDist p₀ p₁
  let dx := p₁.1 - p₀.1
  let dy := p₁.2 - p₀.2
  let ux := p₂.1 - p₀.1
  let uy := p₂.2 - p₀.2
  (L, ((ux * dx + uy * dy) / L ^ 2, |-(ux * dy) + uy * dx| / L ^ 2))

/-- The rigid embedding of `triVerts L (wx, wy)` recovers `(p₀, p₁, p₂)` identically! -/
lemma triEmbed_canonShape {p₀ p₁ p₂ : Pt} (hL : 0 < euclidDist p₀ p₁) :
    let sh := canonShape p₀ p₁ p₂
    let L := sh.1
    let c := (p₁.1 - p₀.1) / L
    let s := (p₁.2 - p₀.2) / L
    let refl := decide (-(p₂.1 - p₀.1) * (p₁.2 - p₀.2) + (p₂.2 - p₀.2) * (p₁.1 - p₀.1) < 0)
    c ^ 2 + s ^ 2 = 1 ∧
    triEmbed p₀ c s refl 1 (triVerts L sh.2 0) = p₀ ∧
    triEmbed p₀ c s refl 1 (triVerts L sh.2 1) = p₁ ∧
    triEmbed p₀ c s refl 1 (triVerts L sh.2 2) = p₂ := by
  intro sh L c s refl
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hL2 : L ^ 2 = (p₁.1 - p₀.1) ^ 2 + (p₁.2 - p₀.2) ^ 2 := by
    dsimp only [L, sh, canonShape]; rw [euclidDist_sq]; unfold sqDist; ring
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    dsimp only [c, s]; field_simp [hL_ne]; linarith
  refine ⟨hcs, ?_, ?_, ?_⟩
  · unfold triEmbed triVerts; cases refl <;> simp
  · have htri1 : triVerts L sh.2 1 = (L, 0) := rfl
    rw [htri1]; unfold triEmbed
    cases refl <;> simp only [one_mul, mul_zero, sub_zero, add_zero, neg_zero, ↓reduceIte, Bool.false_eq_true] <;>
      exact Prod.ext (by dsimp only [c]; field_simp [hL_ne]; ring) (by dsimp only [s]; field_simp [hL_ne]; ring)
  · have htri2 : triVerts L sh.2 2 = (L * sh.2.1, L * sh.2.2) := rfl
    rw [htri2]
    set dx := p₁.1 - p₀.1
    set dy := p₁.2 - p₀.2
    set ux := p₂.1 - p₀.1
    set uy := p₂.2 - p₀.2
    have hsigned : (if refl then -(L * sh.2.2) else L * sh.2.2) = (-(ux * dy) + uy * dx) / L := by
      have hsh2 : sh.2.2 = |-(ux * dy) + uy * dx| / L ^ 2 := rfl
      rw [hsh2]
      by_cases hneg : -(ux * dy) + uy * dx < 0
      · have hrefl : refl = true := by
          dsimp only [refl]
          exact decide_eq_true (show -(p₂.1 - p₀.1) * (p₁.2 - p₀.2) + (p₂.2 - p₀.2) * (p₁.1 - p₀.1) < 0 by
            dsimp only [dx, dy, ux, uy] at hneg; linarith)
        rw [hrefl, if_pos rfl, abs_of_neg hneg]; field_simp [hL_ne]
      · have hrefl : refl = false := by
          dsimp only [refl]
          exact decide_eq_false (show ¬ (-(p₂.1 - p₀.1) * (p₁.2 - p₀.2) + (p₂.2 - p₀.2) * (p₁.1 - p₀.1) < 0) by
            dsimp only [dx, dy, ux, uy] at hneg; linarith)
        rw [hrefl]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [abs_of_nonneg (not_lt.mp hneg)]; field_simp [hL_ne]
    have hx_val : L * sh.2.1 = (ux * dx + uy * dy) / L := by
      have hsh1 : sh.2.1 = (ux * dx + uy * dy) / L ^ 2 := rfl
      rw [hsh1]; field_simp [hL_ne]
    unfold triEmbed
    have hpair : (if refl then (L * sh.2.1, -(L * sh.2.2)) else (L * sh.2.1, L * sh.2.2)) =
        ((ux * dx + uy * dy) / L, (-(ux * dy) + uy * dx) / L) := by
      by_cases hr : refl = true
      · simp only [hr] at hsigned ⊢
        exact Prod.ext hx_val hsigned
      · simp only [hr] at hsigned ⊢
        exact Prod.ext hx_val hsigned
    rw [hpair]
    dsimp only [c, s]
    apply Prod.ext
    · have h1 : p₀.1 + 1 * (dx / L * ((ux * dx + uy * dy) / L) - dy / L * ((-(ux * dy) + uy * dx) / L)) =
          p₀.1 + ux * ((dx ^ 2 + dy ^ 2) / L ^ 2) := by field_simp [hL_ne]; ring
      rw [h1, ← hL2, div_self (pow_ne_zero 2 hL_ne), mul_one]; dsimp only [ux]; ring
    · have h2 : p₀.2 + 1 * (dy / L * ((ux * dx + uy * dy) / L) + dx / L * ((-(ux * dy) + uy * dx) / L)) =
          p₀.2 + uy * ((dx ^ 2 + dy ^ 2) / L ^ 2) := by field_simp [hL_ne]; ring
      rw [h2, ← hL2, div_self (pow_ne_zero 2 hL_ne), mul_one]; dsimp only [uy]; ring

/-- Squared edge lengths of `(p₀, p₁, p₂)` in terms of `canonShape p₀ p₁ p₂`. -/
lemma canonShape_edge_dists {p₀ p₁ p₂ : Pt} (hL : 0 < euclidDist p₀ p₁) :
    let sh := canonShape p₀ p₁ p₂
    euclidDist p₀ p₁ = sh.1 ∧
    euclidDist p₀ p₂ = sh.1 * euclidNorm sh.2 ∧
    euclidDist p₁ p₂ = sh.1 * euclidNorm (1 - sh.2.1, sh.2.2) := by
  intro sh
  have hemb := triEmbed_canonShape (p₂ := p₂) hL
  dsimp only at hemb
  set refl := decide (-(p₂.1 - p₀.1) * (p₁.2 - p₀.2) + (p₂.2 - p₀.2) * (p₁.1 - p₀.1) < 0)
  have h01 : euclidDist p₀ p₁ = sh.1 := rfl
  have hsh1_nn : 0 ≤ sh.1 := le_of_lt hL
  have h02 : euclidDist p₀ p₂ = sh.1 * euclidNorm sh.2 := by
    have h02' := triEmbed_euclidDist p₀ hemb.1 refl zero_le_one (triVerts sh.1 sh.2 0) (triVerts sh.1 sh.2 2)
    rw [hemb.2.1, hemb.2.2.2, one_mul] at h02'
    rw [h02']
    have h0 : triVerts sh.1 sh.2 0 = (0, 0) := rfl
    have h2 : triVerts sh.1 sh.2 2 = (sh.1 * sh.2.1, sh.1 * sh.2.2) := rfl
    rw [h0, h2]; unfold euclidDist euclidNorm sqDist
    have hsq : ((0 : ℝ) - sh.1 * sh.2.1) ^ 2 + ((0 : ℝ) - sh.1 * sh.2.2) ^ 2 =
        sh.1 ^ 2 * (sh.2.1 ^ 2 + sh.2.2 ^ 2) := by ring
    dsimp only; rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hsh1_nn]
  have h12 : euclidDist p₁ p₂ = sh.1 * euclidNorm (1 - sh.2.1, sh.2.2) := by
    have h12' := triEmbed_euclidDist p₀ hemb.1 refl zero_le_one (triVerts sh.1 sh.2 1) (triVerts sh.1 sh.2 2)
    rw [hemb.2.2.1, hemb.2.2.2, one_mul] at h12'
    rw [h12']
    have h1 : triVerts sh.1 sh.2 1 = (sh.1, 0) := rfl
    have h2 : triVerts sh.1 sh.2 2 = (sh.1 * sh.2.1, sh.1 * sh.2.2) := rfl
    rw [h1, h2]; unfold euclidDist euclidNorm sqDist
    have hsq : (sh.1 - sh.1 * sh.2.1) ^ 2 + ((0 : ℝ) - sh.1 * sh.2.2) ^ 2 =
        sh.1 ^ 2 * ((1 - sh.2.1) ^ 2 + sh.2.2 ^ 2) := by ring
    dsimp only; rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hsh1_nn]
  exact ⟨h01, h02, h12⟩

/-- Strict edge ordering for any triple with canonical shape in `(0, ∞) × quarterLens`:
`d(p₀, p₂) < d(p₁, p₂) < d(p₀, p₁)`! -/
lemma canonShape_strict_edges {p₀ p₁ p₂ : Pt}
    (hL : 0 < (canonShape p₀ p₁ p₂).1) (hql : (canonShape p₀ p₁ p₂).2 ∈ quarterLens) :
    euclidDist p₀ p₂ < euclidDist p₁ p₂ ∧ euclidDist p₁ p₂ < euclidDist p₀ p₁ := by
  have hd := canonShape_edge_dists (p₂ := p₂) hL
  set L := (canonShape p₀ p₁ p₂).1
  set wx := (canonShape p₀ p₁ p₂).2.1
  set wy := (canonShape p₀ p₁ p₂).2.2
  have h1 : wx ^ 2 + wy ^ 2 < (1 - wx) ^ 2 + wy ^ 2 := by nlinarith [hql.1, hql.2.1]
  have h2 : (1 - wx) ^ 2 + wy ^ 2 < 1 := hql.2.2.2
  have hn1 : euclidNorm (wx, wy) < euclidNorm (1 - wx, wy) := by
    unfold euclidNorm; exact Real.sqrt_lt_sqrt (by positivity) h1
  have hn2 : euclidNorm (1 - wx, wy) < 1 := by
    unfold euclidNorm; exact lt_of_lt_of_eq (Real.sqrt_lt_sqrt (by positivity) h2) Real.sqrt_one
  rw [hd.1, hd.2.1, hd.2.2]
  exact ⟨mul_lt_mul_of_pos_left hn1 hL, by nlinarith⟩

/-- Uniqueness of canonical ordering: among all orderings of `{a, b, c}`, at most ONE ordering
maps into `(0, ∞) × quarterLens`! -/
lemma canonShape_unique_ordering {n : ℕ} {X : Fin n → Pt}
    {u₁ v₁ t₁ u₂ v₂ t₂ : Fin n}
    (hset : ({u₁, v₁, t₁} : Finset (Fin n)) = {u₂, v₂, t₂})
    (h1L : 0 < (canonShape (X u₁) (X v₁) (X t₁)).1)
    (h1q : (canonShape (X u₁) (X v₁) (X t₁)).2 ∈ quarterLens)
    (h2L : 0 < (canonShape (X u₂) (X v₂) (X t₂)).1)
    (h2q : (canonShape (X u₂) (X v₂) (X t₂)).2 ∈ quarterLens) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ t₁ = t₂ := by
  have he1 := canonShape_strict_edges h1L h1q
  have he2 := canonShape_strict_edges h2L h2q
  have hne1 : u₁ ≠ v₁ ∧ u₁ ≠ t₁ ∧ v₁ ≠ t₁ := by
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [h, euclidDist_self] at he1; linarith [euclidDist_nonneg (X v₁) (X t₁)]
    · intro h; subst h
      have : 0 < (canonShape (X u₁) (X v₁) (X u₁)).2.2 := h1q.2.2.1
      have h0 : (canonShape (X u₁) (X v₁) (X u₁)).2.2 = 0 := by unfold canonShape; simp
      linarith
    · intro h; rw [h, euclidDist_self] at he1; linarith [euclidDist_nonneg (X u₁) (X t₁)]
  have hmem2 : u₂ ∈ ({u₁, v₁, t₁} : Finset (Fin n)) ∧ v₂ ∈ ({u₁, v₁, t₁} : Finset (Fin n)) ∧
      t₂ ∈ ({u₁, v₁, t₁} : Finset (Fin n)) := by
    rw [hset]; exact ⟨by simp, by simp, by simp⟩
  have hne2 : u₂ ≠ v₂ ∧ u₂ ≠ t₂ ∧ v₂ ≠ t₂ := by
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [h, euclidDist_self] at he2; linarith [euclidDist_nonneg (X v₂) (X t₂)]
    · intro h; subst h
      have : 0 < (canonShape (X u₂) (X v₂) (X u₂)).2.2 := h2q.2.2.1
      have h0 : (canonShape (X u₂) (X v₂) (X u₂)).2.2 = 0 := by unfold canonShape; simp
      linarith
    · intro h; rw [h, euclidDist_self] at he2; linarith [euclidDist_nonneg (X u₂) (X t₂)]
  rcases hmem2 with ⟨hu2, hv2, ht2⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu2 hv2 ht2
  rcases hu2 with rfl | rfl | rfl <;> rcases hv2 with rfl | rfl | rfl <;> rcases ht2 with rfl | rfl | rfl <;>
    try (exfalso; tauto)
  · exact ⟨rfl, rfl, rfl⟩
  all_goals
    exfalso
    have := euclidDist_symm (X u₂) (X v₂)
    have := euclidDist_symm (X u₂) (X t₂)
    have := euclidDist_symm (X v₂) (X t₂)
    linarith

/-- List of `(yPrev, rj, yj)` level triples of a box certificate. -/
def boxLevelTriples : List (Int × Int) → Int → List (Int × Int × Int)
  | [], _ => []
  | (rj, yj) :: rest, yPrev => (yPrev, rj, yj) :: boxLevelTriples rest yj

lemma boxLevelsIntegral_eq_sum_triples (rho w : Array Int)
    (act : BoxCert → Int → Int → Int → Bool) (b : BoxCert) :
    ∀ (lvls : List (Int × Int)) (yPrev : Int),
      boxLevelsIntegral rho w act b lvls yPrev =
        ((boxLevelTriples lvls yPrev).map fun t =>
          if act b t.1 t.2.1 t.2.2 then levelGain rho w b t.1 t.2.1 t.2.2 else 0).sum := by
  intro lvls
  induction lvls with
  | nil => intro _; simp [boxLevelsIntegral, boxLevelTriples]
  | cons p rest ih =>
    rcases p with ⟨rj, yj⟩
    intro yPrev
    simp [boxLevelsIntegral, boxLevelTriples, ih yj]

/-- Total active moat width accumulated on clearance `R` for box `b` under mask `act`. -/
def activeMoatWidth (act : BoxCert → Int → Int → Int → Bool) (b : BoxCert)
    (lvls : List (Int × Int)) (yPrev : Int) (R : ℝ) : ℝ :=
  ((boxLevelTriples lvls yPrev).map fun t =>
    if act b t.1 t.2.1 t.2.2 ∧ toR t.2.1 < R then toR t.2.2 - toR t.1 else 0).sum

/-- Elementary list-induction telescoping inequality for `activeMoatWidth`:
handles inactive levels (via convexity of `φ`) with ZERO loss! -/
lemma activeMoatWidth_telescoping_le (act : BoxCert → Int → Int → Int → Bool) (b : BoxCert)
    {pi01 : Int} {R : ℝ} {φ : ℝ → ℝ}
    (hφ_conv : ∀ a b d : ℝ, a ≤ b → 0 ≤ d → φ (a + d) - φ a ≤ φ (b + d) - φ b) :
    ∀ (lvls : List (Int × Int)) (rPrev yPrev : Int) (Y : ℝ),
      LevelsValid pi01 rPrev yPrev lvls → Y ≤ toR yPrev →
      ((boxLevelTriples lvls yPrev).map fun t =>
        if act b t.1 t.2.1 t.2.2 ∧ toR t.2.1 < R then
          2 * (toR t.2.2 - toR t.1) - (φ (toR t.2.2) - φ (toR t.1))
        else 0).sum ≤
      2 * activeMoatWidth act b lvls yPrev R -
        (φ (Y + activeMoatWidth act b lvls yPrev R) - φ Y) := by
  intro lvls
  induction lvls with
  | nil =>
    intro _ _ Y _ _
    simp [boxLevelTriples, activeMoatWidth]
  | cons p rest ih =>
    rcases p with ⟨rj, yj⟩
    intro rPrev yPrev Y hlv hY
    rcases hlv with ⟨hr_lt, hy_lt, _, hrest⟩
    by_cases hR : toR rj < R
    · by_cases hact : act b yPrev rj yj = true
      · have hdy_nn : 0 ≤ toR yj - toR yPrev := sub_nonneg.mpr (toR_le_toR (le_of_lt hy_lt))
        set Y' := Y + (toR yj - toR yPrev)
        have hY'_le : Y' ≤ toR yj := by dsimp only [Y']; linarith
        have hih := ih rj yj Y' hrest hY'_le
        have hstep := hφ_conv Y (toR yPrev) (toR yj - toR yPrev) hY hdy_nn
        have hadd_eq : toR yPrev + (toR yj - toR yPrev) = toR yj := by ring
        rw [hadd_eq] at hstep
        simp only [boxLevelTriples, activeMoatWidth, List.map_cons, List.sum_cons, hact, hR,
          and_self, ↓reduceIte] at hih ⊢
        have hassoc : Y + (toR yj - toR yPrev + activeMoatWidth act b rest yj R) =
            Y' + activeMoatWidth act b rest yj R := by dsimp only [Y']; ring
        unfold activeMoatWidth at hassoc
        rw [hassoc]; linarith
      · have hY_le' : Y ≤ toR yj := hY.trans (toR_le_toR (le_of_lt hy_lt))
        have hih := ih rj yj Y hrest hY_le'
        simp only [boxLevelTriples, activeMoatWidth, List.map_cons, List.sum_cons] at hih ⊢
        rw [if_neg (fun h => hact h.1), if_neg (fun h => hact h.1), zero_add, zero_add]
        exact hih
    · -- Since `r` is strictly increasing, NO remaining level has `toR r' < R`!
      have hall_zero : ∀ (ls : List (Int × Int)) (rp yp : Int),
          LevelsValid pi01 rp yp ls → rj ≤ rp →
          ((boxLevelTriples ls yp).map fun t =>
            if act b t.1 t.2.1 t.2.2 ∧ toR t.2.1 < R then
              2 * (toR t.2.2 - toR t.1) - (φ (toR t.2.2) - φ (toR t.1))
            else 0).sum = 0 ∧
          activeMoatWidth act b ls yp R = 0 := by
        intro ls
        induction ls with
        | nil => intro _ _ _ _; simp [boxLevelTriples, activeMoatWidth]
        | cons q qs ihq =>
          rcases q with ⟨rq, yq⟩
          intro rp yp hlvq hrp
          rcases hlvq with ⟨hrq, _, _, hqs⟩
          have hnotR : ¬ toR rq < R := fun hlt => hR ((toR_le_toR (by omega : rj ≤ rq)).trans_lt hlt)
          have hq := ihq rq yq hqs (by omega)
          simp only [boxLevelTriples, activeMoatWidth, List.map_cons, List.sum_cons, hnotR,
            and_false, ↓reduceIte, zero_add]
          exact hq
      have hz := hall_zero rest rj yj hrest le_rfl
      simp only [boxLevelTriples, activeMoatWidth, List.map_cons, List.sum_cons, hR,
        and_false, ↓reduceIte, zero_add]
      unfold activeMoatWidth at hz
      rw [hz.1, hz.2]; simp

/-- Nonnegativity & half-clearance witness for `activeMoatWidth`:
if `0 < activeMoatWidth`, there exists a cleared level `rj` with `toR rj < R`,
`activeMoatWidth ≤ toR yj`, `rPrev < rj`, and `2 * (pi01 + yj) ≤ rj`. -/
lemma activeMoatWidth_nonneg_and_clearance (act : BoxCert → Int → Int → Int → Bool) (b : BoxCert)
    {pi01 : Int} {R : ℝ} :
    ∀ (lvls : List (Int × Int)) (rPrev yPrev : Int) (Y : ℝ),
      LevelsValid pi01 rPrev yPrev lvls → 0 ≤ Y → Y ≤ toR yPrev →
      0 ≤ activeMoatWidth act b lvls yPrev R ∧
      (0 < activeMoatWidth act b lvls yPrev R →
        ∃ rj yj : Int, rPrev < rj ∧ toR rj < R ∧ Y + activeMoatWidth act b lvls yPrev R ≤ toR yj ∧
          2 * (pi01 + yj) ≤ rj) := by
  intro lvls
  induction lvls with
  | nil =>
    intro _ _ _ _ _ _
    simp [activeMoatWidth, boxLevelTriples]
  | cons p rest ih =>
    rcases p with ⟨rj, yj⟩
    intro rPrev yPrev Y hlv hY0 hY
    rcases hlv with ⟨hr_lt, hy_lt, hhalf, hrest⟩
    by_cases hact : act b yPrev rj yj = true ∧ toR rj < R
    · set Y' := Y + (toR yj - toR yPrev)
      have hdy_pos : 0 < toR yj - toR yPrev := sub_pos.mpr (div_lt_div_of_pos_right (by exact_mod_cast hy_lt) S_pos)
      have hih := ih rj yj Y' hrest (by dsimp only [Y']; linarith) (by dsimp only [Y']; linarith)
      simp only [activeMoatWidth, boxLevelTriples, List.map_cons, List.sum_cons, hact.1, hact.2, and_self, ↓reduceIte]
      unfold activeMoatWidth at hih
      refine ⟨by linarith [hih.1], fun _ => ?_⟩
      by_cases hrest_pos : 0 < ((boxLevelTriples rest yj).map fun t =>
          if act b t.1 t.2.1 t.2.2 ∧ toR t.2.1 < R then toR t.2.2 - toR t.1 else 0).sum
      · obtain ⟨rj', yj', hr', hR', hY', hh'⟩ := hih.2 hrest_pos
        exact ⟨rj', yj', lt_trans hr_lt hr', hR', by dsimp only [Y'] at hY'; linarith, hh'⟩
      · have hrest0 : ((boxLevelTriples rest yj).map fun t =>
            if act b t.1 t.2.1 t.2.2 ∧ toR t.2.1 < R then toR t.2.2 - toR t.1 else 0).sum = 0 :=
          le_antisymm (not_lt.mp hrest_pos) hih.1
        exact ⟨rj, yj, hr_lt, hact.2, by rw [hrest0]; linarith, hhalf⟩
    · have hih := ih rj yj Y hrest hY0 (hY.trans (toR_le_toR (le_of_lt hy_lt)))
      simp only [activeMoatWidth, boxLevelTriples, List.map_cons, List.sum_cons]
      rw [if_neg hact, zero_add]
      unfold activeMoatWidth at hih
      refine ⟨hih.1, fun hpos => ?_⟩
      obtain ⟨rj', yj', hr', hR', hY', hh'⟩ := hih.2 hpos
      exact ⟨rj', yj', lt_trans hr_lt hr', hR', hY', hh'⟩

/-- Clearance radius `R_clear d S` of a 3-subset `S` (for `n ≥ 4`, so `univ \ S` is nonempty). -/
def tripleClearance {n : ℕ} (hn : 4 ≤ n) (d : Fin n → Fin n → ℝ) (S : Finset (Fin n))
    (hcard : S.card = 3) : ℝ :=
  have hne : (S ×ˢ (Finset.univ \ S)).Nonempty := by
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hC : (Finset.univ \ S).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]; omega)
    exact hS.product hC
  (S ×ˢ (Finset.univ \ S)).inf' hne fun p => d p.1 p.2

lemma lt_tripleClearance_iff {n : ℕ} (hn : 4 ≤ n) (d : Fin n → Fin n → ℝ)
    (S : Finset (Fin n)) (hcard : S.card = 3) (r : ℝ) :
    r < tripleClearance hn d S hcard ↔ ∀ u ∈ S, ∀ v ∉ S, r < d u v := by
  unfold tripleClearance
  rw [Finset.lt_inf'_iff]
  constructor
  · intro h u hu v hv
    exact h (u, v) (Finset.mem_product.mpr ⟨hu, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩⟩)
  · intro h p hp
    rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
    exact h p.1 h1 p.2 (Finset.mem_sdiff.mp h2).2

/-- Ordered triple matching predicate: `(u, v, t)` are distinct, `X u ∈ interiorBox rBuf`, and
their rescaled canonical shape lies in `boxRegion b`. -/
def MatchesBox {n : ℕ} (b : BoxCert) (rBuf : ℝ) (X : Fin n → Pt) (u v t : Fin n) : Prop :=
  u ≠ v ∧ u ≠ t ∧ v ≠ t ∧
  X u ∈ interiorBox rBuf ∧
  canonShape (Real.sqrt (n : ℝ) * (X u).1, Real.sqrt (n : ℝ) * (X u).2)
    (Real.sqrt (n : ℝ) * (X v).1, Real.sqrt (n : ℝ) * (X v).2)
    (Real.sqrt (n : ℝ) * (X t).1, Real.sqrt (n : ℝ) * (X t).2) ∈ boxRegion b

/-- **Deterministic Pointwise Dual Lower Bound on `Fin n → Pt` (`n ≥ 4`).**

For every point configuration `X : Fin n → Pt`, the rescaled optimal tour length `√n * tourLength X`
is bounded below by the base 2-factor dual plus the linear sum over all boxes `b ∈ boxes`, all
ordered triples `(u, v, t)` matching `b`, and all active cleared levels `(yPrev, rj, yj)` of `b`. -/
theorem pointwise_dual_lower_bound {n : ℕ} (hn : 4 ≤ n)
    {rho w : Array Int} {boxes : List BoxCert}
    (act : BoxCert → Int → Int → Int → Bool)
    (hpot : ValidStepPot rho w)
    (hboxes : ∀ b ∈ boxes, ValidBox rho w b)
    (hdisj : PairwiseDisjointBoxes boxes)
    (rBuf : ℝ) (X : Fin n → Pt) :
    let d := rescaledDist X
    let pot := fun u : Fin n => stepPot rho w (nn2 (by omega) d u)
    2 * (∑ u : Fin n, pot u)
      - (1 / 2 : ℝ) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, max 0 (pot u + pot v - d u v)
      + (boxes.map fun b =>
          ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
            if MatchesBox b rBuf X u v t then
              ((boxLevelTriples b.levels 0).map fun lv =>
                if act b lv.1 lv.2.1 lv.2.2 ∧
                    (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)), toR lv.2.1 < d x z) then
                  2 * (toR lv.2.2 - toR lv.1) -
                    ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                      (max 0 (pot x + toR lv.2.2 + pot z - d x z) - max 0 (pot x + toR lv.1 + pot z - d x z))
                else 0).sum
            else 0).sum
      ≤ Real.sqrt (n : ℝ) * tourLength X := by
  intro d pot
  -- Auxiliary scaled configuration `Y i = √n • X i`
  let Y : Fin n → Pt := fun i => (Real.sqrt (n : ℝ) * (X i).1, Real.sqrt (n : ℝ) * (X i).2)
  have hY_dist : ∀ i j : Fin n, euclidDist (Y i) (Y j) = d i j := fun i j => by
    unfold d rescaledDist euclidDist sqDist Y
    have hsq : (Real.sqrt (n : ℝ) * (X i).1 - Real.sqrt (n : ℝ) * (X j).1) ^ 2 +
        (Real.sqrt (n : ℝ) * (X i).2 - Real.sqrt (n : ℝ) * (X j).2) ^ 2 =
        (Real.sqrt (n : ℝ)) ^ 2 * (((X i).1 - (X j).1) ^ 2 + ((X i).2 - (X j).2) ^ 2) := by ring
    dsimp only; rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)]
  -- For any 3-subset `S`, define `y S` as the active moat width if `S` matches some (unique!) `(b, u, v, t)`.
  let tripleY : Finset (Fin n) → ℝ := fun S =>
    if hcard : S.card = 3 then
      (boxes.map fun b =>
        ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
          if MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S then
            activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard)
          else 0).sum
    else 0
  -- Uniqueness: for a fixed 3-subset `S`, at most ONE `(b ∈ boxes, u, v, t)` satisfies `MatchesBox b rBuf X u v t ∧ {u,v,t} = S`!
  have huniq_match : ∀ {b₁ b₂ : BoxCert} {u₁ v₁ t₁ u₂ v₂ t₂ : Fin n},
      b₁ ∈ boxes → b₂ ∈ boxes →
      MatchesBox b₁ rBuf X u₁ v₁ t₁ → MatchesBox b₂ rBuf X u₂ v₂ t₂ →
      ({u₁, v₁, t₁} : Finset (Fin n)) = {u₂, v₂, t₂} →
      b₁ = b₂ ∧ u₁ = u₂ ∧ v₁ = v₂ ∧ t₁ = t₂ := by
    intro b₁ b₂ u₁ v₁ t₁ u₂ v₂ t₂ hb₁ hb₂ hm₁ hm₂ hset
    have hql₁ := boxRegion_mem_quarterLens (hboxes b₁ hb₁) hm₁.2.2.2.2
    have hql₂ := boxRegion_mem_quarterLens (hboxes b₂ hb₂) hm₂.2.2.2.2
    obtain ⟨hu, hv, ht⟩ := canonShape_unique_ordering (X := Y) hset hql₁.1 hql₁.2 hql₂.1 hql₂.2
    subst hu; subst hv; subst ht
    refine ⟨?_, rfl, rfl, rfl⟩
    by_contra hne
    -- Extract pairwise disjointness of `b₁ ≠ b₂` from `PairwiseDisjointBoxes boxes`!
    have hdisj_b : Disjoint (boxRegion b₁) (boxRegion b₂) := by
      have hpw : ∀ (ls : List BoxCert), PairwiseDisjointBoxes ls →
          ∀ a ∈ ls, ∀ c ∈ ls, a ≠ c → Disjoint (boxRegion a) (boxRegion c) := by
        intro ls
        induction ls with
        | nil => intro _ _ ha; exact absurd ha (by simp)
        | cons hd tl ihtl =>
          intro hpw' a ha c hc hac
          rcases List.pairwise_cons.mp hpw' with ⟨hhd, htl⟩
          rcases List.mem_cons.mp ha with rfl | hat
          · rcases List.mem_cons.mp hc with rfl | hct
            · exact absurd rfl hac
            · exact hhd c hct
          · rcases List.mem_cons.mp hc with rfl | hct
            · exact (hhd a hat).symm
            · exact ihtl htl a hat c hct hac
      exact hpw boxes hdisj b₁ hb₁ b₂ hb₂ hne
    exact Set.disjoint_left.mp hdisj_b hm₁.2.2.2.2 hm₂.2.2.2.2
  -- Also `boxes` has no duplicates (any valid box has a nonempty open `boxRegion`, so `¬ Disjoint (boxRegion b) (boxRegion b)`)!
  have hnodup : boxes.Nodup := by
    have hnd : ∀ (ls : List BoxCert), (∀ b ∈ ls, ValidBox rho w b) → PairwiseDisjointBoxes ls → ls.Nodup := by
      intro ls
      induction ls with
      | nil => intro _ _; exact List.nodup_nil
      | cons hd tl ih =>
        intro hvb hpw
        rcases List.pairwise_cons.mp hpw with ⟨hhd, htl⟩
        refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih (fun b hb => hvb b (List.mem_cons_of_mem _ hb)) htl⟩
        have hd_disj : Disjoint (boxRegion hd) (boxRegion hd) := hhd hd hmem
        have hvh := hvb hd List.mem_cons_self
        have hmid : ((toR hd.l0 + toR hd.l1) / 2, ((toR hd.x0 + toR hd.x1) / 2, (toR hd.y0 + toR hd.y1) / 2)) ∈ boxRegion hd := by
          have hl : toR hd.l0 < toR hd.l1 := div_lt_div_of_pos_right (by exact_mod_cast hvh.l0_lt_l1) S_pos
          have hx : toR hd.x0 < toR hd.x1 := div_lt_div_of_pos_right (by exact_mod_cast hvh.x0_lt_x1) S_pos
          have hy : toR hd.y0 < toR hd.y1 := div_lt_div_of_pos_right (by exact_mod_cast hvh.y0_lt_y1) S_pos
          exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
        exact Set.disjoint_left.mp hd_disj hmid hmid
    exact hnd boxes hboxes hdisj
  -- Key property of `tripleY S`: whenever `S` has card 3, either `tripleY S = 0`, OR there is a unique
  -- `(b ∈ boxes, u, v, t)` matching `S` and `tripleY S = activeMoatWidth ...`!
  have htripleY_nn : ∀ S : Finset (Fin n), 0 ≤ tripleY S := by
    intro S
    dsimp only [tripleY]
    split_ifs with hcard
    · refine List.sum_nonneg fun x hx => ?_
      rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
      refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun t _ => ?_
      split_ifs
      · exact (activeMoatWidth_nonneg_and_clearance act b b.levels b.l1 0 0 (hboxes b hb).levels_valid le_rfl (by rw [toR_zero])).1
      · exact le_rfl
    · exact le_rfl
  -- Active triple family `F := {S ∈ powersetCard 3 univ | 0 < tripleY S}`
  let F : Finset (Finset (Fin n)) := (Finset.powersetCard 3 Finset.univ).filter fun S => 0 < tripleY S
  -- Every `S ∈ F` is isolated AND satisfies half-clearance!
  have hF_prop : ∀ S ∈ F,
      S.Nonempty ∧ S ≠ Finset.univ ∧ IsIsolated d S ∧
      (∃ r : ℝ, (∀ x ∈ S, ∀ z ∉ S, r < d x z) ∧ (∀ x ∈ S, pot x + tripleY S ≤ r / 2)) := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hpow, hy_pos⟩
    have hcard : S.card = 3 := (Finset.mem_powersetCard.mp hpow).2
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hproper : S ≠ Finset.univ := fun he => by
      have : S.card = n := by rw [he, Finset.card_univ, Fintype.card_fin]
      omega
    -- Extract the unique `(b ∈ boxes, u, v, t)` with `0 < activeMoatWidth`!
    have hex_match : ∃ b ∈ boxes, ∃ u v t : Fin n,
        MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S ∧
        tripleY S = activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard) := by
      have hpos' : 0 < (boxes.map fun b =>
          ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
            if MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S then
              activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard)
            else 0).sum := by
        dsimp only [tripleY] at hy_pos; rwa [dif_pos hcard] at hy_pos
      have hex_b : ∃ b ∈ boxes, 0 < ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
          if MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S then
            activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard)
          else 0 := by
        by_contra hall; push Not at hall
        have hle : (boxes.map fun b =>
            ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
              if MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S then
                activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard)
              else 0).sum ≤ 0 := by
          have hle_list : ∀ (L : List ℝ), (∀ x ∈ L, x ≤ 0) → L.sum ≤ 0 := fun L => by
            induction L with
            | nil => intro _; simp
            | cons a as iha =>
              intro hL; simp only [List.sum_cons]
              linarith [hL a List.mem_cons_self, iha fun y hy => hL y (List.mem_cons_of_mem _ hy)]
          exact hle_list _ fun x hx => by
            rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩; exact hall b hb
        linarith
      obtain ⟨b, hb, hb_pos⟩ := hex_b
      have hex_uvt : ∃ u v t : Fin n, MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S := by
        by_contra hall; push Not at hall
        have hz : ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
            (if MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S then
              activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard)
            else 0) = 0 := by
          refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun t _ => ?_
          rw [if_neg (fun hm => hall u v t hm.1 hm.2)]
        linarith
      obtain ⟨u, v, t, hmatch, hSeq⟩ := hex_uvt
      refine ⟨b, hb, u, v, t, hmatch, hSeq, ?_⟩
      dsimp only [tripleY]; rw [dif_pos hcard]
      -- By uniqueness + `hnodup`, ONLY `(b, u, v, t)` contributes!
      have hsum_single : ∀ b' ∈ boxes,
          (∑ u' : Fin n, ∑ v' : Fin n, ∑ t' : Fin n,
            if MatchesBox b' rBuf X u' v' t' ∧ ({u', v', t'} : Finset (Fin n)) = S then
              activeMoatWidth act b' b'.levels 0 (tripleClearance hn d S hcard)
            else 0) =
          if b' = b then activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard) else 0 := by
        intro b' hb'
        by_cases hbb : b' = b
        · subst hbb; rw [if_pos rfl]
          rw [Finset.sum_eq_single u]
          · rw [Finset.sum_eq_single v]
            · rw [Finset.sum_eq_single t]
              · rw [if_pos ⟨hmatch, hSeq⟩]
              · intro t' _ ht'; rw [if_neg fun h => ht' (huniq_match hb' hb h.1 hmatch (h.2.trans hSeq.symm)).2.2.2]
              · intro hm; exact absurd (Finset.mem_univ t) hm
            · intro v' _ hv'
              exact Finset.sum_eq_zero fun t' _ =>
                if_neg fun h => hv' (huniq_match hb' hb h.1 hmatch (h.2.trans hSeq.symm)).2.2.1
            · intro hm; exact absurd (Finset.mem_univ v) hm
          · intro u' _ hu'
            exact Finset.sum_eq_zero fun v' _ => Finset.sum_eq_zero fun t' _ =>
              if_neg fun h => hu' (huniq_match hb' hb h.1 hmatch (h.2.trans hSeq.symm)).2.1
          · intro hm; exact absurd (Finset.mem_univ u) hm
        · rw [if_neg hbb]
          refine Finset.sum_eq_zero fun u' _ => Finset.sum_eq_zero fun v' _ => Finset.sum_eq_zero fun t' _ => ?_
          rw [if_neg fun h => hbb (huniq_match hb' hb h.1 hmatch (h.2.trans hSeq.symm)).1]
      have hmap_eq : boxes.map (fun b' =>
          ∑ u' : Fin n, ∑ v' : Fin n, ∑ t' : Fin n,
            if MatchesBox b' rBuf X u' v' t' ∧ ({u', v', t'} : Finset (Fin n)) = S then
              activeMoatWidth act b' b'.levels 0 (tripleClearance hn d S hcard)
            else 0) =
          boxes.map (fun b' => if b' = b then activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard) else 0) :=
        List.map_congr_left hsum_single
      rw [hmap_eq]
      -- Sum of `(if b' = b then c else 0)` over a `Nodup` list containing `b` equals `c`!
      have hlist_single : ∀ (ls : List BoxCert) (c : ℝ), ls.Nodup → b ∈ ls →
          (ls.map fun b' => if b' = b then c else 0).sum = c := by
        intro ls c
        induction ls with
        | nil => intro _ hm; exact absurd hm (by simp)
        | cons a as iha =>
          intro hnd hm
          rcases List.nodup_cons.mp hnd with ⟨hnot, hnd_as⟩
          rcases List.mem_cons.mp hm with rfl | hmas
          · simp only [List.map_cons, List.sum_cons, ↓reduceIte]
            have hz : (as.map fun b' => if b' = b then c else 0).sum = 0 := by
              have h0 : as.map (fun b' => if b' = b then c else 0) = as.map (fun _ => (0 : ℝ)) :=
                List.map_congr_left fun x hx => if_neg (fun (he : x = b) => hnot (he ▸ hx))
              rw [h0]; induction as with | nil => simp | cons _ _ _ => simp
            linarith
          · have hne_ab : a ≠ b := fun he => hnot (he ▸ hmas)
            simp only [List.map_cons, List.sum_cons, hne_ab, ↓reduceIte, zero_add]
            exact iha hnd_as hmas
      exact hlist_single boxes _ hnodup hb
    obtain ⟨b, hb, u, v, t, hmatch, hSeq, hyS_eq⟩ := hex_match
    have hact_pos : 0 < activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard) := by
      linarith
    have hcl := (activeMoatWidth_nonneg_and_clearance act b b.levels b.l1 0 0
      (hboxes b hb).levels_valid le_rfl (by rw [toR_zero])).2 hact_pos
    obtain ⟨rj, yj, hrj_gt, hrj_R, hy_le, hhalf⟩ := hcl
    rw [zero_add] at hy_le
    have hql := boxRegion_mem_quarterLens (hboxes b hb) hmatch.2.2.2.2
    have hedges := canonShape_strict_edges hql.1 hql.2
    have hL_lt_l1 : euclidDist (Y u) (Y v) < toR b.l1 := hmatch.2.2.2.2.2.1
    have hL_lt_rj : euclidDist (Y u) (Y v) < toR rj :=
      hL_lt_l1.trans (div_lt_div_of_pos_right (by exact_mod_cast hrj_gt) S_pos)
    have hrj_out : ∀ x ∈ S, ∀ z ∉ S, toR rj < d x z :=
      (lt_tripleClearance_iff hn d S hcard (toR rj)).mp hrj_R
    have hiso : IsIsolated d S := by
      intro x hx a ha z hz
      have hxz : toR rj < d x z := hrj_out x hx z hz
      have hxa : d x a ≤ euclidDist (Y u) (Y v) := by
        rw [← hY_dist]
        rw [← hSeq] at hx ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ha
        rcases hx with rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl
        · rw [euclidDist_self]; exact euclidDist_nonneg _ _
        · exact le_rfl
        · exact le_of_lt (hedges.1.trans hedges.2)
        · rw [euclidDist_symm]
        · rw [euclidDist_self]; exact euclidDist_nonneg _ _
        · exact le_of_lt hedges.2
        · rw [euclidDist_symm]; exact le_of_lt (hedges.1.trans hedges.2)
        · rw [euclidDist_symm]; exact le_of_lt hedges.2
        · rw [euclidDist_self]; exact euclidDist_nonneg _ _
      linarith
    have hpi_le : ∀ x ∈ S, pot x ≤ toR (evalStepPot rho w b.l1) := by
      intro x hx
      have hnn2_le : nn2 (by omega) d x ≤ toR b.l1 := by
        rw [← hSeq] at hx hiso
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · rw [nn2_isolated_triple (by omega) hmatch.1 hmatch.2.1 hmatch.2.2.1 hiso, ← hY_dist, ← hY_dist]
          exact max_le (le_of_lt hL_lt_l1) (le_of_lt ((hedges.1.trans hedges.2).trans hL_lt_l1))
        · have hiso' : IsIsolated d ({x, u, t} : Finset (Fin n)) := by
            convert hiso using 1; ext q; simp; tauto
          rw [nn2_isolated_triple (by omega) hmatch.1.symm hmatch.2.2.1 hmatch.2.1 hiso', ← hY_dist, ← hY_dist]
          rw [euclidDist_symm (Y x) (Y u)]
          exact max_le (le_of_lt hL_lt_l1) (le_of_lt (hedges.2.trans hL_lt_l1))
        · have hiso' : IsIsolated d ({x, u, v} : Finset (Fin n)) := by
            convert hiso using 1; ext q; simp; tauto
          rw [nn2_isolated_triple (by omega) hmatch.2.1.symm hmatch.2.2.1.symm hmatch.1 hiso', ← hY_dist, ← hY_dist]
          rw [euclidDist_symm (Y x) (Y u), euclidDist_symm (Y x) (Y v)]
          exact max_le (le_of_lt ((hedges.1.trans hedges.2).trans hL_lt_l1)) (le_of_lt (hedges.2.trans hL_lt_l1))
      exact stepPot_le_evalStepPot hpot hnn2_le
    refine ⟨hne, hproper, hiso, toR rj, hrj_out, fun x hx => ?_⟩
    have h2 : 2 * (toR (evalStepPot rho w b.l1) + toR yj) ≤ toR rj := by
      have htmp := toR_le_toR hhalf
      unfold toR at htmp ⊢; push_cast at htmp ⊢
      rw [← add_div, ← mul_div_assoc]; exact htmp
    linarith [hpi_le x hx, hy_le, hyS_eq]
  -- Pairwise disjointness & non-interference of `F`!
  have hF_disj : (F : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro S₁ hS₁ S₂ hS₂ hne
    have hc1 : S₁.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS₁).1).2
    have hc2 : S₂.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS₂).1).2
    exact isolated_pairwiseDisjoint d 3 hc1 hc2 (hF_prop S₁ hS₁).2.2.1 (hF_prop S₂ hS₂).2.2.1 hne
  have hNI := nonInterference_of_halfClearance d (rescaledDist_symm X) pot F hF_disj tripleY
    fun S hS _ => (hF_prop S hS).2.2.2
  -- Apply `twoFactor_moat_dual_lower_bound` to an optimal tour `σ` of `X`!
  obtain ⟨σ, hσ⟩ := exists_optimal_tour X
  have hdual := twoFactor_moat_dual_lower_bound (by omega) d (rescaledDist_symm X) pot F
    (fun S hS => (hF_prop S hS).1) (fun S hS => (hF_prop S hS).2.1) hF_disj tripleY
    (fun S _ => htripleY_nn S) hNI σ
  have htour_eq : ∑ i : Fin n, d (σ i) (σ (finRotate n i)) = Real.sqrt (n : ℝ) * tourLength X := by
    rw [hσ, Finset.mul_sum]; rfl
  rw [htour_eq] at hdual
  -- Finally, telescope each active moat term in `F` and compare to the linear sum over `(b, u, v, t, lv)`!
  refine le_trans ?_ hdual
  refine add_le_add le_rfl ?_
  -- Rewrite the linear sum by grouping over `S ∈ powersetCard 3 univ` (since every matched `(u,v,t)` has `{u,v,t}.card = 3`)!
  have hgroup :
      (boxes.map fun b =>
        ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
          if MatchesBox b rBuf X u v t then
            ((boxLevelTriples b.levels 0).map fun lv =>
              if act b lv.1 lv.2.1 lv.2.2 ∧
                  (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)), toR lv.2.1 < d x z) then
                2 * (toR lv.2.2 - toR lv.1) -
                  ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                    (max 0 (pot x + toR lv.2.2 + pot z - d x z) - max 0 (pot x + toR lv.1 + pot z - d x z))
              else 0).sum
          else 0).sum =
      ∑ S ∈ Finset.powersetCard 3 Finset.univ,
        (boxes.map fun b =>
          ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
            if MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S then
              ((boxLevelTriples b.levels 0).map fun lv =>
                if act b lv.1 lv.2.1 lv.2.2 ∧
                    (∀ x ∈ S, ∀ z ∉ S, toR lv.2.1 < d x z) then
                  2 * (toR lv.2.2 - toR lv.1) -
                    ∑ x ∈ S, ∑ z ∈ Finset.univ \ S,
                      (max 0 (pot x + toR lv.2.2 + pot z - d x z) - max 0 (pot x + toR lv.1 + pot z - d x z))
                else 0).sum
            else 0).sum := by
    -- Swap `List.sum` over `boxes` and `Finset.sum` over `S`!
    have hlist_finset : ∀ (ls : List BoxCert) (f : BoxCert → Finset (Fin n) → ℝ),
        (ls.map fun b => ∑ S ∈ Finset.powersetCard 3 Finset.univ, f b S).sum =
        ∑ S ∈ Finset.powersetCard 3 Finset.univ, (ls.map fun b => f b S).sum := by
      intro ls f
      induction ls with
      | nil => simp
      | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]
    rw [← hlist_finset]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp_rw [Finset.sum_comm (s := Finset.powersetCard 3 Finset.univ)]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases hm : MatchesBox b rBuf X u v t
    · rw [if_pos hm]
      have hcard3 : ({u, v, t} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hm.1, hm.2.1]),
            Finset.card_insert_of_notMem (by simp [hm.2.2.1]), Finset.card_singleton]
      have hmem3 : ({u, v, t} : Finset (Fin n)) ∈ Finset.powersetCard 3 Finset.univ :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard3⟩
      rw [Finset.sum_eq_single ({u, v, t} : Finset (Fin n))]
      · rw [if_pos ⟨hm, rfl⟩]
      · intro S _ hne; rw [if_neg (fun h => hne h.2.symm)]
      · intro hnm; exact absurd hmem3 hnm
    · rw [if_neg hm]; symm
      exact Finset.sum_eq_zero fun S _ => if_neg (fun h => hm h.1)
  rw [hgroup]
  -- Compare term-by-term over `S ∈ powersetCard 3 univ` (terms with `tripleY S = 0` are `0` on both sides)!
  have hsum_F : ∑ S ∈ F, (2 * tripleY S - ∑ u ∈ S, ∑ v ∈ Finset.univ \ S,
        (max 0 (pot u + tripleY S + pot v - d u v) - max 0 (pot u + pot v - d u v))) =
      ∑ S ∈ Finset.powersetCard 3 Finset.univ, (2 * tripleY S - ∑ u ∈ S, ∑ v ∈ Finset.univ \ S,
        (max 0 (pot u + tripleY S + pot v - d u v) - max 0 (pot u + pot v - d u v))) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun S hS hnotF => ?_)
    have hy0 : tripleY S = 0 := by
      have hle : tripleY S ≤ 0 := not_lt.mp (fun hp => hnotF (Finset.mem_filter.mpr ⟨hS, hp⟩))
      exact le_antisymm hle (htripleY_nn S)
    simp [hy0]
  rw [hsum_F]
  refine Finset.sum_le_sum fun S hS => ?_
  have hcard : S.card = 3 := (Finset.mem_powersetCard.mp hS).2
  let φ : ℝ → ℝ := fun y =>
    ∑ x ∈ S, ∑ z ∈ Finset.univ \ S, (max 0 (pot x + y + pot z - d x z) - max 0 (pot x + pot z - d x z))
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hφ_conv : ∀ a b δ : ℝ, a ≤ b → 0 ≤ δ → φ (a + δ) - φ a ≤ φ (b + δ) - φ b := by
    intro a b δ hab hδ
    dsimp only [φ]
    simp_rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => ?_
    have hsimp : ∀ t : ℝ, (max 0 (pot x + (t + δ) + pot z - d x z) - max 0 (pot x + pot z - d x z)) -
        (max 0 (pot x + t + pot z - d x z) - max 0 (pot x + pot z - d x z)) =
        max 0 (pot x + t + δ + pot z - d x z) - max 0 (pot x + t + pot z - d x z) := fun t => by ring_nf
    rw [hsimp a, hsimp b]
    set c := pot x + pot z - d x z
    have hmono : max 0 (c + a + δ) - max 0 (c + a) ≤ max 0 (c + b + δ) - max 0 (c + b) := by
      simp only [max_def]; split_ifs <;> linarith
    have hEq1 : pot x + a + δ + pot z - d x z = c + a + δ := by dsimp only [c]; ring
    have hEq2 : pot x + a + pot z - d x z = c + a := by dsimp only [c]; ring
    have hEq3 : pot x + b + δ + pot z - d x z = c + b + δ := by dsimp only [c]; ring
    have hEq4 : pot x + b + pot z - d x z = c + b := by dsimp only [c]; ring
    rw [hEq1, hEq2, hEq3, hEq4]; exact hmono
  -- Case split: does `S` match some `(b ∈ boxes, u, v, t)`?
  by_cases hex : ∃ b ∈ boxes, ∃ u v t : Fin n, MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S
  · obtain ⟨b, hb, u, v, t, hmatch, hSeq⟩ := hex
    -- Both LHS and `tripleY S` collapse to the single matching `(b, u, v, t)`!
    have hcollapse : ∀ (g : BoxCert → ℝ),
        (boxes.map fun b' => ∑ u' : Fin n, ∑ v' : Fin n, ∑ t' : Fin n,
          if MatchesBox b' rBuf X u' v' t' ∧ ({u', v', t'} : Finset (Fin n)) = S then g b' else 0).sum =
        g b := by
      intro g
      have h1 : ∀ b' ∈ boxes,
          (∑ u' : Fin n, ∑ v' : Fin n, ∑ t' : Fin n,
            if MatchesBox b' rBuf X u' v' t' ∧ ({u', v', t'} : Finset (Fin n)) = S then g b' else 0) =
          if b' = b then g b else 0 := by
        intro b' hb'
        by_cases hbb : b' = b
        · subst hbb; rw [if_pos rfl]
          rw [Finset.sum_eq_single u]
          · rw [Finset.sum_eq_single v]
            · rw [Finset.sum_eq_single t]
              · rw [if_pos ⟨hmatch, hSeq⟩]
              · intro t' _ ht'; rw [if_neg fun h => ht' (huniq_match hb' hb h.1 hmatch (h.2.trans hSeq.symm)).2.2.2]
              · intro hm; exact absurd (Finset.mem_univ t) hm
            · intro v' _ hv'
              exact Finset.sum_eq_zero fun t' _ =>
                if_neg fun h => hv' (huniq_match hb' hb h.1 hmatch (h.2.trans hSeq.symm)).2.2.1
            · intro hm; exact absurd (Finset.mem_univ v) hm
          · intro u' _ hu'
            exact Finset.sum_eq_zero fun v' _ => Finset.sum_eq_zero fun t' _ =>
              if_neg fun h => hu' (huniq_match hb' hb h.1 hmatch (h.2.trans hSeq.symm)).2.1
          · intro hm; exact absurd (Finset.mem_univ u) hm
        · rw [if_neg hbb]
          exact Finset.sum_eq_zero fun u' _ => Finset.sum_eq_zero fun v' _ => Finset.sum_eq_zero fun t' _ =>
            if_neg fun h => hbb (huniq_match hb' hb h.1 hmatch (h.2.trans hSeq.symm)).1
      rw [List.map_congr_left h1]
      have hls : ∀ (ls : List BoxCert), ls.Nodup → b ∈ ls → (ls.map fun b' => if b' = b then g b else 0).sum = g b := by
        intro ls
        induction ls with
        | nil => intro _ hm; exact absurd hm (by simp)
        | cons a as iha =>
          intro hnd hm
          rcases List.nodup_cons.mp hnd with ⟨hnot, hnd_as⟩
          rcases List.mem_cons.mp hm with rfl | hmas
          · simp only [List.map_cons, List.sum_cons, ↓reduceIte]
            have hz : (as.map fun b' => if b' = b then g b else 0).sum = 0 := by
              rw [List.map_congr_left fun x hx => if_neg (fun (he : x = b) => hnot (he ▸ hx))]
              induction as with | nil => simp | cons _ _ _ => simp
            linarith
          · have hne_ab : a ≠ b := fun he => hnot (he ▸ hmas)
            simp only [List.map_cons, List.sum_cons, hne_ab, ↓reduceIte, zero_add]
            exact iha hnd_as hmas
      exact hls boxes hnodup hb
    have hyS_eq : tripleY S = activeMoatWidth act b b.levels 0 (tripleClearance hn d S hcard) := by
      dsimp only [tripleY]; rw [dif_pos hcard]
      exact hcollapse (fun b' => activeMoatWidth act b' b'.levels 0 (tripleClearance hn d S hcard))
    rw [hyS_eq, hcollapse (fun b' =>
      ((boxLevelTriples b'.levels 0).map fun lv =>
        if act b' lv.1 lv.2.1 lv.2.2 ∧ (∀ x ∈ S, ∀ z ∉ S, toR lv.2.1 < d x z) then
          2 * (toR lv.2.2 - toR lv.1) -
            ∑ x ∈ S, ∑ z ∈ Finset.univ \ S,
              (max 0 (pot x + toR lv.2.2 + pot z - d x z) - max 0 (pot x + toR lv.1 + pot z - d x z))
        else 0).sum)]
    have htel := activeMoatWidth_telescoping_le act b (R := tripleClearance hn d S hcard) hφ_conv b.levels b.l1 0 0
      (hboxes b hb).levels_valid (by rw [toR_zero])
    rw [zero_add, hφ0, sub_zero] at htel
    refine le_trans ?_ htel
    refine le_of_eq (congrArg List.sum (List.map_congr_left fun lv _ => ?_))
    refine if_congr (and_congr_right fun _ => (lt_tripleClearance_iff hn d S hcard (toR lv.2.1)).symm) ?_ rfl
    congr 1
    dsimp only [φ]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  · push Not at hex
    have hzero_list : ∀ (g : BoxCert → ℝ),
        (boxes.map fun b => ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
          if MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S then g b else 0).sum = 0 := by
      intro g
      have h0 : boxes.map (fun b => ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
          if MatchesBox b rBuf X u v t ∧ ({u, v, t} : Finset (Fin n)) = S then g b else 0) =
          boxes.map (fun _ => (0 : ℝ)) :=
        List.map_congr_left fun b hb => Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ =>
          Finset.sum_eq_zero fun t _ => if_neg fun h => hex b hb u v t h.1 h.2
      rw [h0]; induction boxes with | nil => simp | cons _ _ _ => simp
    have hy0 : tripleY S = 0 := by
      dsimp only [tripleY]; rw [dif_pos hcard]; exact hzero_list _
    rw [hzero_list, hy0]; simp

end

end BHHBounds.Dual

