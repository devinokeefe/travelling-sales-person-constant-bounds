import BHHBounds.Dual.PoissonIntegrals

/-!
# Soundness of the 1D Base Fixed-Point Verifier (`baseVerifyInt`)

Proves `baseVerifyInt_le_baseIntegral`: for any valid step potential `(rho, w)` and `nD > 0`,
  `(baseVerifyInt rho w nD : ℝ) / 10 ^ 9 ≤ baseIntegral rho w`.

Splits cleanly into three parts:
1. `baseTerm1Loop_le`: first-order term `2 E[π(N₂(0))]`.
2. `basePenMarg_le`: marginal pair-penalty integral via `intDPosNum_eq`.
3. `basePenInter_le`: supermodular 2D interaction integral over `rho`-aligned `d`-knots using
   `diskInterArea_antitone_d`, `jointSurvHi_sound`, and `intDPosNum_eq`.
-/

open MeasureTheory Set Real
open BHHBounds.Geometry
open BHHBounds.Dual

namespace BHHBounds.Cert

/-! ## Helper: `expNegLo` Nonnegativity & `intDPosNum` Nonnegativity -/

private lemma expNegLo_nonneg (x : Int) : 0 ≤ expNegLo x := by
  unfold expNegLo
  by_cases h1 : x ≤ 0
  · rw [if_pos h1]; decide
  · rw [if_neg h1]
    dsimp only
    by_cases h2 : (x / 250000).toNat > 64
    · rw [if_pos h2]
    · rw [if_neg h2]
      split_ifs with h3
      · exact le_rfl
      · push Not at h3
        exact mulLo_nonneg (le_of_lt h3) (powLo_nonneg _ (by decide))

private lemma expNegHi_nonneg (x : Int) : 0 ≤ expNegHi x := by
  by_cases hx : 0 ≤ x
  · exact nonneg_of_toR_nonneg ((Real.exp_nonneg _).trans (le_expNegHi hx))
  · unfold expNegHi; rw [if_pos (by omega)]; decide

private lemma intDPosNum_nonneg {a b c : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ intDPosNum a b c := by
  have heq := intDPosNum_eq (c := c) hab
  have hnn : 0 ≤ ∫ d in (toR a)..(toR b), d * max 0 (toR c - d) := by
    refine intervalIntegral.integral_nonneg (toR_le_toR hab) fun d hd => ?_
    exact mul_nonneg ((toR_nonneg ha).trans hd.1) (le_max_left _ _)
  rw [← heq] at hnn
  have hden : (0 : ℝ) < 6 * (S : ℝ) ^ 3 := mul_pos (by norm_num) (pow_pos S_pos 3)
  have hnum : (0 : ℝ) ≤ (intDPosNum a b c : ℝ) := by
    by_contra hlt; push Not at hlt
    have : (intDPosNum a b c : ℝ) / (6 * (S : ℝ) ^ 3) < 0 := div_neg_of_neg_of_pos hlt hden
    linarith
  exact_mod_cast hnum

/-! ## Part 1: First-Order Term (`baseTerm1Loop_le`) -/

private lemma baseTerm1Loop_le_aux {rho w : Array Int} (hpot : ValidStepPot rho w) :
    ∀ (i : Nat) (acc : Int), i ≤ rho.size →
      (baseTerm1Loop rho w i acc : ℝ) / 10 ^ 9 ≤
        (acc : ℝ) / 10 ^ 9 +
        2 * ∑ j ∈ Finset.Ico i rho.size,
          (toR (w.getD j 0) - toR (wPrev w j)) *
            (1 + Real.pi * (toR (rho.getD j 0)) ^ 2) *
            Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2)) := by
  intro i acc hi
  induction hn : rho.size - i generalizing i acc with
  | zero =>
    have hieq : i = rho.size := by omega
    subst hieq
    rw [baseTerm1Loop, if_pos le_rfl]
    simp
  | succ m ih =>
    have hilt : i < rho.size := by omega
    rw [baseTerm1Loop, if_neg (by omega)]
    dsimp only
    set ri := rho.getD i 0
    set wi := w.getD i 0
    set wp := if (i == 0) = true then 0 else w.getD (i - 1) 0
    have hwp_eq : wp = wPrev w i := by
      dsimp only [wp]; unfold wPrev; by_cases h0 : i = 0 <;> simp [h0]
    set dw := wi - wp
    set aHi := mulHi piHi (mulHi ri ri)
    set eLo := expNegLo aHi
    set pLo := mulLo (S + aHi) eLo
    have hri_nn : 0 ≤ ri := hpot.rho_nonneg hilt
    have hdw_nn : 0 ≤ dw := by
      dsimp only [dw, wi]; rw [hwp_eq]
      have := stepPot_dw_nonneg hpot ⟨i, hilt⟩
      rw [← toR_sub] at this
      exact nonneg_of_toR_nonneg this
    have haHi_nn : 0 ≤ aHi := mulHi_nonneg (by decide) (mulHi_nonneg hri_nn hri_nn)
    have ha_le : Real.pi * (toR ri) ^ 2 ≤ toR aHi := by
      have hsq : (toR ri) ^ 2 ≤ toR (mulHi ri ri) := by rw [sq]; exact le_mulHi
      calc Real.pi * (toR ri) ^ 2
          ≤ toR piHi * toR (mulHi ri ri) :=
            mul_le_mul pi_le_piHi hsq (sq_nonneg _) (toR_nonneg (by decide))
        _ ≤ toR aHi := le_mulHi
    have heLo_nn : 0 ≤ eLo := expNegLo_nonneg aHi
    have heLo_le : toR eLo ≤ Real.exp (-toR aHi) := expNegLo_le haHi_nn
    have hpLo_le : toR pLo ≤
        (1 + Real.pi * (toR ri) ^ 2) * Real.exp (-(Real.pi * (toR ri) ^ 2)) := by
      have h1 : toR pLo ≤ toR (S + aHi) * toR eLo := mulLo_le
      have h2 : toR (S + aHi) * toR eLo ≤ (1 + toR aHi) * Real.exp (-toR aHi) := by
        rw [toR_add, toR_S]
        exact mul_le_mul_of_nonneg_left heLo_le (by linarith [toR_nonneg haHi_nn])
      have h3 : (1 + toR aHi) * Real.exp (-toR aHi) ≤
          (1 + Real.pi * (toR ri) ^ 2) * Real.exp (-(Real.pi * (toR ri) ^ 2)) := by
        simpa [extSurvProb] using
          extSurvProb_antitone (m₁ := 0) (m₂ := 0) le_rfl (by positivity) ha_le
      exact (h1.trans h2).trans h3
    have hstep : (((2 * dw * pLo) / 1000 : Int) : ℝ) / 10 ^ 9 ≤
        2 * (toR (w.getD i 0) - toR (wPrev w i)) *
          (1 + Real.pi * (toR (rho.getD i 0)) ^ 2) *
          Real.exp (-(Real.pi * (toR (rho.getD i 0)) ^ 2)) := by
      have h1 := int_ediv_le_real_div (a := 2 * dw * pLo) (b := 1000) (by decide)
      have h2 := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 10 ^ 9)
      have h3 : ((2 * dw * pLo : Int) : ℝ) / (1000 : ℝ) / 10 ^ 9 = 2 * toR dw * toR pLo := by
        unfold toR S; push_cast; ring
      have hdw_eq : toR dw = toR (w.getD i 0) - toR (wPrev w i) := by
        dsimp only [dw, wi]; rw [hwp_eq, toR_sub]
      have h4 : 2 * toR dw * toR pLo ≤
          2 * toR dw * ((1 + Real.pi * (toR ri) ^ 2) * Real.exp (-(Real.pi * (toR ri) ^ 2))) :=
        mul_le_mul_of_nonneg_left hpLo_le (mul_nonneg (by norm_num) (toR_nonneg hdw_nn))
      push_cast at h2 h3
      rw [hdw_eq] at h3 h4
      linarith
    have hih := ih (i + 1) (acc + (2 * dw * pLo) / 1000) (by omega) (by omega)
    have hsum : ∑ j ∈ Finset.Ico i rho.size,
        (toR (w.getD j 0) - toR (wPrev w j)) *
          (1 + Real.pi * (toR (rho.getD j 0)) ^ 2) *
          Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2)) =
        (toR (w.getD i 0) - toR (wPrev w i)) *
          (1 + Real.pi * (toR (rho.getD i 0)) ^ 2) *
          Real.exp (-(Real.pi * (toR (rho.getD i 0)) ^ 2)) +
        ∑ j ∈ Finset.Ico (i + 1) rho.size,
          (toR (w.getD j 0) - toR (wPrev w j)) *
            (1 + Real.pi * (toR (rho.getD j 0)) ^ 2) *
            Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2)) :=
      Finset.sum_eq_sum_Ico_succ_bot hilt _
    rw [hsum]
    push_cast at hih
    rw [add_div] at hih
    linarith

lemma baseTerm1Loop_le {rho w : Array Int} (hpot : ValidStepPot rho w) :
    (baseTerm1Loop rho w 0 0 : ℝ) / 10 ^ 9 ≤ baseTerm1 rho w := by
  have h := baseTerm1Loop_le_aux hpot 0 0 (Nat.zero_le _)
  simp only [Int.cast_zero, zero_div, zero_add] at h
  unfold baseTerm1
  rw [Fin.sum_univ_eq_sum_range (fun j =>
      (toR (w.getD j 0) - toR (wPrev w j)) *
        (1 + Real.pi * (toR (rho.getD j 0)) ^ 2) *
        Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2)))]
  simpa [Nat.Ico_zero_eq_range] using h

/-! ## Part 2: Marginal Pair-Penalty Term (`basePenMarg_le`) -/

private lemma basePenMargLoop_ge_aux {rho w : Array Int} (hpot : ValidStepPot rho w) :
    ∀ (i : Nat) (acc : Int), i ≤ rho.size →
      (acc : ℝ) / 10 ^ 9 +
      ∑ j ∈ Finset.Ico i rho.size,
        2 * Real.pi *
          ∫ d in (0 : ℝ)..(toR (w.getD j 0)),
            d * (max 0 (toR (w.getD j 0) - d) - max 0 (toR (wPrev w j) - d)) *
              (if d ≤ toR (rho.getD j 0) then
                Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2))
              else
                (1 + Real.pi * (toR (rho.getD j 0)) ^ 2) *
                  Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2))) ≤
        (basePenMargLoop rho w i acc : ℝ) / 10 ^ 9 := by
  intro i acc hi
  induction hn : rho.size - i generalizing i acc with
  | zero =>
    have hieq : i = rho.size := by omega
    subst hieq
    rw [basePenMargLoop, if_pos le_rfl]
    simp
  | succ m ih =>
    have hilt : i < rho.size := by omega
    rw [basePenMargLoop, if_neg (by omega)]
    dsimp only
    set denMarg : Int := 3000000000000000000000
    set ri := rho.getD i 0
    set wi := w.getD i 0
    set wp := if (i == 0) = true then 0 else w.getD (i - 1) 0
    have hwp_eq : wp = wPrev w i := by
      dsimp only [wp]; unfold wPrev; by_cases h0 : i = 0 <;> simp [h0]
    set aLo := mulLo piLo (mulLo ri ri)
    set pLoHi := expNegHi aLo
    set pHiHi := mulHi (S + aLo) pLoHi
    set intLo := intDPosNum 0 ri wi - intDPosNum 0 ri wp
    set intHi := if wi > ri then intDPosNum ri wi wi - intDPosNum ri wi wp else 0
    set numTot := pLoHi * intLo + pHiHi * intHi
    set term := (piHi * numTot + denMarg - 1) / denMarg
    have hri_nn : 0 ≤ ri := hpot.rho_nonneg hilt
    have hwi_nn : 0 ≤ wi := hpot.w_nonneg hilt
    have hwp_le : wp ≤ wi := by
      rw [hwp_eq]
      have := stepPot_dw_nonneg hpot ⟨i, hilt⟩
      rw [← toR_sub] at this
      have h0 := nonneg_of_toR_nonneg this
      dsimp only at h0
      dsimp only [wi]; omega
    have haLo_nn : 0 ≤ aLo := mulLo_nonneg (by decide) (mulLo_nonneg hri_nn hri_nn)
    have ha_ge : toR aLo ≤ Real.pi * (toR ri) ^ 2 := by
      have hsq : toR (mulLo ri ri) ≤ (toR ri) ^ 2 := by rw [sq]; exact mulLo_le
      calc toR aLo ≤ toR piLo * toR (mulLo ri ri) := mulLo_le
        _ ≤ Real.pi * (toR ri) ^ 2 :=
            mul_le_mul piLo_le_pi hsq (toR_nonneg (mulLo_nonneg hri_nn hri_nn)) (le_of_lt Real.pi_pos)
    have hpLo_ge : Real.exp (-(Real.pi * (toR ri) ^ 2)) ≤ toR pLoHi :=
      (Real.exp_le_exp.mpr (by linarith)).trans (le_expNegHi haLo_nn)
    have hpHi_ge : (1 + Real.pi * (toR ri) ^ 2) * Real.exp (-(Real.pi * (toR ri) ^ 2)) ≤ toR pHiHi := by
      have h1 : (1 + Real.pi * (toR ri) ^ 2) * Real.exp (-(Real.pi * (toR ri) ^ 2)) ≤
          (1 + toR aLo) * Real.exp (-toR aLo) := by
        simpa [extSurvProb] using
          extSurvProb_antitone (m₁ := 0) (m₂ := 0) le_rfl (toR_nonneg haLo_nn) ha_ge
      have h2 : (1 + toR aLo) * Real.exp (-toR aLo) ≤ toR (S + aLo) * toR pLoHi := by
        rw [toR_add, toR_S]
        exact mul_le_mul_of_nonneg_left (le_expNegHi haLo_nn) (by linarith [toR_nonneg haLo_nn])
      exact (h1.trans h2).trans le_mulHi
    have hpLo_le_pHi : Real.exp (-(Real.pi * (toR ri) ^ 2)) ≤ toR pHiHi := by
      have hpi2 : 0 ≤ Real.pi * (toR ri) ^ 2 := mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)
      calc Real.exp (-(Real.pi * (toR ri) ^ 2))
          ≤ (1 + Real.pi * (toR ri) ^ 2) * Real.exp (-(Real.pi * (toR ri) ^ 2)) := by
            nlinarith [Real.exp_pos (-(Real.pi * (toR ri) ^ 2))]
        _ ≤ toR pHiHi := hpHi_ge
    -- Bound the radial integral `∫ d in 0..(toR wi), ...`
    let g : ℝ → ℝ := fun d => d * (max 0 (toR wi - d) - max 0 (toR wp - d))
    let qf : ℝ → ℝ := fun d =>
      if d ≤ toR ri then Real.exp (-(Real.pi * (toR ri) ^ 2))
      else (1 + Real.pi * (toR ri) ^ 2) * Real.exp (-(Real.pi * (toR ri) ^ 2))
    have hg_cont : Continuous g := by dsimp only [g]; fun_prop
    have hg_nn : ∀ d, 0 ≤ d → 0 ≤ g d := fun d hd => by
      dsimp only [g]
      exact mul_nonneg hd (sub_nonneg.mpr (max_le_max_left 0 (by linarith [toR_le_toR hwp_le])))
    have hg_int : ∀ a b : Int, a ≤ b →
        ∫ d in (toR a)..(toR b), g d = ((intDPosNum a b wi - intDPosNum a b wp : Int) : ℝ) / (6 * (S : ℝ) ^ 3) := by
      intro a b hab
      have h1 := intDPosNum_eq (a := a) (b := b) (c := wi) hab
      have h2 := intDPosNum_eq (a := a) (b := b) (c := wp) hab
      have hsub : (∫ d in (toR a)..(toR b), d * max 0 (toR wi - d)) -
          (∫ d in (toR a)..(toR b), d * max 0 (toR wp - d)) =
          ∫ d in (toR a)..(toR b), g d := by
        rw [← intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun d : ℝ => d * max 0 (toR wi - d)).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun d : ℝ => d * max 0 (toR wp - d)).intervalIntegrable _ _)]
        refine intervalIntegral.integral_congr fun d _ => ?_
        dsimp only [g]; ring
      rw [← hsub, ← h1, ← h2]
      push_cast; ring
    have hint_le : ∫ d in (0 : ℝ)..(toR wi), g d * qf d ≤
        (numTot : ℝ) / (6 * (S : ℝ) ^ 4) := by
      by_cases hgt : wi > ri
      · have hsplit : IntervalIntegrable (fun d => g d * qf d) volume 0 (toR ri) ∧
            IntervalIntegrable (fun d => g d * qf d) volume (toR ri) (toR wi) := by
          constructor
          · refine ((hg_cont.mul (continuous_const (y := Real.exp (-(Real.pi * (toR ri) ^ 2))))).intervalIntegrable 0 (toR ri)).congr_ae ?_
            rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
            refine Filter.Eventually.of_forall fun d hd => ?_
            rw [Set.uIoc_of_le (toR_nonneg hri_nn)] at hd
            dsimp only [Pi.mul_apply, qf]; rw [if_pos hd.2]
          · refine ((hg_cont.mul (continuous_const (y := (1 + Real.pi * (toR ri) ^ 2) * Real.exp (-(Real.pi * (toR ri) ^ 2))))).intervalIntegrable (toR ri) (toR wi)).congr_ae ?_
            rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
            refine Filter.Eventually.of_forall fun d hd => ?_
            rw [Set.uIoc_of_le (toR_le_toR (le_of_lt hgt))] at hd
            dsimp only [Pi.mul_apply, qf]; rw [if_neg (not_le.mpr hd.1)]
        rw [← intervalIntegral.integral_add_adjacent_intervals hsplit.1 hsplit.2]
        have hpart1 : ∫ d in (0 : ℝ)..(toR ri), g d * qf d ≤
            toR pLoHi * (((intLo : Int) : ℝ) / (6 * (S : ℝ) ^ 3)) := by
          have hle := intervalIntegral.integral_mono_on (toR_nonneg hri_nn) hsplit.1
            ((hg_cont.mul continuous_const).intervalIntegrable _ _) fun d hd => by
              have hq : qf d ≤ toR pLoHi := by dsimp only [qf]; rw [if_pos hd.2]; exact hpLo_ge
              exact mul_le_mul_of_nonneg_left hq (hg_nn d hd.1)
          dsimp only [Pi.mul_apply] at hle
          rw [intervalIntegral.integral_mul_const, mul_comm] at hle
          have hzero : (0 : ℝ) = toR 0 := toR_zero.symm
          rw [hzero, hg_int 0 ri hri_nn] at hle
          rw [toR_zero] at hle
          exact hle
        have hpart2 : ∫ d in (toR ri)..(toR wi), g d * qf d ≤
            toR pHiHi * (((intHi : Int) : ℝ) / (6 * (S : ℝ) ^ 3)) := by
          have hle := intervalIntegral.integral_mono_on (toR_le_toR (le_of_lt hgt)) hsplit.2
            ((hg_cont.mul continuous_const).intervalIntegrable _ _) fun d hd => by
              have hq : qf d ≤ toR pHiHi := by
                dsimp only [qf]; split_ifs
                · exact hpLo_le_pHi
                · exact hpHi_ge
              exact mul_le_mul_of_nonneg_left hq (hg_nn d ((toR_nonneg hri_nn).trans hd.1))
          dsimp only [Pi.mul_apply] at hle
          rw [intervalIntegral.integral_mul_const, mul_comm] at hle
          rw [hg_int ri wi (le_of_lt hgt)] at hle
          dsimp only [intHi]; rw [if_pos hgt]; exact hle
        have hrhs : toR pLoHi * (((intLo : Int) : ℝ) / (6 * (S : ℝ) ^ 3)) +
            toR pHiHi * (((intHi : Int) : ℝ) / (6 * (S : ℝ) ^ 3)) =
            (numTot : ℝ) / (6 * (S : ℝ) ^ 4) := by
          dsimp only [numTot]; unfold toR; push_cast; ring
        linarith
      · -- Case `wi ≤ ri`: `qf d = exp(-π r^2)` on all of `[0, toR wi]`, and `g d = 0` on `[toR wi, toR ri]`!
        have hwle : wi ≤ ri := by omega
        have hint1 : IntervalIntegrable (fun d => g d * qf d) volume 0 (toR wi) := by
          refine ((hg_cont.mul (continuous_const (y := Real.exp (-(Real.pi * (toR ri) ^ 2))))).intervalIntegrable 0 (toR wi)).congr_ae ?_
          rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
          refine Filter.Eventually.of_forall fun d hd => ?_
          rw [Set.uIoc_of_le (toR_nonneg hwi_nn)] at hd
          dsimp only [Pi.mul_apply, qf]; rw [if_pos (hd.2.trans (toR_le_toR hwle))]
        have hle := intervalIntegral.integral_mono_on (toR_nonneg hwi_nn) hint1
          ((hg_cont.mul continuous_const).intervalIntegrable _ _) fun d hd => by
            have hq : qf d ≤ toR pLoHi := by
              dsimp only [qf]; rw [if_pos (hd.2.trans (toR_le_toR hwle))]; exact hpLo_ge
            exact mul_le_mul_of_nonneg_left hq (hg_nn d hd.1)
        dsimp only [Pi.mul_apply] at hle
        rw [intervalIntegral.integral_mul_const, mul_comm] at hle
        have hzero_tail : ∫ d in (toR wi)..(toR ri), g d = 0 := by
          have hc : ∫ d in (toR wi)..(toR ri), g d = ∫ _ in (toR wi)..(toR ri), (0 : ℝ) := by
            refine intervalIntegral.integral_congr fun d hd => ?_
            rw [Set.uIcc_of_le (toR_le_toR hwle)] at hd
            dsimp only [g]
            rw [max_eq_left (by linarith [hd.1]), max_eq_left (by linarith [hd.1, toR_le_toR hwp_le]),
                sub_self, mul_zero]
          rw [hc]; simp
        have heq_ext : ∫ d in (0 : ℝ)..(toR wi), g d = ∫ d in (0 : ℝ)..(toR ri), g d := by
          rw [← intervalIntegral.integral_add_adjacent_intervals
              (hg_cont.intervalIntegrable 0 (toR wi)) (hg_cont.intervalIntegrable (toR wi) (toR ri)),
              hzero_tail, add_zero]
        rw [heq_ext, show (0 : ℝ) = toR 0 from toR_zero.symm, hg_int 0 ri hri_nn] at hle
        rw [toR_zero] at hle
        have hnum_eq : numTot = pLoHi * intLo := by
          dsimp only [numTot, intHi]; rw [if_neg hgt]; ring
        have hrhs : toR pLoHi * (((intLo : Int) : ℝ) / (6 * (S : ℝ) ^ 3)) =
            (numTot : ℝ) / (6 * (S : ℝ) ^ 4) := by
          rw [hnum_eq]; unfold toR; push_cast; ring
        linarith
    have hint_nn : 0 ≤ ∫ d in (0 : ℝ)..(toR wi), g d * qf d := by
      refine intervalIntegral.integral_nonneg (toR_nonneg hwi_nn) fun d hd => ?_
      refine mul_nonneg (hg_nn d hd.1) ?_
      dsimp only [qf]; split_ifs
      · exact Real.exp_nonneg _
      · exact mul_nonneg (by positivity) (Real.exp_nonneg _)
    have hstep : 2 * Real.pi * ∫ d in (0 : ℝ)..(toR wi), g d * qf d ≤ (term : ℝ) / 10 ^ 9 := by
      have h1 : 2 * Real.pi * ∫ d in (0 : ℝ)..(toR wi), g d * qf d ≤
          2 * toR piHi * ((numTot : ℝ) / (6 * (S : ℝ) ^ 4)) := by
        have hnum_nn : 0 ≤ (numTot : ℝ) / (6 * (S : ℝ) ^ 4) := hint_nn.trans hint_le
        calc 2 * Real.pi * ∫ d in (0 : ℝ)..(toR wi), g d * qf d
            ≤ 2 * toR piHi * ∫ d in (0 : ℝ)..(toR wi), g d * qf d :=
              mul_le_mul_of_nonneg_right (by linarith [pi_le_piHi]) hint_nn
          _ ≤ 2 * toR piHi * ((numTot : ℝ) / (6 * (S : ℝ) ^ 4)) :=
              mul_le_mul_of_nonneg_left hint_le (by linarith [toR_nonneg (by decide : (0 : Int) ≤ piHi)])
      have h2 : 2 * toR piHi * ((numTot : ℝ) / (6 * (S : ℝ) ^ 4)) =
          ((piHi * numTot : Int) : ℝ) / (denMarg : ℝ) / 10 ^ 9 := by
        dsimp only [denMarg]; unfold toR S; push_cast; ring
      have h3 := div_le_div_of_nonneg_right
        (real_div_le_int_cdiv (a := piHi * numTot) (b := denMarg) (by dsimp only [denMarg]; decide))
        (by positivity : (0 : ℝ) ≤ 10 ^ 9)
      linarith
    have hih := ih (i + 1) (acc + term) (by omega) (by omega)
    have hsum : ∑ j ∈ Finset.Ico i rho.size,
        2 * Real.pi *
          ∫ d in (0 : ℝ)..(toR (w.getD j 0)),
            d * (max 0 (toR (w.getD j 0) - d) - max 0 (toR (wPrev w j) - d)) *
              (if d ≤ toR (rho.getD j 0) then
                Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2))
              else
                (1 + Real.pi * (toR (rho.getD j 0)) ^ 2) *
                  Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2))) =
        (2 * Real.pi * ∫ d in (0 : ℝ)..(toR wi), g d * qf d) +
        ∑ j ∈ Finset.Ico (i + 1) rho.size,
          2 * Real.pi *
            ∫ d in (0 : ℝ)..(toR (w.getD j 0)),
              d * (max 0 (toR (w.getD j 0) - d) - max 0 (toR (wPrev w j) - d)) *
                (if d ≤ toR (rho.getD j 0) then
                  Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2))
                else
                  (1 + Real.pi * (toR (rho.getD j 0)) ^ 2) *
                    Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2))) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hilt]
      congr 1; dsimp only [g, qf, wi, ri]; rw [hwp_eq]
    rw [hsum]
    push_cast at hih
    rw [add_div] at hih
    linarith

lemma basePenMarg_le {rho w : Array Int} (hpot : ValidStepPot rho w) :
    basePenMarg rho w ≤ (basePenMargLoop rho w 0 0 : ℝ) / 10 ^ 9 := by
  have h := basePenMargLoop_ge_aux hpot 0 0 (Nat.zero_le _)
  simp only [Int.cast_zero, zero_div, zero_add] at h
  unfold basePenMarg
  rw [Fin.sum_univ_eq_sum_range (fun j =>
      2 * Real.pi *
        ∫ d in (0 : ℝ)..(toR (w.getD j 0)),
          d * (max 0 (toR (w.getD j 0) - d) - max 0 (toR (wPrev w j) - d)) *
            (if d ≤ toR (rho.getD j 0) then
              Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2))
            else
              (1 + Real.pi * (toR (rho.getD j 0)) ^ 2) *
                Real.exp (-(Real.pi * (toR (rho.getD j 0)) ^ 2))))]
  simpa [Nat.Ico_zero_eq_range] using h

/-! ## Part 3: Knot-List Properties & 2D Interaction Term (`basePenInter_le`) -/

private lemma mem_mergeSortedLists {xs ys : List Int} {z : Int} :
    z ∈ mergeSortedLists xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  induction xs generalizing ys with
  | nil => simp [mergeSortedLists]
  | cons x xs ihx =>
    induction ys with
    | nil => simp [mergeSortedLists]
    | cons y ys ihy =>
      unfold mergeSortedLists
      split_ifs with h1 h2
      · simp only [List.mem_cons, ihx]; tauto
      · simp only [List.mem_cons, ihy]; tauto
      · have hxy : x = y := by omega
        subst hxy
        simp only [List.mem_cons, ihx]; tauto

private lemma pairwise_mergeSortedLists {xs ys : List Int}
    (hxs : xs.Pairwise (· ≤ ·)) (hys : ys.Pairwise (· ≤ ·)) :
    (mergeSortedLists xs ys).Pairwise (· ≤ ·) := by
  induction xs generalizing ys with
  | nil => simpa [mergeSortedLists] using hys
  | cons x xs ihx =>
    induction ys with
    | nil => simpa [mergeSortedLists] using hxs
    | cons y ys ihy =>
      unfold mergeSortedLists
      rcases List.pairwise_cons.mp hxs with ⟨hx_le, hxs'⟩
      rcases List.pairwise_cons.mp hys with ⟨hy_le, hys'⟩
      split_ifs with h1 h2
      · refine List.pairwise_cons.mpr ⟨?_, ihx hxs' hys⟩
        intro z hz
        rcases mem_mergeSortedLists.mp hz with hzx | hzy
        · exact hx_le z hzx
        · rcases List.mem_cons.mp hzy with rfl | hzy'
          · exact le_of_lt h1
          · exact (le_of_lt h1).trans (hy_le z hzy')
      · refine List.pairwise_cons.mpr ⟨?_, ihy hys'⟩
        intro z hz
        rcases mem_mergeSortedLists.mp hz with hzx | hzy
        · rcases List.mem_cons.mp hzx with rfl | hzx'
          · exact le_of_lt h2
          · exact (le_of_lt h2).trans (hx_le z hzx')
        · exact hy_le z hzy
      · have hxy : x = y := by omega
        subst hxy
        refine List.pairwise_cons.mpr ⟨?_, ihx hxs' hys'⟩
        intro z hz
        rcases mem_mergeSortedLists.mp hz with hzx | hzy
        · exact hx_le z hzx
        · exact hy_le z hzy

private lemma mergeSortedLists_head {xs ys : List Int} {a : Int}
    (hxs : xs.head? = some a) (hys : ∀ y ∈ ys, a < y) :
    (mergeSortedLists xs ys).head? = some a := by
  cases xs with
  | nil => simp at hxs
  | cons x xs' =>
    simp only [List.head?_cons, Option.some.injEq] at hxs
    subst hxs
    cases ys with
    | nil => simp [mergeSortedLists]
    | cons y ys' =>
      have hlt : x < y := hys y List.mem_cons_self
      unfold mergeSortedLists; rw [if_pos hlt]; simp

private lemma mergeSortedLists_getLast {xs ys : List Int} {b : Int}
    (hxs : xs.getLast? = some b) (hxs_le : ∀ x ∈ xs, x ≤ b) (hys : ∀ y ∈ ys, y < b) :
    (mergeSortedLists xs ys).getLast? = some b := by
  induction xs generalizing ys with
  | nil => simp at hxs
  | cons x xs' ihx =>
    induction ys with
    | nil => simpa [mergeSortedLists] using hxs
    | cons y ys' ihy =>
      have hyb : y < b := hys y List.mem_cons_self
      have hys_lt : ∀ z ∈ ys', z < b := fun z hz => hys z (List.mem_cons_of_mem y hz)
      have hne : ∀ l : List Int, l.getLast? = some b → l ≠ [] := fun l hl h => by rw [h] at hl; simp at hl
      unfold mergeSortedLists
      split_ifs with h1 h2
      · -- `x < y < b`, so `xs'` cannot be `[]`!
        have hxs_ne : xs' ≠ [] := by
          intro hnil; subst hnil
          simp only [List.getLast?_singleton, Option.some.injEq] at hxs
          omega
        have hxs'_last : xs'.getLast? = some b := by rwa [List.getLast?_cons_of_ne_nil hxs_ne] at hxs
        have hrec := ihx hxs'_last (fun z hz => hxs_le z (List.mem_cons_of_mem x hz)) hys
        rw [List.getLast?_cons_of_ne_nil (hne _ hrec), hrec]
      · have hrec := ihy hys_lt
        rw [List.getLast?_cons_of_ne_nil (hne _ hrec), hrec]
      · have hxy : x = y := by omega
        have hxs_ne : xs' ≠ [] := by
          intro hnil; subst hnil
          simp only [List.getLast?_singleton, Option.some.injEq] at hxs
          omega
        have hxs'_last : xs'.getLast? = some b := by rwa [List.getLast?_cons_of_ne_nil hxs_ne] at hxs
        have hrec := ihx hxs'_last (fun z hz => hxs_le z (List.mem_cons_of_mem x hz)) hys_lt
        rw [List.getLast?_cons_of_ne_nil (hne _ hrec), hrec]

private lemma buildDKnots_spec {rho w : Array Int} (hpot : ValidStepPot rho w)
    {dMax : Int} (hdMax : 0 ≤ dMax) {nD : Nat} (hnD : 0 < nD) :
    let knots := buildDKnots rho dMax nD
    knots.Pairwise (· ≤ ·) ∧
    knots.head? = some 0 ∧
    knots.getLast? = some dMax ∧
    (∀ i : Nat, i < rho.size → 0 < rho.getD i 0 → rho.getD i 0 < dMax → rho.getD i 0 ∈ knots) := by
  unfold buildDKnots
  set unif := (List.range (nD + 1)).map fun m => (dMax * Int.ofNat m) / Int.ofNat nD
  set rhoList := rho.toList.filter fun r => 0 < r ∧ r < dMax
  have hunif_pw : unif.Pairwise (· ≤ ·) := by
    dsimp only [unif]
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp fun {a b} hab => ?_
    simp only [Int.ofNat_eq_natCast]
    refine Int.ediv_le_ediv (by omega) ?_
    have : (a : Int) ≤ (b : Int) := by exact_mod_cast le_of_lt hab
    exact mul_le_mul_of_nonneg_left this hdMax
  have hrho_pw : rho.toList.Pairwise (· ≤ ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < rho.size := by simpa using hi
    have hj' : j < rho.size := by simpa using hj
    have hle := hpot.rho_le_of_le (le_of_lt hij) hj'
    simpa [Array.getD, dif_pos hi', dif_pos hj'] using hle
  have hrhoList_pw : rhoList.Pairwise (· ≤ ·) := hrho_pw.filter _
  have hunif_head : unif.head? = some 0 := by
    dsimp only [unif]
    rw [List.range_eq_range', List.range'_succ]
    simp
  have hunif_last : unif.getLast? = some dMax := by
    dsimp only [unif]
    rw [List.range_succ, List.map_append, List.getLast?_append_of_ne_nil _ (by simp)]
    simp only [List.map_singleton, List.getLast?_singleton, Option.some.injEq]
    simp only [Int.ofNat_eq_natCast]
    exact Int.mul_ediv_cancel dMax (by omega)
  have hunif_le : ∀ x ∈ unif, x ≤ dMax := by
    intro x hx
    dsimp only [unif] at hx
    rcases List.mem_map.mp hx with ⟨m, hm, rfl⟩
    rw [List.mem_range] at hm
    have h1 : dMax * (m : Int) ≤ dMax * (nD : Int) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_of_lt_succ hm) hdMax
    have h2 := Int.ediv_le_ediv (by omega : (0 : Int) < (nD : Int)) h1
    rw [Int.mul_ediv_cancel dMax (by omega : (nD : Int) ≠ 0)] at h2
    simpa only [Int.ofNat_eq_natCast] using h2
  have hrhoList_pos : ∀ r ∈ rhoList, 0 < r := fun r hr => by
    have := (List.mem_filter.mp hr).2; rw [decide_eq_true_eq] at this; exact this.1
  have hrhoList_lt : ∀ r ∈ rhoList, r < dMax := fun r hr => by
    have := (List.mem_filter.mp hr).2; rw [decide_eq_true_eq] at this; exact this.2
  refine ⟨pairwise_mergeSortedLists hunif_pw hrhoList_pw,
          mergeSortedLists_head hunif_head hrhoList_pos,
          mergeSortedLists_getLast hunif_last hunif_le hrhoList_lt, ?_⟩
  intro i hi hpos hlt
  rw [mem_mergeSortedLists]
  right
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · have heq : rho.getD i 0 = rho.toList[i]'(by simpa using hi) := by
      simp [Array.getD, dif_pos hi]
    rw [heq]
    exact List.getElem_mem _
  · rw [decide_eq_true_eq]; exact ⟨hpos, hlt⟩

/-- Measurability + integrability of `jointSurvReal` on `[a, b]` for fixed flags `(k1, k2)`. -/
private lemma intervalIntegrable_jointSurvReal (r1 r2 : ℝ) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (k1 k2 : Bool) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun d : ℝ => jointSurvReal d r1 r2 k1 k2) volume a b := by
  have hmeas_I : Measurable (fun d : ℝ => diskInterArea d r1 r2) := by
    unfold diskInterArea
    have hseg : Continuous segArea := by
      unfold segArea
      have hc : Continuous (fun c : ℝ => ∫ t in c..(1 : ℝ), Real.sqrt (1 - t ^ 2)) := by
        have heq : (fun c : ℝ => ∫ t in c..(1 : ℝ), Real.sqrt (1 - t ^ 2)) =
            fun c => -(∫ t in (1 : ℝ)..c, Real.sqrt (1 - t ^ 2)) := by
          funext c; rw [intervalIntegral.integral_symm]
        rw [heq]
        exact (intervalIntegral.continuous_primitive (μ := volume)
          (fun x y => (by fun_prop : Continuous fun t : ℝ => Real.sqrt (1 - t ^ 2)).intervalIntegrable x y) 1).neg
      exact continuous_const.mul hc
    have hm1 : MeasurableSet {d : ℝ | r1 ≤ 0 ∨ r2 ≤ 0 ∨ r1 + r2 ≤ d} := by
      by_cases h0 : r1 ≤ 0 ∨ r2 ≤ 0
      · have : {d : ℝ | r1 ≤ 0 ∨ r2 ≤ 0 ∨ r1 + r2 ≤ d} = Set.univ := by ext d; simp; tauto
        rw [this]; exact MeasurableSet.univ
      · have : {d : ℝ | r1 ≤ 0 ∨ r2 ≤ 0 ∨ r1 + r2 ≤ d} = {d : ℝ | r1 + r2 ≤ d} := by ext d; simp; tauto
        rw [this]; exact measurableSet_le measurable_const measurable_id
    refine Measurable.ite hm1 measurable_const ?_
    refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
    have hc1 : Measurable (fun d : ℝ => (d ^ 2 + r1 ^ 2 - r2 ^ 2) / (2 * d * r1)) := by fun_prop
    have hc2 : Measurable (fun d : ℝ => (d ^ 2 + r2 ^ 2 - r1 ^ 2) / (2 * d * r2)) := by fun_prop
    exact (measurable_const.mul (hseg.measurable.comp hc1)).add
      (measurable_const.mul (hseg.measurable.comp hc2))
  have hmeas : Measurable (fun d : ℝ => jointSurvReal d r1 r2 k1 k2) := by
    unfold jointSurvReal jointSurvCore
    cases k1 <;> cases k2 <;> dsimp only <;> fun_prop
  set C : ℝ := (1 + Real.pi * r1 ^ 2) * (1 + Real.pi * r2 ^ 2) + Real.pi * (min r1 r2) ^ 2 + 1
  have hbdd : ∀ d ∈ Set.uIcc a b, ‖jointSurvReal d r1 r2 k1 k2‖ ≤ C := by
    intro d hd
    rw [Set.uIcc_of_le hab] at hd
    have hd_nn : 0 ≤ d := ha.trans hd.1
    have hI0 : 0 ≤ diskInterArea d r1 r2 := diskInterArea_nonneg d r1 r2
    have hImin : diskInterArea d r1 r2 ≤ Real.pi * (min r1 r2) ^ 2 :=
      diskInterArea_le_min_disk hd_nn hr1 hr2
    have hI1 : diskInterArea d r1 r2 ≤ Real.pi * r1 ^ 2 :=
      hImin.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min hr1 hr2) (min_le_left _ _) 2) (le_of_lt Real.pi_pos))
    have hI2 : diskInterArea d r1 r2 ≤ Real.pi * r2 ^ 2 :=
      hImin.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min hr1 hr2) (min_le_right _ _) 2) (le_of_lt Real.pi_pos))
    have hau : 0 ≤ Real.pi * r1 ^ 2 + Real.pi * r2 ^ 2 - diskInterArea d r1 r2 := by linarith
    have hexp1 : Real.exp (-(Real.pi * r1 ^ 2 + Real.pi * r2 ^ 2 - diskInterArea d r1 r2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hnn : 0 ≤ jointSurvReal d r1 r2 k1 k2 := by
      unfold jointSurvReal jointSurvCore
      cases k1 <;> cases k2 <;> dsimp only
      · exact Real.exp_nonneg _
      · exact mul_nonneg (by linarith) (Real.exp_nonneg _)
      · exact mul_nonneg (by linarith) (Real.exp_nonneg _)
      · exact mul_nonneg (by nlinarith) (Real.exp_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    unfold jointSurvReal jointSurvCore
    cases k1 <;> cases k2 <;> dsimp only <;> dsimp only [C]
    · have : 0 ≤ (1 + Real.pi * r1 ^ 2) * (1 + Real.pi * r2 ^ 2) + Real.pi * (min r1 r2) ^ 2 := by positivity
      linarith
    · have h1 : 1 + (Real.pi * r2 ^ 2 - diskInterArea d r1 r2) ≤ 1 + Real.pi * r2 ^ 2 := by linarith
      have h2 : (1 + Real.pi * r2 ^ 2) ≤ (1 + Real.pi * r1 ^ 2) * (1 + Real.pi * r2 ^ 2) := by
        nlinarith [sq_nonneg r1, sq_nonneg r2, Real.pi_pos]
      have h3 : 0 ≤ Real.pi * (min r1 r2) ^ 2 := by positivity
      have h4 := mul_le_of_le_one_right (show 0 ≤ 1 + (Real.pi * r2 ^ 2 - diskInterArea d r1 r2) by linarith) hexp1
      linarith
    · have h1 : 1 + (Real.pi * r1 ^ 2 - diskInterArea d r1 r2) ≤ 1 + Real.pi * r1 ^ 2 := by linarith
      have h2 : (1 + Real.pi * r1 ^ 2) ≤ (1 + Real.pi * r1 ^ 2) * (1 + Real.pi * r2 ^ 2) := by
        nlinarith [sq_nonneg r1, sq_nonneg r2, Real.pi_pos]
      have h3 : 0 ≤ Real.pi * (min r1 r2) ^ 2 := by positivity
      have h4 := mul_le_of_le_one_right (show 0 ≤ 1 + (Real.pi * r1 ^ 2 - diskInterArea d r1 r2) by linarith) hexp1
      linarith
    · have h1 : (1 + (Real.pi * r1 ^ 2 - diskInterArea d r1 r2)) *
          (1 + (Real.pi * r2 ^ 2 - diskInterArea d r1 r2)) + diskInterArea d r1 r2 ≤
          (1 + Real.pi * r1 ^ 2) * (1 + Real.pi * r2 ^ 2) + Real.pi * (min r1 r2) ^ 2 := by
        nlinarith
      have hpos : 0 ≤ (1 + (Real.pi * r1 ^ 2 - diskInterArea d r1 r2)) *
          (1 + (Real.pi * r2 ^ 2 - diskInterArea d r1 r2)) + diskInterArea d r1 r2 := by nlinarith
      have h4 := mul_le_of_le_one_right hpos hexp1
      linarith
  exact MeasureTheory.IntegrableOn.intervalIntegrable
    (MeasureTheory.IntegrableOn.of_bound (by simp) hmeas.aestronglyMeasurable C
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIcc hbdd))

/-- Single-knot-interval upper bound on one `(i, j)` interaction integral (without `π` factor,
scaled to match `basePenInterJ`'s `10^12` accumulator units). -/
private lemma basePenInter_pair_le {rho w : Array Int} (hpot : ValidStepPot rho w)
    {da db : Int} (hda : 0 ≤ da) (hdb : da < db)
    (i j : Fin rho.size)
    (hno_i : rho.getD i.val 0 ≤ da ∨ db ≤ rho.getD i.val 0)
    (hno_j : rho.getD j.val 0 ≤ da ∨ db ≤ rho.getD j.val 0) :
    let ri := rho.getD i.val 0
    let rj := rho.getD j.val 0
    let wi := w.getD i.val 0
    let wip := wPrev w i.val
    let wj := w.getD j.val 0
    let wjp := wPrev w j.val
    let k1 := decide (db > ri)
    let k2 := decide (db > rj)
    let coeffNum := intDPosNum da db (wi + wj) - intDPosNum da db (wip + wj)
      - intDPosNum da db (wi + wjp) + intDPosNum da db (wip + wjp)
    ∫ d in (toR da)..(toR db),
      d * baseInterCoeff w i.val j.val d *
        jointSurvReal d (toR ri) (toR rj) (decide (toR ri < d)) (decide (toR rj < d)) ≤
      (coeffNum : ℝ) / (6 * (S : ℝ) ^ 3) * toR (jointSurvHi da ri rj k1 k2) := by
  intro ri rj wi wip wj wjp k1 k2 coeffNum
  have habR : toR da ≤ toR db := toR_le_toR (le_of_lt hdb)
  have hri_nn : 0 ≤ ri := hpot.rho_nonneg i.isLt
  have hrj_nn : 0 ≤ rj := hpot.rho_nonneg j.isLt
  -- For all `d ∈ Ioo (toR da) (toR db)`, `(toR ri < d) = k1` and `(toR rj < d) = k2`!
  have hflag : ∀ (r : Int), (r ≤ da ∨ db ≤ r) → ∀ d ∈ Set.Ioo (toR da) (toR db),
      decide (toR r < d) = decide (db > r) := by
    intro r hr d hd
    rcases hr with hle | hge
    · have h1 : toR r < d := lt_of_le_of_lt (toR_le_toR hle) hd.1
      have h2 : db > r := lt_of_le_of_lt hle hdb
      simp [h1, h2]
    · have h1 : ¬ (toR r < d) := not_lt.mpr ((le_of_lt hd.2).trans (toR_le_toR hge))
      have h2 : ¬ (db > r) := not_lt.mpr hge
      simp [h1, h2]
  have hjs_int : IntervalIntegrable (fun d => d * baseInterCoeff w i.val j.val d *
      jointSurvReal d (toR ri) (toR rj) k1 k2) volume (toR da) (toR db) := by
    have hcont : Continuous (fun d : ℝ => d * baseInterCoeff w i.val j.val d) := by
      unfold baseInterCoeff; fun_prop
    exact (intervalIntegrable_jointSurvReal (toR ri) (toR rj) (toR_nonneg hri_nn) (toR_nonneg hrj_nn)
      k1 k2 (toR da) (toR db) (toR_nonneg hda) habR).continuousOn_mul hcont.continuousOn
      |> fun h => by simpa [mul_comm] using h
  -- Rewrite integrand to constant flags `(k1, k2)` a.e. on `Ioc (toR da) (toR db)`!
  have hae : ∀ᵐ d ∂volume, d ∈ Set.uIoc (toR da) (toR db) →
      d * baseInterCoeff w i.val j.val d *
        jointSurvReal d (toR ri) (toR rj) (decide (toR ri < d)) (decide (toR rj < d)) =
      d * baseInterCoeff w i.val j.val d *
        jointSurvReal d (toR ri) (toR rj) k1 k2 := by
    have hne : ∀ᵐ d ∂volume, d ≠ toR db := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with d hdne hdmem
    rw [Set.uIoc_of_le habR] at hdmem
    have hIoo : d ∈ Set.Ioo (toR da) (toR db) := ⟨hdmem.1, lt_of_le_of_ne hdmem.2 hdne⟩
    rw [hflag ri hno_i d hIoo, hflag rj hno_j d hIoo]
  rw [intervalIntegral.integral_congr_ae hae]
  -- Pointwise bound: for all `d ∈ [toR da, toR db]`, `jointSurvReal d ≤ toR (jointSurvHi da ri rj k1 k2)`!
  have hjs_le : ∀ d ∈ Set.Icc (toR da) (toR db),
      jointSurvReal d (toR ri) (toR rj) k1 k2 ≤ toR (jointSurvHi da ri rj k1 k2) := by
    intro d hd
    have hI_le : diskInterArea d (toR ri) (toR rj) ≤ diskInterArea (toR da) (toR ri) (toR rj) :=
      diskInterArea_antitone_d (toR_nonneg hri_nn) (toR_nonneg hrj_nn) (toR_nonneg hda) hd.1
    have hmono : jointSurvReal d (toR ri) (toR rj) k1 k2 ≤
        jointSurvReal (toR da) (toR ri) (toR rj) k1 k2 := by
      unfold jointSurvReal
      have hI1 := diskInterArea_le_min_disk ((toR_nonneg hda).trans hd.1) (toR_nonneg hri_nn) (toR_nonneg hrj_nn)
      have hI2 := diskInterArea_le_min_disk (toR_nonneg hda) (toR_nonneg hri_nn) (toR_nonneg hrj_nn)
      have hm1 : Real.pi * (min (toR ri) (toR rj)) ^ 2 ≤ Real.pi * (toR ri) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min (toR_nonneg hri_nn) (toR_nonneg hrj_nn)) (min_le_left _ _) 2) (le_of_lt Real.pi_pos)
      have hm2 : Real.pi * (min (toR ri) (toR rj)) ^ 2 ≤ Real.pi * (toR rj) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min (toR_nonneg hri_nn) (toR_nonneg hrj_nn)) (min_le_right _ _) 2) (le_of_lt Real.pi_pos)
      exact jointSurvCore_mono le_rfl le_rfl (diskInterArea_nonneg _ _ _) (hI1.trans hm1) (hI1.trans hm2)
        (diskInterArea_nonneg _ _ _) (hI2.trans hm1) (hI2.trans hm2) (Or.inl hI_le) k1 k2
    exact hmono.trans (jointSurvHi_sound hda hri_nn hrj_nn k1 k2)
  have hcont_c : Continuous (fun d : ℝ => d * baseInterCoeff w i.val j.val d) := by
    unfold baseInterCoeff; fun_prop
  have hmono_int := intervalIntegral.integral_mono_on habR hjs_int
    ((hcont_c.mul continuous_const).intervalIntegrable _ _) fun d hd =>
      mul_le_mul_of_nonneg_left (hjs_le d hd)
        (mul_nonneg ((toR_nonneg hda).trans hd.1) (baseInterCoeff_nonneg hpot i j d))
  dsimp only [Pi.mul_apply] at hmono_int
  rw [intervalIntegral.integral_mul_const] at hmono_int
  -- Evaluate `∫ d in (toR da)..(toR db), d * baseInterCoeff w i j d = coeffNum / (6 S^3)`!
  have hcoeff_eq : ∫ d in (toR da)..(toR db), d * baseInterCoeff w i.val j.val d =
      (coeffNum : ℝ) / (6 * (S : ℝ) ^ 3) := by
    have h1 := intDPosNum_eq (a := da) (b := db) (c := wi + wj) (le_of_lt hdb)
    have h2 := intDPosNum_eq (a := da) (b := db) (c := wip + wj) (le_of_lt hdb)
    have h3 := intDPosNum_eq (a := da) (b := db) (c := wi + wjp) (le_of_lt hdb)
    have h4 := intDPosNum_eq (a := da) (b := db) (c := wip + wjp) (le_of_lt hdb)
    simp only [toR_add] at h1 h2 h3 h4
    have hci : ∀ c : ℝ, IntervalIntegrable (fun d : ℝ => d * max 0 (c - d)) volume (toR da) (toR db) :=
      fun c => (by fun_prop : Continuous fun d : ℝ => d * max 0 (c - d)).intervalIntegrable _ _
    have hlin : (∫ d in (toR da)..(toR db), d * max 0 (toR wi + toR wj - d)) -
        (∫ d in (toR da)..(toR db), d * max 0 (toR wip + toR wj - d)) -
        (∫ d in (toR da)..(toR db), d * max 0 (toR wi + toR wjp - d)) +
        (∫ d in (toR da)..(toR db), d * max 0 (toR wip + toR wjp - d)) =
        ∫ d in (toR da)..(toR db), d * baseInterCoeff w i.val j.val d := by
      rw [← intervalIntegral.integral_sub (hci _) (hci _),
          ← intervalIntegral.integral_sub ((hci _).sub (hci _)) (hci _),
          ← intervalIntegral.integral_add (((hci _).sub (hci _)).sub (hci _)) (hci _)]
      refine intervalIntegral.integral_congr fun d _ => ?_
      unfold baseInterCoeff; dsimp only [wi, wip, wj, wjp]; ring
    rw [← hlin, ← h1, ← h2, ← h3, ← h4]
    dsimp only [coeffNum]; push_cast; ring
  rw [hcoeff_eq] at hmono_int
  exact hmono_int

/-- Inner `j` loop bound on `[da, db]`. -/
private lemma basePenInterJ_ge {rho w : Array Int} (hpot : ValidStepPot rho w)
    {da db : Int} (hda : 0 ≤ da) (hdb : da < db)
    (hno : ∀ k : Nat, k < rho.size → rho.getD k 0 ≤ da ∨ db ≤ rho.getD k 0)
    (i : Fin rho.size) :
    let ri := rho.getD i.val 0
    let wi := w.getD i.val 0
    let wip := if (i.val == 0) = true then 0 else w.getD (i.val - 1) 0
    let k1 := decide (db > ri)
    ∀ (j : Nat) (acc : Int), j ≤ rho.size →
      (acc : ℝ) / (6 * (S : ℝ) ^ 2) +
      ∑ jj ∈ (Finset.univ.filter fun x : Fin rho.size => j ≤ x.val),
        (if i.val = jj.val then (1 : ℝ) else 2) *
        ∫ d in (toR da)..(toR db),
          d * baseInterCoeff w i.val jj.val d *
            jointSurvReal d (toR ri) (toR (rho.getD jj.val 0))
              (decide (toR ri < d)) (decide (toR (rho.getD jj.val 0) < d)) ≤
        (basePenInterJ rho w da db i.val ri wi wip k1 j acc : ℝ) / (6 * (S : ℝ) ^ 2) := by
  intro ri wi wip k1 j acc hj
  have hwip_eq : wip = wPrev w i.val := by
    dsimp only [wip]; unfold wPrev; by_cases h0 : i.val = 0 <;> simp [h0]
  induction hn : rho.size - j generalizing j acc with
  | zero =>
    have hjeq : j = rho.size := by omega
    subst hjeq
    rw [basePenInterJ, if_pos le_rfl]
    have hemp : (Finset.univ.filter fun x : Fin rho.size => rho.size ≤ x.val) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [hemp, Finset.sum_empty, add_zero]
  | succ m ih =>
    have hjlt : j < rho.size := by omega
    rw [basePenInterJ, if_neg (by omega)]
    dsimp only
    let jf : Fin rho.size := ⟨j, hjlt⟩
    set wj := w.getD j 0
    set wjp := if (j == 0) = true then 0 else w.getD (j - 1) 0
    have hwjp_eq : wjp = wPrev w j := by
      dsimp only [wjp]; unfold wPrev; by_cases h0 : j = 0 <;> simp [h0]
    set mult : Int := if (i.val == j) = true then 1 else 2
    have hmultR : (mult : ℝ) = if i.val = j then (1 : ℝ) else 2 := by
      dsimp only [mult]; by_cases hEq : i.val = j <;> simp [hEq]
    -- Split `jf` out of the filtered Finset sum
    have hfilt_eq : (Finset.univ.filter fun x : Fin rho.size => j ≤ x.val) =
        insert jf (Finset.univ.filter fun x : Fin rho.size => j + 1 ≤ x.val) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff, jf]; omega
    have hnotmem : jf ∉ Finset.univ.filter (fun x : Fin rho.size => j + 1 ≤ x.val) := by
      simp [jf]
    rw [hfilt_eq, Finset.sum_insert hnotmem]
    -- Prove the single-step bound for `jf`
    set acc' :=
      if wi + wj > da then
        let coeffNum := intDPosNum da db (wi + wj) - intDPosNum da db (wip + wj)
          - intDPosNum da db (wi + wjp) + intDPosNum da db (wip + wjp)
        if coeffNum > 0 then
          let rj := rho.getD j 0
          let k2 := decide (db > rj)
          let jsHi := jointSurvHi da ri rj k1 k2
          acc + (mult * coeffNum * jsHi + 999999999999) / 1000000000000
        else acc
      else acc
    have hpair_step : (if i.val = j then (1 : ℝ) else 2) *
        ∫ d in (toR da)..(toR db),
          d * baseInterCoeff w i.val j d *
            jointSurvReal d (toR ri) (toR (rho.getD j 0))
              (decide (toR ri < d)) (decide (toR (rho.getD j 0) < d)) ≤
        ((acc' - acc : Int) : ℝ) / (6 * (S : ℝ) ^ 2) := by
      have hpair := basePenInter_pair_le hpot hda hdb i jf (hno i.val i.isLt) (hno j hjlt)
      dsimp only [jf] at hpair
      set coeffNum := intDPosNum da db (wi + wj) - intDPosNum da db (wip + wj)
        - intDPosNum da db (wi + wjp) + intDPosNum da db (wip + wjp)
      have hcoeff_eq : intDPosNum da db (w.getD i.val 0 + w.getD j 0) -
          intDPosNum da db (wPrev w i.val + w.getD j 0) -
          intDPosNum da db (w.getD i.val 0 + wPrev w j) +
          intDPosNum da db (wPrev w i.val + wPrev w j) = coeffNum := by
        dsimp only [coeffNum, wi, wj]; rw [hwip_eq, hwjp_eq]
      rw [hcoeff_eq] at hpair
      have hmult_nn : (0 : ℝ) ≤ if i.val = j then 1 else 2 := by split_ifs <;> norm_num
      by_cases hwiwj : wi + wj > da
      · by_cases hpos : coeffNum > 0
        · have hacc' : acc' - acc = (mult * coeffNum * jointSurvHi da ri (rho.getD j 0) k1 (decide (db > rho.getD j 0)) + 999999999999) / 1000000000000 := by
            dsimp only [acc']; rw [if_pos hwiwj, if_pos hpos]; ring
          rw [hacc']
          set jsHi := jointSurvHi da ri (rho.getD j 0) k1 (decide (db > rho.getD j 0))
          have h1 := mul_le_mul_of_nonneg_left hpair hmult_nn
          have h2 : (if i.val = j then (1 : ℝ) else 2) * ((coeffNum : ℝ) / (6 * (S : ℝ) ^ 3) * toR jsHi) =
              ((mult * coeffNum * jsHi : Int) : ℝ) / (1000000000000 : ℝ) / (6 * (S : ℝ) ^ 2) := by
            rw [← hmultR]; unfold toR S; push_cast; ring
          have h3 := real_div_le_int_cdiv (a := mult * coeffNum * jsHi) (b := 1000000000000) (by decide)
          rw [show mult * coeffNum * jsHi + 1000000000000 - 1 =
              mult * coeffNum * jsHi + 999999999999 by omega] at h3
          have h4 := div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 6 * (S : ℝ) ^ 2)
          push_cast at h2 h4
          linarith
        · have hacc' : acc' - acc = 0 := by dsimp only [acc']; rw [if_pos hwiwj, if_neg hpos]; ring
          rw [hacc', Int.cast_zero, zero_div]
          have hjs_nn : 0 ≤ toR (jointSurvHi da ri (rho.getD j 0) k1 (decide (db > rho.getD j 0))) := by
            have := jointSurvHi_sound hda (hpot.rho_nonneg i.isLt) (hpot.rho_nonneg hjlt) k1 (decide (db > rho.getD j 0))
            have h0 : 0 ≤ jointSurvReal (toR da) (toR ri) (toR (rho.getD j 0)) k1 (decide (db > rho.getD j 0)) := by
              unfold jointSurvReal jointSurvCore
              have hI0 := diskInterArea_nonneg (toR da) (toR ri) (toR (rho.getD j 0))
              have hImin := diskInterArea_le_min_disk (toR_nonneg hda) (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg hjlt))
              have hm1 : Real.pi * (min (toR ri) (toR (rho.getD j 0))) ^ 2 ≤ Real.pi * (toR ri) ^ 2 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg hjlt))) (min_le_left _ _) 2) (le_of_lt Real.pi_pos)
              have hm2 : Real.pi * (min (toR ri) (toR (rho.getD j 0))) ^ 2 ≤ Real.pi * (toR (rho.getD j 0)) ^ 2 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg hjlt))) (min_le_right _ _) 2) (le_of_lt Real.pi_pos)
              cases k1 <;> cases (decide (db > rho.getD j 0)) <;> dsimp only
              · exact Real.exp_nonneg _
              · exact mul_nonneg (by linarith) (Real.exp_nonneg _)
              · exact mul_nonneg (by linarith) (Real.exp_nonneg _)
              · exact mul_nonneg (by nlinarith) (Real.exp_nonneg _)
            exact h0.trans this
          have hcnp : (coeffNum : ℝ) ≤ 0 := by exact_mod_cast (by omega : coeffNum ≤ 0)
          have hrhs_np : (coeffNum : ℝ) / (6 * (S : ℝ) ^ 3) * toR (jointSurvHi da ri (rho.getD j 0) k1 (decide (db > rho.getD j 0))) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hcnp (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt S_pos) 3))) hjs_nn
          exact mul_nonpos_of_nonneg_of_nonpos hmult_nn (hpair.trans hrhs_np)
      · -- `wi + wj ≤ da`: `baseInterCoeff w i j d = 0` for all `d ≥ toR da`!
        have hacc' : acc' - acc = 0 := by dsimp only [acc']; rw [if_neg hwiwj]; ring
        rw [hacc', Int.cast_zero, zero_div]
        have hzero : ∫ d in (toR da)..(toR db),
            d * baseInterCoeff w i.val j d *
              jointSurvReal d (toR ri) (toR (rho.getD j 0))
                (decide (toR ri < d)) (decide (toR (rho.getD j 0) < d)) = 0 := by
          have hc : (∫ d in (toR da)..(toR db),
              d * baseInterCoeff w i.val j d *
                jointSurvReal d (toR ri) (toR (rho.getD j 0))
                  (decide (toR ri < d)) (decide (toR (rho.getD j 0) < d))) =
              ∫ _ in (toR da)..(toR db), (0 : ℝ) := by
            refine intervalIntegral.integral_congr fun d hd => ?_
            rw [Set.uIcc_of_le (toR_le_toR (le_of_lt hdb))] at hd
            have hle : toR wi + toR wj ≤ d := by
              have : wi + wj ≤ da := by omega
              have hR := toR_le_toR this
              rw [toR_add] at hR; linarith [hd.1]
            have hdw_i := stepPot_dw_nonneg hpot i
            have hdw_j := stepPot_dw_nonneg hpot jf
            have hcoeff0 : baseInterCoeff w i.val j d = 0 := by
              unfold baseInterCoeff
              rw [max_eq_left (by linarith), max_eq_left (by linarith),
                  max_eq_left (by linarith), max_eq_left (by linarith)]
              ring
            rw [hcoeff0, mul_zero, zero_mul]
          rw [hc]; simp
        rw [hzero, mul_zero]
    have hih := ih (j + 1) acc' (by omega) (by omega)
    have hacc_split : (acc' : ℝ) / (6 * (S : ℝ) ^ 2) =
        (acc : ℝ) / (6 * (S : ℝ) ^ 2) + ((acc' - acc : Int) : ℝ) / (6 * (S : ℝ) ^ 2) := by
      push_cast; ring
    linarith

/-- Outer `i` loop bound on a single knot interval `[da, db]`. -/
private lemma basePenInterI_ge {rho w : Array Int} (hpot : ValidStepPot rho w)
    {da db : Int} (hda : 0 ≤ da) (hdb : da < db)
    (hno : ∀ k : Nat, k < rho.size → rho.getD k 0 ≤ da ∨ db ≤ rho.getD k 0) :
    let wMax := w.getD (rho.size - 1) 0
    ∀ (i : Nat) (acc : Int), i ≤ rho.size →
      (acc : ℝ) / (6 * (S : ℝ) ^ 2) +
      ∑ ii ∈ (Finset.univ.filter fun x : Fin rho.size => i ≤ x.val),
        ∑ jj ∈ (Finset.univ.filter fun x : Fin rho.size => ii.val ≤ x.val),
          (if ii.val = jj.val then (1 : ℝ) else 2) *
          ∫ d in (toR da)..(toR db),
            d * baseInterCoeff w ii.val jj.val d *
              jointSurvReal d (toR (rho.getD ii.val 0)) (toR (rho.getD jj.val 0))
                (decide (toR (rho.getD ii.val 0) < d)) (decide (toR (rho.getD jj.val 0) < d)) ≤
        (basePenInterI rho w da db wMax i acc : ℝ) / (6 * (S : ℝ) ^ 2) := by
  intro wMax i acc hi
  induction hn : rho.size - i generalizing i acc with
  | zero =>
    have hieq : i = rho.size := by omega
    subst hieq
    rw [basePenInterI, if_pos le_rfl]
    have hemp : (Finset.univ.filter fun x : Fin rho.size => rho.size ≤ x.val) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [hemp, Finset.sum_empty, add_zero]
  | succ m ih =>
    have hilt : i < rho.size := by omega
    rw [basePenInterI, if_neg (by omega)]
    dsimp only
    let fi : Fin rho.size := ⟨i, hilt⟩
    have hfilt_eq : (Finset.univ.filter fun x : Fin rho.size => i ≤ x.val) =
        insert fi (Finset.univ.filter fun x : Fin rho.size => i + 1 ≤ x.val) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff, fi]; omega
    have hnotmem : fi ∉ Finset.univ.filter (fun x : Fin rho.size => i + 1 ≤ x.val) := by
      simp [fi]
    rw [hfilt_eq, Finset.sum_insert hnotmem]
    set wi := w.getD i 0
    set acc' :=
      if wi + wMax > da then
        let wip := if (i == 0) = true then 0 else w.getD (i - 1) 0
        let ri := rho.getD i 0
        let k1 := decide (db > ri)
        basePenInterJ rho w da db i ri wi wip k1 i acc
      else acc
    have hrow : (acc : ℝ) / (6 * (S : ℝ) ^ 2) +
        ∑ jj ∈ (Finset.univ.filter fun x : Fin rho.size => i ≤ x.val),
          (if i = jj.val then (1 : ℝ) else 2) *
          ∫ d in (toR da)..(toR db),
            d * baseInterCoeff w i jj.val d *
              jointSurvReal d (toR (rho.getD i 0)) (toR (rho.getD jj.val 0))
                (decide (toR (rho.getD i 0) < d)) (decide (toR (rho.getD jj.val 0) < d)) ≤
        (acc' : ℝ) / (6 * (S : ℝ) ^ 2) := by
      by_cases hgt : wi + wMax > da
      · dsimp only [acc']; rw [if_pos hgt]
        exact basePenInterJ_ge hpot hda hdb hno fi i acc (le_of_lt hilt)
      · dsimp only [acc']; rw [if_neg hgt]
        have hzero : ∑ jj ∈ (Finset.univ.filter fun x : Fin rho.size => i ≤ x.val),
            (if i = jj.val then (1 : ℝ) else 2) *
            ∫ d in (toR da)..(toR db),
              d * baseInterCoeff w i jj.val d *
                jointSurvReal d (toR (rho.getD i 0)) (toR (rho.getD jj.val 0))
                  (decide (toR (rho.getD i 0) < d)) (decide (toR (rho.getD jj.val 0) < d)) = 0 := by
          refine Finset.sum_eq_zero fun jj _ => ?_
          have hjj_le : w.getD jj.val 0 ≤ wMax := hpot.w_le_of_le (by omega) (by omega)
          have hle_da : wi + w.getD jj.val 0 ≤ da := by omega
          have h0 : (∫ d in (toR da)..(toR db),
              d * baseInterCoeff w i jj.val d *
                jointSurvReal d (toR (rho.getD i 0)) (toR (rho.getD jj.val 0))
                  (decide (toR (rho.getD i 0) < d)) (decide (toR (rho.getD jj.val 0) < d))) = 0 := by
            have hc : (∫ d in (toR da)..(toR db),
                d * baseInterCoeff w i jj.val d *
                  jointSurvReal d (toR (rho.getD i 0)) (toR (rho.getD jj.val 0))
                    (decide (toR (rho.getD i 0) < d)) (decide (toR (rho.getD jj.val 0) < d))) =
                ∫ _ in (toR da)..(toR db), (0 : ℝ) := by
              refine intervalIntegral.integral_congr fun d hd => ?_
              rw [Set.uIcc_of_le (toR_le_toR (le_of_lt hdb))] at hd
              have hle : toR wi + toR (w.getD jj.val 0) ≤ d := by
                have hR := toR_le_toR hle_da
                rw [toR_add] at hR; linarith [hd.1]
              have hdw_i := stepPot_dw_nonneg hpot fi
              have hdw_j := stepPot_dw_nonneg hpot jj
              have hcoeff0 : baseInterCoeff w i jj.val d = 0 := by
                unfold baseInterCoeff
                rw [max_eq_left (by linarith), max_eq_left (by linarith),
                    max_eq_left (by linarith), max_eq_left (by linarith)]
                ring
              rw [hcoeff0, mul_zero, zero_mul]
            rw [hc]; simp
          rw [h0, mul_zero]
        rw [hzero, add_zero]
    have hih := ih (i + 1) acc' (by omega) (by omega)
    linarith

/-- Symmetry of the double sum over `(i, j)` into the upper triangle `i ≤ j` with multiplicity `1` or `2`. -/
private lemma sum_symm_upper {n : Nat} (f : Fin n → Fin n → ℝ) (hsymm : ∀ i j, f i j = f j i) :
    ∑ i : Fin n, ∑ j : Fin n, f i j =
      ∑ i : Fin n, ∑ j ∈ (Finset.univ.filter fun x : Fin n => i.val ≤ x.val),
        (if i.val = j.val then (1 : ℝ) else 2) * f i j := by
  have hsplit : ∀ i : Fin n, ∑ j : Fin n, f i j =
      (∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val = x.val), f i j) +
      (∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val < x.val), f i j) +
      (∑ j ∈ Finset.univ.filter (fun x : Fin n => x.val < i.val), f i j) := by
    intro i
    have h1 := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun x : Fin n => i.val ≤ x.val) (f := fun j => f i j)
    have h2 := Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter fun x : Fin n => i.val ≤ x.val)
      (p := fun x : Fin n => i.val = x.val) (f := fun j => f i j)
    have hfeq1 : (Finset.univ.filter fun x : Fin n => ¬ i.val ≤ x.val) =
        Finset.univ.filter fun x : Fin n => x.val < i.val := by ext x; simp
    have hfeq2 : ((Finset.univ.filter fun x : Fin n => i.val ≤ x.val).filter fun x : Fin n => i.val = x.val) =
        Finset.univ.filter fun x : Fin n => i.val = x.val := by ext x; simp; omega
    have hfeq3 : ((Finset.univ.filter fun x : Fin n => i.val ≤ x.val).filter fun x : Fin n => ¬ i.val = x.val) =
        Finset.univ.filter fun x : Fin n => i.val < x.val := by ext x; simp; omega
    rw [hfeq1] at h1; rw [hfeq2, hfeq3] at h2; linarith
  have hlower : ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun x : Fin n => x.val < i.val), f i j =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val < x.val), f i j := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i]
  have hrhs_split : ∀ i : Fin n,
      ∑ j ∈ (Finset.univ.filter fun x : Fin n => i.val ≤ x.val),
        (if i.val = j.val then (1 : ℝ) else 2) * f i j =
      (∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val = x.val), f i j) +
      2 * (∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val < x.val), f i j) := by
    intro i
    have h2 := Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter fun x : Fin n => i.val ≤ x.val)
      (p := fun x : Fin n => i.val = x.val)
      (f := fun j => (if i.val = j.val then (1 : ℝ) else 2) * f i j)
    have hfeq2 : ((Finset.univ.filter fun x : Fin n => i.val ≤ x.val).filter fun x : Fin n => i.val = x.val) =
        Finset.univ.filter fun x : Fin n => i.val = x.val := by ext x; simp; omega
    have hfeq3 : ((Finset.univ.filter fun x : Fin n => i.val ≤ x.val).filter fun x : Fin n => ¬ i.val = x.val) =
        Finset.univ.filter fun x : Fin n => i.val < x.val := by ext x; simp; omega
    rw [hfeq2, hfeq3] at h2
    have ha : (∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val = x.val),
        (if i.val = j.val then (1 : ℝ) else 2) * f i j) =
        ∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val = x.val), f i j :=
      Finset.sum_congr rfl fun j hj => by simp [(Finset.mem_filter.mp hj).2]
    have hb : (∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val < x.val),
        (if i.val = j.val then (1 : ℝ) else 2) * f i j) =
        2 * ∑ j ∈ Finset.univ.filter (fun x : Fin n => i.val < x.val), f i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : i.val ≠ j.val := ne_of_lt (Finset.mem_filter.mp hj).2
      simp [hne]
    linarith
  simp_rw [hsplit, hrhs_split, Finset.sum_add_distrib]
  rw [hlower, ← Finset.mul_sum]
  ring

/-- Walk `basePenInterKnots` over any sorted knot list `ks` covering `[a, b]` with no `rho`-knots
strictly inside consecutive pairs. -/
private lemma basePenInterKnots_ge {rho w : Array Int} (hpot : ValidStepPot rho w) :
    let wMax := w.getD (rho.size - 1) 0
    ∀ (ks : List Int) (a b : Int) (acc : Int),
      ks.Pairwise (· ≤ ·) →
      ks.head? = some a →
      ks.getLast? = some b →
      0 ≤ a →
      (∀ k : Nat, k < rho.size → ∀ da db : Int,
        (∃ l₁ l₂, ks = l₁ ++ da :: db :: l₂) → rho.getD k 0 ≤ da ∨ db ≤ rho.getD k 0) →
      (acc : ℝ) / (6 * (S : ℝ) ^ 2) +
      ∫ d in (toR a)..(toR b),
        d * ∑ i : Fin rho.size, ∑ j : Fin rho.size,
          baseInterCoeff w i.val j.val d *
            jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
              (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) ≤
        (basePenInterKnots rho w wMax ks acc : ℝ) / (6 * (S : ℝ) ^ 2) := by
  intro wMax ks
  induction ks with
  | nil => intro a b acc _ hhead; simp at hhead
  | cons da rest ih =>
    cases rest with
    | nil =>
      intro a b acc _ hhead hlast _ _
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hhead; subst hlast
      simp [basePenInterKnots]
    | cons db rest' =>
      intro a b acc hpw hhead hlast ha hno
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      have hpw_tail : (db :: rest').Pairwise (· ≤ ·) := (List.pairwise_cons.mp hpw).2
      have hda_db : da ≤ db := (List.pairwise_cons.mp hpw).1 db List.mem_cons_self
      have hlast_tail : (db :: rest').getLast? = some b := by
        rwa [List.getLast?_cons_of_ne_nil (by simp)] at hlast
      have hno_head : ∀ k : Nat, k < rho.size → rho.getD k 0 ≤ da ∨ db ≤ rho.getD k 0 :=
        fun k hk => hno k hk da db ⟨[], rest', rfl⟩
      have hno_tail : ∀ k : Nat, k < rho.size → ∀ x y : Int,
          (∃ l₁ l₂, db :: rest' = l₁ ++ x :: y :: l₂) → rho.getD k 0 ≤ x ∨ y ≤ rho.getD k 0 := by
        intro k hk x y ⟨l₁, l₂, heq⟩
        exact hno k hk x y ⟨da :: l₁, l₂, by simp [heq]⟩
      set F : ℝ → ℝ := fun d => d * ∑ i : Fin rho.size, ∑ j : Fin rho.size,
        baseInterCoeff w i.val j.val d *
          jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
            (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))
      -- Helper: `F` is integrable on any `[toR x, toR y]` with `0 ≤ x ≤ y`!
      have hF_int : ∀ x y : Int, 0 ≤ x → x ≤ y →
          (∀ k : Nat, k < rho.size → rho.getD k 0 ≤ x ∨ y ≤ rho.getD k 0) →
          IntervalIntegrable F volume (toR x) (toR y) := by
        intro x y hx hxy hno_xy
        by_cases hlt : x < y
        · have hterm : ∀ i j : Fin rho.size,
              IntervalIntegrable (fun d => d * baseInterCoeff w i.val j.val d *
                jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                  (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)))
                volume (toR x) (toR y) := by
            intro i j
            set ri := rho.getD i.val 0
            set rj := rho.getD j.val 0
            set k1 := decide (y > ri)
            set k2 := decide (y > rj)
            have hcont : Continuous (fun d : ℝ => d * baseInterCoeff w i.val j.val d) := by
              unfold baseInterCoeff; fun_prop
            have hbase : IntervalIntegrable (fun d => d * baseInterCoeff w i.val j.val d *
                jointSurvReal d (toR ri) (toR rj) k1 k2) volume (toR x) (toR y) := by
              simpa [mul_comm] using (intervalIntegrable_jointSurvReal (toR ri) (toR rj)
                (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg j.isLt))
                k1 k2 (toR x) (toR y) (toR_nonneg hx) (toR_le_toR hxy)).continuousOn_mul hcont.continuousOn
            refine hbase.congr_ae ?_
            rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
            have hne : ∀ᵐ d ∂volume, d ≠ toR y := by rw [MeasureTheory.ae_iff]; simp
            filter_upwards [hne] with d hdne hdmem
            rw [Set.uIoc_of_le (toR_le_toR hxy)] at hdmem
            have hIoo : d ∈ Set.Ioo (toR x) (toR y) := ⟨hdmem.1, lt_of_le_of_ne hdmem.2 hdne⟩
            have hf : ∀ (r : Int), (r ≤ x ∨ y ≤ r) → decide (toR r < d) = decide (y > r) := by
              intro r hr; rcases hr with hle | hge
              · simp [lt_of_le_of_lt (toR_le_toR hle) hIoo.1, lt_of_le_of_lt hle hlt]
              · simp [not_lt.mpr ((le_of_lt hIoo.2).trans (toR_le_toR hge)), not_lt.mpr hge]
            rw [hf ri (hno_xy i.val i.isLt), hf rj (hno_xy j.val j.isLt)]
          have hsum_int : IntervalIntegrable (fun d => ∑ i : Fin rho.size, ∑ j : Fin rho.size,
              d * baseInterCoeff w i.val j.val d *
                jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                  (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)))
              volume (toR x) (toR y) := by
            have h1 : ∀ i : Fin rho.size, IntervalIntegrable (fun d => ∑ j : Fin rho.size,
                d * baseInterCoeff w i.val j.val d *
                  jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                    (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)))
                volume (toR x) (toR y) := fun i => by
              have h := IntervalIntegrable.sum Finset.univ fun j _ => hterm i j
              exact h.congr fun d _ => Finset.sum_apply d _ _
            have h := IntervalIntegrable.sum Finset.univ fun i _ => h1 i
            exact h.congr fun d _ => Finset.sum_apply d _ _
          refine hsum_int.congr fun d _ => ?_
          dsimp only [F]; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        · have heq : x = y := by omega
          subst heq; exact IntervalIntegrable.refl
      -- Also `F` is integrable on `[toR db, toR b]` by induction along any sorted chain!
      have hF_chain : ∀ (l : List Int) (x : Int),
          l.Pairwise (· ≤ ·) → l.head? = some x → l.getLast? = some b → 0 ≤ x →
          (∀ k : Nat, k < rho.size → ∀ u v : Int,
            (∃ l₁ l₂, l = l₁ ++ u :: v :: l₂) → rho.getD k 0 ≤ u ∨ v ≤ rho.getD k 0) →
          IntervalIntegrable F volume (toR x) (toR b) := by
        intro l
        induction l with
        | nil => intro _ _ hh; simp at hh
        | cons u us ihu =>
          cases us with
          | nil =>
            intro x _ hh hl _ _
            simp only [List.head?_cons, Option.some.injEq] at hh
            simp only [List.getLast?_singleton, Option.some.injEq] at hl
            subst hh; subst hl; exact IntervalIntegrable.refl
          | cons v vs =>
            intro x hpwu hhu hlu hxu hnou
            simp only [List.head?_cons, Option.some.injEq] at hhu
            subst hhu
            have huv : u ≤ v := (List.pairwise_cons.mp hpwu).1 v List.mem_cons_self
            have h1 := hF_int u v hxu huv (fun k hk => hnou k hk u v ⟨[], vs, rfl⟩)
            have h2 := ihu v (List.pairwise_cons.mp hpwu).2 rfl
              (by rwa [List.getLast?_cons_of_ne_nil (by simp)] at hlu) (hxu.trans huv)
              (fun k hk p q ⟨l₁, l₂, heq⟩ => hnou k hk p q ⟨u :: l₁, l₂, by simp [heq]⟩)
            exact h1.trans h2
      have hF_tail : IntervalIntegrable F volume (toR db) (toR b) :=
        hF_chain (db :: rest') db hpw_tail rfl hlast_tail (ha.trans hda_db) hno_tail
      have hF_head : IntervalIntegrable F volume (toR da) (toR db) :=
        hF_int da db ha hda_db hno_head
      rw [← intervalIntegral.integral_add_adjacent_intervals hF_head hF_tail]
      unfold basePenInterKnots
      set acc' := if db > da then basePenInterI rho w da db wMax 0 acc else acc
      have hstep_head : (acc : ℝ) / (6 * (S : ℝ) ^ 2) + ∫ d in (toR da)..(toR db), F d ≤
          (acc' : ℝ) / (6 * (S : ℝ) ^ 2) := by
        by_cases hgt : db > da
        · dsimp only [acc']; rw [if_pos hgt]
          have hI := basePenInterI_ge hpot ha hgt hno_head 0 acc (Nat.zero_le _)
          -- Rewrite `∫ d in (toR da)..(toR db), F d` into the symmetric upper-triangle sum
          have hterm_int : ∀ i j : Fin rho.size,
              IntervalIntegrable (fun d => d * baseInterCoeff w i.val j.val d *
                jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                  (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)))
                volume (toR da) (toR db) := by
            intro i j
            set ri := rho.getD i.val 0
            set rj := rho.getD j.val 0
            have hcont : Continuous (fun d : ℝ => d * baseInterCoeff w i.val j.val d) := by
              unfold baseInterCoeff; fun_prop
            have hbase : IntervalIntegrable (fun d => d * baseInterCoeff w i.val j.val d *
                jointSurvReal d (toR ri) (toR rj) (decide (db > ri)) (decide (db > rj)))
                volume (toR da) (toR db) := by
              simpa [mul_comm] using (intervalIntegrable_jointSurvReal (toR ri) (toR rj)
                (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg j.isLt))
                (decide (db > ri)) (decide (db > rj)) (toR da) (toR db)
                (toR_nonneg ha) (toR_le_toR hda_db)).continuousOn_mul hcont.continuousOn
            refine hbase.congr_ae ?_
            rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
            have hne : ∀ᵐ d ∂volume, d ≠ toR db := by rw [MeasureTheory.ae_iff]; simp
            filter_upwards [hne] with d hdne hdmem
            rw [Set.uIoc_of_le (toR_le_toR hda_db)] at hdmem
            have hIoo : d ∈ Set.Ioo (toR da) (toR db) := ⟨hdmem.1, lt_of_le_of_ne hdmem.2 hdne⟩
            have hf : ∀ (r : Int), (r ≤ da ∨ db ≤ r) → decide (toR r < d) = decide (db > r) := by
              intro r hr; rcases hr with hle | hge
              · simp [lt_of_le_of_lt (toR_le_toR hle) hIoo.1, lt_of_le_of_lt hle hgt]
              · simp [not_lt.mpr ((le_of_lt hIoo.2).trans (toR_le_toR hge)), not_lt.mpr hge]
            rw [hf ri (hno_head i.val i.isLt), hf rj (hno_head j.val j.isLt)]
          have hFeq : ∫ d in (toR da)..(toR db), F d =
              ∑ i : Fin rho.size, ∑ j : Fin rho.size,
                ∫ d in (toR da)..(toR db),
                  d * baseInterCoeff w i.val j.val d *
                    jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                      (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) := by
            have hcongr : ∫ d in (toR da)..(toR db), F d =
                ∫ d in (toR da)..(toR db), ∑ i : Fin rho.size, ∑ j : Fin rho.size,
                  d * baseInterCoeff w i.val j.val d *
                    jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                      (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) := by
              refine intervalIntegral.integral_congr fun d _ => ?_
              dsimp only [F]; rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            rw [hcongr, intervalIntegral.integral_finsetSum]
            · refine Finset.sum_congr rfl fun i _ => intervalIntegral.integral_finsetSum fun j _ => hterm_int i j
            · exact fun i _ => (IntervalIntegrable.sum Finset.univ fun j _ => hterm_int i j).congr fun d _ => Finset.sum_apply d _ _
          have hdisk_comm : ∀ d r₁ r₂ : ℝ, diskInterArea d r₁ r₂ = diskInterArea d r₂ r₁ := by
            intro d r₁ r₂; unfold diskInterArea
            have h1 : (r₁ ≤ 0 ∨ r₂ ≤ 0 ∨ r₁ + r₂ ≤ d) ↔ (r₂ ≤ 0 ∨ r₁ ≤ 0 ∨ r₂ + r₁ ≤ d) := by
              rw [add_comm r₁ r₂]; tauto
            have h2 : (d ≤ |r₁ - r₂|) ↔ (d ≤ |r₂ - r₁|) := by rw [abs_sub_comm]
            by_cases hc1 : r₁ ≤ 0 ∨ r₂ ≤ 0 ∨ r₁ + r₂ ≤ d
            · rw [if_pos hc1, if_pos (h1.mp hc1)]
            · rw [if_neg hc1, if_neg (mt h1.mpr hc1)]
              by_cases hc2 : d ≤ |r₁ - r₂|
              · rw [if_pos hc2, if_pos (h2.mp hc2), min_comm]
              · rw [if_neg hc2, if_neg (mt h2.mpr hc2)]; ring
          rw [hFeq, sum_symm_upper _ (fun i j => by
            refine intervalIntegral.integral_congr fun d _ => ?_
            rw [baseInterCoeff_symm w i.val j.val d]
            have hsymm : jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) =
                jointSurvReal d (toR (rho.getD j.val 0)) (toR (rho.getD i.val 0))
                (decide (toR (rho.getD j.val 0) < d)) (decide (toR (rho.getD i.val 0) < d)) := by
              unfold jointSurvReal
              rw [jointSurvCore_symm, hdisk_comm]
            rw [hsymm])]
          have hfilt0 : (Finset.univ.filter fun x : Fin rho.size => 0 ≤ x.val) = Finset.univ := by
            ext x; simp
          rw [hfilt0] at hI
          exact hI
        · have heq : da = db := by omega
          subst heq
          dsimp only [acc']; rw [if_neg hgt, intervalIntegral.integral_same, add_zero]
      have hih := ih db b acc' hpw_tail rfl hlast_tail (ha.trans hda_db) hno_tail
      linarith

lemma basePenInter_le {rho w : Array Int} (hpot : ValidStepPot rho w)
    {nD : Nat} (hnD : 0 < nD) :
    let wMax := w.getD (rho.size - 1) 0
    let knots := buildDKnots rho (2 * wMax) nD
    let penInterRaw := basePenInterKnots rho w wMax knots 0
    let penInter_9 := (piHi * penInterRaw + 5999999999) / 6000000000
    basePenInter rho w ≤ (penInter_9 : ℝ) / 10 ^ 9 := by
  intro wMax knots penInterRaw penInter_9
  have hwMax_nn : 0 ≤ wMax := hpot.w_nonneg (by have := hpot.size_pos; omega)
  have hspec := buildDKnots_spec hpot (dMax := 2 * wMax) (by omega) hnD
  rcases hspec with ⟨hpw, hhead, hlast, hmem⟩
  change knots.Pairwise (· ≤ ·) at hpw
  change knots.head? = some 0 at hhead
  change knots.getLast? = some (2 * wMax) at hlast
  change ∀ i < rho.size, 0 < rho.getD i 0 → rho.getD i 0 < 2 * wMax → rho.getD i 0 ∈ knots at hmem
  have hno : ∀ k : Nat, k < rho.size → ∀ da db : Int,
      (∃ l₁ l₂, knots = l₁ ++ da :: db :: l₂) → rho.getD k 0 ≤ da ∨ db ≤ rho.getD k 0 := by
    intro k hk da db ⟨l₁, l₂, heq⟩
    have hrk_nn : 0 ≤ rho.getD k 0 := hpot.rho_nonneg hk
    by_cases h0 : rho.getD k 0 = 0
    · left
      have hda_nn : 0 ≤ da := by
        cases l₁ with
        | nil =>
          rw [heq] at hhead; simp at hhead; omega
        | cons z zs =>
          rw [heq] at hhead hpw
          simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          exact (List.pairwise_cons.mp hpw).1 da (by simp)
      omega
    · by_cases hhi : rho.getD k 0 < 2 * wMax
      · have hrin : rho.getD k 0 ∈ knots := hmem k hk (by omega) hhi
        rw [heq] at hrin hpw
        rcases List.mem_append.mp hrin with hin1 | hin2
        · left
          have hpw_app := List.pairwise_append.mp hpw
          exact hpw_app.2.2 (rho.getD k 0) hin1 da List.mem_cons_self
        · rcases List.mem_cons.mp hin2 with hEq | hin3
          · left; omega
          · rcases List.mem_cons.mp hin3 with hEq | hin4
            · right; omega
            · right
              have hpw_tail := ((List.pairwise_append.mp hpw).2.1)
              have hpw_db := (List.pairwise_cons.mp hpw_tail).2
              exact (List.pairwise_cons.mp hpw_db).1 (rho.getD k 0) hin4
      · right
        have hdb_le : db ≤ 2 * wMax := by
          rw [heq] at hpw hlast
          have hlast_in : 2 * wMax ∈ l₁ ++ da :: db :: l₂ := List.mem_of_getLast? hlast
          have hpw_tail := (List.pairwise_append.mp hpw).2.1
          have hpw_db := (List.pairwise_cons.mp hpw_tail).2
          have hne_db : (db :: l₂) ≠ [] := List.cons_ne_nil _ _
          have hlast_db : (db :: l₂).getLast? = some (2 * wMax) := by
            rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
                List.getLast?_cons_of_ne_nil hne_db] at hlast
            exact hlast
          cases l₂ with
          | nil => simp at hlast_db; omega
          | cons z zs =>
            rw [List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)] at hlast_db
            exact (List.pairwise_cons.mp hpw_db).1 (2 * wMax) (List.mem_of_getLast? hlast_db)
        omega
  have hknots := basePenInterKnots_ge hpot knots 0 (2 * wMax) 0 hpw hhead hlast le_rfl hno
  simp only [Int.cast_zero, zero_div, zero_add] at hknots
  have h2w : toR (2 * wMax) = 2 * toR wMax := by unfold toR; push_cast; ring
  have h0R : toR 0 = 0 := toR_zero
  rw [h0R, h2w] at hknots
  have hint_nn : 0 ≤ ∫ d in (0 : ℝ)..(2 * toR wMax),
      d * ∑ i : Fin rho.size, ∑ j : Fin rho.size,
        baseInterCoeff w i.val j.val d *
          jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
            (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) := by
    refine intervalIntegral.integral_nonneg (by linarith [toR_nonneg hwMax_nn]) fun d hd => ?_
    refine mul_nonneg hd.1 (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
    refine mul_nonneg (baseInterCoeff_nonneg hpot i j d) ?_
    have hI0 := diskInterArea_nonneg d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
    have hImin := diskInterArea_le_min_disk hd.1 (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg j.isLt))
    have hm1 : Real.pi * (min (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))) ^ 2 ≤ Real.pi * (toR (rho.getD i.val 0)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg j.isLt))) (min_le_left _ _) 2) (le_of_lt Real.pi_pos)
    have hm2 : Real.pi * (min (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))) ^ 2 ≤ Real.pi * (toR (rho.getD j.val 0)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg j.isLt))) (min_le_right _ _) 2) (le_of_lt Real.pi_pos)
    unfold jointSurvReal jointSurvCore
    cases decide (toR (rho.getD i.val 0) < d) <;> cases decide (toR (rho.getD j.val 0) < d) <;> dsimp only
    · exact Real.exp_nonneg _
    · exact mul_nonneg (by linarith) (Real.exp_nonneg _)
    · exact mul_nonneg (by linarith) (Real.exp_nonneg _)
    · exact mul_nonneg (by nlinarith) (Real.exp_nonneg _)
  unfold basePenInter
  calc Real.pi * ∫ d in (0 : ℝ)..(2 * toR wMax),
        d * ∑ i : Fin rho.size, ∑ j : Fin rho.size,
          baseInterCoeff w i.val j.val d *
            jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
              (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))
      ≤ toR piHi * ((penInterRaw : ℝ) / (6 * (S : ℝ) ^ 2)) :=
        mul_le_mul pi_le_piHi hknots hint_nn (toR_nonneg (by decide))
    _ = ((piHi * penInterRaw : Int) : ℝ) / (6000000000 : ℝ) / 10 ^ 9 := by
        unfold toR S; push_cast; ring
    _ ≤ (penInter_9 : ℝ) / 10 ^ 9 := by
        have h := real_div_le_int_cdiv (a := piHi * penInterRaw) (b := 6000000000) (by decide)
        rw [show piHi * penInterRaw + 6000000000 - 1 = piHi * penInterRaw + 5999999999 by omega] at h
        have h' : ((piHi * penInterRaw : Int) : ℝ) / (6000000000 : ℝ) ≤ (penInter_9 : ℝ) := by
          dsimp only [penInter_9]; simpa using h
        exact div_le_div_of_nonneg_right h' (by positivity)

/-! ## Headline 1D Base Soundness Theorem -/

/-- **Certified Soundness of `baseVerifyInt`**: for any valid step potential `(rho, w)` and
`nD > 0`, `(baseVerifyInt rho w nD : ℝ) / 10^9 ≤ baseIntegral rho w`. -/
theorem baseVerifyInt_le_baseIntegral {rho w : Array Int} (hpot : ValidStepPot rho w)
    {nD : Nat} (hnD : 0 < nD) :
    (baseVerifyInt rho w nD : ℝ) / 10 ^ 9 ≤ baseIntegral rho w := by
  unfold baseVerifyInt baseIntegral
  have hcond : ¬ ((rho.size == 0) = true ∨ (w.size != rho.size) = true ∨ (nD == 0) = true) := by
    have h1 := Nat.ne_of_gt hpot.size_pos
    have h2 := hpot.size_eq
    have h3 := Nat.ne_of_gt hnD
    simp [h1, h2, h3]
  rw [if_neg hcond]
  dsimp only
  have h1 := baseTerm1Loop_le hpot
  have h2 := basePenMarg_le hpot
  have h3 := basePenInter_le hpot hnD
  push_cast
  rw [sub_div, sub_div]
  linarith

end BHHBounds.Cert
