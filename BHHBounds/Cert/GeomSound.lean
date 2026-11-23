import BHHBounds.Cert.ArithSound
import BHHBounds.Geometry.DiskIntersection
import BHHBounds.Geometry.ThreeDiskArea

/-!
# Soundness of Geometric Fixed-Point Primitives

Proves that every geometric bounding function in `BHHBounds.Cert.Kernel` is sound with respect to
the exact real geometric quantities in `BHHBounds.Geometry`:
1. `segEvalHi_sound`: `segArea (toR c) ≤ toR (segEvalHi c)` for `c ∈ [-S, S]`.
2. `circleInterHi_sound`: `diskInterArea (toR d) (toR r₁) (toR r₂) ≤ toR (circleInterHi d r₁ r₂)`.
3. `chordPoly6Hi_sound`, `excessXHi_sound`, `triAreaHi_sound`:
   `unionDiskArea ![(0,0), (L,0), (L*w.1, L*w.2)] (toR rad) ≤ toR (triAreaHi l0 l1 x0 x1 y0 y1 rad)`.
4. `jointSurvReal` & `jointSurvHi_sound`: exact Poisson joint survival upper bound (using only
   elementary `1 + x ≤ exp x`).
5. `boxNorm2LoHi_sound`, `cornerDotLoHi_sound`, `dotIntervalInt_sound`: squared-norm and
   angle-addition dot-product interval soundness on axis-aligned boxes.
-/

open MeasureTheory Set Real
open BHHBounds.Geometry

namespace BHHBounds.Cert

/-! ## Helper: `toR` Algebra & `Int` Division -/

lemma toR_nonneg {a : Int} (ha : 0 ≤ a) : 0 ≤ toR a :=
  div_nonneg (by exact_mod_cast ha) (le_of_lt S_pos)

lemma toR_le_toR {a b : Int} (h : a ≤ b) : toR a ≤ toR b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) (le_of_lt S_pos)

lemma le_of_toR_le {a b : Int} (h : toR a ≤ toR b) : a ≤ b := by
  have : (a : ℝ) ≤ (b : ℝ) := (div_le_div_iff_of_pos_right S_pos).mp h
  exact_mod_cast this

lemma nonneg_of_toR_nonneg {a : Int} (h : 0 ≤ toR a) : 0 ≤ a := by
  have h0 : toR 0 = 0 := by unfold toR; simp
  rw [← h0] at h; exact le_of_toR_le h

lemma pos_of_toR_pos {a : Int} (h : 0 < toR a) : 0 < a := by
  have : (0 : ℝ) < (a : ℝ) := by
    have h1 : (0 : ℝ) / (S : ℝ) < (a : ℝ) / (S : ℝ) := by simpa [toR] using h
    exact (div_lt_div_iff_of_pos_right S_pos).mp h1
  exact_mod_cast this

lemma toR_add (a b : Int) : toR (a + b) = toR a + toR b := by
  unfold toR; push_cast; ring

lemma toR_sub (a b : Int) : toR (a - b) = toR a - toR b := by
  unfold toR; push_cast; ring

lemma toR_neg (a : Int) : toR (-a) = -toR a := by
  unfold toR; push_cast; ring

lemma toR_zero : toR 0 = 0 := by
  unfold toR; simp

lemma toR_S : toR S = 1 := by
  unfold toR; exact div_self S_ne_zero

lemma toR_min (a b : Int) : toR (min a b) = min (toR a) (toR b) := by
  unfold toR; rw [Int.cast_min, min_div_div_right (le_of_lt S_pos)]

lemma toR_max (a b : Int) : toR (max a b) = max (toR a) (toR b) := by
  unfold toR; rw [Int.cast_max, max_div_div_right (le_of_lt S_pos)]

lemma toR_div_le_cdiv {a d : Int} (hd : 0 < d) :
    toR a / (d : ℝ) ≤ toR ((a + d - 1) / d) := by
  have h1 := real_div_le_int_cdiv (a := a) hd
  have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
  unfold toR
  have : (a : ℝ) / (d : ℝ) / (S : ℝ) = (a : ℝ) / (S : ℝ) / (d : ℝ) := by ring
  linarith

lemma toR_ediv_le {a d : Int} (hd : 0 < d) :
    toR (a / d) ≤ toR a / (d : ℝ) := by
  have h1 := int_ediv_le_real_div (a := a) hd
  have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
  unfold toR
  have : (a : ℝ) / (d : ℝ) / (S : ℝ) = (a : ℝ) / (S : ℝ) / (d : ℝ) := by ring
  linarith

/-! ## Section 1: Circular Segment Table (`segEvalHi_sound`) -/

lemma segBinAreaHi_sound {k : Nat} (hk : k < 512) :
    segArea (((k : ℝ) - 256) / 256) - segArea ((((k + 1 : Nat) : ℝ) - 256) / 256) ≤
      toR (segBinAreaHi k) := by
  set a : ℝ := ((k : ℝ) - 256) / 256
  set b : ℝ := (((k + 1 : Nat) : ℝ) - 256) / 256
  have ha : -1 ≤ a := by
    dsimp only [a]; linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
  have hab : a < b := by dsimp only [a, b]; push_cast; linarith
  have hb : b ≤ 1 := by
    have hkR : (k : ℝ) + 1 ≤ 512 := by exact_mod_cast hk
    dsimp only [b]; push_cast; linarith
  have hmid := segArea_sub_le_midpoint ha hab hb
  unfold segBinAreaHi
  set denom : Int := 512
  set numM : Int := Int.ofNat (2 * k + 1) - denom
  set rad2 : Int := denom * denom - numM * numM
  have hrad2_eq : 1 - ((a + b) / 2) ^ 2 = (rad2 : ℝ) / (512 : ℝ) ^ 2 := by
    dsimp only [a, b, rad2, numM, denom]
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  have hba : b - a = 1 / 256 := by dsimp only [a, b]; push_cast; ring
  have hrad2_nn : 0 ≤ (rad2 : ℝ) := by
    have : 0 ≤ 1 - ((a + b) / 2) ^ 2 := by nlinarith
    rw [hrad2_eq] at this
    linarith [show (0 : ℝ) < (512 : ℝ) ^ 2 by norm_num, (div_nonneg_iff.mp this)]
  have hsqrt_eq : 2 * (b - a) * Real.sqrt (1 - ((a + b) / 2) ^ 2) =
      Real.sqrt ((rad2 * S * S : Int) / (S : ℝ) ^ 2) / (256 * 256 : ℝ) := by
    rw [hba, hrad2_eq, Real.sqrt_div hrad2_nn, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 512)]
    have hsimp : ((rad2 * S * S : Int) : ℝ) / (S : ℝ) ^ 2 = (rad2 : ℝ) := by
      push_cast
      rw [mul_assoc, ← sq, mul_div_cancel_right₀ _ (pow_ne_zero 2 S_ne_zero)]
    rw [hsimp]; ring
  have hsr : Real.sqrt ((rad2 * S * S : Int) / (S : ℝ) ^ 2) ≤ toR (sqrtSqHi (rad2 * S * S)) :=
    le_sqrtSqHi (rad2 * S * S)
  have hdiv := toR_div_le_cdiv (a := sqrtSqHi (rad2 * S * S)) (d := 256 * 256) (by decide)
  push_cast at hdiv
  calc segArea a - segArea b
      ≤ 2 * (b - a) * Real.sqrt (1 - ((a + b) / 2) ^ 2) := hmid
    _ = Real.sqrt ((rad2 * S * S : Int) / (S : ℝ) ^ 2) / (256 * 256 : ℝ) := hsqrt_eq
    _ ≤ toR (sqrtSqHi (rad2 * S * S)) / (256 * 256 : ℝ) :=
        div_le_div_of_nonneg_right hsr (by norm_num)
    _ ≤ toR ((sqrtSqHi (rad2 * S * S) + 256 * 256 - 1) / (256 * 256)) := by
        norm_num at hdiv ⊢; exact hdiv

lemma segSuffixSum_sound (k : Nat) (hk : k ≤ 512) :
    segArea (((k : ℝ) - 256) / 256) ≤ toR (segSuffixSum k) := by
  induction hn : 512 - k generalizing k with
  | zero =>
    have hkeq : k = 512 := by omega
    subst hkeq
    have h512 : segSuffixSum 512 = 0 := by unfold segSuffixSum segNTot; simp
    rw [h512, toR_zero]
    have : (((512 : Nat) : ℝ) - 256) / 256 = 1 := by norm_num
    rw [this, segArea_one]
  | succ m ih =>
    have hklt : k < 512 := by omega
    have hstep : segSuffixSum k = segBinAreaHi k + segSuffixSum (k + 1) := by
      rw [segSuffixSum]; simp [segNTot, Nat.not_le.mpr hklt]
    rw [hstep, toR_add]
    have h1 := segBinAreaHi_sound hklt
    have h2 := ih (k + 1) (by omega) (by omega)
    linarith

lemma buildSegTabAux_getElem? (k : Nat) (hk : k ≤ 512) (l : List Int)
    (hl : l.headD 0 = segSuffixSum k) :
    ∀ i : Nat, (buildSegTabAux k l)[i]? = if i < k then some (segSuffixSum i) else l[i - k]? := by
  induction k generalizing l with
  | zero =>
    intro i; simp [buildSegTabAux]
  | succ k ih =>
    intro i
    simp only [buildSegTabAux]
    have hhead : l.headD 0 + segBinAreaHi k = segSuffixSum k := by
      have hklt : k < 512 := by omega
      have hstep : segSuffixSum k = segBinAreaHi k + segSuffixSum (k + 1) := by
        rw [segSuffixSum]; simp [segNTot, Nat.not_le.mpr hklt]
      rw [hl, hstep]; omega
    have hih := ih (by omega) ((l.headD 0 + segBinAreaHi k) :: l) (by simpa [List.headD_cons] using hhead) i
    rw [hih]
    by_cases hik : i < k
    · rw [if_pos hik, if_pos (by omega)]
    · rw [if_neg hik]
      by_cases hi_eq : i = k
      · subst hi_eq
        rw [if_pos (by omega)]
        simpa [List.headD] using hhead
      · rw [if_neg (by omega)]
        have hsub : i - k = (i - (k + 1)) + 1 := by omega
        rw [hsub]
        simp

lemma segTabHiArr_getD {k : Nat} (hk : k ≤ 512) :
    segTabHiArr.getD k 0 = segSuffixSum k := by
  unfold segTabHiArr segNTot
  have h512 : segSuffixSum 512 = 0 := by unfold segSuffixSum segNTot; simp
  have hget : (buildSegTabAux 512 [0])[k]? = some (segSuffixSum k) := by
    rw [buildSegTabAux_getElem? 512 le_rfl [0] (by simp [h512]) k]
    by_cases hlt : k < 512
    · simp [hlt]
    · have hkeq : k = 512 := by omega
      subst hkeq; simp [h512]
  have aux : ∀ (l : List Int) (v : Int), l[k]? = some v → l.toArray.getD k 0 = v := by
    intro l v h
    rcases List.getElem?_eq_some_iff.mp h with ⟨hlen, hval⟩
    simp only [Array.getD]
    rw [dif_pos (by simpa using hlen)]
    exact hval
  exact aux (buildSegTabAux 512 [0]) (segSuffixSum k) hget

lemma segSlopeHiArr_getD {k : Nat} (hk : k < 512) :
    segSlopeHiArr.getD k (2 * S) = segBinSlopeHi k := by
  unfold segSlopeHiArr segNTot
  simp [Array.getD, hk]

lemma segBinSlopeHi_sound {k : Nat} (hk : k < 512) :
    let a : ℝ := ((k : ℝ) - 256) / 256
    let b : ℝ := (((k + 1 : Nat) : ℝ) - 256) / 256
    let aI : Int := Int.ofNat k - 256
    let bI : Int := aI + 1
    let tMinAbs : Int := if aI ≤ 0 ∧ 0 ≤ bI then 0 else min aI.natAbs bI.natAbs
    (∀ t ∈ Icc a b, ((tMinAbs : ℝ) / 256) ^ 2 ≤ t ^ 2) ∧
    2 * Real.sqrt (1 - ((tMinAbs : ℝ) / 256) ^ 2) ≤ toR (segBinSlopeHi k) := by
  intro a b aI bI tMinAbs
  have ha_eq : a = (aI : ℝ) / 256 := by dsimp only [a, aI]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  have hb_eq : b = (bI : ℝ) / 256 := by dsimp only [b, bI, aI]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  constructor
  · intro t ht
    rw [ha_eq, hb_eq] at ht
    dsimp only [tMinAbs]
    split_ifs with h0
    · simp; exact sq_nonneg t
    · push Not at h0
      have hcases : bI < 0 ∨ 0 < aI := by omega
      rcases hcases with hneg | hpos
      · have ha_neg : aI < 0 := by omega
        have hmin : min (aI.natAbs : Int) (bI.natAbs : Int) = (bI.natAbs : Int) := by omega
        rw [hmin]
        have hbabs : ((bI.natAbs : Int) : ℝ) = -(bI : ℝ) := by
          have : (bI.natAbs : Int) = -bI := by omega
          exact_mod_cast this
        rw [hbabs]
        have htb : t ≤ (bI : ℝ) / 256 := ht.2
        have hb0 : (bI : ℝ) / 256 ≤ 0 := by
          have : (bI : ℝ) ≤ 0 := by exact_mod_cast le_of_lt hneg
          linarith
        nlinarith
      · have hb_pos : 0 < bI := by omega
        have hmin : min (aI.natAbs : Int) (bI.natAbs : Int) = (aI.natAbs : Int) := by omega
        rw [hmin]
        have haabs : ((aI.natAbs : Int) : ℝ) = (aI : ℝ) := by
          have : (aI.natAbs : Int) = aI := by omega
          exact_mod_cast this
        rw [haabs]
        have hta : (aI : ℝ) / 256 ≤ t := ht.1
        have ha0 : 0 ≤ (aI : ℝ) / 256 := by
          have : (0 : ℝ) ≤ (aI : ℝ) := by exact_mod_cast le_of_lt hpos
          linarith
        nlinarith
  · unfold segBinSlopeHi
    change 2 * Real.sqrt (1 - ((tMinAbs : ℝ) / 256) ^ 2) ≤
      toR ((sqrtSqHi (4 * (256 * 256 - tMinAbs * tMinAbs) * S * S) + 255) / 256)
    have htMin_le : tMinAbs ≤ 256 ∧ 0 ≤ tMinAbs := by
      dsimp only [tMinAbs, aI, bI]; simp only [Int.ofNat_eq_natCast]; split_ifs <;> omega
    have hsRad2_nn : (0 : ℝ) ≤ ((256 * 256 - tMinAbs * tMinAbs : Int) : ℝ) := by
      have : (0 : Int) ≤ 256 * 256 - tMinAbs * tMinAbs := by nlinarith
      exact_mod_cast this
    have hsq_eq : 2 * Real.sqrt (1 - ((tMinAbs : ℝ) / 256) ^ 2) =
        Real.sqrt ((4 * (256 * 256 - tMinAbs * tMinAbs) * S * S : Int) / (S : ℝ) ^ 2) / 256 := by
      have h1 : 1 - ((tMinAbs : ℝ) / 256) ^ 2 =
          ((256 * 256 - tMinAbs * tMinAbs : Int) : ℝ) / (256 : ℝ) ^ 2 := by
        push_cast; ring
      have h2 : ((4 * (256 * 256 - tMinAbs * tMinAbs) * S * S : Int) : ℝ) / (S : ℝ) ^ 2 =
          4 * ((256 * 256 - tMinAbs * tMinAbs : Int) : ℝ) := by
        push_cast
        have hS2 : (S : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 S_ne_zero
        rw [mul_assoc _ (S : ℝ) (S : ℝ), ← sq (S : ℝ), mul_div_cancel_right₀ _ hS2]
      rw [h1, h2, Real.sqrt_div hsRad2_nn, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 256),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num]
      ring
    have hsr := le_sqrtSqHi (4 * (256 * 256 - tMinAbs * tMinAbs) * S * S)
    have hdiv := toR_div_le_cdiv (a := sqrtSqHi (4 * (256 * 256 - tMinAbs * tMinAbs) * S * S))
      (d := 256) (by decide)
    rw [show sqrtSqHi (4 * (256 * 256 - tMinAbs * tMinAbs) * S * S) + 256 - 1 =
        sqrtSqHi (4 * (256 * 256 - tMinAbs * tMinAbs) * S * S) + 255 by omega] at hdiv
    push_cast at hdiv
    calc 2 * Real.sqrt (1 - ((tMinAbs : ℝ) / 256) ^ 2)
        = Real.sqrt ((4 * (256 * 256 - tMinAbs * tMinAbs) * S * S : Int) / (S : ℝ) ^ 2) / 256 := hsq_eq
      _ ≤ toR (sqrtSqHi (4 * (256 * 256 - tMinAbs * tMinAbs) * S * S)) / 256 :=
          div_le_div_of_nonneg_right hsr (by norm_num)
      _ ≤ toR ((sqrtSqHi (4 * (256 * 256 - tMinAbs * tMinAbs) * S * S) + 255) / 256) := hdiv

/-- **Certified Circular Segment Upper Bound**: for all `c ∈ [-S, S]`,
`segArea (toR c) ≤ toR (segEvalHi c)`. -/
theorem segEvalHi_sound {c : Int} (hc1 : -S ≤ c) (hc2 : c ≤ S) :
    segArea (toR c) ≤ toR (segEvalHi c) := by
  unfold segEvalHi
  split_ifs with hge hle
  · have hce : c = S := le_antisymm hc2 hge
    subst hce; rw [toR_S, segArea_one, toR_zero]
  · have hce : c = -S := le_antisymm hle hc1
    subst hce; rw [toR_neg, toR_S, segArea_neg_one]; exact pi_le_piHi
  · push Not at hge hle
    set num : Int := (c + S) * 256
    set idx : Nat := (num / S).toNat
    set remNum : Int := Int.ofNat (idx + 1) * S - num
    set denom : Int := 256 * S
    have hnum_nn : 0 ≤ num := by dsimp only [num]; unfold S at *; omega
    have hnum_lt : num < 512 * S := by dsimp only [num]; unfold S at *; omega
    have hq_nn : 0 ≤ num / S := Int.ediv_nonneg hnum_nn (by decide)
    have hidx_eq : (idx : Int) = num / S := Int.toNat_of_nonneg hq_nn
    have hidx_lt : idx < 512 := by
      have h1 : num / S < 512 := Int.ediv_lt_of_lt_mul (by decide) (by omega)
      omega
    have hq_lo : (idx : Int) * S ≤ num := by
      have hmod := Int.emod_nonneg num (by decide : (S : Int) ≠ 0)
      have hdiv := Int.mul_ediv_add_emod num S
      rw [← hidx_eq] at hdiv; nlinarith
    have hq_hi : num < (idx + 1 : Int) * S := by
      have hmod := Int.emod_lt_of_pos num (by decide : (0 : Int) < S)
      have hdiv := Int.mul_ediv_add_emod num S
      rw [← hidx_eq] at hdiv; nlinarith
    have hrem_pos : 0 < remNum := by
      dsimp only [remNum]; simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]; omega
    set a : ℝ := ((idx : ℝ) - 256) / 256
    set b : ℝ := (((idx + 1 : Nat) : ℝ) - 256) / 256
    have hac : a ≤ toR c := by
      dsimp only [a]; unfold toR
      have h1 : ((idx : Int) * S : ℝ) ≤ ((c + S) * 256 : ℝ) := by exact_mod_cast hq_lo
      push_cast at h1; rw [div_le_div_iff₀ (by norm_num) S_pos]; linarith
    have hcb : toR c ≤ b := by
      dsimp only [b]; unfold toR
      have h1 : ((c + S) * 256 : ℝ) ≤ ((idx + 1 : Int) * S : ℝ) := by exact_mod_cast le_of_lt hq_hi
      push_cast at h1 ⊢; rw [div_le_div_iff₀ S_pos (by norm_num)]; linarith
    have hbc_eq : b - toR c = (remNum : ℝ) / (denom : ℝ) := by
      dsimp only [b, remNum, denom, num]; unfold toR
      simp only [Int.ofNat_eq_natCast]
      push_cast
      rw [div_sub_div _ _ (by norm_num : (256 : ℝ) ≠ 0) S_ne_zero]
      congr 1; ring
    have hslope_arr : segSlopeHiArr.getD idx (2 * S) = segBinSlopeHi idx := segSlopeHiArr_getD hidx_lt
    have htab_arr : segTabHiArr.getD (idx + 1) 0 = segSuffixSum (idx + 1) := segTabHiArr_getD (by omega)
    dsimp only
    rw [hslope_arr, htab_arr, toR_min]
    refine le_min ?_ ?_
    · have hcIcc : toR c ∈ Icc (-1 : ℝ) 1 := by
        constructor
        · rw [← toR_S, ← toR_neg]; exact toR_le_toR hc1
        · rw [← toR_S]; exact toR_le_toR hc2
      exact (segArea_le_pi hcIcc).trans pi_le_piHi
    · have hsb := segBinSlopeHi_sound hidx_lt
      have hdiff := segArea_sub_le_slope hac hcb hsb.1
      have hbase := segSuffixSum_sound (idx + 1) (by omega)
      have hden_pos : (0 : Int) < denom := by dsimp only [denom]; unfold S; decide
      have hextra : toR (segBinSlopeHi idx) * ((remNum : ℝ) / (denom : ℝ)) ≤
          toR ((segBinSlopeHi idx * remNum + denom - 1) / denom) := by
        have h1 := toR_div_le_cdiv (a := segBinSlopeHi idx * remNum) hden_pos
        have h2 : toR (segBinSlopeHi idx) * ((remNum : ℝ) / (denom : ℝ)) =
            toR (segBinSlopeHi idx * remNum) / (denom : ℝ) := by
          unfold toR; push_cast; ring
        linarith
      have hmul := mul_le_mul_of_nonneg_right hsb.2 (show 0 ≤ b - toR c by linarith)
      rw [hbc_eq] at hmul hdiff
      rw [toR_add]
      change segArea (toR c) ≤ toR (segSuffixSum (idx + 1)) +
        toR ((segBinSlopeHi idx * remNum + denom - 1) / denom)
      linarith [hdiff, hbase, hmul, hextra]

/-! ## Section 2: Two-Disk Intersection Upper Bound (`circleInterHi_sound`) -/

theorem circleInterHi_sound {d r1 r2 : Int} (hd : 0 ≤ d) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) :
    diskInterArea (toR d) (toR r1) (toR r2) ≤ toR (circleInterHi d r1 r2) := by
  have hdR : 0 ≤ toR d := toR_nonneg hd
  have hr1R : 0 ≤ toR r1 := toR_nonneg hr1
  have hr2R : 0 ≤ toR r2 := toR_nonneg hr2
  unfold circleInterHi
  by_cases h1 : r1 ≤ 0 ∨ r2 ≤ 0 ∨ d ≥ r1 + r2
  · rw [if_pos h1, toR_zero]
    unfold diskInterArea
    have h1R : toR r1 ≤ 0 ∨ toR r2 ≤ 0 ∨ toR r1 + toR r2 ≤ toR d := by
      rcases h1 with h | h | h
      · left; rw [← toR_zero]; exact toR_le_toR h
      · right; left; rw [← toR_zero]; exact toR_le_toR h
      · right; right; rw [← toR_add]; exact toR_le_toR h
    rw [if_pos h1R]
  · rw [if_neg h1]
    push Not at h1
    rcases h1 with ⟨hr1p, hr2p, hsep⟩
    have hr1pR : 0 < toR r1 := div_pos (by exact_mod_cast hr1p) S_pos
    have hr2pR : 0 < toR r2 := div_pos (by exact_mod_cast hr2p) S_pos
    have hsepR : toR d < toR r1 + toR r2 := by
      rw [← toR_add]; exact div_lt_div_of_pos_right (by exact_mod_cast hsep) S_pos
    have hmin_bound : Real.pi * (min (toR r1) (toR r2)) ^ 2 ≤
        toR (mulHi piHi (mulHi (min r1 r2) (min r1 r2))) := by
      have hrmin_nn : 0 ≤ min r1 r2 := le_min hr1 hr2
      have hsq : (min (toR r1) (toR r2)) ^ 2 ≤ toR (mulHi (min r1 r2) (min r1 r2)) := by
        rw [← toR_min, sq]; exact le_mulHi
      calc Real.pi * (min (toR r1) (toR r2)) ^ 2
          ≤ toR piHi * toR (mulHi (min r1 r2) (min r1 r2)) :=
            mul_le_mul pi_le_piHi hsq (sq_nonneg _) (toR_nonneg (by decide))
        _ ≤ toR (mulHi piHi (mulHi (min r1 r2) (min r1 r2))) := le_mulHi
    have habs_eq : |toR r1 - toR r2| = toR (max r1 r2 - min r1 r2) := by
      rw [toR_sub, toR_max, toR_min]
      rcases le_total (toR r1) (toR r2) with h | h
      · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]
    dsimp only
    by_cases h2 : d ≤ max r1 r2 - min r1 r2
    · rw [if_pos h2]
      have h2R : toR d ≤ |toR r1 - toR r2| := by rw [habs_eq]; exact toR_le_toR h2
      have hdisk : diskInterArea (toR d) (toR r1) (toR r2) = Real.pi * (min (toR r1) (toR r2)) ^ 2 := by
        unfold diskInterArea
        rw [if_neg (by push Not; exact ⟨hr1pR, hr2pR, hsepR⟩), if_pos h2R]
      rw [hdisk]; exact hmin_bound
    · rw [if_neg h2]
      push Not at h2
      have h2R : |toR r1 - toR r2| < toR d := by
        rw [habs_eq]; exact div_lt_div_of_pos_right (by exact_mod_cast h2) S_pos
      have hd_pos : 0 < d := by omega
      have hd_posR : 0 < toR d := div_pos (by exact_mod_cast hd_pos) S_pos
      have hdisk_min : diskInterArea (toR d) (toR r1) (toR r2) ≤
          Real.pi * (min (toR r1) (toR r2)) ^ 2 := diskInterArea_le_min_disk hdR hr1R hr2R
      rw [toR_min]
      refine le_min (hdisk_min.trans hmin_bound) ?_
      have hdisk_eq : diskInterArea (toR d) (toR r1) (toR r2) =
          (toR r1) ^ 2 * segArea (((toR d) ^ 2 + (toR r1) ^ 2 - (toR r2) ^ 2) / (2 * toR d * toR r1)) +
          (toR r2) ^ 2 * segArea (((toR d) ^ 2 + (toR r2) ^ 2 - (toR r1) ^ 2) / (2 * toR d * toR r2)) := by
        unfold diskInterArea
        rw [if_neg (by push Not; exact ⟨hr1pR, hr2pR, hsepR⟩), if_neg (not_le.mpr h2R)]
      rw [hdisk_eq, toR_add]
      have hdiff : toR r1 - toR r2 < toR d ∧ toR r2 - toR r1 < toR d := by
        have := abs_lt.mp h2R; constructor <;> linarith
      -- Helper for each of the two cap terms
      have hcap : ∀ (ra rb : Int), 0 < ra → 0 < rb →
          toR d < toR ra + toR rb → toR ra - toR rb < toR d → toR rb - toR ra < toR d →
          (toR ra) ^ 2 * segArea (((toR d) ^ 2 + (toR ra) ^ 2 - (toR rb) ^ 2) / (2 * toR d * toR ra)) ≤
            toR (mulHi (mulHi ra ra)
              (segEvalHi (max (-S) (min S (fdiv ((d * d + ra * ra - rb * rb) * S) (2 * d * ra)))))) := by
        intro ra rb hrap hrbp hsum hd1 hd2
        have hrapR : 0 < toR ra := div_pos (by exact_mod_cast hrap) S_pos
        set c := ((toR d) ^ 2 + (toR ra) ^ 2 - (toR rb) ^ 2) / (2 * toR d * toR ra)
        have hc_lo : -1 ≤ c := by
          dsimp only [c]; rw [le_div_iff₀ (by positivity)]; nlinarith
        have hc_hi : c ≤ 1 := by
          dsimp only [c]; rw [div_le_one (by positivity)]; nlinarith
        set q := fdiv ((d * d + ra * ra - rb * rb) * S) (2 * d * ra)
        have hq_le : toR q ≤ c := by
          have hden_pos : (0 : Int) < 2 * d * ra := by positivity
          have hf := fdiv_le_real_div (a := (d * d + ra * ra - rb * rb) * S) hden_pos
          have hf2 := div_le_div_of_nonneg_right hf (le_of_lt S_pos)
          have hrhs : (((d * d + ra * ra - rb * rb) * S : Int) : ℝ) / ((2 * d * ra : Int) : ℝ) / (S : ℝ) = c := by
            dsimp only [c]; unfold toR; push_cast; field_simp [S_ne_zero]
          unfold toR at hf2 ⊢; linarith
        set cLo := max (-S) (min S q)
        have hcLo_range : -S ≤ cLo ∧ cLo ≤ S := by
          dsimp only [cLo]; constructor
          · exact le_max_left _ _
          · exact max_le (by unfold S; decide) (min_le_left _ _)
        have hcLo_le : toR cLo ≤ c := by
          dsimp only [cLo]
          rw [toR_max, toR_min, toR_neg, toR_S]
          exact max_le hc_lo ((min_le_right _ _).trans hq_le)
        have hseg_le : segArea c ≤ toR (segEvalHi cLo) := by
          have hcLoIcc : toR cLo ∈ Icc (-1 : ℝ) 1 := by
            constructor
            · rw [← toR_S, ← toR_neg]; exact toR_le_toR hcLo_range.1
            · rw [← toR_S]; exact toR_le_toR hcLo_range.2
          exact (segArea_antitoneOn hcLoIcc ⟨hc_lo, hc_hi⟩ hcLo_le).trans
            (segEvalHi_sound hcLo_range.1 hcLo_range.2)
        have hra2_le : (toR ra) ^ 2 ≤ toR (mulHi ra ra) := by rw [sq]; exact le_mulHi
        have hra2_nn : 0 ≤ toR (mulHi ra ra) := toR_nonneg (mulHi_nonneg (le_of_lt hrap) (le_of_lt hrap))
        calc (toR ra) ^ 2 * segArea c
            ≤ toR (mulHi ra ra) * toR (segEvalHi cLo) :=
              mul_le_mul hra2_le hseg_le (segArea_nonneg hc_hi) hra2_nn
          _ ≤ toR (mulHi (mulHi ra ra) (segEvalHi cLo)) := le_mulHi
      exact add_le_add
        (hcap r1 r2 hr1p hr2p hsepR hdiff.1 hdiff.2)
        (hcap r2 r1 hr2p hr1p (by linarith) hdiff.2 hdiff.1)

/-! ## Section 3: Three-Disk Union Area Upper Bound (`triAreaHi_sound`) -/

lemma chordPoly6Hi_sound {d : Int} (hd0 : 0 ≤ d) (hd1 : d ≤ S) :
    chordArea (toR d) ≤ toR (chordPoly6Hi d) := by
  have hd0R : 0 ≤ toR d := toR_nonneg hd0
  have hd1R : toR d ≤ 1 := by rw [← toR_S]; exact toR_le_toR hd1
  have hpoly := chordArea_le_poly6 hd0R hd1R
  unfold chordPoly6Hi
  have hclamp : max 0 (min S d) = d := by rw [min_eq_right hd1, max_eq_right hd0]
  rw [hclamp]
  set d2 := mulLo d d
  set d3 := mulLo d2 d
  set d5 := mulLo d3 d2
  set d7 := mulLo d5 d2
  set d9 := mulLo d7 d2
  set d11 := mulLo d9 d2
  set d13 := mulLo d11 d2
  have hd2_nn : 0 ≤ d2 := mulLo_nonneg hd0 hd0
  have hd3_nn : 0 ≤ d3 := mulLo_nonneg hd2_nn hd0
  have hd5_nn : 0 ≤ d5 := mulLo_nonneg hd3_nn hd2_nn
  have hd7_nn : 0 ≤ d7 := mulLo_nonneg hd5_nn hd2_nn
  have hd9_nn : 0 ≤ d9 := mulLo_nonneg hd7_nn hd2_nn
  have hd11_nn : 0 ≤ d11 := mulLo_nonneg hd9_nn hd2_nn
  have hd2_le : toR d2 ≤ toR d ^ 2 := by rw [sq]; exact mulLo_le
  have hd3_le : toR d3 ≤ toR d ^ 3 := by
    calc toR d3 ≤ toR d2 * toR d := mulLo_le
      _ ≤ toR d ^ 2 * toR d := mul_le_mul_of_nonneg_right hd2_le hd0R
      _ = toR d ^ 3 := by ring
  have hd5_le : toR d5 ≤ toR d ^ 5 := by
    calc toR d5 ≤ toR d3 * toR d2 := mulLo_le
      _ ≤ toR d ^ 3 * toR d ^ 2 := mul_le_mul hd3_le hd2_le (toR_nonneg hd2_nn) (by positivity)
      _ = toR d ^ 5 := by ring
  have hd7_le : toR d7 ≤ toR d ^ 7 := by
    calc toR d7 ≤ toR d5 * toR d2 := mulLo_le
      _ ≤ toR d ^ 5 * toR d ^ 2 := mul_le_mul hd5_le hd2_le (toR_nonneg hd2_nn) (by positivity)
      _ = toR d ^ 7 := by ring
  have hd9_le : toR d9 ≤ toR d ^ 9 := by
    calc toR d9 ≤ toR d7 * toR d2 := mulLo_le
      _ ≤ toR d ^ 7 * toR d ^ 2 := mul_le_mul hd7_le hd2_le (toR_nonneg hd2_nn) (by positivity)
      _ = toR d ^ 9 := by ring
  have hd11_le : toR d11 ≤ toR d ^ 11 := by
    calc toR d11 ≤ toR d9 * toR d2 := mulLo_le
      _ ≤ toR d ^ 9 * toR d ^ 2 := mul_le_mul hd9_le hd2_le (toR_nonneg hd2_nn) (by positivity)
      _ = toR d ^ 11 := by ring
  have hd13_le : toR d13 ≤ toR d ^ 13 := by
    calc toR d13 ≤ toR d11 * toR d2 := mulLo_le
      _ ≤ toR d ^ 11 * toR d ^ 2 := mul_le_mul hd11_le hd2_le (toR_nonneg hd2_nn) (by positivity)
      _ = toR d ^ 13 := by ring
  have ht3 : toR (d3 / 12) ≤ (1 / 12 : ℝ) * toR d ^ 3 := by
    have := toR_ediv_le (a := d3) (d := 12) (by decide); push_cast at this; linarith
  have ht5 : toR (d5 / 320) ≤ (1 / 320 : ℝ) * toR d ^ 5 := by
    have := toR_ediv_le (a := d5) (d := 320) (by decide); push_cast at this; linarith
  have ht7 : toR (d7 / 3584) ≤ (1 / 3584 : ℝ) * toR d ^ 7 := by
    have := toR_ediv_le (a := d7) (d := 3584) (by decide); push_cast at this; linarith
  have ht9 : toR ((5 * d9) / 147456) ≤ (5 / 147456 : ℝ) * toR d ^ 9 := by
    have := toR_ediv_le (a := 5 * d9) (d := 147456) (by decide)
    have hmul : toR (5 * d9) = 5 * toR d9 := by unfold toR; push_cast; ring
    rw [hmul] at this; push_cast at this; linarith
  have ht11 : toR ((7 * d11) / 1441792) ≤ (7 / 1441792 : ℝ) * toR d ^ 11 := by
    have := toR_ediv_le (a := 7 * d11) (d := 1441792) (by decide)
    have hmul : toR (7 * d11) = 7 * toR d11 := by unfold toR; push_cast; ring
    rw [hmul] at this; push_cast at this; linarith
  have ht13 : toR ((21 * d13) / 27262976) ≤ (21 / 27262976 : ℝ) * toR d ^ 13 := by
    have := toR_ediv_le (a := 21 * d13) (d := 27262976) (by decide)
    have hmul : toR (21 * d13) = 21 * toR d13 := by unfold toR; push_cast; ring
    rw [hmul] at this; push_cast at this; linarith
  have hsum : toR (2 * d - d3 / 12 - d5 / 320 - d7 / 3584 - (5 * d9) / 147456 -
      (7 * d11) / 1441792 - (21 * d13) / 27262976) =
      2 * toR d - toR (d3 / 12) - toR (d5 / 320) - toR (d7 / 3584) -
      toR ((5 * d9) / 147456) - toR ((7 * d11) / 1441792) - toR ((21 * d13) / 27262976) := by
    unfold toR; push_cast; ring
  rw [hsum]
  unfold chordPoly6 at hpoly
  linarith

lemma excessXBin_sound {r : ℝ} {w : Pt} {r0 r1 x0 x1 y0 : Int}
    (hr_pos : 0 < r) (hr0_nn : 0 ≤ r0) (hr0_le : toR r0 ≤ r) (hr1_ge : r ≤ toR r1)
    (hx0 : toR x0 ≤ w.1) (hx1 : w.1 ≤ toR x1) (hy0_nn : 0 ≤ y0) (hy0 : toR y0 ≤ w.2)
    {i : Nat} (hi : i < 8) :
    ∫ t in ((i : ℝ) / 8)..(((i + 1 : Nat) : ℝ) / 8),
      max 0 (Real.sqrt (max 0 (1 - (r * t - r * w.1) ^ 2)) - r * w.2 -
        Real.sqrt (1 - (r * min t (1 - t)) ^ 2)) ≤
      toR (excessXBin r0 r1 x0 x1 y0 i) := by
  set f : ℝ → ℝ := fun t => max 0 (Real.sqrt (max 0 (1 - (r * t - r * w.1) ^ 2)) - r * w.2 -
    Real.sqrt (1 - (r * min t (1 - t)) ^ 2))
  set a : ℝ := (i : ℝ) / 8
  set b : ℝ := ((i + 1 : Nat) : ℝ) / 8
  have hab : a ≤ b := by dsimp only [a, b]; push_cast; linarith
  have hdt : toR 125000 = 1 / 8 := by unfold toR S; norm_num
  have hta : toR (Int.ofNat i * 125000) = a := by
    dsimp only [a]; unfold toR S; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  have htb : toR (Int.ofNat i * 125000 + 125000) = b := by
    dsimp only [b]; unfold toR S; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  have hcont : Continuous f := by dsimp only [f]; fun_prop
  unfold excessXBin
  dsimp only
  set ta : Int := Int.ofNat i * 125000
  set tb : Int := ta + 125000
  set mHi : Int := if ta ≤ 500000 ∧ 500000 ≤ tb then 500000
    else max (min ta (S - ta)) (min tb (S - tb))
  set rmHi := mulHi r1 mHi
  set lowerSq := sqrtSqLo (S * S - rmHi * rmHi)
  set distTx : Int := if tb < x0 then x0 - tb else if ta > x1 then ta - x1 else 0
  set rdLo := mulLo r0 distTx
  set upperSq := sqrtSqHi (S * S - rdLo * rdLo)
  set diff := upperSq - mulLo r0 y0 - lowerSq
  have hta_nn : 0 ≤ ta := by dsimp only [ta]; simp only [Int.ofNat_eq_natCast]; omega
  have htb_le : tb ≤ S := by dsimp only [tb, ta, S]; simp only [Int.ofNat_eq_natCast]; omega
  have hmHi_nn : 0 ≤ mHi := by dsimp only [mHi]; split_ifs <;> omega
  have hr1_nn : 0 ≤ r1 := nonneg_of_toR_nonneg ((le_of_lt hr_pos).trans hr1_ge)
  have hdist_nn : 0 ≤ distTx := by dsimp only [distTx]; split_ifs <;> omega
  have hpt : ∀ t ∈ Icc a b, f t ≤ max 0 (toR diff) := by
    intro t ht
    have ht0 : 0 ≤ t := (show (0 : ℝ) ≤ a by dsimp only [a]; positivity).trans ht.1
    have ht1 : t ≤ 1 := ht.2.trans (by
      dsimp only [b]; have : ((i + 1 : Nat) : ℝ) ≤ 8 := by exact_mod_cast hi
      linarith)
    -- Bound `min t (1 - t) ≤ toR mHi`
    have hmin_le : min t (1 - t) ≤ toR mHi := by
      dsimp only [mHi]
      split_ifs with hhalf
      · have h500 : toR 500000 = 1 / 2 := by unfold toR S; norm_num
        rw [h500]
        rcases le_total t (1 / 2) with h | h
        · exact (min_le_left _ _).trans h
        · exact (min_le_right _ _).trans (by linarith)
      · rw [toR_max, toR_min, toR_min, toR_sub, toR_sub, toR_S, hta, htb]
        have hcases : tb < 500000 ∨ 500000 < ta := by omega
        rcases hcases with hlt | hgt
        · have hb_half : b ≤ 1 / 2 := by
            rw [← htb]; unfold toR S; have : (tb : ℝ) ≤ 500000 := by exact_mod_cast le_of_lt hlt
            linarith
          have ht_le_b : t ≤ b := ht.2
          have hmin_b : min b (1 - b) = b := min_eq_left (by linarith)
          calc min t (1 - t) ≤ t := min_le_left _ _
            _ ≤ b := ht_le_b
            _ = min b (1 - b) := hmin_b.symm
            _ ≤ max (min a (1 - a)) (min b (1 - b)) := le_max_right _ _
        · have ha_half : 1 / 2 ≤ a := by
            rw [← hta]; unfold toR S; have : (500000 : ℝ) ≤ (ta : ℝ) := by exact_mod_cast le_of_lt hgt
            linarith
          have h1t_le : 1 - t ≤ 1 - a := by linarith [ht.1]
          have hmin_a : min a (1 - a) = 1 - a := min_eq_right (by linarith)
          calc min t (1 - t) ≤ 1 - t := min_le_right _ _
            _ ≤ 1 - a := h1t_le
            _ = min a (1 - a) := hmin_a.symm
            _ ≤ max (min a (1 - a)) (min b (1 - b)) := le_max_left _ _
    have hrm : r * min t (1 - t) ≤ toR rmHi := by
      calc r * min t (1 - t) ≤ toR r1 * toR mHi :=
            mul_le_mul hr1_ge hmin_le (le_min ht0 (by linarith)) (toR_nonneg hr1_nn)
        _ ≤ toR rmHi := le_mulHi
    have hlow : toR lowerSq ≤ Real.sqrt (1 - (r * min t (1 - t)) ^ 2) := by
      have h1 : toR lowerSq ≤ Real.sqrt (((S * S - rmHi * rmHi : Int) : ℝ) / (S : ℝ) ^ 2) :=
        sqrtSqLo_le _
      have h2 : ((S * S - rmHi * rmHi : Int) : ℝ) / (S : ℝ) ^ 2 = 1 - (toR rmHi) ^ 2 := by
        unfold toR; push_cast
        rw [sub_div, show (S : ℝ) * (S : ℝ) / (S : ℝ) ^ 2 = 1 by rw [← sq, div_self (pow_ne_zero 2 S_ne_zero)]]
        ring
      rw [h2] at h1
      have hsq : (r * min t (1 - t)) ^ 2 ≤ (toR rmHi) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (le_of_lt hr_pos) (le_min ht0 (by linarith))) hrm 2
      exact h1.trans (Real.sqrt_le_sqrt (by linarith))
    -- Bound `toR distTx ≤ |t - w.1|`
    have hdist_le : toR distTx ≤ |t - w.1| := by
      dsimp only [distTx]
      split_ifs with hlt hgt
      · rw [toR_sub, htb, abs_sub_comm]
        exact (by linarith [ht.2, hx0] : toR x0 - b ≤ w.1 - t).trans (le_abs_self _)
      · rw [toR_sub, hta]
        exact (by linarith [ht.1, hx1] : a - toR x1 ≤ t - w.1).trans (le_abs_self _)
      · rw [toR_zero]; exact abs_nonneg _
    have hrd : toR rdLo ≤ r * |t - w.1| := by
      calc toR rdLo ≤ toR r0 * toR distTx := mulLo_le
        _ ≤ r * |t - w.1| := mul_le_mul hr0_le hdist_le (toR_nonneg hdist_nn) (le_of_lt hr_pos)
    have hupp : Real.sqrt (max 0 (1 - (r * t - r * w.1) ^ 2)) ≤ toR upperSq := by
      have h1 : Real.sqrt (((S * S - rdLo * rdLo : Int) : ℝ) / (S : ℝ) ^ 2) ≤ toR upperSq :=
        le_sqrtSqHi _
      have h2 : ((S * S - rdLo * rdLo : Int) : ℝ) / (S : ℝ) ^ 2 = 1 - (toR rdLo) ^ 2 := by
        unfold toR; push_cast
        rw [sub_div, show (S : ℝ) * (S : ℝ) / (S : ℝ) ^ 2 = 1 by rw [← sq, div_self (pow_ne_zero 2 S_ne_zero)]]
        ring
      rw [h2] at h1
      have hsq : (toR rdLo) ^ 2 ≤ (r * t - r * w.1) ^ 2 := by
        have habs : (r * |t - w.1|) ^ 2 = (r * t - r * w.1) ^ 2 := by
          rw [mul_pow, sq_abs]; ring
        rw [← habs]
        exact pow_le_pow_left₀ (toR_nonneg (mulLo_nonneg hr0_nn hdist_nn)) hrd 2
      have hupp_nn : 0 ≤ toR upperSq := toR_nonneg (sqrtSqHi_nonneg _)
      rcases le_total (1 - (r * t - r * w.1) ^ 2) 0 with hnp | hnn
      · rw [max_eq_left hnp, Real.sqrt_zero]; exact hupp_nn
      · rw [max_eq_right hnn]
        exact (Real.sqrt_le_sqrt (by linarith)).trans h1
    have hry : toR (mulLo r0 y0) ≤ r * w.2 := by
      calc toR (mulLo r0 y0) ≤ toR r0 * toR y0 := mulLo_le
        _ ≤ r * w.2 := mul_le_mul hr0_le hy0 (toR_nonneg hy0_nn) (le_of_lt hr_pos)
    have hdiff_eq : toR diff = toR upperSq - toR (mulLo r0 y0) - toR lowerSq := by
      dsimp only [diff]; rw [toR_sub, toR_sub]
    dsimp only [f]
    exact max_le_max_left 0 (by linarith)
  have hint_le := intervalIntegral.integral_mono_on (μ := volume) hab (hcont.intervalIntegrable a b)
    intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint_le
  have hba : b - a = toR 125000 := by dsimp only [a, b]; rw [hdt]; push_cast; ring
  rw [hba] at hint_le
  split_ifs with hpos
  · have hdiff_pos : 0 ≤ toR diff := toR_nonneg (le_of_lt hpos)
    rw [max_eq_right hdiff_pos, mul_comm] at hint_le
    exact hint_le.trans le_mulHi
  · push Not at hpos
    have hdiff_np : toR diff ≤ 0 := by rw [← toR_zero]; exact toR_le_toR hpos
    rw [max_eq_left hdiff_np, mul_zero] at hint_le
    rw [toR_zero]; exact hint_le

lemma excessXSum_eq_sum (r0 r1 x0 x1 y0 : Int) (n : Nat) :
    toR (excessXSum r0 r1 x0 x1 y0 n) = ∑ i ∈ Finset.range n, toR (excessXBin r0 r1 x0 x1 y0 i) := by
  induction n with
  | zero => simp [excessXSum, toR_zero]
  | succ k ih =>
    rw [excessXSum, toR_add, ih, Finset.sum_range_succ]

lemma excessXHi_sound {r : ℝ} {w : Pt} {r0 r1 x0 x1 y0 : Int}
    (hr_pos : 0 < r) (hr_lt : r < 1) (hr0_nn : 0 ≤ r0) (hr0_le : toR r0 ≤ r) (hr1_ge : r ≤ toR r1)
    (hx0 : toR x0 ≤ w.1) (hx1 : w.1 ≤ toR x1) (hy0_nn : 0 ≤ y0) (hy0 : toR y0 ≤ w.2) :
    excessX r w ≤ toR (excessXHi r0 r1 x0 x1 y0) := by
  -- Change of variables `s = r * t` on `[0, 1]`
  set g : ℝ → ℝ := fun t => max 0 (Real.sqrt (max 0 (1 - (r * t - r * w.1) ^ 2)) - r * w.2 -
    Real.sqrt (1 - (r * min t (1 - t)) ^ 2))
  have hcov : excessX r w = r * ∫ t in (0 : ℝ)..1, g t := by
    unfold excessX
    have h1 := intervalIntegral.integral_comp_mul_left
      (f := fun s : ℝ => max 0 (Real.sqrt (max 0 (1 - (s - r * w.1) ^ 2)) - r * w.2 -
        Real.sqrt (1 - (min s (r - s)) ^ 2))) (a := 0) (b := 1) (c := r) (ne_of_gt hr_pos)
    rw [mul_zero, mul_one, smul_eq_mul] at h1
    have h2 : (∫ s in (0 : ℝ)..r, max 0 (Real.sqrt (max 0 (1 - (s - r * w.1) ^ 2)) - r * w.2 -
        Real.sqrt (1 - (min s (r - s)) ^ 2))) =
        r * ∫ t in (0 : ℝ)..1, max 0 (Real.sqrt (max 0 (1 - (r * t - r * w.1) ^ 2)) - r * w.2 -
        Real.sqrt (1 - (min (r * t) (r - r * t)) ^ 2)) := by
      have := congrArg (r * ·) h1
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr_pos), one_mul] at this
      exact this.symm
    rw [h2]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hmin : min (r * t) (r - r * t) = r * min t (1 - t) := by
      rw [show r - r * t = r * (1 - t) by ring, ← mul_min_of_nonneg _ _ (le_of_lt hr_pos)]
    rw [hmin]
  rw [hcov]
  unfold excessXHi
  dsimp only
  set baseMin := sqrtSqLo (S * S - (r1 * r1 + 3) / 4)
  have hry : toR (mulLo r0 y0) ≤ r * w.2 := by
    calc toR (mulLo r0 y0) ≤ toR r0 * toR y0 := mulLo_le
      _ ≤ r * w.2 := mul_le_mul hr0_le hy0 (toR_nonneg hy0_nn) (le_of_lt hr_pos)
  split_ifs with htriv
  · -- Integrand is identically 0 on `[0, 1]`!
    rw [toR_zero]
    have hzero : ∫ t in (0 : ℝ)..1, g t = 0 := by
      have hcongr : ∫ t in (0 : ℝ)..1, g t = ∫ _ in (0 : ℝ)..1, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le zero_le_one] at ht
        have hmin_half : min t (1 - t) ≤ 1 / 2 := by
          rcases le_total t (1 / 2) with h | h
          · exact (min_le_left _ _).trans h
          · exact (min_le_right _ _).trans (by linarith)
        have hmin_nn : 0 ≤ min t (1 - t) := le_min ht.1 (by linarith [ht.2])
        have hbase_le : toR baseMin ≤ Real.sqrt (1 - (r * min t (1 - t)) ^ 2) := by
          have h1 : toR baseMin ≤ Real.sqrt (((S * S - (r1 * r1 + 3) / 4 : Int) : ℝ) / (S : ℝ) ^ 2) :=
            sqrtSqLo_le _
          have hdiv4 : (r1 * r1 : ℝ) / 4 ≤ (((r1 * r1 + 3) / 4 : Int) : ℝ) := by
            have := real_div_le_int_cdiv (a := r1 * r1) (b := 4) (by decide)
            rw [show r1 * r1 + 4 - 1 = r1 * r1 + 3 by omega] at this
            push_cast at this; exact this
          have hsq : (r * min t (1 - t)) ^ 2 ≤ (toR r1) ^ 2 / 4 := by
            have : r * min t (1 - t) ≤ toR r1 * (1 / 2) :=
              mul_le_mul hr1_ge hmin_half hmin_nn (by linarith)
            have hnn : 0 ≤ r * min t (1 - t) := mul_nonneg (le_of_lt hr_pos) hmin_nn
            nlinarith
          have hrad : ((S * S - (r1 * r1 + 3) / 4 : Int) : ℝ) / (S : ℝ) ^ 2 ≤
              1 - (r * min t (1 - t)) ^ 2 := by
            unfold toR at hsq
            push_cast
            have hdiv4' : (r1 : ℝ) ^ 2 / (4 * (S : ℝ) ^ 2) ≤
                (((r1 * r1 + 3) / 4 : Int) : ℝ) / (S : ℝ) ^ 2 := by
              rw [show (r1 : ℝ) ^ 2 / (4 * (S : ℝ) ^ 2) = ((r1 * r1 : ℝ) / 4) / (S : ℝ) ^ 2 by ring]
              exact div_le_div_of_nonneg_right hdiv4 (sq_nonneg _)
            have hS2 : (S : ℝ) ^ 2 / (S : ℝ) ^ 2 = 1 := div_self (pow_ne_zero 2 S_ne_zero)
            rw [sub_div, show ((S : ℝ) * (S : ℝ)) / (S : ℝ) ^ 2 = 1 by rw [← sq, hS2]]
            have : ((r1 : ℝ) / (S : ℝ)) ^ 2 / 4 = (r1 : ℝ) ^ 2 / (4 * (S : ℝ) ^ 2) := by ring
            linarith
          exact h1.trans (Real.sqrt_le_sqrt hrad)
        have hsqrt1 : Real.sqrt (max 0 (1 - (r * t - r * w.1) ^ 2)) ≤ 1 := by
          rw [Real.sqrt_le_one]
          exact max_le zero_le_one (by nlinarith [sq_nonneg (r * t - r * w.1)])
        have htrivR : 1 - toR (mulLo r0 y0) - toR baseMin ≤ 0 := by
          have : toR (S - mulLo r0 y0 - baseMin) ≤ 0 := by
            rw [← toR_zero]; exact toR_le_toR htriv
          rw [toR_sub, toR_sub, toR_S] at this; exact this
        dsimp only [g]
        exact max_eq_left (by linarith)
      rw [hcongr]; simp
    rw [hzero, mul_zero]
  · -- Split `[0, 1]` into 8 uniform subintervals of width `1/8`
    have hcont : Continuous g := by dsimp only [g]; fun_prop
    have hsplit : ∫ t in (0 : ℝ)..1, g t =
        ∑ i ∈ Finset.range 8, ∫ t in ((i : ℝ) / 8)..(((i + 1 : Nat) : ℝ) / 8), g t := by
      have hrec : ∀ m : Nat, ∫ t in (0 : ℝ)..((m : ℝ) / 8), g t =
          ∑ i ∈ Finset.range m, ∫ t in ((i : ℝ) / 8)..(((i + 1 : Nat) : ℝ) / 8), g t := by
        intro m; induction m with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ← ih, intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
      have h8 := hrec 8
      norm_num at h8
      simpa [Nat.cast_add, Nat.cast_one] using h8
    have hsum_le : ∫ t in (0 : ℝ)..1, g t ≤ toR (excessXSum r0 r1 x0 x1 y0 8) := by
      rw [hsplit, excessXSum_eq_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      exact excessXBin_sound hr_pos hr0_nn hr0_le hr1_ge hx0 hx1 hy0_nn hy0 (Finset.mem_range.mp hi)
    have hint_nn : 0 ≤ ∫ t in (0 : ℝ)..1, g t :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ => le_max_left _ _
    have hr1_nn : 0 ≤ toR r1 := (le_of_lt hr_pos).trans hr1_ge
    calc r * ∫ t in (0 : ℝ)..1, g t
        ≤ toR r1 * toR (excessXSum r0 r1 x0 x1 y0 8) :=
          mul_le_mul hr1_ge hsum_le hint_nn hr1_nn
      _ ≤ toR (mulHi r1 (excessXSum r0 r1 x0 x1 y0 8)) := le_mulHi

/-- **Certified Three-Disk Union Area Upper Bound**: for any triangle `(L, w)` in the box
`[l0/S, l1/S] × [x0/S, x1/S] × [y0/S, y1/S]` with `w ∈ quarterLens` and `0 < L < rad / S`,
`unionDiskArea ![(0,0), (L,0), (L*w.1, L*w.2)] (toR rad) ≤ toR (triAreaHi l0 l1 x0 x1 y0 y1 rad)`. -/
theorem triAreaHi_sound {l0 l1 x0 x1 y0 y1 rad : Int} {L : ℝ} {w : Pt}
    (hl0_nn : 0 ≤ l0) (_hx0_nn : 0 ≤ x0) (hy0_nn : 0 ≤ y0)
    (hL_pos : 0 < L) (hL_lt : L < toR rad)
    (hL_lo : toR l0 ≤ L) (hL_hi : L ≤ toR l1)
    (hx_lo : toR x0 ≤ w.1) (hx_hi : w.1 ≤ toR x1)
    (hy_lo : toR y0 ≤ w.2) (hy_hi : w.2 ≤ toR y1)
    (hw : w ∈ quarterLens) :
    unionDiskArea ![((0 : ℝ), (0 : ℝ)), (L, 0), (L * w.1, L * w.2)] (toR rad) ≤
      toR (triAreaHi l0 l1 x0 x1 y0 y1 rad) := by
  have hR_pos : 0 < toR rad := hL_pos.trans hL_lt
  have hrad_pos : 0 < rad := pos_of_toR_pos hR_pos
  have hbase := threeDiskArea_scale_le hL_pos hL_lt hw
  set r : ℝ := L / toR rad
  have hr_pos : 0 < r := div_pos hL_pos hR_pos
  have hr_lt : r < 1 := (div_lt_one hR_pos).mpr hL_lt
  unfold triAreaHi
  set r0 : Int := (l0 * S) / rad
  set r1 : Int := divHi l1 rad
  have hr0_nn : 0 ≤ r0 := Int.ediv_nonneg (mul_nonneg hl0_nn (by decide)) (le_of_lt hrad_pos)
  have hr0_le : toR r0 ≤ r := by
    have h1 := int_ediv_le_real_div (a := l0 * S) hrad_pos
    have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
    have h3 : ((l0 * S : Int) : ℝ) / (rad : ℝ) / (S : ℝ) = toR l0 / toR rad := by
      unfold toR; push_cast; field_simp [S_ne_zero]
    unfold toR at h2 ⊢
    calc (r0 : ℝ) / (S : ℝ) ≤ toR l0 / toR rad := by linarith
      _ ≤ L / toR rad := div_le_div_of_nonneg_right hL_lo (le_of_lt hR_pos)
  have hl1_nn : 0 ≤ l1 := nonneg_of_toR_nonneg ((le_of_lt hL_pos).trans hL_hi)
  have hr1_ge : r ≤ toR r1 := by
    calc r = L / toR rad := rfl
      _ ≤ toR l1 / toR rad := div_le_div_of_nonneg_right hL_hi (le_of_lt hR_pos)
      _ ≤ toR (divHi l1 rad) := le_divHi hrad_pos
  have hr1_nn : 0 ≤ r1 := nonneg_of_toR_nonneg ((le_of_lt hr_pos).trans hr1_ge)
  have hy1_nn : 0 ≤ y1 := nonneg_of_toR_nonneg ((le_of_lt hw.2.2.1).trans hy_hi)
  -- 1. Triangle area term `r^2 * w.2 / 2 ≤ toR triTerm`
  have htri_le : r ^ 2 * w.2 / 2 ≤ toR ((mulHi (mulHi r1 r1) y1 + 1) / 2) := by
    have hr2 : r ^ 2 ≤ toR (mulHi r1 r1) := by
      rw [sq]; exact (mul_le_mul hr1_ge hr1_ge (le_of_lt hr_pos) (toR_nonneg hr1_nn)).trans le_mulHi
    have hr2y : r ^ 2 * w.2 ≤ toR (mulHi (mulHi r1 r1) y1) := by
      exact (mul_le_mul hr2 hy_hi (le_of_lt hw.2.2.1) (toR_nonneg (mulHi_nonneg hr1_nn hr1_nn))).trans le_mulHi
    have hdiv := toR_div_le_cdiv (a := mulHi (mulHi r1 r1) y1) (d := 2) (by decide)
    rw [show mulHi (mulHi r1 r1) y1 + 2 - 1 = mulHi (mulHi r1 r1) y1 + 1 by omega] at hdiv
    push_cast at hdiv; linarith
  -- 2. Chord terms
  set e0 := min S r1
  set n1Hi := sqrtSqHi (x1 * x1 + y1 * y1)
  set e1 := min S (mulHi r1 n1Hi)
  set omx0 := S - x0
  set n2Hi := sqrtSqHi (omx0 * omx0 + y1 * y1)
  set e2 := min S (mulHi r1 n2Hi)
  have he0_range : 0 ≤ e0 ∧ e0 ≤ S := ⟨le_min (by decide) hr1_nn, min_le_left _ _⟩
  have he0_ge : r ≤ toR e0 := by
    dsimp only [e0]; rw [toR_min, toR_S]; exact le_min (le_of_lt hr_lt) hr1_ge
  have hc0 : chordArea r ≤ toR (chordPoly6Hi e0) :=
    (chordArea_monoOn ⟨le_of_lt hr_pos, le_of_lt hr_lt⟩
      ⟨toR_nonneg he0_range.1, by rw [← toR_S]; exact toR_le_toR he0_range.2⟩ he0_ge).trans
      (chordPoly6Hi_sound he0_range.1 he0_range.2)
  have hn1_ge : euclidNorm w ≤ toR n1Hi := by
    have h1 := le_sqrtSqHi (x1 * x1 + y1 * y1)
    have h2 : ((x1 * x1 + y1 * y1 : Int) : ℝ) / (S : ℝ) ^ 2 = (toR x1) ^ 2 + (toR y1) ^ 2 := by
      unfold toR; push_cast; ring
    rw [h2] at h1
    have hsq : w.1 ^ 2 + w.2 ^ 2 ≤ (toR x1) ^ 2 + (toR y1) ^ 2 := by
      nlinarith [hw.1, hw.2.2.1, hx_hi, hy_hi]
    exact (Real.sqrt_le_sqrt hsq).trans h1
  have he1_nn : 0 ≤ e1 := le_min (by decide) (mulHi_nonneg hr1_nn (sqrtSqHi_nonneg _))
  have he1_leS : e1 ≤ S := min_le_left _ _
  have hrw_lt1 : r * euclidNorm w < 1 := by
    have := quarterLens_euclidNorm_lt_one hw; nlinarith [Real.sqrt_nonneg (w.1 ^ 2 + w.2 ^ 2)]
  have he1_ge : r * euclidNorm w ≤ toR e1 := by
    dsimp only [e1]; rw [toR_min, toR_S]
    refine le_min (le_of_lt hrw_lt1) ?_
    exact (mul_le_mul hr1_ge hn1_ge (Real.sqrt_nonneg _) (toR_nonneg hr1_nn)).trans le_mulHi
  have hc1 : chordArea (r * euclidNorm w) ≤ toR (chordPoly6Hi e1) :=
    (chordArea_monoOn ⟨mul_nonneg (le_of_lt hr_pos) (Real.sqrt_nonneg _), le_of_lt hrw_lt1⟩
      ⟨toR_nonneg he1_nn, by rw [← toR_S]; exact toR_le_toR he1_leS⟩ he1_ge).trans
      (chordPoly6Hi_sound he1_nn he1_leS)
  have hn2_ge : euclidNorm (1 - w.1, w.2) ≤ toR n2Hi := by
    have h1 := le_sqrtSqHi (omx0 * omx0 + y1 * y1)
    have h2 : ((omx0 * omx0 + y1 * y1 : Int) : ℝ) / (S : ℝ) ^ 2 =
        (1 - toR x0) ^ 2 + (toR y1) ^ 2 := by
      dsimp only [omx0]; unfold toR; push_cast
      rw [add_div, show ((S : ℝ) - (x0 : ℝ)) * ((S : ℝ) - (x0 : ℝ)) / (S : ℝ) ^ 2 =
          (((S : ℝ) - (x0 : ℝ)) / (S : ℝ)) ^ 2 by ring, sub_div, div_self S_ne_zero]
      ring
    rw [h2] at h1
    have hsq : (1 - w.1) ^ 2 + w.2 ^ 2 ≤ (1 - toR x0) ^ 2 + (toR y1) ^ 2 := by
      have h1w : 0 ≤ 1 - w.1 := by linarith [hw.2.1]
      nlinarith [hw.2.2.1, hx_lo, hy_hi]
    exact (Real.sqrt_le_sqrt hsq).trans h1
  have he2_nn : 0 ≤ e2 := le_min (by decide) (mulHi_nonneg hr1_nn (sqrtSqHi_nonneg _))
  have he2_leS : e2 ≤ S := min_le_left _ _
  have hrw2_lt1 : r * euclidNorm (1 - w.1, w.2) < 1 := by
    have := quarterLens_euclidNorm_sub_lt_one hw; nlinarith [Real.sqrt_nonneg ((1 - w.1) ^ 2 + w.2 ^ 2)]
  have he2_ge : r * euclidNorm (1 - w.1, w.2) ≤ toR e2 := by
    dsimp only [e2]; rw [toR_min, toR_S]
    refine le_min (le_of_lt hrw2_lt1) ?_
    exact (mul_le_mul hr1_ge hn2_ge (Real.sqrt_nonneg _) (toR_nonneg hr1_nn)).trans le_mulHi
  have hc2 : chordArea (r * euclidNorm (1 - w.1, w.2)) ≤ toR (chordPoly6Hi e2) :=
    (chordArea_monoOn ⟨mul_nonneg (le_of_lt hr_pos) (Real.sqrt_nonneg _), le_of_lt hrw2_lt1⟩
      ⟨toR_nonneg he2_nn, by rw [← toR_S]; exact toR_le_toR he2_leS⟩ he2_ge).trans
      (chordPoly6Hi_sound he2_nn he2_leS)
  have hchord_le : (chordArea r + chordArea (r * euclidNorm w) +
      chordArea (r * euclidNorm (1 - w.1, w.2))) / 2 ≤
      toR ((chordPoly6Hi e0 + chordPoly6Hi e1 + chordPoly6Hi e2 + 1) / 2) := by
    have hdiv := toR_div_le_cdiv (a := chordPoly6Hi e0 + chordPoly6Hi e1 + chordPoly6Hi e2) (d := 2) (by decide)
    rw [show chordPoly6Hi e0 + chordPoly6Hi e1 + chordPoly6Hi e2 + 2 - 1 =
        chordPoly6Hi e0 + chordPoly6Hi e1 + chordPoly6Hi e2 + 1 by omega] at hdiv
    rw [toR_add, toR_add] at hdiv
    push_cast at hdiv; linarith
  -- 3. ExcessX term
  have hex_le : excessX r w ≤ toR (excessXHi r0 r1 x0 x1 y0) :=
    excessXHi_sound hr_pos hr_lt hr0_nn hr0_le hr1_ge hx_lo hx_hi hy0_nn hy_lo
  -- 4. Combine all terms and multiply by `R² ≤ toR (mulHi rad rad)`
  set triTerm := (mulHi (mulHi r1 r1) y1 + 1) / 2
  set chordTerm := (chordPoly6Hi e0 + chordPoly6Hi e1 + chordPoly6Hi e2 + 1) / 2
  set exTerm := excessXHi r0 r1 x0 x1 y0
  have hinner : threeDiskAreaBound r w ≤ toR (piHi + triTerm + chordTerm + exTerm) := by
    unfold threeDiskAreaBound
    rw [toR_add, toR_add, toR_add]
    linarith [pi_le_piHi]
  have hbound_nn : 0 ≤ threeDiskAreaBound r w := by
    unfold threeDiskAreaBound
    have h1 : 0 ≤ r ^ 2 * w.2 / 2 := by have := hw.2.2.1; positivity
    have h2 : 0 ≤ chordArea r := chordArea_nonneg (le_of_lt hr_pos)
    have h3 : 0 ≤ chordArea (r * euclidNorm w) :=
      chordArea_nonneg (mul_nonneg (le_of_lt hr_pos) (Real.sqrt_nonneg _))
    have h4 : 0 ≤ chordArea (r * euclidNorm (1 - w.1, w.2)) :=
      chordArea_nonneg (mul_nonneg (le_of_lt hr_pos) (Real.sqrt_nonneg _))
    have h5 : 0 ≤ excessX r w :=
      intervalIntegral.integral_nonneg (le_of_lt hr_pos) fun _ _ => le_max_left _ _
    linarith [Real.pi_pos]
  have hrad2 : (toR rad) ^ 2 ≤ toR (mulHi rad rad) := by rw [sq]; exact le_mulHi
  have hrad2_nn : 0 ≤ toR (mulHi rad rad) := toR_nonneg (mulHi_nonneg (le_of_lt hrad_pos) (le_of_lt hrad_pos))
  calc unionDiskArea ![((0 : ℝ), (0 : ℝ)), (L, 0), (L * w.1, L * w.2)] (toR rad)
      ≤ (toR rad) ^ 2 * threeDiskAreaBound r w := hbase
    _ ≤ toR (mulHi rad rad) * toR (piHi + triTerm + chordTerm + exTerm) :=
        mul_le_mul hrad2 hinner hbound_nn hrad2_nn
    _ ≤ toR (mulHi (mulHi rad rad) (piHi + triTerm + chordTerm + exTerm)) := le_mulHi

/-! ## Section 4: Joint Poisson Survival Upper Bound (`jointSurvHi_sound`) -/

/-- Exact Poisson joint survival probability for two disks of areas `a₁, a₂` with overlap `I`
(`0 ≤ I ≤ min a₁ a₂`), parametrized by flags `(k₁, k₂)` indicating whether the `N₂` event allows
one additional point inside each disk. -/
noncomputable def jointSurvCore (a₁ a₂ I : ℝ) (k₁ k₂ : Bool) : ℝ :=
  let a10 := a₁ - I
  let a01 := a₂ - I
  let au := a₁ + a₂ - I
  match k₁, k₂ with
  | false, false => Real.exp (-au)
  | true, false => (1 + a10) * Real.exp (-au)
  | false, true => (1 + a01) * Real.exp (-au)
  | true, true => ((1 + a10) * (1 + a01) + I) * Real.exp (-au)

/-- Exact Poisson joint survival probability at center distance `d` and radii `r₁, r₂`. -/
noncomputable def jointSurvReal (d r₁ r₂ : ℝ) (k₁ k₂ : Bool) : ℝ :=
  jointSurvCore (Real.pi * r₁ ^ 2) (Real.pi * r₂ ^ 2) (diskInterArea d r₁ r₂) k₁ k₂

lemma jointSurvCore_symm (a₁ a₂ I : ℝ) (k₁ k₂ : Bool) :
    jointSurvCore a₁ a₂ I k₁ k₂ = jointSurvCore a₂ a₁ I k₂ k₁ := by
  cases k₁ <;> cases k₂ <;> unfold jointSurvCore <;> ring_nf

/-- Elementary monotonicity of `jointSurvCore` in `(a₁, a₂, I)` using ONLY `1 + δ ≤ exp δ`! -/
lemma jointSurvCore_mono {a₁ a₂ I a₁' a₂' I' : ℝ}
    (ha1 : a₁' ≤ a₁) (ha2 : a₂' ≤ a₂)
    (hI0 : 0 ≤ I) (hI1 : I ≤ a₁) (hI2 : I ≤ a₂)
    (hI0' : 0 ≤ I') (hI1' : I' ≤ a₁') (hI2' : I' ≤ a₂')
    (hI_case : I ≤ I' ∨ I' = min a₁' a₂') (k₁ k₂ : Bool) :
    jointSurvCore a₁ a₂ I k₁ k₂ ≤ jointSurvCore a₁' a₂' I' k₁ k₂ := by
  -- Helper: `(A + Δ) * exp(-δ) ≤ A` whenever `0 ≤ δ`, `0 ≤ Δ ≤ δ * A`, `0 ≤ A`
  have hshift : ∀ A Δ δ : ℝ, 0 ≤ A → 0 ≤ δ → Δ ≤ δ * A →
      (A + Δ) * Real.exp (-δ) ≤ A := by
    intro A Δ δ hA hδ hΔ
    have hexp : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
    have hmul : A + Δ ≤ A * Real.exp δ := by nlinarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos δ)]
    exact hmul
  -- Step 1: Antitonicity in `a₁` at fixed `(a₂, I)`
  have hanti1 : ∀ (u₁ u₁' u₂ J : ℝ) (b₁ b₂ : Bool),
      0 ≤ J → J ≤ u₁' → u₁' ≤ u₁ → J ≤ u₂ →
      jointSurvCore u₁ u₂ J b₁ b₂ ≤ jointSurvCore u₁' u₂ J b₁ b₂ := by
    intro u₁ u₁' u₂ J b₁ b₂ hJ0 hJu1 h1 hJu2
    set δ := u₁ - u₁'
    have hδ : 0 ≤ δ := by linarith
    have hexp : Real.exp (-(u₁ + u₂ - J)) = Real.exp (-δ) * Real.exp (-(u₁' + u₂ - J)) := by
      rw [← Real.exp_add]; congr 1; dsimp only [δ]; ring
    cases b₁ <;> cases b₂ <;> unfold jointSurvCore <;> dsimp only <;> rw [hexp]
    · have : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.exp_pos (-(u₁' + u₂ - J))]
    · have hexp1 : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h1u : 0 ≤ 1 + (u₂ - J) := by linarith
      have h2 : Real.exp (-δ) * Real.exp (-(u₁' + u₂ - J)) ≤ Real.exp (-(u₁' + u₂ - J)) := by
        nlinarith [Real.exp_pos (-(u₁' + u₂ - J))]
      exact mul_le_mul_of_nonneg_left h2 h1u
    · have hA : 0 ≤ 1 + (u₁' - J) := by linarith
      have hs := hshift (1 + (u₁' - J)) δ δ hA hδ (by nlinarith)
      have hrew : (1 + (u₁ - J)) * (Real.exp (-δ) * Real.exp (-(u₁' + u₂ - J))) =
          ((1 + (u₁' - J) + δ) * Real.exp (-δ)) * Real.exp (-(u₁' + u₂ - J)) := by
        dsimp only [δ]; ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
    · set x := u₁' - J
      set y := u₂ - J
      have hx : 0 ≤ x := by linarith
      have hy : 0 ≤ y := by linarith
      have hA : 0 ≤ (1 + x) * (1 + y) + J := by nlinarith
      have hΔ : δ * (1 + y) ≤ δ * ((1 + x) * (1 + y) + J) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hδ
      have hs := hshift ((1 + x) * (1 + y) + J) (δ * (1 + y)) δ hA hδ hΔ
      have hrew : ((1 + (u₁ - J)) * (1 + (u₂ - J)) + J) * (Real.exp (-δ) * Real.exp (-(u₁' + u₂ - J))) =
          (((1 + x) * (1 + y) + J + δ * (1 + y)) * Real.exp (-δ)) * Real.exp (-(u₁' + u₂ - J)) := by
        dsimp only [δ, x, y]; ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
  -- Step 2: Monotonicity in `I` at fixed `(a₁, a₂)`
  have hmonoI : ∀ (u₁ u₂ J J' : ℝ) (b₁ b₂ : Bool),
      0 ≤ J → J ≤ J' → J' ≤ u₁ → J' ≤ u₂ →
      jointSurvCore u₁ u₂ J b₁ b₂ ≤ jointSurvCore u₁ u₂ J' b₁ b₂ := by
    intro u₁ u₂ J J' b₁ b₂ hJ0 hJJ h1 h2
    set δ := J' - J
    have hδ : 0 ≤ δ := by linarith
    have hδJ' : δ ≤ J' := by linarith
    have hexp : Real.exp (-(u₁ + u₂ - J)) = Real.exp (-δ) * Real.exp (-(u₁ + u₂ - J')) := by
      rw [← Real.exp_add]; congr 1; dsimp only [δ]; ring
    cases b₁ <;> cases b₂ <;> unfold jointSurvCore <;> dsimp only <;> rw [hexp]
    · have : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.exp_pos (-(u₁ + u₂ - J'))]
    · set y := u₂ - J'
      have hy : 0 ≤ y := by linarith
      have hs := hshift (1 + y) δ δ (by linarith) hδ (by nlinarith)
      have hrew : (1 + (u₂ - J)) * (Real.exp (-δ) * Real.exp (-(u₁ + u₂ - J'))) =
          ((1 + y + δ) * Real.exp (-δ)) * Real.exp (-(u₁ + u₂ - J')) := by dsimp only [δ, y]; ring
      rw [hrew]; exact mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
    · set x := u₁ - J'
      have hx : 0 ≤ x := by linarith
      have hs := hshift (1 + x) δ δ (by linarith) hδ (by nlinarith)
      have hrew : (1 + (u₁ - J)) * (Real.exp (-δ) * Real.exp (-(u₁ + u₂ - J'))) =
          ((1 + x + δ) * Real.exp (-δ)) * Real.exp (-(u₁ + u₂ - J')) := by dsimp only [δ, x]; ring
      rw [hrew]; exact mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
    · set x := u₁ - J'
      set y := u₂ - J'
      have hx : 0 ≤ x := by linarith
      have hy : 0 ≤ y := by linarith
      have hA : 0 ≤ (1 + x) * (1 + y) + J' := by nlinarith
      have hΔ : δ * (1 + x + y) + δ ^ 2 ≤ δ * ((1 + x) * (1 + y) + J') := by
        have h1 : 1 + x + y + δ ≤ (1 + x) * (1 + y) + J' := by nlinarith
        have h2 := mul_le_mul_of_nonneg_left h1 hδ
        linarith [show δ * (1 + x + y + δ) = δ * (1 + x + y) + δ ^ 2 by ring]
      have hs := hshift ((1 + x) * (1 + y) + J') (δ * (1 + x + y) + δ ^ 2) δ hA hδ hΔ
      have hrew : ((1 + (u₁ - J)) * (1 + (u₂ - J)) + J) * (Real.exp (-δ) * Real.exp (-(u₁ + u₂ - J'))) =
          (((1 + x) * (1 + y) + J' + (δ * (1 + x + y) + δ ^ 2)) * Real.exp (-δ)) *
            Real.exp (-(u₁ + u₂ - J')) := by dsimp only [δ, x, y]; ring
      rw [hrew]; exact mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
  -- Case split on `I ≤ I'` vs `I' = min a₁' a₂'`
  rcases hI_case with hIle | hIeq
  · have hIa1' : I ≤ a₁' := hIle.trans hI1'
    have hIa2' : I ≤ a₂' := hIle.trans hI2'
    calc jointSurvCore a₁ a₂ I k₁ k₂
        ≤ jointSurvCore a₁' a₂ I k₁ k₂ := hanti1 a₁ a₁' a₂ I k₁ k₂ hI0 hIa1' ha1 hI2
      _ = jointSurvCore a₂ a₁' I k₂ k₁ := jointSurvCore_symm _ _ _ _ _
      _ ≤ jointSurvCore a₂' a₁' I k₂ k₁ := hanti1 a₂ a₂' a₁' I k₂ k₁ hI0 hIa2' ha2 hIa1'
      _ = jointSurvCore a₁' a₂' I k₁ k₂ := jointSurvCore_symm _ _ _ _ _
      _ ≤ jointSurvCore a₁' a₂' I' k₁ k₂ := hmonoI a₁' a₂' I I' k₁ k₂ hI0 hIle hI1' hI2'
  · -- Handle `I' = min a₁' a₂'` (WLOG `a₁' ≤ a₂'` by symmetry!)
    have hcase_le : ∀ (u₁ u₂ J u₁' u₂' : ℝ) (b₁ b₂ : Bool),
        u₁' ≤ u₁ → u₂' ≤ u₂ → 0 ≤ J → J ≤ u₁ → J ≤ u₂ → 0 ≤ u₁' → u₁' ≤ u₂' →
        jointSurvCore u₁ u₂ J b₁ b₂ ≤ jointSurvCore u₁' u₂' u₁' b₁ b₂ := by
      intro u₁ u₂ J u₁' u₂' b₁ b₂ hu1 hu2 hJ0 hJu1 hJu2 hu1'0 hu12'
      -- First increase `J` to `min u₁ u₂`? No, compare directly against `au = u₂ + (u₁ - J)`!
      set u := u₁ - J
      set v := u₂ - J
      have hu : 0 ≤ u := by linarith
      have hv : 0 ≤ v := by linarith
      have hδ2 : 0 ≤ u₂ - u₂' := by linarith
      have hexp : Real.exp (-(u₁ + u₂ - J)) = Real.exp (-(u + (u₂ - u₂'))) * Real.exp (-u₂') := by
        rw [← Real.exp_add]; congr 1; dsimp only [u]; ring
      have hexp' : u₁' + u₂' - u₁' = u₂' := by ring
      cases b₁ <;> cases b₂ <;> unfold jointSurvCore <;> dsimp only <;> rw [hexp, hexp']
      · have : Real.exp (-(u + (u₂ - u₂'))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        nlinarith [Real.exp_pos (-u₂')]
      · -- `(1 + u₂ - J) * exp(-(u + (u₂ - u₂'))) ≤ (1 + u₂' - u₁')`
        have hA : 0 ≤ 1 + (u₂' - u₁') := by linarith
        have h1 : 1 + (u₂ - J) ≤ (1 + (u₂' - u₁')) + (u + (u₂ - u₂')) := by
          dsimp only [u]; linarith
        have hΔ : u + (u₂ - u₂') ≤ (u + (u₂ - u₂')) * (1 + (u₂' - u₁')) := by nlinarith
        have hs := hshift (1 + (u₂' - u₁')) (u + (u₂ - u₂')) (u + (u₂ - u₂')) hA (by linarith) hΔ
        calc (1 + (u₂ - J)) * (Real.exp (-(u + (u₂ - u₂'))) * Real.exp (-u₂'))
            = ((1 + (u₂ - J)) * Real.exp (-(u + (u₂ - u₂')))) * Real.exp (-u₂') := by ring
          _ ≤ ((1 + (u₂' - u₁') + (u + (u₂ - u₂'))) * Real.exp (-(u + (u₂ - u₂')))) * Real.exp (-u₂') :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _)))
                (le_of_lt (Real.exp_pos _))
          _ ≤ (1 + (u₂' - u₁')) * Real.exp (-u₂') :=
              mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
      · -- `(1 + u) * exp(-(u + (u₂ - u₂'))) ≤ 1`
        have hs := hshift 1 (u + (u₂ - u₂')) (u + (u₂ - u₂')) zero_le_one (by linarith) (by linarith)
        have h1 : 1 + u ≤ 1 + (u + (u₂ - u₂')) := by linarith
        calc (1 + u) * (Real.exp (-(u + (u₂ - u₂'))) * Real.exp (-u₂'))
            = ((1 + u) * Real.exp (-(u + (u₂ - u₂')))) * Real.exp (-u₂') := by ring
          _ ≤ ((1 + (u + (u₂ - u₂'))) * Real.exp (-(u + (u₂ - u₂')))) * Real.exp (-u₂') :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _)))
                (le_of_lt (Real.exp_pos _))
          _ ≤ 1 * Real.exp (-u₂') := mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
          _ = (1 + (u₁' - u₁')) * Real.exp (-u₂') := by ring
      · -- `((1 + u)(1 + v) + J) * exp(-(u + (u₂ - u₂'))) ≤ 1 + u₂'`
        -- First step: `((1 + u)(1 + v) + J) * exp(-u) ≤ 1 + u₂`
        have hstep1 : ((1 + u) * (1 + v) + J) * Real.exp (-u) ≤ 1 + u₂ := by
          have hA : 0 ≤ 1 + u₂ := by linarith
          have hrew : (1 + u) * (1 + v) + J = (1 + u₂) + u * (1 + v) := by dsimp only [v]; ring
          have hv_le : v ≤ u₂ := by dsimp only [v]; linarith
          have hΔ : u * (1 + v) ≤ u * (1 + u₂) := by nlinarith
          rw [hrew]; exact hshift (1 + u₂) (u * (1 + v)) u hA hu hΔ
        -- Second step: `(1 + u₂) * exp(-(u₂ - u₂')) ≤ 1 + u₂'`
        have hstep2 : (1 + u₂) * Real.exp (-(u₂ - u₂')) ≤ 1 + u₂' := by
          have hA : 0 ≤ 1 + u₂' := by linarith
          have hrew : 1 + u₂ = (1 + u₂') + (u₂ - u₂') := by ring
          rw [hrew]; exact hshift (1 + u₂') (u₂ - u₂') (u₂ - u₂') hA hδ2 (by nlinarith)
        have hexp2 : Real.exp (-(u + (u₂ - u₂'))) = Real.exp (-u) * Real.exp (-(u₂ - u₂')) := by
          rw [← Real.exp_add]; congr 1; ring
        have hrhs : (1 + (u₁' - u₁')) * (1 + (u₂' - u₁')) + u₁' = 1 + u₂' := by ring
        rw [hexp2, hrhs]
        calc ((1 + u) * (1 + v) + J) * (Real.exp (-u) * Real.exp (-(u₂ - u₂')) * Real.exp (-u₂'))
            = (((1 + u) * (1 + v) + J) * Real.exp (-u)) * Real.exp (-(u₂ - u₂')) * Real.exp (-u₂') := by ring
          _ ≤ ((1 + u₂) * Real.exp (-(u₂ - u₂'))) * Real.exp (-u₂') :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hstep1 (le_of_lt (Real.exp_pos _)))
                (le_of_lt (Real.exp_pos _))
          _ ≤ (1 + u₂') * Real.exp (-u₂') :=
              mul_le_mul_of_nonneg_right hstep2 (le_of_lt (Real.exp_pos _))
    rcases le_total a₁' a₂' with h12 | h21
    · rw [hIeq, min_eq_left h12]
      exact hcase_le a₁ a₂ I a₁' a₂' k₁ k₂ ha1 ha2 hI0 hI1 hI2 (hI0'.trans hI1') h12
    · rw [hIeq, min_eq_right h21, jointSurvCore_symm a₁ a₂, jointSurvCore_symm a₁' a₂']
      exact hcase_le a₂ a₁ I a₂' a₁' k₂ k₁ ha2 ha1 hI0 hI2 hI1 (hI0'.trans hI2') h21

/-- **Certified Joint Poisson Survival Upper Bound**: for all `0 ≤ d, r1, r2`,
`jointSurvReal (toR d) (toR r1) (toR r2) k1 k2 ≤ toR (jointSurvHi d r1 r2 k1 k2)`. -/
theorem jointSurvHi_sound {d r1 r2 : Int} (hd : 0 ≤ d) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (k1 k2 : Bool) :
    jointSurvReal (toR d) (toR r1) (toR r2) k1 k2 ≤ toR (jointSurvHi d r1 r2 k1 k2) := by
  unfold jointSurvReal jointSurvHi
  set a1Lo := mulLo piLo (mulLo r1 r1)
  set a2Lo := mulLo piLo (mulLo r2 r2)
  set interHi := min (min a1Lo a2Lo) (circleInterHi d r1 r2)
  have ha1Lo_nn : 0 ≤ a1Lo := mulLo_nonneg (by decide) (mulLo_nonneg hr1 hr1)
  have ha2Lo_nn : 0 ≤ a2Lo := mulLo_nonneg (by decide) (mulLo_nonneg hr2 hr2)
  have ha1Lo_le : toR a1Lo ≤ Real.pi * (toR r1) ^ 2 := by
    calc toR a1Lo ≤ toR piLo * toR (mulLo r1 r1) := mulLo_le
      _ ≤ Real.pi * (toR r1) ^ 2 := by
        have hsq : toR (mulLo r1 r1) ≤ (toR r1) ^ 2 := by rw [sq]; exact mulLo_le
        exact mul_le_mul piLo_le_pi hsq (toR_nonneg (mulLo_nonneg hr1 hr1)) (le_of_lt Real.pi_pos)
  have ha2Lo_le : toR a2Lo ≤ Real.pi * (toR r2) ^ 2 := by
    calc toR a2Lo ≤ toR piLo * toR (mulLo r2 r2) := mulLo_le
      _ ≤ Real.pi * (toR r2) ^ 2 := by
        have hsq : toR (mulLo r2 r2) ≤ (toR r2) ^ 2 := by rw [sq]; exact mulLo_le
        exact mul_le_mul piLo_le_pi hsq (toR_nonneg (mulLo_nonneg hr2 hr2)) (le_of_lt Real.pi_pos)
  have hI0 : 0 ≤ diskInterArea (toR d) (toR r1) (toR r2) := diskInterArea_nonneg _ _ _
  have hImin : diskInterArea (toR d) (toR r1) (toR r2) ≤
      Real.pi * (min (toR r1) (toR r2)) ^ 2 :=
    diskInterArea_le_min_disk (toR_nonneg hd) (toR_nonneg hr1) (toR_nonneg hr2)
  have hI1 : diskInterArea (toR d) (toR r1) (toR r2) ≤ Real.pi * (toR r1) ^ 2 := by
    refine hImin.trans (mul_le_mul_of_nonneg_left ?_ (le_of_lt Real.pi_pos))
    exact pow_le_pow_left₀ (le_min (toR_nonneg hr1) (toR_nonneg hr2)) (min_le_left _ _) 2
  have hI2 : diskInterArea (toR d) (toR r1) (toR r2) ≤ Real.pi * (toR r2) ^ 2 := by
    refine hImin.trans (mul_le_mul_of_nonneg_left ?_ (le_of_lt Real.pi_pos))
    exact pow_le_pow_left₀ (le_min (toR_nonneg hr1) (toR_nonneg hr2)) (min_le_right _ _) 2
  have hI_le_ci : diskInterArea (toR d) (toR r1) (toR r2) ≤ toR (circleInterHi d r1 r2) :=
    circleInterHi_sound hd hr1 hr2
  have hci_nn : 0 ≤ circleInterHi d r1 r2 := nonneg_of_toR_nonneg (hI0.trans hI_le_ci)
  have hinter_nn : 0 ≤ interHi := le_min (le_min ha1Lo_nn ha2Lo_nn) hci_nn
  have hinter_le1 : interHi ≤ a1Lo := (min_le_left _ _).trans (min_le_left _ _)
  have hinter_le2 : interHi ≤ a2Lo := (min_le_left _ _).trans (min_le_right _ _)
  have hI_case : diskInterArea (toR d) (toR r1) (toR r2) ≤ toR interHi ∨
      toR interHi = min (toR a1Lo) (toR a2Lo) := by
    dsimp only [interHi]
    rw [toR_min, toR_min]
    rcases le_total (min (toR a1Lo) (toR a2Lo)) (toR (circleInterHi d r1 r2)) with h | h
    · right; exact min_eq_left h
    · left; rw [min_eq_right h]; exact hI_le_ci
  have hcore := jointSurvCore_mono ha1Lo_le ha2Lo_le hI0 hI1 hI2
    (toR_nonneg hinter_nn) (toR_le_toR hinter_le1) (toR_le_toR hinter_le2) hI_case k1 k2
  refine hcore.trans ?_
  set a10 := max 0 (a1Lo - interHi)
  set a01 := max 0 (a2Lo - interHi)
  set au := a1Lo + a2Lo - interHi
  have ha10_eq : a10 = a1Lo - interHi := max_eq_right (by omega)
  have ha01_eq : a01 = a2Lo - interHi := max_eq_right (by omega)
  have hau_nn : 0 ≤ au := by dsimp only [au]; omega
  have heHi : Real.exp (-(toR a1Lo + toR a2Lo - toR interHi)) ≤ toR (expNegHi au) := by
    have : toR a1Lo + toR a2Lo - toR interHi = toR au := by dsimp only [au]; rw [toR_sub, toR_add]
    rw [this]; exact le_expNegHi hau_nn
  have he_nn : 0 ≤ Real.exp (-(toR a1Lo + toR a2Lo - toR interHi)) := Real.exp_nonneg _
  have h1a10 : 1 + (toR a1Lo - toR interHi) = toR (S + a10) := by
    rw [ha10_eq, toR_add, toR_sub, toR_S]
  have h1a01 : 1 + (toR a2Lo - toR interHi) = toR (S + a01) := by
    rw [ha01_eq, toR_add, toR_sub, toR_S]
  have h1a10_nn : 0 ≤ toR (S + a10) := toR_nonneg (by dsimp only [a10]; unfold S; omega)
  have h1a01_nn : 0 ≤ toR (S + a01) := toR_nonneg (by dsimp only [a01]; unfold S; omega)
  cases k1 <;> cases k2 <;> unfold jointSurvCore <;> dsimp only
  · exact heHi
  · rw [h1a01]
    exact (mul_le_mul_of_nonneg_left heHi h1a01_nn).trans le_mulHi
  · rw [h1a10]
    exact (mul_le_mul_of_nonneg_left heHi h1a10_nn).trans le_mulHi
  · rw [h1a10, h1a01]
    have hprod : toR (S + a10) * toR (S + a01) + toR interHi ≤
        toR (mulHi (S + a10) (S + a01) + interHi) := by
      rw [toR_add (mulHi (S + a10) (S + a01)) interHi]
      linarith [le_mulHi (a := S + a10) (b := S + a01)]
    have hfac_nn : 0 ≤ toR (mulHi (S + a10) (S + a01) + interHi) :=
      (by nlinarith [toR_nonneg hinter_nn] : 0 ≤ toR (S + a10) * toR (S + a01) + toR interHi).trans hprod
    calc (toR (S + a10) * toR (S + a01) + toR interHi) * Real.exp (-(toR a1Lo + toR a2Lo - toR interHi))
        ≤ toR (mulHi (S + a10) (S + a01) + interHi) * toR (expNegHi au) :=
          mul_le_mul hprod heHi he_nn hfac_nn
      _ ≤ toR (mulHi (mulHi (S + a10) (S + a01) + interHi) (expNegHi au)) := le_mulHi

/-! ## Section 5: Box Norm & Angle-Addition Dot Product Soundness -/

lemma boxNorm2LoHi_sound {x0 x1 y0 y1 : Int} {x y : ℝ}
    (hx0 : toR x0 ≤ x) (hx1 : x ≤ toR x1) (hy0 : toR y0 ≤ y) (hy1 : y ≤ toR y1) :
    let (q2Lo, q2Hi) := boxNorm2LoHi x0 x1 y0 y1
    (q2Lo : ℝ) / (S : ℝ) ^ 2 ≤ x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ (q2Hi : ℝ) / (S : ℝ) ^ 2 := by
  have h1d : ∀ (a b : Int) (t : ℝ), toR a ≤ t → t ≤ toR b →
      let l : Int := if a ≤ 0 ∧ 0 ≤ b then 0 else min a.natAbs b.natAbs
      let h : Int := max a.natAbs b.natAbs
      (l * l : ℝ) / (S : ℝ) ^ 2 ≤ t ^ 2 ∧ t ^ 2 ≤ (h * h : ℝ) / (S : ℝ) ^ 2 := by
    intro a b t ha hb l h
    constructor
    · dsimp only [l]
      split_ifs with h0
      · simp; exact sq_nonneg t
      · push Not at h0
        have hcases : b < 0 ∨ 0 < a := by omega
        rcases hcases with hneg | hpos
        · have hab : a ≤ b := le_of_toR_le (ha.trans hb)
          have hmin : min (a.natAbs : Int) (b.natAbs : Int) = (b.natAbs : Int) := by omega
          rw [hmin]
          have hbabs : ((b.natAbs : Int) : ℝ) = -(b : ℝ) := by
            have : (b.natAbs : Int) = -b := by omega
            exact_mod_cast this
          rw [hbabs]; unfold toR at hb
          have hb0 : (b : ℝ) / (S : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_lt hneg) (le_of_lt S_pos)
          have : (-(b : ℝ) * -(b : ℝ)) / (S : ℝ) ^ 2 = ((b : ℝ) / (S : ℝ)) ^ 2 := by ring
          rw [this]; nlinarith
        · have hab : a ≤ b := le_of_toR_le (ha.trans hb)
          have hmin : min (a.natAbs : Int) (b.natAbs : Int) = (a.natAbs : Int) := by omega
          rw [hmin]
          have haabs : ((a.natAbs : Int) : ℝ) = (a : ℝ) := by
            have : (a.natAbs : Int) = a := by omega
            exact_mod_cast this
          rw [haabs]; unfold toR at ha
          have ha0 : 0 ≤ (a : ℝ) / (S : ℝ) := div_nonneg (by exact_mod_cast le_of_lt hpos) (le_of_lt S_pos)
          have : ((a : ℝ) * (a : ℝ)) / (S : ℝ) ^ 2 = ((a : ℝ) / (S : ℝ)) ^ 2 := by ring
          rw [this]; nlinarith
    · have habs : |t| ≤ (h : ℝ) / (S : ℝ) := by
        rw [abs_le]
        have ha_le : -((h : ℝ) / (S : ℝ)) ≤ toR a := by
          unfold toR; rw [← neg_div]
          refine div_le_div_of_nonneg_right ?_ (le_of_lt S_pos)
          have : -h ≤ a := by dsimp only [h]; omega
          exact_mod_cast this
        have hb_le : toR b ≤ (h : ℝ) / (S : ℝ) := by
          unfold toR
          refine div_le_div_of_nonneg_right ?_ (le_of_lt S_pos)
          have : b ≤ h := by dsimp only [h]; omega
          exact_mod_cast this
        exact ⟨ha_le.trans ha, hb.trans hb_le⟩
      have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      have hrhs : (h * h : ℝ) / (S : ℝ) ^ 2 = ((h : ℝ) / (S : ℝ)) ^ 2 := by ring
      rw [hsq, hrhs]
      exact pow_le_pow_left₀ (abs_nonneg t) habs 2
  have hx := h1d x0 x1 x hx0 hx1
  have hy := h1d y0 y1 y hy0 hy1
  unfold boxNorm2LoHi
  dsimp only at hx hy ⊢
  rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_mul]
  constructor <;> rw [add_div] <;> linarith

lemma cornerDotLoHi_sound {qx qy clo chi slo shi ch sh : Int} {tm u : ℝ}
    (hclo : toR clo ≤ Real.cos tm) (hchi : Real.cos tm ≤ toR chi)
    (hslo : toR slo ≤ Real.sin tm) (hshi : Real.sin tm ≤ toR shi)
    (hch_nn : 0 ≤ ch) (hch : toR ch ≤ Real.cos u) (hsh : |Real.sin u| ≤ toR sh) :
    let (lo, hi) := cornerDotLoHi qx qy clo chi slo shi ch sh
    toR lo ≤ toR qx * Real.cos (tm + u) + toR qy * Real.sin (tm + u) ∧
    toR qx * Real.cos (tm + u) + toR qy * Real.sin (tm + u) ≤ toR hi := by
  have hadd : toR qx * Real.cos (tm + u) + toR qy * Real.sin (tm + u) =
      (toR qx * Real.cos tm + toR qy * Real.sin tm) * Real.cos u +
      (-toR qx * Real.sin tm + toR qy * Real.cos tm) * Real.sin u := by
    rw [Real.cos_add, Real.sin_add]; ring
  rw [hadd]
  -- Helper: interval bound for `q * v` when `toR lo ≤ v ≤ toR hi`
  have hmul_int : ∀ (q lo hi : Int) (v : ℝ), toR lo ≤ v → v ≤ toR hi →
      ((min (q * lo) (q * hi) : Int) : ℝ) / (S : ℝ) ^ 2 ≤ toR q * v ∧
      toR q * v ≤ ((max (q * lo) (q * hi) : Int) : ℝ) / (S : ℝ) ^ 2 := by
    intro q lo hi v hlo hhi
    unfold toR at hlo hhi ⊢
    rw [Int.cast_min, Int.cast_max, ← min_div_div_right (sq_nonneg _), ← max_div_div_right (sq_nonneg _)]
    push_cast
    have hmul_eq : ∀ z : Int, ((q : ℝ) * (z : ℝ)) / (S : ℝ) ^ 2 = ((q : ℝ) / (S : ℝ)) * ((z : ℝ) / (S : ℝ)) :=
      fun z => by ring
    rw [hmul_eq lo, hmul_eq hi]
    rcases le_total (0 : ℝ) ((q : ℝ) / (S : ℝ)) with hq | hq
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlo hq),
        (mul_le_mul_of_nonneg_left hhi hq).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hhi hq),
        (mul_le_mul_of_nonpos_left hlo hq).trans (le_max_left _ _)⟩
  unfold cornerDotLoHi
  dsimp only
  set A := toR qx * Real.cos tm + toR qy * Real.sin tm
  set B := -toR qx * Real.sin tm + toR qy * Real.cos tm
  set p1l := min (qx * clo) (qx * chi)
  set p1h := max (qx * clo) (qx * chi)
  set p2l := min (qy * slo) (qy * shi)
  set p2h := max (qy * slo) (qy * shi)
  set aLo := fdiv (p1l + p2l) S
  set aHi := cdiv (p1h + p2h) S
  set b1l := min (-qx * slo) (-qx * shi)
  set b1h := max (-qx * slo) (-qx * shi)
  set b2l := min (qy * clo) (qy * chi)
  set b2h := max (qy * clo) (qy * chi)
  set bSumLo := b1l + b2l
  set bSumHi := b1h + b2h
  set bAbsMax : Int := max bSumLo.natAbs bSumHi.natAbs
  set bAbsHi := (bAbsMax + S - 1) / S
  set acLo := if aLo ≥ 0 then (aLo * ch) / S else aLo
  set acHi := if aHi ≥ 0 then aHi else -(((-aHi) * ch) / S)
  set bTerm := (bAbsHi * sh + S - 1) / S
  have hp1 := hmul_int qx clo chi (Real.cos tm) hclo hchi
  have hp2 := hmul_int qy slo shi (Real.sin tm) hslo hshi
  have hA_lo : toR aLo ≤ A := by
    have hf := fdiv_le_real_div (a := p1l + p2l) (b := S) (by decide)
    have hf2 := div_le_div_of_nonneg_right hf (le_of_lt S_pos)
    have hrew : ((p1l + p2l : Int) : ℝ) / (S : ℝ) / (S : ℝ) =
        (p1l : ℝ) / (S : ℝ) ^ 2 + (p2l : ℝ) / (S : ℝ) ^ 2 := by push_cast; ring
    unfold toR at hf2 ⊢; dsimp only [A]; linarith
  have hA_hi : A ≤ toR aHi := by
    have hc := real_div_le_cdiv (a := p1h + p2h) (b := S) (by decide)
    have hc2 := div_le_div_of_nonneg_right hc (le_of_lt S_pos)
    have hrew : ((p1h + p2h : Int) : ℝ) / (S : ℝ) / (S : ℝ) =
        (p1h : ℝ) / (S : ℝ) ^ 2 + (p2h : ℝ) / (S : ℝ) ^ 2 := by push_cast; ring
    unfold toR at hc2 ⊢; dsimp only [A, aHi]; linarith
  have hb1 := hmul_int (-qx) slo shi (Real.sin tm) hslo hshi
  have hb2 := hmul_int qy clo chi (Real.cos tm) hclo hchi
  rw [toR_neg] at hb1
  have hB_abs : |B| ≤ toR bAbsHi := by
    have hB_lo : (bSumLo : ℝ) / (S : ℝ) ^ 2 ≤ B := by
      dsimp only [bSumLo, B]; push_cast; rw [add_div]; linarith
    have hB_hi : B ≤ (bSumHi : ℝ) / (S : ℝ) ^ 2 := by
      dsimp only [bSumHi, B]; push_cast; rw [add_div]; linarith
    have hmax_ge : |B| ≤ (bAbsMax : ℝ) / (S : ℝ) ^ 2 := by
      rw [abs_le]
      have h1 : -bAbsMax ≤ bSumLo := by dsimp only [bAbsMax]; omega
      have h2 : bSumHi ≤ bAbsMax := by dsimp only [bAbsMax]; omega
      have h1R : -((bAbsMax : ℝ) / (S : ℝ) ^ 2) ≤ (bSumLo : ℝ) / (S : ℝ) ^ 2 := by
        rw [← neg_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (sq_nonneg _)
      have h2R : (bSumHi : ℝ) / (S : ℝ) ^ 2 ≤ (bAbsMax : ℝ) / (S : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by exact_mod_cast h2) (sq_nonneg _)
      exact ⟨h1R.trans hB_lo, hB_hi.trans h2R⟩
    have hc := toR_div_le_cdiv (a := bAbsMax) (d := S) (by decide)
    have hrew : toR bAbsMax / (S : ℝ) = (bAbsMax : ℝ) / (S : ℝ) ^ 2 := by unfold toR; ring
    linarith
  have hcos_nn : 0 ≤ Real.cos u := (toR_nonneg hch_nn).trans hch
  have hcos_le1 : Real.cos u ≤ 1 := Real.cos_le_one u
  have hAc_lo : toR acLo ≤ A * Real.cos u := by
    dsimp only [acLo]
    split_ifs with ha0
    · have h1 : toR ((aLo * ch) / S) ≤ toR aLo * toR ch := mulLo_le
      have h2 : toR aLo * toR ch ≤ A * Real.cos u :=
        mul_le_mul hA_lo hch (toR_nonneg hch_nn) ((toR_nonneg ha0).trans hA_lo)
      exact h1.trans h2
    · push Not at ha0
      have h1 : toR aLo ≤ toR aLo * Real.cos u := by
        have : toR aLo ≤ 0 := by rw [← toR_zero]; exact toR_le_toR (le_of_lt ha0)
        nlinarith
      have h2 : toR aLo * Real.cos u ≤ A * Real.cos u := mul_le_mul_of_nonneg_right hA_lo hcos_nn
      exact h1.trans h2
  have hAc_hi : A * Real.cos u ≤ toR acHi := by
    dsimp only [acHi]
    split_ifs with ha0
    · have h1 : A * Real.cos u ≤ toR aHi * Real.cos u := mul_le_mul_of_nonneg_right hA_hi hcos_nn
      have h2 : toR aHi * Real.cos u ≤ toR aHi := by nlinarith [toR_nonneg ha0]
      exact h1.trans h2
    · push Not at ha0
      have h1 : A * Real.cos u ≤ toR aHi * Real.cos u := mul_le_mul_of_nonneg_right hA_hi hcos_nn
      have h2 : toR aHi * Real.cos u ≤ toR aHi * toR ch := by
        have : toR aHi ≤ 0 := by rw [← toR_zero]; exact toR_le_toR (le_of_lt ha0)
        nlinarith
      have h3 : toR aHi * toR ch ≤ toR (-(((-aHi) * ch) / S)) := by
        rw [toR_neg]
        have hlo : toR (((-aHi) * ch) / S) ≤ toR (-aHi) * toR ch := mulLo_le
        rw [toR_neg] at hlo; linarith
      exact (h1.trans h2).trans h3
  have hBs_abs : |B * Real.sin u| ≤ toR bTerm := by
    rw [abs_mul]
    have h1 : |B| * |Real.sin u| ≤ toR bAbsHi * toR sh :=
      mul_le_mul hB_abs hsh (abs_nonneg _) ((abs_nonneg B).trans hB_abs)
    have h2 : toR bAbsHi * toR sh ≤ toR bTerm := le_mulHi
    exact h1.trans h2
  have hBs_bnds := abs_le.mp hBs_abs
  rw [toR_sub, toR_add]
  exact ⟨by linarith, by linarith⟩

/-- **Box Angle-Addition Dot Product Soundness**: for any `(x, y)` in `[toR x0, toR x1] × [toR y0, toR y1]`
and any `u` with `toR ch ≤ cos u` (`0 ≤ ch`), `|sin u| ≤ toR sh`, the dot product
`x * cos (tm + u) + y * sin (tm + u)` lies inside `dotIntervalInt`. -/
theorem dotIntervalInt_sound {x0 x1 y0 y1 clo chi slo shi ch sh : Int} {x y tm u : ℝ}
    (hx0 : toR x0 ≤ x) (hx1 : x ≤ toR x1) (hy0 : toR y0 ≤ y) (hy1 : y ≤ toR y1)
    (hclo : toR clo ≤ Real.cos tm) (hchi : Real.cos tm ≤ toR chi)
    (hslo : toR slo ≤ Real.sin tm) (hshi : Real.sin tm ≤ toR shi)
    (hch_nn : 0 ≤ ch) (hch : toR ch ≤ Real.cos u) (hsh : |Real.sin u| ≤ toR sh) :
    let (lo, hi) := dotIntervalInt x0 x1 y0 y1 clo chi slo shi ch sh
    toR lo ≤ x * Real.cos (tm + u) + y * Real.sin (tm + u) ∧
    x * Real.cos (tm + u) + y * Real.sin (tm + u) ≤ toR hi := by
  have h00 := cornerDotLoHi_sound (qx := x0) (qy := y0) hclo hchi hslo hshi hch_nn hch hsh
  have h01 := cornerDotLoHi_sound (qx := x0) (qy := y1) hclo hchi hslo hshi hch_nn hch hsh
  have h10 := cornerDotLoHi_sound (qx := x1) (qy := y0) hclo hchi hslo hshi hch_nn hch hsh
  have h11 := cornerDotLoHi_sound (qx := x1) (qy := y1) hclo hchi hslo hshi hch_nn hch hsh
  set c := Real.cos (tm + u)
  set s := Real.sin (tm + u)
  -- Affine function on a rectangle achieves its min and max at one of the 4 corners!
  have hxc : min (toR x0 * c) (toR x1 * c) ≤ x * c ∧ x * c ≤ max (toR x0 * c) (toR x1 * c) := by
    rcases le_total 0 c with hc | hc
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx0 hc),
        (mul_le_mul_of_nonneg_right hx1 hc).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx1 hc),
        (mul_le_mul_of_nonpos_right hx0 hc).trans (le_max_left _ _)⟩
  have hys : min (toR y0 * s) (toR y1 * s) ≤ y * s ∧ y * s ≤ max (toR y0 * s) (toR y1 * s) := by
    rcases le_total 0 s with hs | hs
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hy0 hs),
        (mul_le_mul_of_nonneg_right hy1 hs).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hy1 hs),
        (mul_le_mul_of_nonpos_right hy0 hs).trans (le_max_left _ _)⟩
  unfold dotIntervalInt
  dsimp only
  rw [toR_min, toR_min, toR_min, toR_max, toR_max, toR_max]
  constructor
  · rcases min_choice (toR x0 * c) (toR x1 * c) with hx_eq | hx_eq <;>
    rcases min_choice (toR y0 * s) (toR y1 * s) with hy_eq | hy_eq
    · have : toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).1 ≤ toR x0 * c + toR y0 * s := h00.1
      have : min (min (toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).1)
          (toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).1))
          (min (toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).1)
          (toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).1)) ≤
          toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).1 := (min_le_left _ _).trans (min_le_left _ _)
      linarith
    · have : toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).1 ≤ toR x0 * c + toR y1 * s := h01.1
      have : min (min (toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).1)
          (toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).1))
          (min (toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).1)
          (toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).1)) ≤
          toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).1 := (min_le_left _ _).trans (min_le_right _ _)
      linarith
    · have : toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).1 ≤ toR x1 * c + toR y0 * s := h10.1
      have : min (min (toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).1)
          (toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).1))
          (min (toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).1)
          (toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).1)) ≤
          toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).1 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    · have : toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).1 ≤ toR x1 * c + toR y1 * s := h11.1
      have : min (min (toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).1)
          (toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).1))
          (min (toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).1)
          (toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).1)) ≤
          toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).1 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
  · rcases max_choice (toR x0 * c) (toR x1 * c) with hx_eq | hx_eq <;>
    rcases max_choice (toR y0 * s) (toR y1 * s) with hy_eq | hy_eq
    · have : toR x0 * c + toR y0 * s ≤ toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).2 := h00.2
      have : toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).2 ≤
          max (max (toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).2)
          (toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).2))
          (max (toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).2)
          (toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).2)) := (le_max_left _ _).trans (le_max_left _ _)
      linarith
    · have : toR x0 * c + toR y1 * s ≤ toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).2 := h01.2
      have : toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).2 ≤
          max (max (toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).2)
          (toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).2))
          (max (toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).2)
          (toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).2)) := (le_max_right _ _).trans (le_max_left _ _)
      linarith
    · have : toR x1 * c + toR y0 * s ≤ toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).2 := h10.2
      have : toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).2 ≤
          max (max (toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).2)
          (toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).2))
          (max (toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).2)
          (toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).2)) := (le_max_left _ _).trans (le_max_right _ _)
      linarith
    · have : toR x1 * c + toR y1 * s ≤ toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).2 := h11.2
      have : toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).2 ≤
          max (max (toR (cornerDotLoHi x0 y0 clo chi slo shi ch sh).2)
          (toR (cornerDotLoHi x0 y1 clo chi slo shi ch sh).2))
          (max (toR (cornerDotLoHi x1 y0 clo chi slo shi ch sh).2)
          (toR (cornerDotLoHi x1 y1 clo chi slo shi ch sh).2)) := (le_max_right _ _).trans (le_max_right _ _)
      linarith

end BHHBounds.Cert
