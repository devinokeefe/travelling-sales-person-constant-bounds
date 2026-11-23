import BHHBounds.Cert.Kernel
import BHHBounds.Cert.Data
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Soundness of Fixed-Point Arithmetic, Exponential, Cubic Integral, and Angle Table

Proves real-analytic soundness of all arithmetic primitives in `BHHBounds.Cert.Kernel`:
1. `natSqrt_spec`: `(natSqrt n)² ≤ n < (natSqrt n + 1)²`.
2. `mulLo_le`, `le_mulHi`, `le_divHi`, `sqrtSqLo_le`, `le_sqrtSqHi`, `fdiv_le`, `le_cdiv`.
3. `piLo_le_pi`, `pi_le_piHi`, `eQtrLo_le_exp`, `exp_le_eQtrHi`.
4. `expNegLo_le` and `le_expNegHi`: exact bounds on `Real.exp (-(x / S))` for all `x ≥ 0`.
5. `intDPosNum_eq`: exact evaluation of `∫ d in a..b, d * max 0 (c - d)`.
6. `angleTable40_sound`: certified bounds on `cos`, `sin` at all 40 sector midpoints and half-width `π / 40`.
-/

open Real Set MeasureTheory

namespace BHHBounds.Cert

/-- Real value corresponding to fixed-point integer `x : Int` at scale `S = 10^6`. -/
@[inline] noncomputable def toR (x : Int) : ℝ := (x : ℝ) / (S : ℝ)

lemma S_pos : (0 : ℝ) < (S : ℝ) := by norm_num [S]
lemma S_ne_zero : (S : ℝ) ≠ 0 := ne_of_gt S_pos

/-! ## Soundness of Pure `natSqrt` -/

lemma natSqrtBin_spec (n lo hi : Nat) (hlo : lo * lo ≤ n) (hhi : n < hi * hi) (hlt : lo < hi) :
    let r := natSqrtBin n lo hi
    r * r ≤ n ∧ n < (r + 1) * (r + 1) := by
  unfold natSqrtBin
  split_ifs with h1
  · have heq : hi = lo + 1 := by omega
    subst heq; exact ⟨hlo, hhi⟩
  · dsimp only
    split_ifs with h2
    · have hmid_lt : (lo + hi) / 2 < hi := by omega
      exact natSqrtBin_spec n ((lo + hi) / 2) hi h2 hhi hmid_lt
    · have hmid_gt : lo < (lo + hi) / 2 := by omega
      exact natSqrtBin_spec n lo ((lo + hi) / 2) hlo (Nat.lt_of_not_ge h2) hmid_gt
termination_by hi - lo
decreasing_by all_goals omega

lemma natSqrtUpper_spec (n fuel hi : Nat) :
    n < (natSqrtUpper n fuel hi) * (natSqrtUpper n fuel hi) := by
  induction fuel generalizing hi with
  | zero =>
    unfold natSqrtUpper
    nlinarith
  | succ f ih =>
    unfold natSqrtUpper
    split_ifs with h
    · exact h
    · exact ih (hi * 2)

lemma natSqrt_spec (n : Nat) :
    natSqrt n * natSqrt n ≤ n ∧ n < (natSqrt n + 1) * (natSqrt n + 1) := by
  unfold natSqrt
  split_ifs with h
  · have hn : n = 0 := by simpa using h
    subst hn; simp
  · have hhi := natSqrtUpper_spec n 64 1
    have hpos : 0 < natSqrtUpper n 64 1 := by
      by_contra h0
      have hz : natSqrtUpper n 64 1 = 0 := by omega
      rw [hz] at hhi; simp at hhi
    exact natSqrtBin_spec n 0 (natSqrtUpper n 64 1) (Nat.zero_le n) hhi hpos

/-! ## Rounding Lemmas -/

lemma int_ediv_le_real_div {a b : Int} (hb : 0 < b) :
    ((a / b : Int) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  have h1 : (a / b) * b ≤ a := by
    have hmod := Int.emod_nonneg a (ne_of_gt hb)
    have hdiv := Int.mul_ediv_add_emod a b
    have hmul : b * (a / b) ≤ a := by omega
    linarith [mul_comm b (a / b)]
  exact_mod_cast h1

lemma real_div_le_int_cdiv {a b : Int} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (((a + b - 1) / b : Int) : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  have h1 : a ≤ ((a + b - 1) / b) * b := by
    have hdiv := Int.mul_ediv_add_emod (a + b - 1) b
    have hlt := Int.emod_lt_of_pos (a + b - 1) hb
    have hmul : a ≤ b * ((a + b - 1) / b) := by omega
    linarith [mul_comm b ((a + b - 1) / b)]
  exact_mod_cast h1

lemma fdiv_le_real_div {a b : Int} (hb : 0 < b) :
    ((fdiv a b : Int) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  unfold fdiv
  have h1 : Int.fdiv a b * b ≤ a := by
    have hmod := Int.fmod_nonneg_of_pos a hb
    have hdiv := Int.mul_fdiv_add_fmod a b
    linarith [mul_comm b (Int.fdiv a b)]
  exact_mod_cast h1

lemma real_div_le_cdiv {a b : Int} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((cdiv a b : Int) : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  unfold cdiv
  have h1 : a ≤ Int.fdiv (a + b - 1) b * b := by
    have hlt := Int.fmod_lt_of_pos (a + b - 1) hb
    have hdiv := Int.mul_fdiv_add_fmod (a + b - 1) b
    linarith [mul_comm b (Int.fdiv (a + b - 1) b)]
  exact_mod_cast h1

lemma mulLo_le {a b : Int} :
    toR (mulLo a b) ≤ toR a * toR b := by
  unfold toR mulLo
  have h1 : ((a * b / S : Int) : ℝ) ≤ ((a * b : Int) : ℝ) / (S : ℝ) :=
    int_ediv_le_real_div (by decide : (0 : Int) < S)
  push_cast at h1
  have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
  simpa [div_div, mul_div_mul_comm] using h2

lemma mulLo_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mulLo a b :=
  Int.ediv_nonneg (mul_nonneg ha hb) (by decide)

lemma le_mulHi {a b : Int} :
    toR a * toR b ≤ toR (mulHi a b) := by
  unfold toR mulHi
  have h1 : ((a * b : Int) : ℝ) / (S : ℝ) ≤ (((a * b + S - 1) / S : Int) : ℝ) :=
    real_div_le_int_cdiv (by decide : (0 : Int) < S)
  push_cast at h1
  have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
  simpa [div_div, mul_div_mul_comm] using h2

lemma mulHi_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mulHi a b :=
  Int.ediv_nonneg (by have := mul_nonneg ha hb; unfold S; omega) (by decide)

lemma le_divHi {a b : Int} (hb : 0 < b) :
    toR a / toR b ≤ toR (divHi a b) := by
  unfold toR divHi
  have h1 : ((a * S : Int) : ℝ) / (b : ℝ) ≤ (((a * S + b - 1) / b : Int) : ℝ) :=
    real_div_le_int_cdiv hb
  push_cast at h1
  have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hEq : (a : ℝ) / (S : ℝ) / ((b : ℝ) / (S : ℝ)) = (a : ℝ) * (S : ℝ) / (b : ℝ) / (S : ℝ) := by
    field_simp [S_ne_zero, hbR]
  rwa [hEq]

lemma sqrtSqLo_nonneg (n : Int) : 0 ≤ sqrtSqLo n := by
  unfold sqrtSqLo
  split_ifs
  · exact le_rfl
  · exact Int.natCast_nonneg _

lemma sqrtSqHi_nonneg (n : Int) : 0 ≤ sqrtSqHi n := by
  unfold sqrtSqHi
  split_ifs
  · exact le_rfl
  · dsimp only
    split_ifs <;> exact Int.natCast_nonneg _

lemma sqrtSqLo_le (n : Int) :
    toR (sqrtSqLo n) ≤ Real.sqrt ((n : ℝ) / (S : ℝ) ^ 2) := by
  unfold toR sqrtSqLo
  split_ifs with hn
  · simp [Real.sqrt_nonneg]
  · push Not at hn
    have hnn : 0 ≤ n := le_of_lt hn
    have hto : (n.toNat : Int) = n := Int.toNat_of_nonneg hnn
    have hsq := (natSqrt_spec n.toNat).1
    have hsqR : ((natSqrt n.toNat : ℝ)) ^ 2 ≤ (n : ℝ) := by
      have : ((natSqrt n.toNat * natSqrt n.toNat : Nat) : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast hsq
      have hnR : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hto
      rw [Nat.cast_mul, hnR, ← sq] at this; exact this
    have hnnL : (0 : ℝ) ≤ (Int.ofNat (natSqrt n.toNat) : ℝ) / (S : ℝ) :=
      div_nonneg (by change (0 : ℝ) ≤ ((natSqrt n.toNat : ℕ) : ℝ); exact Nat.cast_nonneg _) (le_of_lt S_pos)
    have hnnR : (0 : ℝ) ≤ (n : ℝ) / (S : ℝ) ^ 2 :=
      div_nonneg (by exact_mod_cast hnn) (sq_nonneg _)
    rw [Real.le_sqrt hnnL hnnR, div_pow]
    exact div_le_div_of_nonneg_right (by simpa using hsqR) (sq_nonneg _)

lemma le_sqrtSqHi (n : Int) :
    Real.sqrt ((n : ℝ) / (S : ℝ) ^ 2) ≤ toR (sqrtSqHi n) := by
  unfold toR sqrtSqHi
  split_ifs with hn
  · have hnp : (n : ℝ) / (S : ℝ) ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hn) (sq_nonneg _)
    rw [Real.sqrt_eq_zero_of_nonpos hnp]; simp
  · push Not at hn
    dsimp only
    have hnn : 0 ≤ n := le_of_lt hn
    have hto : (n.toNat : Int) = n := Int.toNat_of_nonneg hnn
    split_ifs with heq
    · have hmul : natSqrt n.toNat * natSqrt n.toNat = n.toNat := by simpa using heq
      have hsqR : (n : ℝ) ≤ ((natSqrt n.toNat : ℝ)) ^ 2 := by
        have : (n.toNat : ℝ) = ((natSqrt n.toNat * natSqrt n.toNat : Nat) : ℝ) := by exact_mod_cast hmul.symm
        have hnR : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hto
        rw [Nat.cast_mul, ← sq] at this; linarith
      have hnnR : (0 : ℝ) ≤ (Int.ofNat (natSqrt n.toNat) : ℝ) / (S : ℝ) :=
        div_nonneg (by change (0 : ℝ) ≤ ((natSqrt n.toNat : ℕ) : ℝ); exact Nat.cast_nonneg _) (le_of_lt S_pos)
      rw [Real.sqrt_le_left hnnR, div_pow]
      exact div_le_div_of_nonneg_right (by simpa using hsqR) (sq_nonneg _)
    · have hlt := (natSqrt_spec n.toNat).2
      have hsqR : (n : ℝ) ≤ ((natSqrt n.toNat + 1 : Nat) : ℝ) ^ 2 := by
        have : (n.toNat : ℝ) < (((natSqrt n.toNat + 1) * (natSqrt n.toNat + 1) : Nat) : ℝ) := by
          exact_mod_cast hlt
        have hnR : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hto
        rw [Nat.cast_mul, ← sq] at this; linarith
      have hnnR : (0 : ℝ) ≤ (Int.ofNat (natSqrt n.toNat + 1) : ℝ) / (S : ℝ) :=
        div_nonneg (by change (0 : ℝ) ≤ (((natSqrt n.toNat + 1 : ℕ) : ℝ)); exact Nat.cast_nonneg _) (le_of_lt S_pos)
      rw [Real.sqrt_le_left hnnR, div_pow]
      exact div_le_div_of_nonneg_right (by simpa using hsqR) (sq_nonneg _)

/-! ## Certified Constants: `π` and `exp(-1/4)` -/

lemma piLo_le_pi : toR piLo ≤ Real.pi := by
  unfold toR piLo S
  have := Real.pi_gt_d6
  linarith

lemma pi_le_piHi : Real.pi ≤ toR piHi := by
  unfold toR piHi S
  have := Real.pi_lt_d6
  linarith

lemma eQtrLo_le_exp : toR eQtrLo ≤ Real.exp (-(1 / 4 : ℝ)) := by
  have hb := Real.exp_bound (x := -(1 / 4 : ℝ)) (n := 7) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num [toR, eQtrLo, S, abs_le] at hb ⊢
  linarith [hb.1]

lemma exp_le_eQtrHi : Real.exp (-(1 / 4 : ℝ)) ≤ toR eQtrHi := by
  have hb := Real.exp_bound (x := -(1 / 4 : ℝ)) (n := 7) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num [toR, eQtrHi, S, abs_le] at hb ⊢
  linarith [hb.2]

/-! ## Soundness of `expNegLo` and `expNegHi` -/

lemma powLo_nonneg (q : Nat) {b : Int} (hb : 0 ≤ b) : 0 ≤ powLo q b := by
  induction q with
  | zero => simp [powLo, S]
  | succ k ih => exact mulLo_nonneg hb ih

lemma powLo_le (q : Nat) {b : Int} {r : ℝ} (hb : 0 ≤ b) (hbr : toR b ≤ r) :
    toR (powLo q b) ≤ r ^ q := by
  induction q with
  | zero => simp [powLo, toR, S]
  | succ k ih =>
    unfold powLo
    have hnn_b : 0 ≤ toR b := div_nonneg (by exact_mod_cast hb) (le_of_lt S_pos)
    have hr0 : 0 ≤ r := hnn_b.trans hbr
    have hnn_p : 0 ≤ powLo k b := powLo_nonneg k hb
    calc toR (mulLo b (powLo k b))
        ≤ toR b * toR (powLo k b) := mulLo_le
      _ ≤ r * r ^ k := mul_le_mul hbr ih (div_nonneg (by exact_mod_cast hnn_p) (le_of_lt S_pos)) hr0
      _ = r ^ (k + 1) := by rw [pow_succ']

lemma powHi_nonneg (q : Nat) {b : Int} (hb : 0 ≤ b) : 0 ≤ powHi q b := by
  induction q with
  | zero => simp [powHi, S]
  | succ k ih => exact mulHi_nonneg hb ih

lemma le_powHi (q : Nat) {b : Int} {r : ℝ} (hr0 : 0 ≤ r) (hb : 0 ≤ b) (hrb : r ≤ toR b) :
    r ^ q ≤ toR (powHi q b) := by
  induction q with
  | zero => simp [powHi, toR, S]
  | succ k ih =>
    unfold powHi
    have hnn_b : 0 ≤ toR b := div_nonneg (by exact_mod_cast hb) (le_of_lt S_pos)
    calc r ^ (k + 1) = r * r ^ k := by rw [pow_succ']
      _ ≤ toR b * toR (powHi k b) := mul_le_mul hrb ih (pow_nonneg hr0 k) hnn_b
      _ ≤ toR (mulHi b (powHi k b)) := le_mulHi

/-- Exact alternating-series lower & upper bounds on `exp(-t)` for `t ∈ [0, 1/4]` using `n = 8`. -/
lemma exp_neg_taylor_lo {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120 ≤ Real.exp (-t) := by
  have habs : |-t| ≤ 1 := by rw [abs_neg, abs_of_nonneg ht0]; linarith
  have hb := Real.exp_bound (x := -t) (n := 7) habs (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  rw [abs_le] at hb
  rw [abs_neg, abs_of_nonneg ht0] at hb
  have h1 := hb.1
  -- `t^6 / 720 - t^7 * (8 / (5040 * 7)) ≥ 0` since `t ≤ 1/4`!
  have hrem : t ^ 7 * ((7 + 1 : ℝ) / ((5040 : ℝ) * 7)) ≤ t ^ 6 / 720 := by
    have ht6 : 0 ≤ t ^ 6 := by positivity
    rw [pow_succ]
    nlinarith
  norm_num at h1 ⊢
  linarith

lemma exp_neg_taylor_hi {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120 + t ^ 6 / 720 := by
  have habs : |-t| ≤ 1 := by rw [abs_neg, abs_of_nonneg ht0]; linarith
  have hb := Real.exp_bound (x := -t) (n := 8) habs (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  rw [abs_le] at hb
  rw [abs_neg, abs_of_nonneg ht0] at hb
  have h2 := hb.2
  have hrem : t ^ 8 * ((8 + 1 : ℝ) / ((40320 : ℝ) * 8)) ≤ t ^ 7 / 5040 := by
    have ht7 : 0 ≤ t ^ 7 := by positivity
    rw [pow_succ]
    nlinarith
  norm_num at h2 ⊢
  linarith

lemma expNegLo_le {x : Int} (hx : 0 ≤ x) :
    toR (expNegLo x) ≤ Real.exp (-toR x) := by
  unfold expNegLo
  split_ifs with hx0
  · have hxe : x = 0 := le_antisymm hx0 hx
    subst hxe; simp [toR, S]
  · push Not at hx0
    dsimp only
    split_ifs with hq64 hpoly
    · simp only [toR, Int.cast_zero, zero_div]; exact Real.exp_nonneg _
    · simp only [toR, Int.cast_zero, zero_div]; exact Real.exp_nonneg _
    · push Not at hq64 hpoly
      set q : Nat := (x / 250000).toNat
      set r : Int := x % 250000
      have hr0 : 0 ≤ r := Int.emod_nonneg x (by decide)
      have hr_lt : r < 250000 := Int.emod_lt_of_pos x (by decide)
      have hq_eq : (q : Int) = x / 250000 := Int.toNat_of_nonneg (Int.ediv_nonneg hx (by decide))
      have hx_split : toR x = (q : ℝ) * (1 / 4 : ℝ) + toR r := by
        unfold toR
        have hdiv := Int.mul_ediv_add_emod x 250000
        have hdivR : (250000 : ℝ) * (q : ℝ) + (r : ℝ) = (x : ℝ) := by
          have : (250000 : Int) * (q : Int) + r = x := by rw [hq_eq]; exact hdiv
          exact_mod_cast this
        unfold S; linarith
      have hexp_split : Real.exp (-toR x) = Real.exp (-toR r) * (Real.exp (-(1 / 4 : ℝ))) ^ q := by
        rw [hx_split, neg_add, Real.exp_add, mul_comm, ← Real.exp_nat_mul]
        congr 2; ring
      rw [hexp_split]
      have ht0 : 0 ≤ toR r := div_nonneg (by exact_mod_cast hr0) (le_of_lt S_pos)
      have ht1 : toR r ≤ 1 / 4 := by
        unfold toR S
        have : (r : ℝ) ≤ 250000 := by exact_mod_cast le_of_lt hr_lt
        linarith
      have hr2Lo : toR (mulLo r r) ≤ toR r * toR r := mulLo_le
      have hr2Hi : toR r * toR r ≤ toR (mulHi r r) := le_mulHi
      have hr2Lo_nn := mulLo_nonneg hr0 hr0
      have hr2Hi_nn := mulHi_nonneg hr0 hr0
      have hr3Hi : toR r ^ 3 ≤ toR (mulHi (mulHi r r) r) := by
        calc toR r ^ 3 = (toR r * toR r) * toR r := by ring
          _ ≤ toR (mulHi r r) * toR r := mul_le_mul_of_nonneg_right hr2Hi ht0
          _ ≤ toR (mulHi (mulHi r r) r) := le_mulHi
      have hr4Lo : toR (mulLo (mulLo r r) (mulLo r r)) ≤ toR r ^ 4 := by
        calc toR (mulLo (mulLo r r) (mulLo r r))
            ≤ toR (mulLo r r) * toR (mulLo r r) := mulLo_le
          _ ≤ (toR r * toR r) * (toR r * toR r) :=
              mul_le_mul hr2Lo hr2Lo (div_nonneg (by exact_mod_cast hr2Lo_nn) (le_of_lt S_pos)) (by positivity)
          _ = toR r ^ 4 := by ring
      have hr4Hi : toR r ^ 4 ≤ toR (mulHi (mulHi r r) (mulHi r r)) := by
        calc toR r ^ 4 = (toR r * toR r) * (toR r * toR r) := by ring
          _ ≤ toR (mulHi r r) * toR (mulHi r r) :=
              mul_le_mul hr2Hi hr2Hi (by positivity) (div_nonneg (by exact_mod_cast hr2Hi_nn) (le_of_lt S_pos))
          _ ≤ toR (mulHi (mulHi r r) (mulHi r r)) := le_mulHi
      have hr5Hi : toR r ^ 5 ≤ toR (mulHi (mulHi (mulHi r r) (mulHi r r)) r) := by
        calc toR r ^ 5 = toR r ^ 4 * toR r := by ring
          _ ≤ toR (mulHi (mulHi r r) (mulHi r r)) * toR r := mul_le_mul_of_nonneg_right hr4Hi ht0
          _ ≤ toR (mulHi (mulHi (mulHi r r) (mulHi r r)) r) := le_mulHi
      have ht2 : toR (mulLo r r / 2) ≤ toR r ^ 2 / 2 := by
        have h1 := int_ediv_le_real_div (a := mulLo r r) (by decide : (0 : Int) < 2)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        unfold toR at hr2Lo ⊢
        push_cast at h2
        have : (mulLo r r : ℝ) / (2 : ℝ) / (S : ℝ) = ((mulLo r r : ℝ) / (S : ℝ)) / 2 := by ring
        rw [this] at h2; linarith [show ((r : ℝ) / (S : ℝ)) * ((r : ℝ) / (S : ℝ)) = ((r : ℝ) / (S : ℝ)) ^ 2 by ring]
      have ht3 : toR r ^ 3 / 6 ≤ toR ((mulHi (mulHi r r) r + 5) / 6) := by
        have h1 := real_div_le_int_cdiv (a := mulHi (mulHi r r) r) (by decide : (0 : Int) < 6)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        rw [show mulHi (mulHi r r) r + 6 - 1 = mulHi (mulHi r r) r + 5 by omega] at h2
        unfold toR at hr3Hi ⊢
        push_cast at h2
        have : (mulHi (mulHi r r) r : ℝ) / (6 : ℝ) / (S : ℝ) = ((mulHi (mulHi r r) r : ℝ) / (S : ℝ)) / 6 := by ring
        rw [this] at h2; linarith
      have ht4 : toR (mulLo (mulLo r r) (mulLo r r) / 24) ≤ toR r ^ 4 / 24 := by
        have h1 := int_ediv_le_real_div (a := mulLo (mulLo r r) (mulLo r r)) (by decide : (0 : Int) < 24)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        unfold toR at hr4Lo ⊢
        push_cast at h2
        have : (mulLo (mulLo r r) (mulLo r r) : ℝ) / (24 : ℝ) / (S : ℝ) =
            ((mulLo (mulLo r r) (mulLo r r) : ℝ) / (S : ℝ)) / 24 := by ring
        rw [this] at h2; linarith
      have ht5 : toR r ^ 5 / 120 ≤ toR ((mulHi (mulHi (mulHi r r) (mulHi r r)) r + 119) / 120) := by
        have h1 := real_div_le_int_cdiv (a := mulHi (mulHi (mulHi r r) (mulHi r r)) r) (by decide : (0 : Int) < 120)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        rw [show mulHi (mulHi (mulHi r r) (mulHi r r)) r + 120 - 1 =
            mulHi (mulHi (mulHi r r) (mulHi r r)) r + 119 by omega] at h2
        unfold toR at hr5Hi ⊢
        push_cast at h2
        have : (mulHi (mulHi (mulHi r r) (mulHi r r)) r : ℝ) / (120 : ℝ) / (S : ℝ) =
            ((mulHi (mulHi (mulHi r r) (mulHi r r)) r : ℝ) / (S : ℝ)) / 120 := by ring
        rw [this] at h2; linarith
      set polyInt : Int := S - r + mulLo r r / 2 - (mulHi (mulHi r r) r + 5) / 6
        + mulLo (mulLo r r) (mulLo r r) / 24 - (mulHi (mulHi (mulHi r r) (mulHi r r)) r + 119) / 120
      have hpoly_le : toR polyInt ≤ Real.exp (-toR r) := by
        have hsum : toR polyInt = 1 - toR r + toR (mulLo r r / 2)
            - toR ((mulHi (mulHi r r) r + 5) / 6)
            + toR (mulLo (mulLo r r) (mulLo r r) / 24)
            - toR ((mulHi (mulHi (mulHi r r) (mulHi r r)) r + 119) / 120) := by
          unfold polyInt toR; push_cast; simp only [add_div, sub_div, div_self S_ne_zero]
        rw [hsum]
        linarith [exp_neg_taylor_lo ht0 ht1]
      have hpow_le : toR (powLo q eQtrLo) ≤ (Real.exp (-(1 / 4 : ℝ))) ^ q :=
        powLo_le q (by decide) eQtrLo_le_exp
      have hpow_nn : 0 ≤ powLo q eQtrLo := powLo_nonneg q (by decide)
      calc toR (mulLo polyInt (powLo q eQtrLo))
          ≤ toR polyInt * toR (powLo q eQtrLo) := mulLo_le
        _ ≤ Real.exp (-toR r) * (Real.exp (-(1 / 4 : ℝ))) ^ q :=
            mul_le_mul hpoly_le hpow_le (div_nonneg (by exact_mod_cast hpow_nn) (le_of_lt S_pos))
              (Real.exp_nonneg _)

lemma le_expNegHi {x : Int} (hx : 0 ≤ x) :
    Real.exp (-toR x) ≤ toR (expNegHi x) := by
  unfold expNegHi
  split_ifs with hx0
  · have hxe : x = 0 := le_antisymm hx0 hx
    subst hxe; simp [toR, S]
  · push Not at hx0
    dsimp only
    split_ifs with hq64
    · have hq_ge : 65 ≤ x / 250000 := by omega
      have hx_ge : (16 : ℝ) ≤ toR x := by
        unfold toR S
        have : (65 : Int) * 250000 ≤ x := by omega
        have hR : (16250000 : ℝ) ≤ (x : ℝ) := by exact_mod_cast this
        linarith
      have h1 : Real.exp (-toR x) ≤ Real.exp (-16) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-16) = (Real.exp (-1)) ^ 16 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : Real.exp (-1) ≤ (37 / 100 : ℝ) := by
        have := Real.exp_one_gt_d9
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith
      have h4 : (Real.exp (-1)) ^ 16 ≤ (37 / 100 : ℝ) ^ 16 :=
        pow_le_pow_left₀ (Real.exp_nonneg _) h3 16
      have h5 : (37 / 100 : ℝ) ^ 16 ≤ toR 1 := by unfold toR S; norm_num
      linarith
    · push Not at hq64
      set q : Nat := (x / 250000).toNat
      set r : Int := x % 250000
      have hr0 : 0 ≤ r := Int.emod_nonneg x (by decide)
      have hr_lt : r < 250000 := Int.emod_lt_of_pos x (by decide)
      have hq_eq : (q : Int) = x / 250000 := Int.toNat_of_nonneg (Int.ediv_nonneg hx (by decide))
      have hx_split : toR x = (q : ℝ) * (1 / 4 : ℝ) + toR r := by
        unfold toR
        have hdiv := Int.mul_ediv_add_emod x 250000
        have hdivR : (250000 : ℝ) * (q : ℝ) + (r : ℝ) = (x : ℝ) := by
          have : (250000 : Int) * (q : Int) + r = x := by rw [hq_eq]; exact hdiv
          exact_mod_cast this
        unfold S; linarith
      have hexp_split : Real.exp (-toR x) = Real.exp (-toR r) * (Real.exp (-(1 / 4 : ℝ))) ^ q := by
        rw [hx_split, neg_add, Real.exp_add, mul_comm, ← Real.exp_nat_mul]
        congr 2; ring
      rw [hexp_split]
      have ht0 : 0 ≤ toR r := div_nonneg (by exact_mod_cast hr0) (le_of_lt S_pos)
      have ht1 : toR r ≤ 1 / 4 := by
        unfold toR S
        have : (r : ℝ) ≤ 250000 := by exact_mod_cast le_of_lt hr_lt
        linarith
      have hr2Lo : toR (mulLo r r) ≤ toR r * toR r := mulLo_le
      have hr2Hi : toR r * toR r ≤ toR (mulHi r r) := le_mulHi
      have hr2Lo_nn := mulLo_nonneg hr0 hr0
      have hr2Hi_nn := mulHi_nonneg hr0 hr0
      have hr3Lo : toR (mulLo (mulLo r r) r) ≤ toR r ^ 3 := by
        calc toR (mulLo (mulLo r r) r)
            ≤ toR (mulLo r r) * toR r := mulLo_le
          _ ≤ (toR r * toR r) * toR r := mul_le_mul_of_nonneg_right hr2Lo ht0
          _ = toR r ^ 3 := by ring
      have hr4Lo : toR (mulLo (mulLo r r) (mulLo r r)) ≤ toR r ^ 4 := by
        calc toR (mulLo (mulLo r r) (mulLo r r))
            ≤ toR (mulLo r r) * toR (mulLo r r) := mulLo_le
          _ ≤ (toR r * toR r) * (toR r * toR r) :=
              mul_le_mul hr2Lo hr2Lo (div_nonneg (by exact_mod_cast hr2Lo_nn) (le_of_lt S_pos)) (by positivity)
          _ = toR r ^ 4 := by ring
      have hr4Hi : toR r ^ 4 ≤ toR (mulHi (mulHi r r) (mulHi r r)) := by
        calc toR r ^ 4 = (toR r * toR r) * (toR r * toR r) := by ring
          _ ≤ toR (mulHi r r) * toR (mulHi r r) :=
              mul_le_mul hr2Hi hr2Hi (by positivity) (div_nonneg (by exact_mod_cast hr2Hi_nn) (le_of_lt S_pos))
          _ ≤ toR (mulHi (mulHi r r) (mulHi r r)) := le_mulHi
      have hr4Hi_nn := mulHi_nonneg hr2Hi_nn hr2Hi_nn
      have hr5Lo : toR (mulLo (mulLo (mulLo r r) (mulLo r r)) r) ≤ toR r ^ 5 := by
        calc toR (mulLo (mulLo (mulLo r r) (mulLo r r)) r)
            ≤ toR (mulLo (mulLo r r) (mulLo r r)) * toR r := mulLo_le
          _ ≤ toR r ^ 4 * toR r := mul_le_mul_of_nonneg_right hr4Lo ht0
          _ = toR r ^ 5 := by ring
      have hr6Hi : toR r ^ 6 ≤ toR (mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r)) := by
        calc toR r ^ 6 = toR r ^ 4 * (toR r * toR r) := by ring
          _ ≤ toR (mulHi (mulHi r r) (mulHi r r)) * toR (mulHi r r) :=
              mul_le_mul hr4Hi hr2Hi (by positivity) (div_nonneg (by exact_mod_cast hr4Hi_nn) (le_of_lt S_pos))
          _ ≤ toR (mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r)) := le_mulHi
      have ht2 : toR r ^ 2 / 2 ≤ toR ((mulHi r r + 1) / 2) := by
        have h1 := real_div_le_int_cdiv (a := mulHi r r) (by decide : (0 : Int) < 2)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        rw [show mulHi r r + 2 - 1 = mulHi r r + 1 by omega] at h2
        unfold toR at hr2Hi ⊢
        push_cast at h2
        have : (mulHi r r : ℝ) / (2 : ℝ) / (S : ℝ) = ((mulHi r r : ℝ) / (S : ℝ)) / 2 := by ring
        rw [this] at h2; linarith [show ((r : ℝ) / (S : ℝ)) * ((r : ℝ) / (S : ℝ)) = ((r : ℝ) / (S : ℝ)) ^ 2 by ring]
      have ht3 : toR (mulLo (mulLo r r) r / 6) ≤ toR r ^ 3 / 6 := by
        have h1 := int_ediv_le_real_div (a := mulLo (mulLo r r) r) (by decide : (0 : Int) < 6)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        unfold toR at hr3Lo ⊢
        push_cast at h2
        have : (mulLo (mulLo r r) r : ℝ) / (6 : ℝ) / (S : ℝ) = ((mulLo (mulLo r r) r : ℝ) / (S : ℝ)) / 6 := by ring
        rw [this] at h2; linarith
      have ht4 : toR r ^ 4 / 24 ≤ toR ((mulHi (mulHi r r) (mulHi r r) + 23) / 24) := by
        have h1 := real_div_le_int_cdiv (a := mulHi (mulHi r r) (mulHi r r)) (by decide : (0 : Int) < 24)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        rw [show mulHi (mulHi r r) (mulHi r r) + 24 - 1 = mulHi (mulHi r r) (mulHi r r) + 23 by omega] at h2
        unfold toR at hr4Hi ⊢
        push_cast at h2
        have : (mulHi (mulHi r r) (mulHi r r) : ℝ) / (24 : ℝ) / (S : ℝ) =
            ((mulHi (mulHi r r) (mulHi r r) : ℝ) / (S : ℝ)) / 24 := by ring
        rw [this] at h2; linarith
      have ht5 : toR (mulLo (mulLo (mulLo r r) (mulLo r r)) r / 120) ≤ toR r ^ 5 / 120 := by
        have h1 := int_ediv_le_real_div (a := mulLo (mulLo (mulLo r r) (mulLo r r)) r) (by decide : (0 : Int) < 120)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        unfold toR at hr5Lo ⊢
        push_cast at h2
        have : (mulLo (mulLo (mulLo r r) (mulLo r r)) r : ℝ) / (120 : ℝ) / (S : ℝ) =
            ((mulLo (mulLo (mulLo r r) (mulLo r r)) r : ℝ) / (S : ℝ)) / 120 := by ring
        rw [this] at h2; linarith
      have ht6 : toR r ^ 6 / 720 ≤ toR ((mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r) + 719) / 720) := by
        have h1 := real_div_le_int_cdiv (a := mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r)) (by decide : (0 : Int) < 720)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt S_pos)
        rw [show mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r) + 720 - 1 =
            mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r) + 719 by omega] at h2
        unfold toR at hr6Hi ⊢
        push_cast at h2
        have : (mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r) : ℝ) / (720 : ℝ) / (S : ℝ) =
            ((mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r) : ℝ) / (S : ℝ)) / 720 := by ring
        rw [this] at h2; linarith
      set polyRaw : Int := S - r + (mulHi r r + 1) / 2 - mulLo (mulLo r r) r / 6
        + (mulHi (mulHi r r) (mulHi r r) + 23) / 24
        - mulLo (mulLo (mulLo r r) (mulLo r r)) r / 120
        + (mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r) + 719) / 720
      set polyInt : Int := min S polyRaw
      have hexp_le_raw : Real.exp (-toR r) ≤ toR polyRaw := by
        have hsum : toR polyRaw = 1 - toR r + toR ((mulHi r r + 1) / 2)
            - toR (mulLo (mulLo r r) r / 6)
            + toR ((mulHi (mulHi r r) (mulHi r r) + 23) / 24)
            - toR (mulLo (mulLo (mulLo r r) (mulLo r r)) r / 120)
            + toR ((mulHi (mulHi (mulHi r r) (mulHi r r)) (mulHi r r) + 719) / 720) := by
          unfold polyRaw toR; push_cast; simp only [add_div, sub_div, div_self S_ne_zero]
        rw [hsum]
        linarith [exp_neg_taylor_hi ht0 ht1]
      have hexp_le_one : Real.exp (-toR r) ≤ toR S := by
        unfold toR at ht0 ⊢; rw [div_self S_ne_zero]; exact Real.exp_le_one_iff.mpr (by linarith)
      have hpoly_ge : Real.exp (-toR r) ≤ toR polyInt := by
        unfold polyInt toR
        rw [Int.cast_min, ← min_div_div_right (le_of_lt S_pos)]
        exact le_min hexp_le_one hexp_le_raw
      have hpoly_nn : 0 ≤ toR polyInt := (Real.exp_nonneg _).trans hpoly_ge
      have hpow_ge : (Real.exp (-(1 / 4 : ℝ))) ^ q ≤ toR (powHi q eQtrHi) :=
        le_powHi q (Real.exp_nonneg _) (by decide) exp_le_eQtrHi
      calc Real.exp (-toR r) * (Real.exp (-(1 / 4 : ℝ))) ^ q
          ≤ toR polyInt * toR (powHi q eQtrHi) :=
            mul_le_mul hpoly_ge hpow_ge (pow_nonneg (Real.exp_nonneg _) q) hpoly_nn
        _ ≤ toR (mulHi polyInt (powHi q eQtrHi)) := le_mulHi

/-! ## Exact Cubic Radial Integral Formula -/

/-- Exact evaluation of `∫ d in a..b, d * max 0 (c - d)` for `a ≤ b`. -/
lemma integral_d_pos_eq {a b c : ℝ} (hab : a ≤ b) :
    ∫ d in a..b, d * max 0 (c - d) =
      if c ≤ a then 0
      else
        let u := min b c
        (u - a) * (3 * c * (u + a) - 2 * (u ^ 2 + u * a + a ^ 2)) / 6 := by
  split_ifs with hca
  · have hz : ∫ d in a..b, d * max 0 (c - d) = ∫ _ in a..b, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun d hd => ?_
      rw [Set.uIcc_of_le hab] at hd
      rw [max_eq_left (by linarith [hd.1]), mul_zero]
    rw [hz]; simp
  · push Not at hca
    set u := min b c
    have hau : a ≤ u := le_min hab (le_of_lt hca)
    have hub : u ≤ b := min_le_left b c
    have huc : u ≤ c := min_le_right b c
    have hint : ∀ x y : ℝ, IntervalIntegrable (fun d : ℝ => d * max 0 (c - d)) volume x y :=
      fun x y => (by fun_prop : Continuous fun d : ℝ => d * max 0 (c - d)).intervalIntegrable x y
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint a u) (hint u b)]
    have hzero : ∫ d in u..b, d * max 0 (c - d) = 0 := by
      rcases le_total b c with hbc | hcb
      · have hu_eq : u = b := min_eq_left hbc
        rw [hu_eq, intervalIntegral.integral_same]
      · have hu_eq : u = c := min_eq_right hcb
        have hz : ∫ d in u..b, d * max 0 (c - d) = ∫ _ in u..b, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun d hd => ?_
          rw [Set.uIcc_of_le hub, hu_eq] at hd
          rw [max_eq_left (by linarith [hd.1]), mul_zero]
        rw [hz]; simp
    rw [hzero, add_zero]
    have hcongr : ∫ d in a..u, d * max 0 (c - d) = ∫ d in a..u, (c * d - d ^ 2) := by
      refine intervalIntegral.integral_congr fun d hd => ?_
      rw [Set.uIcc_of_le hau] at hd
      rw [max_eq_right (by linarith [hd.2, huc])]; ring
    rw [hcongr]
    let F : ℝ → ℝ := fun d => c * d ^ 2 / 2 - d ^ 3 / 3
    have hderiv : ∀ d ∈ Set.uIcc a u, HasDerivAt F (c * d - d ^ 2) d := fun d _ => by
      have h1 : HasDerivAt (fun x : ℝ => c * x ^ 2 / 2) (c * d) d := by
        have := ((hasDerivAt_pow 2 d).const_mul c).div_const 2
        refine this.congr_deriv ?_; ring
      have h2 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (d ^ 2) d := by
        have := (hasDerivAt_pow 3 d).div_const 3
        refine this.congr_deriv ?_; ring
      exact h1.sub h2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun d : ℝ => c * d - d ^ 2).intervalIntegrable a u)
    rw [hftc]
    dsimp only [F]
    ring

lemma intDPosNum_eq {a b c : Int} (hab : a ≤ b) :
    (intDPosNum a b c : ℝ) / (6 * (S : ℝ) ^ 3) =
      ∫ d in (toR a)..(toR b), d * max 0 (toR c - d) := by
  have habR : toR a ≤ toR b := div_le_div_of_nonneg_right (by exact_mod_cast hab) (le_of_lt S_pos)
  rw [integral_d_pos_eq habR]
  unfold intDPosNum
  by_cases h1 : c ≤ a
  · have h2 : toR c ≤ toR a := div_le_div_of_nonneg_right (by exact_mod_cast h1) (le_of_lt S_pos)
    rw [if_pos h1, if_pos h2]; simp
  · have h2 : ¬ toR c ≤ toR a := by
      intro hle; apply h1
      have : (c : ℝ) ≤ (a : ℝ) := (div_le_div_iff_of_pos_right S_pos).mp hle
      exact_mod_cast this
    rw [if_neg h1, if_neg h2]
    dsimp only
    unfold toR
    have hmin : min ((b : ℝ) / (S : ℝ)) ((c : ℝ) / (S : ℝ)) = ((min b c : Int) : ℝ) / (S : ℝ) := by
      rw [Int.cast_min, ← min_div_div_right (le_of_lt S_pos)]
    rw [hmin]
    push_cast
    field_simp [S_ne_zero]

/-! ## Elementary Degree-6/7 Taylor Bounds for `cos` and `sin` & `angleTable40` Soundness -/

/-- Elementary iterated-integral Taylor bounds for `cos x` and `sin x` on `x ≥ 0`:
starting from `cos t ≤ 1`, `-1 ≤ cos t`, integrating 7 times yields degree-6/7 bounds. -/
lemma cos_sin_taylor6 {x : ℝ} (hx : 0 ≤ x) :
    (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x ∧
     Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) ∧
    (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x ∧
     Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880) := by
  -- Helper: if `f 0 = 0` and `f' ≥ 0` on `[0, x]`, then `f x ≥ 0`!
  have nonneg_of_deriv : ∀ (f f' : ℝ → ℝ), f 0 = 0 →
      (∀ t, HasDerivAt f (f' t) t) → (∀ t ≥ 0, 0 ≤ f' t) → ∀ t ≥ 0, 0 ≤ f t := by
    intro f f' h0 hd hnn t ht
    have hmono : MonotoneOn f (Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun y _ => (hd y).continuousAt.continuousWithinAt)
        (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
        (fun y hy => by rw [(hd y).deriv]; exact hnn y (le_of_lt (by simpa [interior_Ici] using hy)))
    linarith [hmono (Set.self_mem_Ici) ht ht]
  have h1 : ∀ t ≥ 0, 0 ≤ t - Real.sin t :=
    nonneg_of_deriv (fun t => t - Real.sin t) (fun t => 1 - Real.cos t) (by simp)
      (fun t => (hasDerivAt_id t).sub (Real.hasDerivAt_sin t))
      (fun t _ => by linarith [Real.cos_le_one t])
  have h2 : ∀ t ≥ 0, 0 ≤ Real.cos t - (1 - t ^ 2 / 2) :=
    nonneg_of_deriv (fun t => Real.cos t - (1 - t ^ 2 / 2)) (fun t => t - Real.sin t) (by simp)
      (fun t => by
        have hd1 := Real.hasDerivAt_cos t
        have hd2 : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2) (-t) t := by
          have := ((hasDerivAt_pow 2 t).div_const 2).const_sub 1
          refine this.congr_deriv ?_; ring
        refine (hd1.sub hd2).congr_deriv ?_; ring)
      h1
  have h3 : ∀ t ≥ 0, 0 ≤ Real.sin t - (t - t ^ 3 / 6) :=
    nonneg_of_deriv (fun t => Real.sin t - (t - t ^ 3 / 6))
      (fun t => Real.cos t - (1 - t ^ 2 / 2)) (by simp)
      (fun t => by
        have hd1 := Real.hasDerivAt_sin t
        have hd2 : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6) (1 - t ^ 2 / 2) t := by
          have := (hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)
          refine this.congr_deriv ?_; ring
        exact hd1.sub hd2)
      h2
  have h4 : ∀ t ≥ 0, 0 ≤ (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t :=
    nonneg_of_deriv (fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t)
      (fun t => Real.sin t - (t - t ^ 3 / 6)) (by simp)
      (fun t => by
        have hd1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24) (-t + t ^ 3 / 6) t := by
          have := (((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add ((hasDerivAt_pow 4 t).div_const 24)
          refine this.congr_deriv ?_; ring
        refine (hd1.sub (Real.hasDerivAt_cos t)).congr_deriv ?_; ring)
      h3
  have h5 : ∀ t ≥ 0, 0 ≤ (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t :=
    nonneg_of_deriv (fun t => (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t)
      (fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t) (by simp)
      (fun t => by
        have hd1 : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6 + u ^ 5 / 120)
            (1 - t ^ 2 / 2 + t ^ 4 / 24) t := by
          have := ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
            ((hasDerivAt_pow 5 t).div_const 120)
          refine this.congr_deriv ?_; ring
        exact hd1.sub (Real.hasDerivAt_sin t))
      h4
  have h6 : ∀ t ≥ 0, 0 ≤ Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) :=
    nonneg_of_deriv (fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
      (fun t => (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t) (by simp)
      (fun t => by
        have hd1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720)
            (-t + t ^ 3 / 6 - t ^ 5 / 120) t := by
          have := ((((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add
            ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)
          refine this.congr_deriv ?_; ring
        refine ((Real.hasDerivAt_cos t).sub hd1).congr_deriv ?_; ring)
      h5
  have h7 : ∀ t ≥ 0, 0 ≤ Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) :=
    nonneg_of_deriv (fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
      (fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)) (by simp)
      (fun t => by
        have hd1 : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040)
            (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) t := by
          have := (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
            ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)
          refine this.congr_deriv ?_; ring
        exact (Real.hasDerivAt_sin t).sub hd1)
      h6
  have h8 : ∀ t ≥ 0, 0 ≤ (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t :=
    nonneg_of_deriv (fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t)
      (fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)) (by simp)
      (fun t => by
        have hd1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320)
            (-t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040) t := by
          have := (((((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add
            ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
            ((hasDerivAt_pow 8 t).div_const 40320)
          refine this.congr_deriv ?_; ring
        refine (hd1.sub (Real.hasDerivAt_cos t)).congr_deriv ?_; ring)
      h7
  have h9 : ∀ t ≥ 0, 0 ≤ (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880) - Real.sin t :=
    nonneg_of_deriv (fun t => (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880) - Real.sin t)
      (fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t) (by simp)
      (fun t => by
        have hd1 : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880)
            (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) t := by
          have := ((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
            ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
            ((hasDerivAt_pow 9 t).div_const 362880)
          refine this.congr_deriv ?_; ring
        exact hd1.sub (Real.hasDerivAt_sin t))
      h8
  exact ⟨⟨by linarith [h6 x hx], by linarith [h8 x hx]⟩,
         ⟨by linarith [h7 x hx], by linarith [h9 x hx]⟩⟩

/-- Monotonicity helper: if `0 ≤ a ≤ θ ≤ b ≤ π / 2`, then
`cos b ≤ cos θ ≤ cos a` and `sin a ≤ sin θ ≤ sin b`. -/
lemma cos_sin_interval_of_le {a θ b : ℝ} (ha : 0 ≤ a) (haθ : a ≤ θ) (hθb : θ ≤ b)
    (hb : b ≤ Real.pi / 2) :
    (Real.cos b ≤ Real.cos θ ∧ Real.cos θ ≤ Real.cos a) ∧
    (Real.sin a ≤ Real.sin θ ∧ Real.sin θ ≤ Real.sin b) := by
  have hb0 : 0 ≤ b := ha.trans (haθ.trans hθb)
  have hθ0 : 0 ≤ θ := ha.trans haθ
  have hpi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  exact ⟨⟨Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (hb.trans hpi) hθb,
          Real.cos_le_cos_of_nonneg_of_le_pi ha ((hθb.trans hb).trans hpi) haθ⟩,
         ⟨Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hθb.trans hb) haθ,
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hb hθb⟩⟩

/-- Certified bounds for the 5 base odd multiples `(2k+1)π/40` (`k = 0..4`) in `[0, π/4]`. -/
lemma base_angle_bounds (k : Fin 5) :
    let θ : ℝ := ((2 * k.val + 1 : ℕ) : ℝ) * Real.pi / 40
    let cLo : ℝ := toR (angleTable40.cmLo.getD k.val 0)
    let cHi : ℝ := toR (angleTable40.cmHi.getD k.val 0)
    let sLo : ℝ := toR (angleTable40.smLo.getD k.val 0)
    let sHi : ℝ := toR (angleTable40.smHi.getD k.val 0)
    (cLo ≤ Real.cos θ ∧ Real.cos θ ≤ cHi) ∧ (sLo ≤ Real.sin θ ∧ Real.sin θ ≤ sHi) := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  -- Extract concrete integer values via `decide` so `norm_num` closes immediately!
  have hv0 : angleTable40.cmLo.getD 0 0 = 996916 ∧ angleTable40.cmHi.getD 0 0 = 996919 ∧
      angleTable40.smLo.getD 0 0 = 78458 ∧ angleTable40.smHi.getD 0 0 = 78461 := by decide
  have hv1 : angleTable40.cmLo.getD 1 0 = 972368 ∧ angleTable40.cmHi.getD 1 0 = 972371 ∧
      angleTable40.smLo.getD 1 0 = 233444 ∧ angleTable40.smHi.getD 1 0 = 233447 := by decide
  have hv2 : angleTable40.cmLo.getD 2 0 = 923878 ∧ angleTable40.cmHi.getD 2 0 = 923881 ∧
      angleTable40.smLo.getD 2 0 = 382682 ∧ angleTable40.smHi.getD 2 0 = 382685 := by decide
  have hv3 : angleTable40.cmLo.getD 3 0 = 852639 ∧ angleTable40.cmHi.getD 3 0 = 852642 ∧
      angleTable40.smLo.getD 3 0 = 522497 ∧ angleTable40.smHi.getD 3 0 = 522500 := by decide
  have hv4 : angleTable40.cmLo.getD 4 0 = 760404 ∧ angleTable40.cmHi.getD 4 0 = 760407 ∧
      angleTable40.smLo.getD 4 0 = 649447 ∧ angleTable40.smHi.getD 4 0 = 649450 := by decide
  fin_cases k
  · dsimp only [Fin.isValue, Fin.val_zero]
    rw [hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2]
    have hI := cos_sin_interval_of_le (a := 3.141592 / 40) (b := 3.141593 / 40)
      (θ := ((2 * 0 + 1 : ℕ) : ℝ) * Real.pi / 40)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by linarith)
    have hta := cos_sin_taylor6 (x := 3.141592 / 40) (by norm_num)
    have htb := cos_sin_taylor6 (x := 3.141593 / 40) (by norm_num)
    unfold toR S; norm_num at hI hta htb ⊢
    exact ⟨⟨by linarith [hI.1.1, htb.1.1], by linarith [hI.1.2, hta.1.2]⟩,
           ⟨by linarith [hI.2.1, hta.2.1], by linarith [hI.2.2, htb.2.2]⟩⟩
  · dsimp only [Fin.isValue, Fin.val_one]
    rw [hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2]
    have hI := cos_sin_interval_of_le (a := 3 * 3.141592 / 40) (b := 3 * 3.141593 / 40)
      (θ := ((2 * 1 + 1 : ℕ) : ℝ) * Real.pi / 40)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by linarith)
    have hta := cos_sin_taylor6 (x := 3 * 3.141592 / 40) (by norm_num)
    have htb := cos_sin_taylor6 (x := 3 * 3.141593 / 40) (by norm_num)
    unfold toR S; norm_num at hI hta htb ⊢
    exact ⟨⟨by linarith [hI.1.1, htb.1.1], by linarith [hI.1.2, hta.1.2]⟩,
           ⟨by linarith [hI.2.1, hta.2.1], by linarith [hI.2.2, htb.2.2]⟩⟩
  · dsimp only [Fin.isValue, Fin.val_two]
    rw [hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2]
    have hI := cos_sin_interval_of_le (a := 5 * 3.141592 / 40) (b := 5 * 3.141593 / 40)
      (θ := ((2 * 2 + 1 : ℕ) : ℝ) * Real.pi / 40)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by linarith)
    have hta := cos_sin_taylor6 (x := 5 * 3.141592 / 40) (by norm_num)
    have htb := cos_sin_taylor6 (x := 5 * 3.141593 / 40) (by norm_num)
    unfold toR S; norm_num at hI hta htb ⊢
    exact ⟨⟨by linarith [hI.1.1, htb.1.1], by linarith [hI.1.2, hta.1.2]⟩,
           ⟨by linarith [hI.2.1, hta.2.1], by linarith [hI.2.2, htb.2.2]⟩⟩
  · dsimp only [Fin.isValue]
    rw [hv3.1, hv3.2.1, hv3.2.2.1, hv3.2.2.2]
    have hI := cos_sin_interval_of_le (a := 7 * 3.141592 / 40) (b := 7 * 3.141593 / 40)
      (θ := ((2 * 3 + 1 : ℕ) : ℝ) * Real.pi / 40)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by linarith)
    have hta := cos_sin_taylor6 (x := 7 * 3.141592 / 40) (by norm_num)
    have htb := cos_sin_taylor6 (x := 7 * 3.141593 / 40) (by norm_num)
    unfold toR S; norm_num at hI hta htb ⊢
    exact ⟨⟨by linarith [hI.1.1, htb.1.1], by linarith [hI.1.2, hta.1.2]⟩,
           ⟨by linarith [hI.2.1, hta.2.1], by linarith [hI.2.2, htb.2.2]⟩⟩
  · dsimp only [Fin.isValue]
    rw [hv4.1, hv4.2.1, hv4.2.2.1, hv4.2.2.2]
    have hI := cos_sin_interval_of_le (a := 9 * 3.141592 / 40) (b := 9 * 3.141593 / 40)
      (θ := ((2 * 4 + 1 : ℕ) : ℝ) * Real.pi / 40)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by linarith)
    have hta := cos_sin_taylor6 (x := 9 * 3.141592 / 40) (by norm_num)
    have htb := cos_sin_taylor6 (x := 9 * 3.141593 / 40) (by norm_num)
    unfold toR S; norm_num at hI hta htb ⊢
    exact ⟨⟨by linarith [hI.1.1, htb.1.1], by linarith [hI.1.2, hta.1.2]⟩,
           ⟨by linarith [hI.2.1, hta.2.1], by linarith [hI.2.2, htb.2.2]⟩⟩

/-- **Complete Soundness of `angleTable40`**:
1. `2π / 40 ≤ toR angleTable40.dtHi`,
2. `toR angleTable40.chLo ≤ cos (π / 40)` and `sin (π / 40) ≤ toR angleTable40.shHi`,
3. For all `it : Fin 40`, with midpoint `tm = (it + 1/2) * (2π / 40) = (2*it + 1) * π / 40`,
   `cmLo[it] ≤ cos tm ≤ cmHi[it]` and `smLo[it] ≤ sin tm ≤ smHi[it]`! -/
theorem angleTable40_sound :
    (2 * Real.pi / 40 ≤ toR angleTable40.dtHi) ∧
    (toR angleTable40.chLo ≤ Real.cos (Real.pi / 40) ∧
     Real.sin (Real.pi / 40) ≤ toR angleTable40.shHi) ∧
    (∀ it : Fin 40,
      let tm : ℝ := ((2 * it.val + 1 : ℕ) : ℝ) * Real.pi / 40
      toR (angleTable40.cmLo.getD it.val 0) ≤ Real.cos tm ∧
      Real.cos tm ≤ toR (angleTable40.cmHi.getD it.val 0) ∧
      toR (angleTable40.smLo.getD it.val 0) ≤ Real.sin tm ∧
      Real.sin tm ≤ toR (angleTable40.smHi.getD it.val 0)) := by
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hbase0 := base_angle_bounds ⟨0, by decide⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold toR S angleTable40; norm_num; linarith
  · have h0 := hbase0
    simp only [Nat.mul_zero, zero_add, Nat.cast_one, one_mul] at h0
    have hch_i : angleTable40.chLo ≤ angleTable40.cmLo.getD 0 0 := by decide
    have hsh_i : angleTable40.smHi.getD 0 0 ≤ angleTable40.shHi := by decide
    have hch : toR angleTable40.chLo ≤ toR (angleTable40.cmLo.getD 0 0) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hch_i) (le_of_lt S_pos)
    have hsh : toR (angleTable40.smHi.getD 0 0) ≤ toR angleTable40.shHi :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsh_i) (le_of_lt S_pos)
    exact ⟨hch.trans h0.1.1, h0.2.2.trans hsh⟩
  · -- Use 8-fold symmetry (`π/2 - θ`, `π - θ`, `2π - θ`) to reduce all 40 indices to `hbase0..4`!
    -- Helper checking symmetry against our concrete arrays via `decide`!
    have hsym_check :
        (∀ i : Fin 5,
          -- Octant 1 (k = 9 - i): cos = sin(i), sin = cos(i)
          angleTable40.cmLo.getD (9 - i.val) 0 ≤ angleTable40.smLo.getD i.val 0 ∧
          angleTable40.smHi.getD i.val 0 ≤ angleTable40.cmHi.getD (9 - i.val) 0 ∧
          angleTable40.smLo.getD (9 - i.val) 0 ≤ angleTable40.cmLo.getD i.val 0 ∧
          angleTable40.cmHi.getD i.val 0 ≤ angleTable40.smHi.getD (9 - i.val) 0) ∧
        (∀ i : Fin 10,
          -- Quadrant 2 (k = 19 - i): cos = -cos(i), sin = sin(i)
          angleTable40.cmLo.getD (19 - i.val) 0 ≤ -angleTable40.cmHi.getD i.val 0 ∧
          -angleTable40.cmLo.getD i.val 0 ≤ angleTable40.cmHi.getD (19 - i.val) 0 ∧
          angleTable40.smLo.getD (19 - i.val) 0 ≤ angleTable40.smLo.getD i.val 0 ∧
          angleTable40.smHi.getD i.val 0 ≤ angleTable40.smHi.getD (19 - i.val) 0) ∧
        (∀ i : Fin 20,
          -- Bottom half (k = 39 - i): cos = cos(i), sin = -sin(i)
          angleTable40.cmLo.getD (39 - i.val) 0 ≤ angleTable40.cmLo.getD i.val 0 ∧
          angleTable40.cmHi.getD i.val 0 ≤ angleTable40.cmHi.getD (39 - i.val) 0 ∧
          angleTable40.smLo.getD (39 - i.val) 0 ≤ -angleTable40.smHi.getD i.val 0 ∧
          -angleTable40.smLo.getD i.val 0 ≤ angleTable40.smHi.getD (39 - i.val) 0) := by
      decide
    have hq1 : ∀ it : Fin 10,
        let tm : ℝ := ((2 * it.val + 1 : ℕ) : ℝ) * Real.pi / 40
        toR (angleTable40.cmLo.getD it.val 0) ≤ Real.cos tm ∧
        Real.cos tm ≤ toR (angleTable40.cmHi.getD it.val 0) ∧
        toR (angleTable40.smLo.getD it.val 0) ≤ Real.sin tm ∧
        Real.sin tm ≤ toR (angleTable40.smHi.getD it.val 0) := by
      intro it
      by_cases h5 : it.val < 5
      · have hb := base_angle_bounds ⟨it.val, h5⟩
        exact ⟨hb.1.1, hb.1.2, hb.2.1, hb.2.2⟩
      · let j : Fin 5 := ⟨9 - it.val, by omega⟩
        have hb := base_angle_bounds j
        have hs := hsym_check.1 j
        have hidx : 9 - j.val = it.val := by dsimp only [j]; omega
        rw [hidx] at hs
        have htm : ((2 * it.val + 1 : ℕ) : ℝ) * Real.pi / 40 =
            Real.pi / 2 - ((2 * j.val + 1 : ℕ) : ℝ) * Real.pi / 40 := by
          have hj : (2 * it.val + 1) + (2 * j.val + 1) = 20 := by dsimp only [j]; omega
          have hjR : ((2 * it.val + 1 : ℕ) : ℝ) + ((2 * j.val + 1 : ℕ) : ℝ) = 20 := by exact_mod_cast hj
          linear_combination (Real.pi / 40) * hjR
        dsimp only; rw [htm, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
        have hcLo : toR (angleTable40.cmLo.getD it.val 0) ≤ toR (angleTable40.smLo.getD j.val 0) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hs.1) (le_of_lt S_pos)
        have hcHi : toR (angleTable40.smHi.getD j.val 0) ≤ toR (angleTable40.cmHi.getD it.val 0) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hs.2.1) (le_of_lt S_pos)
        have hsLo : toR (angleTable40.smLo.getD it.val 0) ≤ toR (angleTable40.cmLo.getD j.val 0) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hs.2.2.1) (le_of_lt S_pos)
        have hsHi : toR (angleTable40.cmHi.getD j.val 0) ≤ toR (angleTable40.smHi.getD it.val 0) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hs.2.2.2) (le_of_lt S_pos)
        exact ⟨hcLo.trans hb.2.1, hb.2.2.trans hcHi, hsLo.trans hb.1.1, hb.1.2.trans hsHi⟩
    have htop : ∀ it : Fin 20,
        let tm : ℝ := ((2 * it.val + 1 : ℕ) : ℝ) * Real.pi / 40
        toR (angleTable40.cmLo.getD it.val 0) ≤ Real.cos tm ∧
        Real.cos tm ≤ toR (angleTable40.cmHi.getD it.val 0) ∧
        toR (angleTable40.smLo.getD it.val 0) ≤ Real.sin tm ∧
        Real.sin tm ≤ toR (angleTable40.smHi.getD it.val 0) := by
      intro it
      by_cases h10 : it.val < 10
      · exact hq1 ⟨it.val, h10⟩
      · let j : Fin 10 := ⟨19 - it.val, by omega⟩
        have hb := hq1 j
        have hs := hsym_check.2.1 j
        have hidx : 19 - j.val = it.val := by dsimp only [j]; omega
        rw [hidx] at hs
        have htm : ((2 * it.val + 1 : ℕ) : ℝ) * Real.pi / 40 =
            Real.pi - ((2 * j.val + 1 : ℕ) : ℝ) * Real.pi / 40 := by
          have hj : (2 * it.val + 1) + (2 * j.val + 1) = 40 := by dsimp only [j]; omega
          have hjR : ((2 * it.val + 1 : ℕ) : ℝ) + ((2 * j.val + 1 : ℕ) : ℝ) = 40 := by exact_mod_cast hj
          linear_combination (Real.pi / 40) * hjR
        dsimp only; rw [htm, Real.cos_pi_sub, Real.sin_pi_sub]
        have hcLo : toR (angleTable40.cmLo.getD it.val 0) ≤ -toR (angleTable40.cmHi.getD j.val 0) := by
          unfold toR; rw [← neg_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast hs.1) (le_of_lt S_pos)
        have hcHi : -toR (angleTable40.cmLo.getD j.val 0) ≤ toR (angleTable40.cmHi.getD it.val 0) := by
          unfold toR; rw [← neg_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast hs.2.1) (le_of_lt S_pos)
        have hsLo : toR (angleTable40.smLo.getD it.val 0) ≤ toR (angleTable40.smLo.getD j.val 0) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hs.2.2.1) (le_of_lt S_pos)
        have hsHi : toR (angleTable40.smHi.getD j.val 0) ≤ toR (angleTable40.smHi.getD it.val 0) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hs.2.2.2) (le_of_lt S_pos)
        exact ⟨by linarith [hb.2.1], by linarith [hb.1], hsLo.trans hb.2.2.1, hb.2.2.2.trans hsHi⟩
    intro it
    by_cases h20 : it.val < 20
    · exact htop ⟨it.val, h20⟩
    · let j : Fin 20 := ⟨39 - it.val, by omega⟩
      have hb := htop j
      have hs := hsym_check.2.2 j
      have hidx : 39 - j.val = it.val := by dsimp only [j]; omega
      rw [hidx] at hs
      have htm : ((2 * it.val + 1 : ℕ) : ℝ) * Real.pi / 40 =
          2 * Real.pi - ((2 * j.val + 1 : ℕ) : ℝ) * Real.pi / 40 := by
        have hj : (2 * it.val + 1) + (2 * j.val + 1) = 80 := by dsimp only [j]; omega
        have hjR : ((2 * it.val + 1 : ℕ) : ℝ) + ((2 * j.val + 1 : ℕ) : ℝ) = 80 := by exact_mod_cast hj
        linear_combination (Real.pi / 40) * hjR
      dsimp only; rw [htm, Real.cos_two_pi_sub, Real.sin_two_pi_sub]
      have hcLo : toR (angleTable40.cmLo.getD it.val 0) ≤ toR (angleTable40.cmLo.getD j.val 0) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hs.1) (le_of_lt S_pos)
      have hcHi : toR (angleTable40.cmHi.getD j.val 0) ≤ toR (angleTable40.cmHi.getD it.val 0) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hs.2.1) (le_of_lt S_pos)
      have hsLo : toR (angleTable40.smLo.getD it.val 0) ≤ -toR (angleTable40.smHi.getD j.val 0) := by
        unfold toR; rw [← neg_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast hs.2.2.1) (le_of_lt S_pos)
      have hsHi : -toR (angleTable40.smLo.getD j.val 0) ≤ toR (angleTable40.smHi.getD it.val 0) := by
        unfold toR; rw [← neg_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast hs.2.2.2) (le_of_lt S_pos)
      exact ⟨hcLo.trans hb.1, hb.2.1.trans hcHi, by linarith [hb.2.2.2], by linarith [hb.2.2.1]⟩

end BHHBounds.Cert
