import BHHBounds.Dual.FiniteN

/-!
# Change of variables for three points

Measurability of `canonShape`, the inverse `triEmbedInv` of the rigid embedding with its
change-of-variables formula, and the resulting formula for integrals over `unitSquarePi 3` of
functions of the canonical shape (`integral_unitSquarePi3_canonShape`).
-/

open MeasureTheory Set Real Filter Finset
open scoped ENNReal Classical
open BHHBounds.Geometry
open BHHBounds.Cert

namespace BHHBounds.Dual

noncomputable section

/-! ## Section 1: Measurability & Integrability of the Finite-`n` Level Integrand -/

private lemma toR_lt_toR {a b : Int} (h : a < b) : toR a < toR b :=
  div_lt_div_of_pos_right (by exact_mod_cast h) S_pos

private lemma abs_max_zero_sub_le (a b : ℝ) : |max 0 a - max 0 b| ≤ |a - b| := by
  rw [abs_le]
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]
    exact ⟨neg_abs_le (a - b), le_abs_self (a - b)⟩
  · rw [max_eq_right ha, max_eq_left hb, sub_zero]
    have hab : 0 ≤ a - b := by linarith
    rw [abs_of_nonneg hab]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_right hb, zero_sub]
    have hab : a - b ≤ 0 := by linarith
    rw [abs_of_nonpos hab]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_left hb, sub_self]
    exact ⟨by linarith [abs_nonneg (a - b)], abs_nonneg _⟩

private lemma measurable_rescaledDist {n : ℕ} (i j : Fin n) :
    Measurable (fun X : Fin n → Pt => rescaledDist X i j) := by
  unfold rescaledDist
  have hpair : Measurable (fun X : Fin n → Pt => (X i, X j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  exact measurable_const.mul (measurable_euclidDist.comp hpair)

private lemma measurable_finset_inf' {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => s.inf' hs fun i => f i a) := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | cons a s' ha ih =>
    by_cases hs' : s'.Nonempty
    · have heq : (fun x => (Finset.cons a s' ha).inf' hs fun i => f i x) =
          fun x => min (f a x) (s'.inf' hs' fun i => f i x) := by
        ext x; exact Finset.inf'_cons (f := fun i => f i x) hs'
      rw [heq]
      exact (hf a (Finset.mem_cons_self a s')).min
        (ih hs' fun i hi => hf i (Finset.mem_cons_of_mem hi))
    · have hempty : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst hempty
      have heq : (fun x => (Finset.cons a ∅ ha).inf' hs fun i => f i x) = fun x => f a x := by
        ext x; simp
      rw [heq]; exact hf a (Finset.mem_cons_self a ∅)

private lemma measurable_nn2 {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    Measurable (fun X : Fin n → Pt => nn2 hn (rescaledDist X) i) := by
  unfold nn2
  exact measurable_finset_inf' (neighborPairs i) (neighborPairs_nonempty hn i)
    (fun p X => max (rescaledDist X i p.1) (rescaledDist X i p.2))
    (fun p _ => (measurable_rescaledDist i p.1).max (measurable_rescaledDist i p.2))

private lemma measurable_stepPot (rho w : Array Int) :
    Measurable (stepPot rho w) := by
  unfold stepPot
  refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const

lemma measurable_canonShape :
    Measurable (fun p : Pt × Pt × Pt => canonShape p.1 p.2.1 p.2.2) := by
  unfold canonShape
  have h0 : Measurable (fun p : Pt × Pt × Pt => p.1) := measurable_fst
  have h1 : Measurable (fun p : Pt × Pt × Pt => p.2.1) := measurable_fst.comp measurable_snd
  have h2 : Measurable (fun p : Pt × Pt × Pt => p.2.2) := measurable_snd.comp measurable_snd
  have hL : Measurable (fun p : Pt × Pt × Pt => euclidDist p.1 p.2.1) :=
    measurable_euclidDist.comp (h0.prodMk h1)
  have hdx : Measurable (fun p : Pt × Pt × Pt => p.2.1.1 - p.1.1) :=
    (measurable_fst.comp h1).sub (measurable_fst.comp h0)
  have hdy : Measurable (fun p : Pt × Pt × Pt => p.2.1.2 - p.1.2) :=
    (measurable_snd.comp h1).sub (measurable_snd.comp h0)
  have hux : Measurable (fun p : Pt × Pt × Pt => p.2.2.1 - p.1.1) :=
    (measurable_fst.comp h2).sub (measurable_fst.comp h0)
  have huy : Measurable (fun p : Pt × Pt × Pt => p.2.2.2 - p.1.2) :=
    (measurable_snd.comp h2).sub (measurable_snd.comp h0)
  refine hL.prodMk ?_
  refine (((hux.mul hdx).add (huy.mul hdy)).div (hL.pow_const 2)).prodMk ?_
  exact (continuous_abs.measurable.comp (((hux.mul hdy).neg.add (huy.mul hdx)))).div (hL.pow_const 2)

lemma measurableSet_boxRegion (b : BoxCert) :
    MeasurableSet (boxRegion b) := by
  unfold boxRegion
  have hL : Measurable (fun p : ℝ × Pt => p.1) := measurable_fst
  have hx : Measurable (fun p : ℝ × Pt => p.2.1) := measurable_fst.comp measurable_snd
  have hy : Measurable (fun p : ℝ × Pt => p.2.2) := measurable_snd.comp measurable_snd
  exact (measurableSet_lt measurable_const hL).inter
    ((measurableSet_lt hL measurable_const).inter
      ((measurableSet_lt measurable_const hx).inter
        ((measurableSet_lt hx measurable_const).inter
          ((measurableSet_lt measurable_const hy).inter
            (measurableSet_lt hy measurable_const)))))

private lemma measurableSet_matchesBox {n : ℕ} (b : BoxCert) (rBuf : ℝ) (u v t : Fin n) :
    MeasurableSet {X : Fin n → Pt | MatchesBox b rBuf X u v t} := by
  by_cases hne : u ≠ v ∧ u ≠ t ∧ v ≠ t
  · have heq : {X : Fin n → Pt | MatchesBox b rBuf X u v t} =
        {X : Fin n → Pt | X u ∈ interiorBox rBuf} ∩
        {X : Fin n → Pt |
          canonShape (Real.sqrt (n : ℝ) * (X u).1, Real.sqrt (n : ℝ) * (X u).2)
            (Real.sqrt (n : ℝ) * (X v).1, Real.sqrt (n : ℝ) * (X v).2)
            (Real.sqrt (n : ℝ) * (X t).1, Real.sqrt (n : ℝ) * (X t).2) ∈ boxRegion b} := by
      ext X; simp [MatchesBox, hne]
    rw [heq]
    have hsc : ∀ i : Fin n, Measurable (fun X : Fin n → Pt =>
        (Real.sqrt (n : ℝ) * (X i).1, Real.sqrt (n : ℝ) * (X i).2)) := fun i =>
      (measurable_const.mul (measurable_fst.comp (measurable_pi_apply i))).prodMk
        (measurable_const.mul (measurable_snd.comp (measurable_pi_apply i)))
    refine ((measurableSet_interiorBox rBuf).preimage (measurable_pi_apply u)).inter ?_
    exact (measurableSet_boxRegion b).preimage
      (measurable_canonShape.comp ((hsc u).prodMk ((hsc v).prodMk (hsc t))))
  · have heq : {X : Fin n → Pt | MatchesBox b rBuf X u v t} = ∅ := by
      ext X; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hm; exact hne ⟨hm.1, hm.2.1, hm.2.2.1⟩
    rw [heq]; exact MeasurableSet.empty

private lemma measurableSet_triClearance {n : ℕ} (rj : Int) (u v t : Fin n) :
    MeasurableSet {X : Fin n → Pt |
      ∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
        toR rj < rescaledDist X x z} := by
  have heq : {X : Fin n → Pt |
      ∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
        toR rj < rescaledDist X x z} =
      ⋂ x ∈ ({u, v, t} : Finset (Fin n)), ⋂ z ∈ (Finset.univ \ ({u, v, t} : Finset (Fin n))),
        {X : Fin n → Pt | toR rj < rescaledDist X x z} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [heq]
  exact MeasurableSet.biInter (Finset.countable_toSet _) fun x _ =>
    MeasurableSet.biInter (Finset.countable_toSet _) fun z _ =>
      measurableSet_lt measurable_const (measurable_rescaledDist x z)

private def levelTerm {n : ℕ} (hn : 4 ≤ n) (rho w : Array Int) (b : BoxCert)
    (yPrev rj yj : Int) (rBuf : ℝ) (u v t : Fin n) (X : Fin n → Pt) : ℝ :=
  if MatchesBox b rBuf X u v t ∧
      (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
        toR rj < rescaledDist X x z) then
    2 * (toR yj - toR yPrev) -
      ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
        (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
         max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
  else 0

private lemma measurable_levelTerm {n : ℕ} (hn : 4 ≤ n) (rho w : Array Int) (b : BoxCert)
    (yPrev rj yj : Int) (rBuf : ℝ) (u v t : Fin n) :
    Measurable (levelTerm hn rho w b yPrev rj yj rBuf u v t) := by
  unfold levelTerm
  refine Measurable.ite
    ((measurableSet_matchesBox b rBuf u v t).inter (measurableSet_triClearance rj u v t)) ?_
    measurable_const
  refine measurable_const.sub ?_
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun z _ => ?_
  have hpx : Measurable (fun X : Fin n → Pt => stepPot rho w (nn2 (by omega) (rescaledDist X) x)) :=
    (measurable_stepPot rho w).comp (measurable_nn2 (by omega) x)
  have hpz : Measurable (fun X : Fin n → Pt => stepPot rho w (nn2 (by omega) (rescaledDist X) z)) :=
    (measurable_stepPot rho w).comp (measurable_nn2 (by omega) z)
  have hd : Measurable (fun X : Fin n → Pt => rescaledDist X x z) := measurable_rescaledDist x z
  exact (measurable_const.max (((hpx.add measurable_const).add hpz).sub hd)).sub
    (measurable_const.max (((hpx.add measurable_const).add hpz).sub hd))

private lemma norm_levelTerm_le {n : ℕ} (hn : 4 ≤ n) (rho w : Array Int) (b : BoxCert)
    (yPrev rj yj : Int) (rBuf : ℝ) (u v t : Fin n) (X : Fin n → Pt) :
    ‖levelTerm hn rho w b yPrev rj yj rBuf u v t X‖ ≤
      (2 + 3 * (n : ℝ)) * |toR yj - toR yPrev| := by
  unfold levelTerm
  split_ifs with h
  · rw [Real.norm_eq_abs]
    set S_sum := ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
        (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
         max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
    have hsum : |S_sum| ≤ (3 * (n : ℝ)) * |toR yj - toR yPrev| := by
      calc |S_sum|
          ≤ ∑ x ∈ ({u, v, t} : Finset (Fin n)), |∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
              (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
                  stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
               max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
                  stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
              |toR yj - toR yPrev| := by
            refine Finset.sum_le_sum fun x _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
            refine Finset.sum_le_sum fun z _ => ?_
            have hab := abs_max_zero_sub_le
              (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
                stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z)
              (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
                stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z)
            have hdiff : (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
                  stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
                  stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) =
                toR yj - toR yPrev := by ring
            rwa [hdiff] at hab
        _ = (({u, v, t} : Finset (Fin n)).card : ℝ) *
              ((Finset.univ \ ({u, v, t} : Finset (Fin n))).card : ℝ) * |toR yj - toR yPrev| := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
        _ ≤ 3 * (n : ℝ) * |toR yj - toR yPrev| := by
            have hc1 : (({u, v, t} : Finset (Fin n)).card : ℝ) ≤ 3 := by
              have h1 : ({u, v, t} : Finset (Fin n)).card ≤ 3 :=
                (Finset.card_insert_le _ _).trans (by
                  have := Finset.card_insert_le v {t}
                  simp only [Finset.card_singleton] at this; omega)
              exact_mod_cast h1
            have hc2 : ((Finset.univ \ ({u, v, t} : Finset (Fin n))).card : ℝ) ≤ (n : ℝ) := by
              have h2 : (Finset.univ \ ({u, v, t} : Finset (Fin n))).card ≤ n := by
                calc (Finset.univ \ ({u, v, t} : Finset (Fin n))).card
                    ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card Finset.sdiff_subset
                  _ = n := by simp
              exact_mod_cast h2
            have hprod : (({u, v, t} : Finset (Fin n)).card : ℝ) *
                ((Finset.univ \ ({u, v, t} : Finset (Fin n))).card : ℝ) ≤ 3 * (n : ℝ) :=
              mul_le_mul hc1 hc2 (Nat.cast_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
    calc |2 * (toR yj - toR yPrev) - S_sum|
        ≤ |2 * (toR yj - toR yPrev)| + |S_sum| := abs_sub _ _
      _ = 2 * |toR yj - toR yPrev| + |S_sum| := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * |toR yj - toR yPrev| + (3 * (n : ℝ)) * |toR yj - toR yPrev| := add_le_add le_rfl hsum
      _ = (2 + 3 * (n : ℝ)) * |toR yj - toR yPrev| := by ring
  · rw [norm_zero]; positivity

private lemma integrable_levelTerm {n : ℕ} (hn : 4 ≤ n) (rho w : Array Int) (b : BoxCert)
    (yPrev rj yj : Int) (rBuf : ℝ) (u v t : Fin n) :
    Integrable (levelTerm hn rho w b yPrev rj yj rBuf u v t) (unitSquarePi n) :=
  Integrable.of_bound
    (measurable_levelTerm hn rho w b yPrev rj yj rBuf u v t).aestronglyMeasurable
    ((2 + 3 * (n : ℝ)) * |toR yj - toR yPrev|)
    (Eventually.of_forall fun X => norm_levelTerm_le hn rho w b yPrev rj yj rBuf u v t X)

/-- Integrability of the finite-`n` triangle-moat level integrand on `unitSquarePi n`. -/
lemma integrable_levelGain_integrand {n : ℕ} (hn : 4 ≤ n)
    {rho w : Array Int} (_hpot : ValidStepPot rho w)
    (b : BoxCert) (yPrev rj yj : Int) (rBuf : ℝ) :
    Integrable (fun X : Fin n → Pt =>
      (1 / (n : ℝ)) * ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
        if MatchesBox b rBuf X u v t ∧
            (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
              toR rj < rescaledDist X x z) then
          2 * (toR yj - toR yPrev) -
            ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
              (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
                  stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
               max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
                  stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
        else 0)
      (unitSquarePi n) := by
  refine Integrable.const_mul ?_ (1 / (n : ℝ))
  refine integrable_finsetSum _ fun u _ =>
    integrable_finsetSum _ fun v _ =>
      integrable_finsetSum _ fun t _ =>
        integrable_levelTerm hn rho w b yPrev rj yj rBuf u v t

/-! ## Section 2: Rigid-Motion Change of Variables & Signed Radial Integration -/

/-- Explicit inverse of `triEmbed x₀ c s refl r` (for `c² + s² = 1` and `r ≠ 0`). -/
def triEmbedInv (x₀ : Pt) (c s : ℝ) (refl : Bool) (r : ℝ) (z : Pt) : Pt :=
  let dx := (z.1 - x₀.1) / r
  let dy := (z.2 - x₀.2) / r
  let vx := c * dx + s * dy
  let vy := -s * dx + c * dy
  if refl then (vx, -vy) else (vx, vy)

lemma triEmbed_triEmbedInv (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (refl : Bool) {r : ℝ} (hr : r ≠ 0) (z : Pt) :
    triEmbed x₀ c s refl r (triEmbedInv x₀ c s refl r z) = z := by
  unfold triEmbed triEmbedInv
  cases refl <;> apply Prod.ext <;> simp only [↓reduceIte, Bool.false_eq_true, neg_neg]
  · have h : x₀.1 + r * (c * (c * ((z.1 - x₀.1) / r) + s * ((z.2 - x₀.2) / r)) -
        s * (-s * ((z.1 - x₀.1) / r) + c * ((z.2 - x₀.2) / r))) =
        x₀.1 + (c ^ 2 + s ^ 2) * (z.1 - x₀.1) := by field_simp [hr]; ring
    rw [h, hcs]; ring
  · have h : x₀.2 + r * (s * (c * ((z.1 - x₀.1) / r) + s * ((z.2 - x₀.2) / r)) +
        c * (-s * ((z.1 - x₀.1) / r) + c * ((z.2 - x₀.2) / r))) =
        x₀.2 + (c ^ 2 + s ^ 2) * (z.2 - x₀.2) := by field_simp [hr]; ring
    rw [h, hcs]; ring
  · have h : x₀.1 + r * (c * (c * ((z.1 - x₀.1) / r) + s * ((z.2 - x₀.2) / r)) -
        s * (-s * ((z.1 - x₀.1) / r) + c * ((z.2 - x₀.2) / r))) =
        x₀.1 + (c ^ 2 + s ^ 2) * (z.1 - x₀.1) := by field_simp [hr]; ring
    rw [h, hcs]; ring
  · have h : x₀.2 + r * (s * (c * ((z.1 - x₀.1) / r) + s * ((z.2 - x₀.2) / r)) +
        c * (-s * ((z.1 - x₀.1) / r) + c * ((z.2 - x₀.2) / r))) =
        x₀.2 + (c ^ 2 + s ^ 2) * (z.2 - x₀.2) := by field_simp [hr]; ring
    rw [h, hcs]; ring

lemma triEmbedInv_triEmbed (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (refl : Bool) {r : ℝ} (hr : r ≠ 0) (v : Pt) :
    triEmbedInv x₀ c s refl r (triEmbed x₀ c s refl r v) = v := by
  unfold triEmbed triEmbedInv
  cases refl <;> apply Prod.ext <;> simp only [↓reduceIte, Bool.false_eq_true]
  · have h : c * ((x₀.1 + r * (c * v.1 - s * v.2) - x₀.1) / r) +
        s * ((x₀.2 + r * (s * v.1 + c * v.2) - x₀.2) / r) = (c ^ 2 + s ^ 2) * v.1 := by
      field_simp [hr]; ring
    rw [h, hcs, one_mul]
  · have h : -s * ((x₀.1 + r * (c * v.1 - s * v.2) - x₀.1) / r) +
        c * ((x₀.2 + r * (s * v.1 + c * v.2) - x₀.2) / r) = (c ^ 2 + s ^ 2) * v.2 := by
      field_simp [hr]; ring
    rw [h, hcs, one_mul]
  · have h : c * ((x₀.1 + r * (c * v.1 - s * -v.2) - x₀.1) / r) +
        s * ((x₀.2 + r * (s * v.1 + c * -v.2) - x₀.2) / r) = (c ^ 2 + s ^ 2) * v.1 := by
      field_simp [hr]; ring
    rw [h, hcs, one_mul]
  · have h : -(-s * ((x₀.1 + r * (c * v.1 - s * -v.2) - x₀.1) / r) +
        c * ((x₀.2 + r * (s * v.1 + c * -v.2) - x₀.2) / r)) = (c ^ 2 + s ^ 2) * v.2 := by
      field_simp [hr]; ring
    rw [h, hcs, one_mul]

lemma measurable_triEmbedInv (x₀ : Pt) (c s : ℝ) (refl : Bool) (r : ℝ) :
    Measurable (triEmbedInv x₀ c s refl r) := by
  unfold triEmbedInv
  cases refl <;> simp only [↓reduceIte, Bool.false_eq_true] <;> fun_prop

lemma map_triEmbedInv_volume (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (refl : Bool) {r : ℝ} (hr : 0 < r) :
    Measure.map (triEmbedInv x₀ c s refl r) volume = ENNReal.ofReal (r ^ 2) • volume := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply (measurable_triEmbedInv x₀ c s refl r) hS, Measure.smul_apply, smul_eq_mul]
  have hpre : triEmbedInv x₀ c s refl r ⁻¹' S = triEmbed x₀ c s refl r '' S := by
    ext z
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hz
      exact ⟨triEmbedInv x₀ c s refl r z, hz, triEmbed_triEmbedInv x₀ hcs refl (ne_of_gt hr) z⟩
    · rintro ⟨v, hv, rfl⟩
      rwa [triEmbedInv_triEmbed x₀ hcs refl (ne_of_gt hr) v]
  rw [hpre, volume_image_triEmbed x₀ hcs refl hr hS]

/-- Exact Lebesgue change of variables along `triEmbedInv x₀ c s refl r`. -/
lemma integral_comp_triEmbedInv (x₀ : Pt) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (refl : Bool) {r : ℝ} (hr : 0 < r) {h : Pt → ℝ} (hh : AEStronglyMeasurable h volume) :
    ∫ z : Pt, h (triEmbedInv x₀ c s refl r z) ∂volume = r ^ 2 * ∫ v : Pt, h v ∂volume := by
  have hmap := map_triEmbedInv_volume x₀ hcs refl hr
  have hh' : AEStronglyMeasurable h (Measure.map (triEmbedInv x₀ c s refl r) volume) := by
    rw [hmap]
    exact hh.mono_ac (Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _)
  rw [← integral_map (measurable_triEmbedInv x₀ c s refl r).aemeasurable hh', hmap,
      integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg r), smul_eq_mul]

/-- Canonical shape of `(√n • x₀, √n • x₁, √n • x₂)` expressed in local coordinates
`x₂ = triEmbed x₀ c s false (L / √n) v`. -/
private lemma canonShape_triEmbedInv {x₀ x₁ x₂ : Pt} {sqn : ℝ} (hsqn : 0 < sqn)
    (hL : 0 < sqn * euclidDist x₀ x₁) :
    let L := sqn * euclidDist x₀ x₁
    let c := (x₁.1 - x₀.1) / (L / sqn)
    let s := (x₁.2 - x₀.2) / (L / sqn)
    let v := triEmbedInv x₀ c s false (L / sqn) x₂
    c ^ 2 + s ^ 2 = 1 ∧
    canonShape (sqn * x₀.1, sqn * x₀.2) (sqn * x₁.1, sqn * x₁.2) (sqn * x₂.1, sqn * x₂.2) =
      (L, (v.1, |v.2|)) := by
  intro L c s v
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hsqn_ne : sqn ≠ 0 := ne_of_gt hsqn
  have hdist_pos : 0 < euclidDist x₀ x₁ := by
    have : 0 < sqn * euclidDist x₀ x₁ := hL
    nlinarith [euclidDist_nonneg x₀ x₁]
  have hr_eq : L / sqn = euclidDist x₀ x₁ := by
    dsimp only [L]; field_simp [hsqn_ne]
  have hd_ne : euclidDist x₀ x₁ ≠ 0 := ne_of_gt hdist_pos
  have hd2 : (x₁.1 - x₀.1) ^ 2 + (x₁.2 - x₀.2) ^ 2 = euclidDist x₀ x₁ ^ 2 := by
    rw [euclidDist_sq]; unfold sqDist; ring
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    dsimp only [c, s]; rw [hr_eq]; field_simp [hd_ne]; linarith
  refine ⟨hcs, ?_⟩
  have hdist_sc : euclidDist (sqn * x₀.1, sqn * x₀.2) (sqn * x₁.1, sqn * x₁.2) = L := by
    unfold euclidDist sqDist L
    have hsq : (sqn * x₀.1 - sqn * x₁.1) ^ 2 + (sqn * x₀.2 - sqn * x₁.2) ^ 2 =
        sqn ^ 2 * ((x₀.1 - x₁.1) ^ 2 + (x₀.2 - x₁.2) ^ 2) := by ring
    dsimp only; rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hsqn)]; rfl
  unfold canonShape
  dsimp only
  rw [hdist_sc]
  refine Prod.ext rfl ?_
  dsimp only [v, triEmbedInv, c, s]
  rw [hr_eq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply Prod.ext
  · dsimp only [L]; field_simp [hsqn_ne, hd_ne]
  · have harg : -((sqn * x₂.1 - sqn * x₀.1) * (sqn * x₁.2 - sqn * x₀.2)) +
        (sqn * x₂.2 - sqn * x₀.2) * (sqn * x₁.1 - sqn * x₀.1) =
        L ^ 2 * (-((x₁.2 - x₀.2) / euclidDist x₀ x₁) * ((x₂.1 - x₀.1) / euclidDist x₀ x₁) +
          (x₁.1 - x₀.1) / euclidDist x₀ x₁ * ((x₂.2 - x₀.2) / euclidDist x₀ x₁)) := by
      dsimp only [L]; field_simp [hsqn_ne, hd_ne]
    rw [harg, abs_mul, abs_of_pos (sq_pos_of_pos hL), mul_div_cancel_left₀ _ (pow_ne_zero 2 hL_ne)]

/-- Signed radial Bochner integral on `ℝ²`: `∫ z, h ‖z‖ = ∫ r ∈ (0, ∞), 2π r h(r)`. -/
private lemma integral_radial_eq_signed {h : ℝ → ℝ} (hh_meas : Measurable h)
    (hh_int : Integrable (fun z : Pt => h (euclidNorm z)) volume)
    (hh_int_r : IntegrableOn (fun r : ℝ => (2 * Real.pi * r) * h r) (Ioi 0) volume) :
    ∫ z : Pt, h (euclidNorm z) = ∫ r in Ioi (0 : ℝ), (2 * Real.pi * r) * h r := by
  let hp : ℝ → ℝ := fun r => max (h r) 0
  let hm : ℝ → ℝ := fun r => max (-h r) 0
  have hhp_meas : Measurable hp := hh_meas.max measurable_const
  have hhm_meas : Measurable hm := hh_meas.neg.max measurable_const
  have hsplit : ∀ r, h r = hp r - hm r := fun r => by
    dsimp only [hp, hm]; rcases le_total 0 (h r) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
  have hnorm_p : ∀ r, ‖hp r‖ ≤ ‖h r‖ := fun r => by
    dsimp only [hp]; rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnorm_m : ∀ r, ‖hm r‖ ≤ ‖h r‖ := fun r => by
    dsimp only [hm]; rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hmeas_norm : Measurable (euclidNorm : Pt → ℝ) := by unfold euclidNorm; fun_prop
  have hp_int : Integrable (fun z : Pt => hp (euclidNorm z)) volume :=
    hh_int.mono (hhp_meas.comp hmeas_norm).aestronglyMeasurable
      (Eventually.of_forall fun z => hnorm_p (euclidNorm z))
  have hm_int : Integrable (fun z : Pt => hm (euclidNorm z)) volume :=
    hh_int.mono (hhm_meas.comp hmeas_norm).aestronglyMeasurable
      (Eventually.of_forall fun z => hnorm_m (euclidNorm z))
  have hp_int_r : IntegrableOn (fun r : ℝ => (2 * Real.pi * r) * hp r) (Ioi 0) volume := by
    refine Integrable.mono hh_int_r ((measurable_const.mul measurable_id).mul hhp_meas).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r _
    rw [norm_mul (2 * Real.pi * r), norm_mul (2 * Real.pi * r)]
    exact mul_le_mul_of_nonneg_left (hnorm_p r) (norm_nonneg (2 * Real.pi * r))
  have hm_int_r : IntegrableOn (fun r : ℝ => (2 * Real.pi * r) * hm r) (Ioi 0) volume := by
    refine Integrable.mono hh_int_r ((measurable_const.mul measurable_id).mul hhm_meas).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r _
    rw [norm_mul (2 * Real.pi * r), norm_mul (2 * Real.pi * r)]
    exact mul_le_mul_of_nonneg_left (hnorm_m r) (norm_nonneg (2 * Real.pi * r))
  have hfun1 : (fun z : Pt => h (euclidNorm z)) =
      fun z => hp (euclidNorm z) - hm (euclidNorm z) := by
    ext z; exact hsplit (euclidNorm z)
  have hfun2 : (fun r : ℝ => (2 * Real.pi * r) * h r) =
      fun r => (2 * Real.pi * r) * hp r - (2 * Real.pi * r) * hm r := by
    ext r; rw [hsplit r]; ring
  rw [hfun1, hfun2, integral_sub hp_int hm_int, integral_sub hp_int_r hm_int_r,
      integral_radial_eq hhp_meas (fun r => le_max_right _ _),
      integral_radial_eq hhm_meas (fun r => le_max_right _ _)]

/-- Equivalence `(Fin 3 → Pt) ≃ Pt × Pt × Pt` preserving `unitSquarePi 3`. -/
private def fin3Equiv : (Fin 3 → Pt) ≃ Pt × Pt × Pt where
  toFun Y := (Y 0, Y 1, Y 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv Y := by
    funext i; fin_cases i <;> rfl
  right_inv p := rfl

private lemma measurable_fin3Equiv_symm : Measurable fin3Equiv.symm := by
  refine measurable_pi_lambda _ fun i => ?_
  fin_cases i
  · exact measurable_fst
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd

private lemma measurePreserving_fin3Equiv_symm :
    MeasurePreserving fin3Equiv.symm
      (unitSquareMeasure.prod (unitSquareMeasure.prod unitSquareMeasure))
      (unitSquarePi 3) := by
  refine ⟨measurable_fin3Equiv_symm, ?_⟩
  symm
  unfold unitSquarePi
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_fin3Equiv_symm (MeasurableSet.univ_pi hs)]
  have hpre : fin3Equiv.symm ⁻¹' Set.pi Set.univ s = s 0 ×ˢ (s 1 ×ˢ s 2) := by
    ext ⟨a, b, c⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod, fin3Equiv]
    constructor
    · intro h; exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩ i; fin_cases i <;> assumption
  rw [hpre, Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_three, mul_assoc]

/-- Exact 3-point change-of-variables formula on `unitSquarePi 3` for any bounded measurable
function of the canonical shape `canonShape (√n • Y 0) (√n • Y 1) (√n • Y 2)`. -/
theorem integral_unitSquarePi3_canonShape {b : BoxCert} {rho w : Array Int}
    (hb : ValidBox rho w b) {n : ℕ} (hn : 1 ≤ n) {Rbuf : ℝ}
    (hRbuf_nn : 0 ≤ Rbuf) (hRbuf_l1 : toR b.l1 ≤ Rbuf)
    (hRbuf_half : Rbuf / Real.sqrt (n : ℝ) ≤ 1 / 2)
    {H : ℝ → Pt → ℝ} (hH_meas : Measurable (fun p : ℝ × Pt => H p.1 p.2))
    (hH_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ L pt, (L, pt) ∈ boxRegion b → ‖H L pt‖ ≤ C) :
    ∫ Y : Fin 3 → Pt,
      (if Y 0 ∈ interiorBox (Rbuf / Real.sqrt (n : ℝ)) ∧
          canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
            (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
            (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2) ∈ boxRegion b
       then H (canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
            (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
            (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2)).1
          (canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
            (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
            (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2)).2
       else 0) ∂(unitSquarePi 3) =
    (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 * (1 / (n : ℝ) ^ 2) *
      ∫ L in (toR b.l0)..(toR b.l1),
        ∫ x in (toR b.x0)..(toR b.x1),
          ∫ y in (toR b.y0)..(toR b.y1),
            (4 * Real.pi * L ^ 3) * H L (x, y) := by
  obtain ⟨C, hC0, hC⟩ := hH_bdd
  set sqn := Real.sqrt (n : ℝ)
  have hsqn_pos : 0 < sqn := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hsqn_sq : sqn ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hl0_pos : 0 < toR b.l0 := toR_lt_toR hb.l0_pos |> fun h => by rwa [toR_zero] at h
  have hl0_lt_l1 : toR b.l0 < toR b.l1 := toR_lt_toR hb.l0_lt_l1
  have hx0_lt_x1 : toR b.x0 < toR b.x1 := toR_lt_toR hb.x0_lt_x1
  have hy0_nn : 0 ≤ toR b.y0 := toR_nonneg hb.y0_nonneg
  have hy0_lt_y1 : toR b.y0 < toR b.y1 := toR_lt_toR hb.y0_lt_y1
  let sh : Pt → Pt → Pt → ℝ × Pt := fun x₀ x₁ x₂ =>
    canonShape (sqn * x₀.1, sqn * x₀.2) (sqn * x₁.1, sqn * x₁.2) (sqn * x₂.1, sqn * x₂.2)
  let F : Pt → Pt → Pt → ℝ := fun x₀ x₁ x₂ =>
    if x₀ ∈ interiorBox (Rbuf / sqn) ∧ sh x₀ x₁ x₂ ∈ boxRegion b then
      H (sh x₀ x₁ x₂).1 (sh x₀ x₁ x₂).2
    else 0
  have hsh_meas : Measurable (fun p : Pt × Pt × Pt => sh p.1 p.2.1 p.2.2) := by
    have hsc : ∀ (g : (Pt × Pt × Pt) → Pt), Measurable g →
        Measurable (fun p => (sqn * (g p).1, sqn * (g p).2)) := fun g hg =>
      (measurable_const.mul (measurable_fst.comp hg)).prodMk
        (measurable_const.mul (measurable_snd.comp hg))
    exact measurable_canonShape.comp
      ((hsc Prod.fst measurable_fst).prodMk
        ((hsc (Prod.fst ∘ Prod.snd) (measurable_fst.comp measurable_snd)).prodMk
          (hsc (Prod.snd ∘ Prod.snd) (measurable_snd.comp measurable_snd))))
  have hF_meas : Measurable (fun p : Pt × Pt × Pt => F p.1 p.2.1 p.2.2) := by
    refine Measurable.ite
      (((measurableSet_interiorBox (Rbuf / sqn)).preimage measurable_fst).inter
        ((measurableSet_boxRegion b).preimage hsh_meas))
      (hH_meas.comp hsh_meas) measurable_const
  have hF_int : Integrable (fun p : Pt × Pt × Pt => F p.1 p.2.1 p.2.2)
      (unitSquareMeasure.prod (unitSquareMeasure.prod unitSquareMeasure)) :=
    Integrable.of_bound hF_meas.aestronglyMeasurable C (Eventually.of_forall fun p => by
      dsimp only [F]; split_ifs with h
      · exact hC _ _ h.2
      · rw [norm_zero]; exact hC0)
  -- Step 1: Unpack `unitSquarePi 3` to iterated integral over `x₀, x₁, x₂`
  have hpi3 : Measurable (fun Y : Fin 3 → Pt => (Y 0, Y 1, Y 2)) :=
    (measurable_pi_apply (0 : Fin 3)).prodMk
      ((measurable_pi_apply (1 : Fin 3)).prodMk (measurable_pi_apply (2 : Fin 3)))
  rw [← measurePreserving_fin3Equiv_symm.map_eq,
      integral_map measurable_fin3Equiv_symm.aemeasurable
        (by rw [measurePreserving_fin3Equiv_symm.map_eq]
            exact (hF_meas.comp hpi3).aestronglyMeasurable)]
  change ∫ p : Pt × Pt × Pt, F p.1 p.2.1 p.2.2 ∂(unitSquareMeasure.prod (unitSquareMeasure.prod unitSquareMeasure)) = _
  rw [MeasureTheory.integral_prod _ hF_int]
  have hF_int2 : ∀ x₀ : Pt, Integrable (fun q : Pt × Pt => F x₀ q.1 q.2)
      (unitSquareMeasure.prod unitSquareMeasure) := fun x₀ =>
    Integrable.of_bound
      (hF_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      C (Eventually.of_forall fun q => by
        dsimp only [F]; split_ifs with h
        · exact hC _ _ h.2
        · rw [norm_zero]; exact hC0)
  simp_rw [fun x₀ => MeasureTheory.integral_prod _ (hF_int2 x₀)]
  -- Define the inner `(x, y)` box integral `I L` using `Ioo`
  let I : ℝ → ℝ := fun L =>
    ∫ x in Ioo (toR b.x0) (toR b.x1), ∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y)
  have hI_eq_int : ∀ L : ℝ,
      I L = ∫ x in (toR b.x0)..(toR b.x1), ∫ y in (toR b.y0)..(toR b.y1), H L (x, y) := fun L => by
    dsimp only [I]
    rw [intervalIntegral.integral_of_le (le_of_lt hx0_lt_x1), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    rw [intervalIntegral.integral_of_le (le_of_lt hy0_lt_y1), MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hI_meas : Measurable I := by
    have h1 : StronglyMeasurable (fun p : ℝ × ℝ => ∫ y in Ioo (toR b.y0) (toR b.y1), H p.1 (p.2, y)) := by
      have hH' : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => H q.1.1 (q.1.2, q.2)) :=
        (hH_meas.comp ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable
      exact hH'.integral_prod_right'
    exact h1.integral_prod_right'.measurable
  have hI_bdd : ∀ L, toR b.l0 < L → L < toR b.l1 →
      ‖I L‖ ≤ C * (toR b.x1 - toR b.x0) * (toR b.y1 - toR b.y0) := by
    intro L hL0 hL1
    have hinner_bdd : ∀ x ∈ Ioo (toR b.x0) (toR b.x1),
        ‖∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y)‖ ≤ C * (toR b.y1 - toR b.y0) := by
      intro x hx
      have hy_int : IntegrableOn (fun y => H L (x, y)) (Ioo (toR b.y0) (toR b.y1)) volume := by
        have hvol_fin : volume (Ioo (toR b.y0) (toR b.y1)) < ⊤ := by
          rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
        haveI : IsFiniteMeasure (volume.restrict (Ioo (toR b.y0) (toR b.y1))) := ⟨by
          rw [Measure.restrict_apply_univ]; exact hvol_fin⟩
        refine Integrable.of_bound
          (hH_meas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
          C ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        exact hC L (x, y) ⟨hL0, hL1, hx.1, hx.2, hy.1, hy.2⟩
      calc ‖∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y)‖
          ≤ ∫ y in Ioo (toR b.y0) (toR b.y1), ‖H L (x, y)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ _ in Ioo (toR b.y0) (toR b.y1), C := by
            have hvol_fin : volume (Ioo (toR b.y0) (toR b.y1)) < ⊤ := by
              rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
            haveI : IsFiniteMeasure (volume.restrict (Ioo (toR b.y0) (toR b.y1))) := ⟨by
              rw [Measure.restrict_apply_univ]; exact hvol_fin⟩
            refine setIntegral_mono_on hy_int.norm (integrable_const C) measurableSet_Ioo fun y hy => ?_
            exact hC L (x, y) ⟨hL0, hL1, hx.1, hx.2, hy.1, hy.2⟩
        _ = C * (toR b.y1 - toR b.y0) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
                ENNReal.toReal_ofReal (by linarith)]; ring
    have hvol_x : volume (Ioo (toR b.x0) (toR b.x1)) < ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    haveI : IsFiniteMeasure (volume.restrict (Ioo (toR b.x0) (toR b.x1))) := ⟨by
      rw [Measure.restrict_apply_univ]; exact hvol_x⟩
    have hx_int : IntegrableOn (fun x => ∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y))
        (Ioo (toR b.x0) (toR b.x1)) volume := by
      have h1 : StronglyMeasurable (fun x : ℝ => ∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y)) := by
        have hH' : StronglyMeasurable (fun q : ℝ × ℝ => H L (q.1, q.2)) :=
          (hH_meas.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
        exact hH'.integral_prod_right'
      refine Integrable.of_bound h1.aestronglyMeasurable (C * (toR b.y1 - toR b.y0)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hinner_bdd x hx
    calc ‖I L‖
        ≤ ∫ x in Ioo (toR b.x0) (toR b.x1), ‖∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _ in Ioo (toR b.x0) (toR b.x1), C * (toR b.y1 - toR b.y0) :=
          setIntegral_mono_on hx_int.norm (integrable_const _) measurableSet_Ioo hinner_bdd
      _ = C * (toR b.x1 - toR b.x0) * (toR b.y1 - toR b.y0) := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
              ENNReal.toReal_ofReal (by linarith)]; ring
  -- Step 2: Inner `x₂`-integral for fixed `x₀ ∈ interiorBox (Rbuf / sqn)` and `x₁`
  have hinner_x2 : ∀ x₀ ∈ interiorBox (Rbuf / sqn), ∀ x₁ : Pt,
      ∫ x₂ : Pt, F x₀ x₁ x₂ ∂unitSquareMeasure =
        if toR b.l0 < sqn * euclidDist x₀ x₁ ∧ sqn * euclidDist x₀ x₁ < toR b.l1 then
          2 * (euclidDist x₀ x₁) ^ 2 * I (sqn * euclidDist x₀ x₁)
        else 0 := by
    intro x₀ hx₀ x₁
    set L := sqn * euclidDist x₀ x₁
    by_cases hL : toR b.l0 < L ∧ L < toR b.l1
    · rw [if_pos hL]
      have hL_pos : 0 < L := lt_trans hl0_pos hL.1
      have hd_pos : 0 < euclidDist x₀ x₁ := by
        have : 0 < sqn * euclidDist x₀ x₁ := hL_pos
        nlinarith [euclidDist_nonneg x₀ x₁]
      set r := L / sqn
      have hr_eq : r = euclidDist x₀ x₁ := by dsimp only [r, L]; field_simp [ne_of_gt hsqn_pos]
      have hr_pos : 0 < r := hr_eq.symm ▸ hd_pos
      set c := (x₁.1 - x₀.1) / r
      set s := (x₁.2 - x₀.2) / r
      have hcs : c ^ 2 + s ^ 2 = 1 := (canonShape_triEmbedInv hsqn_pos hL_pos (x₂ := x₀)).1
      -- Every `x₂` with `sh x₀ x₁ x₂ ∈ boxRegion b` satisfies `x₂ ∈ unitSquare`
      have hsupp_x2 : ∀ x₂ : Pt, sh x₀ x₁ x₂ ∈ boxRegion b → x₂ ∈ unitSquare := by
        intro x₂ hbox
        have hql := boxRegion_mem_quarterLens hb hbox
        have hed := canonShape_strict_edges hql.1 hql.2
        have h02_lt : euclidDist (sqn * x₀.1, sqn * x₀.2) (sqn * x₂.1, sqn * x₂.2) <
            euclidDist (sqn * x₀.1, sqn * x₀.2) (sqn * x₁.1, sqn * x₁.2) := hed.1.trans hed.2
        have hsc_dist : ∀ a c' : Pt, euclidDist (sqn * a.1, sqn * a.2) (sqn * c'.1, sqn * c'.2) =
            sqn * euclidDist a c' := fun a c' => by
          unfold euclidDist sqDist
          have hsq : (sqn * a.1 - sqn * c'.1) ^ 2 + (sqn * a.2 - sqn * c'.2) ^ 2 =
              sqn ^ 2 * ((a.1 - c'.1) ^ 2 + (a.2 - c'.2) ^ 2) := by ring
          dsimp only; rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hsqn_pos)]
        rw [hsc_dist, hsc_dist] at h02_lt
        have hd02 : euclidDist x₀ x₂ ≤ Rbuf / sqn := by
          have h1 : sqn * euclidDist x₀ x₂ < toR b.l1 := lt_trans h02_lt hL.2
          have h2 : sqn * euclidDist x₀ x₂ ≤ Rbuf := (le_of_lt h1).trans hRbuf_l1
          exact (le_div_iff₀ hsqn_pos).mpr (by linarith)
        have hmem_disk : x₂ ∈ disk x₀ (Rbuf / sqn) := by
          rw [disk, Set.mem_setOf_eq, ← euclidDist_sq, euclidDist_symm]
          exact pow_le_pow_left₀ (euclidDist_nonneg _ _) hd02 2
        exact disk_subset_unitSquare hx₀ (div_nonneg hRbuf_nn (le_of_lt hsqn_pos)) le_rfl hmem_disk
      -- Replace `unitSquareMeasure` by full Lebesgue `volume`
      have hvol_eq : ∫ x₂ : Pt, F x₀ x₁ x₂ ∂unitSquareMeasure = ∫ x₂ : Pt, F x₀ x₁ x₂ ∂volume := by
        rw [← restrict_unitSquare_eq]
        refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x₂ hx₂ => ?_
        dsimp only [F]
        rw [if_neg fun h => hx₂ (hsupp_x2 x₂ h.2)]
      rw [hvol_eq]
      -- Express `F x₀ x₁ x₂ = h (triEmbedInv x₀ c s false r x₂)`
      let h : Pt → ℝ := fun v =>
        if v.1 ∈ Ioo (toR b.x0) (toR b.x1) ∧ |v.2| ∈ Ioo (toR b.y0) (toR b.y1) then
          H L (v.1, |v.2|)
        else 0
      have hh_meas : Measurable h := by
        unfold h
        have hS1 : MeasurableSet {v : Pt | v.1 ∈ Ioo (toR b.x0) (toR b.x1)} :=
          measurableSet_Ioo.preimage measurable_fst
        have hS2 : MeasurableSet {v : Pt | |v.2| ∈ Ioo (toR b.y0) (toR b.y1)} :=
          measurableSet_Ioo.preimage (continuous_abs.measurable.comp measurable_snd)
        refine Measurable.ite (hS1.inter hS2) ?_ measurable_const
        exact hH_meas.comp (measurable_const.prodMk
          (measurable_fst.prodMk (continuous_abs.measurable.comp measurable_snd)))
      have hF_eq : (fun x₂ : Pt => F x₀ x₁ x₂) = fun x₂ => h (triEmbedInv x₀ c s false r x₂) := by
        ext x₂
        have hsh_eq := (canonShape_triEmbedInv hsqn_pos hL_pos (x₂ := x₂)).2
        dsimp only [F, h, sh]
        refine if_congr ?_ (by rw [hsh_eq]) rfl
        rw [hsh_eq]
        simp only [hx₀, true_and, boxRegion, Set.mem_setOf_eq, Set.mem_Ioo, and_assoc]
        exact ⟨fun h => h.2.2, fun h => ⟨hL.1, hL.2, h⟩⟩
      rw [hF_eq, integral_comp_triEmbedInv x₀ hcs false hr_pos hh_meas.aestronglyMeasurable, hr_eq]
      -- Compute `∫ v : Pt, h v ∂volume = 2 * I L`
      have hbox_meas : MeasurableSet (Ioo (toR b.x0) (toR b.x1) ×ˢ Ioo (-toR b.y1) (toR b.y1)) :=
        measurableSet_Ioo.prod measurableSet_Ioo
      have hbox_fin : volume (Ioo (toR b.x0) (toR b.x1) ×ˢ Ioo (-toR b.y1) (toR b.y1)) < ⊤ := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hh_int : Integrable h volume := by
        have hdom : Integrable ((Ioo (toR b.x0) (toR b.x1) ×ˢ Ioo (-toR b.y1) (toR b.y1)).indicator fun _ : Pt => C) volume :=
          (integrableOn_const hbox_fin.ne).integrable_indicator hbox_meas
        refine hdom.mono' hh_meas.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
        dsimp only [h]
        split_ifs with hv
        · have hv_mem : v ∈ Ioo (toR b.x0) (toR b.x1) ×ˢ Ioo (-toR b.y1) (toR b.y1) := by
            refine ⟨hv.1, ?_⟩
            have hlt : |v.2| < toR b.y1 := hv.2.2
            exact ⟨by linarith [(abs_lt.mp hlt).1], (abs_lt.mp hlt).2⟩
          rw [Set.indicator_of_mem hv_mem]
          exact hC L (v.1, |v.2|) ⟨hL.1, hL.2, hv.1.1, hv.1.2, hv.2.1, hv.2.2⟩
        · rw [norm_zero]
          by_cases hvm : v ∈ Ioo (toR b.x0) (toR b.x1) ×ˢ Ioo (-toR b.y1) (toR b.y1)
          · rw [Set.indicator_of_mem hvm]; exact hC0
          · rw [Set.indicator_of_notMem hvm]
      have hh_val : ∫ v : Pt, h v ∂volume = 2 * I L := by
        rw [show (volume : Measure Pt) = volume.prod volume from rfl, MeasureTheory.integral_prod _ hh_int]
        have hx_eval : ∀ x : ℝ, (∫ y : ℝ, h (x, y) ∂volume) =
            if x ∈ Ioo (toR b.x0) (toR b.x1) then
              2 * ∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y)
            else 0 := by
          intro x
          by_cases hx : x ∈ Ioo (toR b.x0) (toR b.x1)
          · rw [if_pos hx]
            have hfun : (fun y : ℝ => h (x, y)) =
                fun y => (if y ∈ Ioo (toR b.y0) (toR b.y1) then H L (x, y) else 0) +
                  (if y ∈ Ioo (-toR b.y1) (-toR b.y0) then H L (x, -y) else 0) := by
              ext y; dsimp only [h]
              simp only [hx, true_and, Set.mem_Ioo]
              by_cases hy0 : 0 ≤ y
              · rw [abs_of_nonneg hy0]
                have hneg : ¬ (-toR b.y1 < y ∧ y < -toR b.y0) := fun ⟨_, h2⟩ => by linarith
                rw [if_neg hneg, add_zero]
              · push Not at hy0
                rw [abs_of_neg hy0]
                have hpos : ¬ (toR b.y0 < y ∧ y < toR b.y1) := fun ⟨h1, _⟩ => by linarith
                rw [if_neg hpos, zero_add]
                refine if_congr ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩ rfl rfl
            have hint_pos : Integrable (fun y : ℝ => if y ∈ Ioo (toR b.y0) (toR b.y1) then H L (x, y) else 0) volume := by
              have hfin : volume (Ioo (toR b.y0) (toR b.y1)) < ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
              refine ((integrableOn_const (C := C) hfin.ne).integrable_indicator measurableSet_Ioo).mono' ?_ (Eventually.of_forall fun y => ?_)
              · exact (Measurable.ite measurableSet_Ioo
                  (hH_meas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
                  measurable_const).aestronglyMeasurable
              · split_ifs with hy
                · rw [Set.indicator_of_mem hy]; exact hC L (x, y) ⟨hL.1, hL.2, hx.1, hx.2, hy.1, hy.2⟩
                · rw [norm_zero, Set.indicator_of_notMem hy]
            have hint_neg : Integrable (fun y : ℝ => if y ∈ Ioo (-toR b.y1) (-toR b.y0) then H L (x, -y) else 0) volume := by
              have hfin : volume (Ioo (-toR b.y1) (-toR b.y0)) < ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
              refine ((integrableOn_const (C := C) hfin.ne).integrable_indicator measurableSet_Ioo).mono' ?_ (Eventually.of_forall fun y => ?_)
              · exact (Measurable.ite measurableSet_Ioo
                  (hH_meas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_neg)))
                  measurable_const).aestronglyMeasurable
              · split_ifs with hy
                · rw [Set.indicator_of_mem hy]; exact hC L (x, -y) ⟨hL.1, hL.2, hx.1, hx.2, by linarith [hy.2], by linarith [hy.1]⟩
                · rw [norm_zero, Set.indicator_of_notMem hy]
            rw [hfun, integral_add hint_pos hint_neg]
            have hneg_eq : (∫ y : ℝ, (if y ∈ Ioo (-toR b.y1) (-toR b.y0) then H L (x, -y) else 0) ∂volume) =
                ∫ y : ℝ, (if y ∈ Ioo (toR b.y0) (toR b.y1) then H L (x, y) else 0) ∂volume := by
              rw [← MeasureTheory.integral_neg_eq_self (fun y => if y ∈ Ioo (-toR b.y1) (-toR b.y0) then H L (x, -y) else 0)]
              refine integral_congr_ae (Eventually.of_forall fun y => ?_)
              simp only [neg_neg, Set.mem_Ioo]
              exact if_congr ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩ rfl rfl
            rw [hneg_eq, ← two_mul]
            congr 1
            rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            dsimp only
            by_cases hy : y ∈ Ioo (toR b.y0) (toR b.y1)
            · rw [if_pos hy, Set.indicator_of_mem hy]
            · rw [if_neg hy, Set.indicator_of_notMem hy]
          · rw [if_neg hx]
            have h0 : (fun y : ℝ => h (x, y)) = fun _ => 0 := by ext y; dsimp only [h]; rw [if_neg fun hp => hx hp.1]
            rw [h0, integral_zero]
        simp_rw [hx_eval]
        have hind : (fun x : ℝ => if x ∈ Ioo (toR b.x0) (toR b.x1) then
              2 * ∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y) else 0) =
            (Ioo (toR b.x0) (toR b.x1)).indicator (fun x => 2 * ∫ y in Ioo (toR b.y0) (toR b.y1), H L (x, y)) := by
          ext x; by_cases hx : x ∈ Ioo (toR b.x0) (toR b.x1)
          · rw [if_pos hx, Set.indicator_of_mem hx]
          · rw [if_neg hx, Set.indicator_of_notMem hx]
        rw [hind, MeasureTheory.integral_indicator measurableSet_Ioo, integral_const_mul]
      rw [hh_val]; ring
    · rw [if_neg hL]
      have h0 : ∀ x₂ : Pt, F x₀ x₁ x₂ = 0 := fun x₂ => by
        dsimp only [F]
        refine if_neg fun h => hL ?_
        have hshL : (sh x₀ x₁ x₂).1 = L := by
          dsimp only [sh, canonShape, L]; unfold euclidDist sqDist
          have hsq : (sqn * x₀.1 - sqn * x₁.1) ^ 2 + (sqn * x₀.2 - sqn * x₁.2) ^ 2 =
              sqn ^ 2 * ((x₀.1 - x₁.1) ^ 2 + (x₀.2 - x₁.2) ^ 2) := by ring
          dsimp only; rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hsqn_pos)]
        exact ⟨hshL ▸ h.2.1, hshL ▸ h.2.2.1⟩
      simp_rw [h0]; simp
  -- Step 3: Middle `x₁`-integral for fixed `x₀ ∈ interiorBox (Rbuf / sqn)`
  let M : ℝ := C * (toR b.x1 - toR b.x0) * (toR b.y1 - toR b.y0)
  have hM0 : 0 ≤ M := mul_nonneg (mul_nonneg hC0 (by linarith)) (by linarith)
  let g : ℝ → ℝ := fun ρ =>
    if toR b.l0 < sqn * ρ ∧ sqn * ρ < toR b.l1 then 2 * ρ ^ 2 * I (sqn * ρ) else 0
  have hg_meas : Measurable g := by
    unfold g
    refine Measurable.ite
      ((measurableSet_lt measurable_const (measurable_const.mul measurable_id)).inter
        (measurableSet_lt (measurable_const.mul measurable_id) measurable_const))
      ((measurable_const.mul (measurable_id.pow_const 2)).mul (hI_meas.comp (measurable_const.mul measurable_id)))
      measurable_const
  have hmid_x1 : ∀ x₀ ∈ interiorBox (Rbuf / sqn),
      ∫ x₁ : Pt, (∫ x₂ : Pt, F x₀ x₁ x₂ ∂unitSquareMeasure) ∂unitSquareMeasure =
        (1 / (n : ℝ) ^ 2) * ∫ L in (toR b.l0)..(toR b.l1), (4 * Real.pi * L ^ 3) * I L := by
    intro x₀ hx₀
    simp_rw [hinner_x2 x₀ hx₀]
    change ∫ x₁ : Pt, g (euclidDist x₀ x₁) ∂unitSquareMeasure = _
    have hsupp_x1 : ∀ x₁ : Pt, x₁ ∉ unitSquare → g (euclidDist x₀ x₁) = 0 := by
      intro x₁ hx₁
      dsimp only [g]
      refine if_neg fun hL => hx₁ ?_
      have hd01 : euclidDist x₀ x₁ ≤ Rbuf / sqn :=
        (le_div_iff₀ hsqn_pos).mpr (by linarith [le_of_lt hL.2, hRbuf_l1])
      have hmem : x₁ ∈ disk x₀ (Rbuf / sqn) := by
        rw [disk, Set.mem_setOf_eq, ← euclidDist_sq, euclidDist_symm]
        exact pow_le_pow_left₀ (euclidDist_nonneg _ _) hd01 2
      exact disk_subset_unitSquare hx₀ (div_nonneg hRbuf_nn (le_of_lt hsqn_pos)) le_rfl hmem
    have hvol1 : ∫ x₁ : Pt, g (euclidDist x₀ x₁) ∂unitSquareMeasure =
        ∫ x₁ : Pt, g (euclidDist x₀ x₁) ∂volume := by
      rw [← restrict_unitSquare_eq]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp_x1
    rw [hvol1]
    -- Translate `x₁ = x₀ + z` so `euclidDist x₀ (x₀ + z) = euclidNorm z`
    have hmeas_en : Measurable (euclidNorm : Pt → ℝ) := by unfold euclidNorm; fun_prop
    have hshift : ∫ x₁ : Pt, g (euclidDist x₀ x₁) ∂volume = ∫ z : Pt, g (euclidNorm z) ∂volume := by
      have heq : (fun x₁ : Pt => g (euclidDist x₀ x₁)) = fun x₁ => g (euclidNorm (x₁.1 - x₀.1, x₁.2 - x₀.2)) := by
        ext x₁; congr 1; unfold euclidDist euclidNorm sqDist; congr 1; ring
      rw [heq]
      have hsub := integral_comp_triEmbedInv x₀ (c := 1) (s := 0) (by norm_num) false (r := 1) zero_lt_one
        (hg_meas.comp hmeas_en).aestronglyMeasurable
      have hinv_eq : ∀ z : Pt, triEmbedInv x₀ 1 0 false 1 z = (z.1 - x₀.1, z.2 - x₀.2) := fun z => by
        unfold triEmbedInv; simp
      simp_rw [hinv_eq, one_pow, one_mul] at hsub
      exact hsub
    rw [hshift]
    -- Integrability for signed radial formula
    have hl1_pos : 0 < toR b.l1 := lt_trans hl0_pos hl0_lt_l1
    have hB : 0 ≤ 2 * (toR b.l1 / sqn) ^ 2 * M := by positivity
    have hg_bdd : ∀ ρ : ℝ, ‖g ρ‖ ≤ 2 * (toR b.l1 / sqn) ^ 2 * M := by
      intro ρ; dsimp only [g]
      split_ifs with hL
      · have hρ_nn : 0 ≤ ρ := by nlinarith [hl0_pos, hL.1]
        have hρ_le : ρ ≤ toR b.l1 / sqn := (le_div_iff₀ hsqn_pos).mpr (by linarith [hL.2])
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            Real.norm_of_nonneg (sq_nonneg ρ)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ_nn hρ_le 2) (by norm_num))
          (hI_bdd _ hL.1 hL.2) (norm_nonneg _) (by positivity)
      · rw [norm_zero]; exact hB
    have hdisk_meas : MeasurableSet (disk (0, 0) (toR b.l1 / sqn)) :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    have hdisk_fin : volume (disk (0, 0) (toR b.l1 / sqn)) < ⊤ := by
      rw [volume_disk _ (div_nonneg (le_of_lt hl1_pos) (le_of_lt hsqn_pos))]
      exact ENNReal.ofReal_lt_top
    have hg_int_z : Integrable (fun z : Pt => g (euclidNorm z)) volume := by
      refine ((integrableOn_const (C := 2 * (toR b.l1 / sqn) ^ 2 * M) hdisk_fin.ne).integrable_indicator hdisk_meas).mono'
        (hg_meas.comp hmeas_en).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ disk (0, 0) (toR b.l1 / sqn)
      · rw [Set.indicator_of_mem hz]; exact hg_bdd (euclidNorm z)
      · rw [Set.indicator_of_notMem hz]
        have hgt : toR b.l1 / sqn < euclidNorm z := by
          by_contra hle; push Not at hle; apply hz
          rw [disk, Set.mem_setOf_eq, sqDist]
          have h1 : (z.1 - 0) ^ 2 + (z.2 - 0) ^ 2 = (euclidNorm z) ^ 2 := by
            unfold euclidNorm; rw [Real.sq_sqrt (by positivity)]; ring
          rw [h1]; exact pow_le_pow_left₀ (by unfold euclidNorm; exact Real.sqrt_nonneg _) hle 2
        have hg0 : g (euclidNorm z) = 0 := by
          dsimp only [g]; refine if_neg fun hL => ?_
          have := (div_lt_iff₀ hsqn_pos).mp hgt; linarith [hL.2]
        rw [hg0, norm_zero]
    have hg_int_r : IntegrableOn (fun ρ : ℝ => (2 * Real.pi * ρ) * g ρ) (Ioi 0) volume := by
      have hfin : volume (Ioo (toR b.l0 / sqn) (toR b.l1 / sqn)) < ⊤ := by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      have hdom : IntegrableOn
          ((Ioo (toR b.l0 / sqn) (toR b.l1 / sqn)).indicator fun _ : ℝ =>
            (2 * Real.pi * (toR b.l1 / sqn)) * (2 * (toR b.l1 / sqn) ^ 2 * M)) (Ioi 0) volume :=
        ((integrableOn_const hfin.ne).integrable_indicator measurableSet_Ioo).integrableOn
      refine hdom.mono' ((measurable_const.mul measurable_id).mul hg_meas).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      have hρ_pos : 0 < ρ := hρ
      by_cases hmem : ρ ∈ Ioo (toR b.l0 / sqn) (toR b.l1 / sqn)
      · rw [Set.indicator_of_mem hmem, norm_mul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul (by nlinarith [Real.pi_pos, hmem.2]) (hg_bdd ρ) (norm_nonneg _) (by positivity)
      · rw [Set.indicator_of_notMem hmem]
        have hg0 : g ρ = 0 := by
          dsimp only [g]; refine if_neg fun hL => hmem ⟨(div_lt_iff₀ hsqn_pos).mpr (by linarith [hL.1]),
            (lt_div_iff₀ hsqn_pos).mpr (by linarith [hL.2])⟩
        rw [hg0, mul_zero, norm_zero]
    rw [integral_radial_eq_signed hg_meas hg_int_z hg_int_r]
    -- Restrict `Ioi 0` to `Ioo (l0 / sqn) (l1 / sqn)` and change variable `L = sqn * ρ`
    have hrad_eq : ∫ ρ in Ioi (0 : ℝ), (2 * Real.pi * ρ) * g ρ =
        ∫ ρ in Ioo (toR b.l0 / sqn) (toR b.l1 / sqn), (2 * Real.pi * ρ) * (2 * ρ ^ 2 * I (sqn * ρ)) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← MeasureTheory.integral_indicator measurableSet_Ioo]
      refine integral_congr_ae (Eventually.of_forall fun ρ => ?_)
      by_cases hmem : ρ ∈ Ioo (toR b.l0 / sqn) (toR b.l1 / sqn)
      · have hpos : ρ ∈ Ioi (0 : ℝ) := lt_trans (div_pos hl0_pos hsqn_pos) hmem.1
        rw [Set.indicator_of_mem hpos, Set.indicator_of_mem hmem]
        dsimp only [g]
        rw [if_pos ⟨by nlinarith [(div_lt_iff₀ hsqn_pos).mp hmem.1], by nlinarith [(lt_div_iff₀ hsqn_pos).mp hmem.2]⟩]
      · rw [Set.indicator_of_notMem hmem]
        by_cases hpos : ρ ∈ Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem hpos]
          have hg0 : g ρ = 0 := by
            dsimp only [g]; refine if_neg fun hL => hmem ⟨(div_lt_iff₀ hsqn_pos).mpr (by linarith [hL.1]),
              (lt_div_iff₀ hsqn_pos).mpr (by linarith [hL.2])⟩
          rw [hg0, mul_zero]
        · rw [Set.indicator_of_notMem hpos]
    rw [hrad_eq, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (div_le_div_of_nonneg_right (le_of_lt hl0_lt_l1) (le_of_lt hsqn_pos))]
    have hrew : (fun ρ : ℝ => (2 * Real.pi * ρ) * (2 * ρ ^ 2 * I (sqn * ρ))) =
        fun ρ => (1 / (n : ℝ) ^ 2) * (sqn * ((4 * Real.pi * (sqn * ρ) ^ 3) * I (sqn * ρ))) := by
      ext ρ
      set y := I (sqn * ρ)
      have hsq4 : sqn ^ 4 = (n : ℝ) ^ 2 := by
        calc sqn ^ 4 = (sqn ^ 2) ^ 2 := by ring
          _ = (n : ℝ) ^ 2 := by rw [hsqn_sq]
      rw [← hsq4]
      field_simp [ne_of_gt hsqn_pos]
      ring
    rw [hrew, intervalIntegral.integral_const_mul]
    congr 1
    have hcomp := intervalIntegral.integral_comp_mul_left
      (f := fun L => (4 * Real.pi * L ^ 3) * I L) (a := toR b.l0 / sqn) (b := toR b.l1 / sqn) (ne_of_gt hsqn_pos)
    rw [mul_div_cancel₀ _ (ne_of_gt hsqn_pos), mul_div_cancel₀ _ (ne_of_gt hsqn_pos), smul_eq_mul] at hcomp
    rw [intervalIntegral.integral_const_mul, hcomp, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsqn_pos), one_mul]
  -- Step 4: Outer `x₀`-integral over `interiorBox (Rbuf / sqn)`
  have houter : ∀ x₀ : Pt,
      (∫ x₁ : Pt, (∫ x₂ : Pt, F x₀ x₁ x₂ ∂unitSquareMeasure) ∂unitSquareMeasure) =
        if x₀ ∈ interiorBox (Rbuf / sqn) then
          (1 / (n : ℝ) ^ 2) * ∫ L in (toR b.l0)..(toR b.l1), (4 * Real.pi * L ^ 3) * I L
        else 0 := by
    intro x₀
    by_cases hx₀ : x₀ ∈ interiorBox (Rbuf / sqn)
    · rw [if_pos hx₀]; exact hmid_x1 x₀ hx₀
    · rw [if_neg hx₀]
      have h0 : ∀ x₁ x₂ : Pt, F x₀ x₁ x₂ = 0 := fun x₁ x₂ => by dsimp only [F]; rw [if_neg fun h => hx₀ h.1]
      simp_rw [h0]; simp
  simp_rw [houter]
  have hconst_int : ∫ x₀ : Pt, (if x₀ ∈ interiorBox (Rbuf / sqn) then
        (1 / (n : ℝ) ^ 2) * ∫ L in (toR b.l0)..(toR b.l1), (4 * Real.pi * L ^ 3) * I L
      else 0) ∂unitSquareMeasure =
      (unitSquareMeasure (interiorBox (Rbuf / sqn))).toReal *
        ((1 / (n : ℝ) ^ 2) * ∫ L in (toR b.l0)..(toR b.l1), (4 * Real.pi * L ^ 3) * I L) := by
    have hfun : (fun x₀ : Pt => if x₀ ∈ interiorBox (Rbuf / sqn) then
          (1 / (n : ℝ) ^ 2) * ∫ L in (toR b.l0)..(toR b.l1), (4 * Real.pi * L ^ 3) * I L else 0) =
        fun x₀ => ((1 / (n : ℝ) ^ 2) * ∫ L in (toR b.l0)..(toR b.l1), (4 * Real.pi * L ^ 3) * I L) *
          (if x₀ ∈ interiorBox (Rbuf / sqn) then (1 : ℝ) else 0) := by
      ext x₀; split_ifs <;> ring
    rw [hfun, integral_const_mul, integral_indicator_one_unitSquare (measurableSet_interiorBox _), mul_comm]
  rw [hconst_int, unitSquareMeasure_interiorBox (div_nonneg hRbuf_nn (le_of_lt hsqn_pos)) hRbuf_half,
      ← mul_assoc, show 2 * (Rbuf / sqn) = 2 * Rbuf / sqn by ring]
  congr 1
  refine intervalIntegral.integral_congr fun L _ => ?_
  rw [hI_eq_int L, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← intervalIntegral.integral_const_mul]

end

end BHHBounds.Dual
