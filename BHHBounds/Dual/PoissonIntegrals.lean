import BHHBounds.Cert.AllShards
import BHHBounds.Cert.GeomSound

/-!
# Poisson-Limit Dual Integrals and Step-Potential Algebra

Defines the exact real-valued Poisson-limit integrals for the 2-factor + disjoint telescoping
mutual-triangle moat dual, bridging `BHHBounds.Dual.Expectation` (finite-`n` convergence) and
`BHHBounds.Cert.IntegralSound` (exact fixed-point verification):
1. Structural validity predicates (`ValidStepPot`, `ValidBox`, `PairwiseDisjointBoxes`) and
   proofs that the fast `native_decide` boolean checkers in `AllShards.lean` imply them.
2. Step potential `stepPot rho w r` together with its 1D and 2D Abel-summation identities and
   comparison with `evalStepPot`.
3. 1D base Poisson integral `baseIntegral rho w = baseTerm1 - basePenMarg - basePenInter`.
4. Triangle-moat Poisson integral `boxIntegral rho w act b` and `trianglePlanIntegral`, parameterized
   by an arbitrary boolean level-activation mask `act : BoxCert → Int → Int → Int → Bool`.
-/

open MeasureTheory Set Real
open BHHBounds.Geometry
open BHHBounds.Cert

namespace BHHBounds.Dual

noncomputable section

/-! ## Section 1: Structural Validity Predicates & Boolean Soundness -/

/-- A valid step potential `(rho, w)` has `rho.size = w.size > 0`, `rho[0] = 0`, `w[0] ≥ 0`,
`rho` strictly increasing, and `w` nondecreasing. -/
structure ValidStepPot (rho w : Array Int) : Prop where
  size_pos : 0 < rho.size
  size_eq : w.size = rho.size
  rho_zero : rho.getD 0 0 = 0
  w_zero_nonneg : 0 ≤ w.getD 0 0
  rho_strictMono : ∀ i : Nat, i + 1 < rho.size → rho.getD i 0 < rho.getD (i + 1) 0
  w_mono : ∀ i : Nat, i + 1 < rho.size → w.getD i 0 ≤ w.getD (i + 1) 0

lemma ValidStepPot.rho_lt_of_lt {rho w : Array Int} (h : ValidStepPot rho w)
    {i j : Nat} (hij : i < j) (hj : j < rho.size) :
    rho.getD i 0 < rho.getD j 0 := by
  induction j with
  | zero => omega
  | succ k ih =>
    by_cases hEq : i = k
    · subst hEq; exact h.rho_strictMono i hj
    · exact (ih (by omega) (by omega)).trans (h.rho_strictMono k hj)

lemma ValidStepPot.rho_le_of_le {rho w : Array Int} (h : ValidStepPot rho w)
    {i j : Nat} (hij : i ≤ j) (hj : j < rho.size) :
    rho.getD i 0 ≤ rho.getD j 0 := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (h.rho_lt_of_lt hlt hj)

lemma ValidStepPot.rho_nonneg {rho w : Array Int} (h : ValidStepPot rho w)
    {i : Nat} (hi : i < rho.size) : 0 ≤ rho.getD i 0 := by
  have := h.rho_le_of_le (Nat.zero_le i) hi
  rw [h.rho_zero] at this; exact this

lemma ValidStepPot.w_le_of_le {rho w : Array Int} (h : ValidStepPot rho w)
    {i j : Nat} (hij : i ≤ j) (hj : j < rho.size) :
    w.getD i 0 ≤ w.getD j 0 := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst hi; exact le_rfl
  | succ k ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega) (by omega)).trans (h.w_mono k hj)

lemma ValidStepPot.w_nonneg {rho w : Array Int} (h : ValidStepPot rho w)
    {i : Nat} (hi : i < rho.size) : 0 ≤ w.getD i 0 :=
  h.w_zero_nonneg.trans (h.w_le_of_le (Nat.zero_le i) hi)

private lemma checkMonotoneAux_sound {rho w : Array Int} (i : Nat)
    (h : checkMonotoneAux rho w i = true) :
    ∀ j : Nat, i ≤ j → j + 1 < rho.size →
      rho.getD j 0 < rho.getD (j + 1) 0 ∧ w.getD j 0 ≤ w.getD (j + 1) 0 := by
  induction hn : rho.size - i generalizing i with
  | zero =>
    intro j hij hj; omega
  | succ m ih =>
    intro j hij hj
    rw [checkMonotoneAux] at h
    have hi_lt : i + 1 < rho.size := by omega
    rw [if_neg (by omega)] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact h.1
    · exact ih (i + 1) h.2 (by omega) j (by omega) hj

lemma validStepPot_of_bool {rho w : Array Int} (h : isValidStepPotBool rho w = true) :
    ValidStepPot rho w := by
  unfold isValidStepPotBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hmono := checkMonotoneAux_sound 0 h.2
  exact {
    size_pos := h.1.1.1.1
    size_eq := h.1.1.1.2
    rho_zero := h.1.1.2
    w_zero_nonneg := h.1.2
    rho_strictMono := fun i hi => (hmono i (Nat.zero_le i) hi).1
    w_mono := fun i hi => (hmono i (Nat.zero_le i) hi).2
  }

/-- Inductive validity predicate for a box's telescoping level list `[(r_1, y_1), ...]`. -/
def LevelsValid (pi01 rPrev yPrev : Int) : List (Int × Int) → Prop
  | [] => True
  | (rj, yj) :: rest =>
    rPrev < rj ∧ yPrev < yj ∧ 2 * (pi01 + yj) ≤ rj ∧ LevelsValid pi01 rj yj rest

lemma levelsValid_of_bool {pi01 rPrev yPrev : Int} {lvls : List (Int × Int)}
    (h : levelsValidBool pi01 rPrev yPrev lvls = true) :
    LevelsValid pi01 rPrev yPrev lvls := by
  induction lvls generalizing rPrev yPrev with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨rj, yj⟩
    unfold levelsValidBool at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, ih h.2⟩

/-- A valid certified triangle box lies strictly inside `quarterLens`, satisfies
`evalStepPot rho w (b.l1 - 1) = evalStepPot rho w b.l1`, and has valid telescoping levels. -/
structure ValidBox (rho w : Array Int) (b : BoxCert) : Prop where
  l0_pos : 0 < b.l0
  l0_lt_l1 : b.l0 < b.l1
  x0_nonneg : 0 ≤ b.x0
  x0_lt_x1 : b.x0 < b.x1
  x1_le_half : b.x1 ≤ 500000
  y0_nonneg : 0 ≤ b.y0
  y0_lt_y1 : b.y0 < b.y1
  in_quarterLens : (S - b.x0) * (S - b.x0) + b.y1 * b.y1 ≤ S * S
  pi01_eq : evalStepPot rho w (b.l1 - 1) = evalStepPot rho w b.l1
  levels_valid : LevelsValid (evalStepPot rho w b.l1) b.l1 0 b.levels

lemma validBox_of_bool {rho w : Array Int} {b : BoxCert}
    (h : isValidBoxBool rho w b = true) : ValidBox rho w b := by
  unfold isValidBoxBool at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact {
    l0_pos := h.1.1.1.1.1.1.1.1.1
    l0_lt_l1 := h.1.1.1.1.1.1.1.1.2
    x0_nonneg := h.1.1.1.1.1.1.1.2
    x0_lt_x1 := h.1.1.1.1.1.1.2
    x1_le_half := h.1.1.1.1.1.2
    y0_nonneg := h.1.1.1.1.2
    y0_lt_y1 := h.1.1.1.2
    in_quarterLens := h.1.1.2
    pi01_eq := h.1.2
    levels_valid := levelsValid_of_bool h.2
  }

/-- Open 3D parameter box `(l0/S, l1/S) × (x0/S, x1/S) × (y0/S, y1/S)` of a `BoxCert`. -/
def boxRegion (b : BoxCert) : Set (ℝ × Pt) :=
  {p | toR b.l0 < p.1 ∧ p.1 < toR b.l1 ∧
       toR b.x0 < p.2.1 ∧ p.2.1 < toR b.x1 ∧
       toR b.y0 < p.2.2 ∧ p.2.2 < toR b.y1}

lemma boxRegion_mem_quarterLens {rho w : Array Int} {b : BoxCert} (hb : ValidBox rho w b)
    {L : ℝ} {pt : Pt} (hmem : (L, pt) ∈ boxRegion b) :
    0 < L ∧ pt ∈ quarterLens := by
  rcases hmem with ⟨hl0, _, hx0, hx1, hy0, hy1⟩
  have hL0 : 0 < L := lt_of_le_of_lt (toR_nonneg (le_of_lt hb.l0_pos)) hl0
  have hx_pos : 0 < pt.1 := lt_of_le_of_lt (toR_nonneg hb.x0_nonneg) hx0
  have hx_half : pt.1 < 1 / 2 := by
    have h1 : toR b.x1 ≤ toR 500000 := toR_le_toR hb.x1_le_half
    have h2 : toR 500000 = 1 / 2 := by unfold toR S; norm_num
    linarith
  have hy_pos : 0 < pt.2 := lt_of_le_of_lt (toR_nonneg hb.y0_nonneg) hy0
  have hcirc : (1 - pt.1) ^ 2 + pt.2 ^ 2 < 1 := by
    have h1x : 0 < 1 - pt.1 := by linarith
    have h1x_lt : 1 - pt.1 < 1 - toR b.x0 := by linarith
    have hsq1 : (1 - pt.1) ^ 2 < (1 - toR b.x0) ^ 2 := by nlinarith
    have hsq2 : pt.2 ^ 2 < (toR b.y1) ^ 2 := by nlinarith
    have hbound : (1 - toR b.x0) ^ 2 + (toR b.y1) ^ 2 ≤ 1 := by
      have hInt : (((S - b.x0) * (S - b.x0) + b.y1 * b.y1 : Int) : ℝ) / (S : ℝ) ^ 2 ≤
          ((S * S : Int) : ℝ) / (S : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by exact_mod_cast hb.in_quarterLens) (sq_nonneg _)
      have hLHS : (((S - b.x0) * (S - b.x0) + b.y1 * b.y1 : Int) : ℝ) / (S : ℝ) ^ 2 =
          (1 - toR b.x0) ^ 2 + (toR b.y1) ^ 2 := by
        unfold toR; push_cast
        rw [add_div, show ((S : ℝ) - (b.x0 : ℝ)) * ((S : ℝ) - (b.x0 : ℝ)) / (S : ℝ) ^ 2 =
            (((S : ℝ) - (b.x0 : ℝ)) / (S : ℝ)) ^ 2 by ring, sub_div, div_self S_ne_zero]
        ring
      have hRHS : ((S * S : Int) : ℝ) / (S : ℝ) ^ 2 = 1 := by
        push_cast; rw [← sq, div_self (pow_ne_zero 2 S_ne_zero)]
      linarith
    linarith
  exact ⟨hL0, hx_pos, hx_half, hy_pos, hcirc⟩

/-- Two `BoxCert`s have disjoint open 3D parameter regions. -/
def BoxesDisjoint (a b : BoxCert) : Prop :=
  Disjoint (boxRegion a) (boxRegion b)

lemma boxesDisjoint_of_bool {a b : BoxCert} (h : boxesDisjointBool a b = true) :
    BoxesDisjoint a b := by
  unfold boxesDisjointBool at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rw [BoxesDisjoint, Set.disjoint_left]
  intro p ha hb
  rcases ha with ⟨hal0, hal1, hax0, hax1, hay0, hay1⟩
  rcases hb with ⟨hbl0, hbl1, hbx0, hbx1, hby0, hby1⟩
  rcases h with ((((h1 | h2) | h3) | h4) | h5) | h6
  · have := toR_le_toR h1; linarith
  · have := toR_le_toR h2; linarith
  · have := toR_le_toR h3; linarith
  · have := toR_le_toR h4; linarith
  · have := toR_le_toR h5; linarith
  · have := toR_le_toR h6; linarith

/-- Pairwise disjointness of open parameter regions across a list of `BoxCert`s. -/
def PairwiseDisjointBoxes (boxes : List BoxCert) : Prop :=
  boxes.Pairwise BoxesDisjoint

lemma pairwiseDisjointBoxes_of_bool {boxes : List BoxCert}
    (h : allPairwiseDisjointBool boxes = true) : PairwiseDisjointBoxes boxes := by
  induction boxes with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
    unfold allPairwiseDisjointBool at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons (fun b hb => boxesDisjoint_of_bool (h.1 b hb)) (ih h.2)

/-! ## Section 2: Step Potential & Abel Summation Identities -/

/-- Previous weight `w_{i-1}` (with `w_{-1} = 0`). -/
def wPrev (w : Array Int) (i : Nat) : Int :=
  if i = 0 then 0 else w.getD (i - 1) 0

/-- Step potential `π(r) = ∑_i (w_i - w_{i-1}) · 1_{ρ_i < r}` (left-continuous, nondecreasing). -/
def stepPot (rho w : Array Int) (r : ℝ) : ℝ :=
  ∑ i : Fin rho.size, (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
    if toR (rho.getD i.val 0) < r then 1 else 0

lemma stepPot_dw_nonneg {rho w : Array Int} (h : ValidStepPot rho w) (i : Fin rho.size) :
    0 ≤ toR (w.getD i.val 0) - toR (wPrev w i.val) := by
  unfold wPrev
  split_ifs with h0
  · rw [h0, toR_zero, sub_zero]; exact toR_nonneg h.w_zero_nonneg
  · have hle : w.getD (i.val - 1) 0 ≤ w.getD i.val 0 := h.w_le_of_le (by omega) i.isLt
    linarith [toR_le_toR hle]

lemma stepPot_nonneg {rho w : Array Int} (h : ValidStepPot rho w) (r : ℝ) :
    0 ≤ stepPot rho w r := by
  unfold stepPot
  refine Finset.sum_nonneg fun i _ => mul_nonneg (stepPot_dw_nonneg h i) ?_
  split_ifs <;> norm_num

lemma stepPot_mono {rho w : Array Int} (h : ValidStepPot rho w) :
    Monotone (stepPot rho w) := by
  intro r₁ r₂ hle
  unfold stepPot
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (stepPot_dw_nonneg h i)
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; exact h2 (lt_of_lt_of_le h1 hle)
  · norm_num
  · exact le_rfl

/-- Exact prefix telescope: summing `(w_i - w_{i-1})` over `i ∈ range m` gives `w_{m-1}` (or `0`). -/
lemma sum_dw_range (w : Array Int) (m : Nat) :
    ∑ i ∈ Finset.range m, (toR (w.getD i 0) - toR (wPrev w i)) =
      if m = 0 then 0 else toR (w.getD (m - 1) 0) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hk : k = 0
    · subst hk; simp [wPrev, toR_zero]
    · simp only [hk, ↓reduceIte, wPrev]
      ring

lemma stepPot_le_wMax {rho w : Array Int} (h : ValidStepPot rho w) (r : ℝ) :
    stepPot rho w r ≤ toR (w.getD (rho.size - 1) 0) := by
  have h1 : stepPot rho w r ≤ ∑ i : Fin rho.size, (toR (w.getD i.val 0) - toR (wPrev w i.val)) := by
    unfold stepPot
    refine Finset.sum_le_sum fun i _ => ?_
    have hnn := stepPot_dw_nonneg h i
    split_ifs <;> linarith
  rw [Fin.sum_univ_eq_sum_range (fun i => toR (w.getD i 0) - toR (wPrev w i)),
      sum_dw_range, if_neg (Nat.ne_of_gt h.size_pos)] at h1
  exact h1

lemma stepPot_eq_zero_of_le_zero {rho w : Array Int} (h : ValidStepPot rho w) {r : ℝ} (hr : r ≤ 0) :
    stepPot rho w r = 0 := by
  unfold stepPot
  refine Finset.sum_eq_zero fun i _ => ?_
  have hnn : 0 ≤ toR (rho.getD i.val 0) := toR_nonneg (h.rho_nonneg i.isLt)
  rw [if_neg (not_lt.mpr (hr.trans hnn)), mul_zero]

/-- For a valid step potential, `stepPot rho w r` equals `toR (w[m-1])` where `m` is the count of
knots `< r`. -/
lemma stepPot_eq_prefix {rho w : Array Int} (h : ValidStepPot rho w) (r : ℝ) :
    ∃ m : Nat, m ≤ rho.size ∧
      (∀ i : Nat, i < rho.size → (toR (rho.getD i 0) < r ↔ i < m)) ∧
      stepPot rho w r = if m = 0 then 0 else toR (w.getD (m - 1) 0) := by
  let S_idx : Finset Nat := (Finset.range rho.size).filter fun i => toR (rho.getD i 0) < r
  let m : Nat := S_idx.card
  have hm_le : m ≤ rho.size := by
    calc m = S_idx.card := rfl
      _ ≤ (Finset.range rho.size).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = rho.size := Finset.card_range _
  have hdown : ∀ i j : Nat, j ∈ S_idx → i ≤ j → i ∈ S_idx := by
    intro i j hj hij
    rcases Finset.mem_filter.mp hj with ⟨hj_lt, hj_r⟩
    rw [Finset.mem_range] at hj_lt
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact lt_of_le_of_lt (toR_le_toR (h.rho_le_of_le hij hj_lt)) hj_r
  have hS_eq : S_idx = Finset.range m := by
    ext i
    rw [Finset.mem_range]
    constructor
    · intro hi
      have hsub : Finset.range (i + 1) ⊆ S_idx := by
        intro j hj; exact hdown j i hi (by rw [Finset.mem_range] at hj; omega)
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this; omega
    · intro hilt
      by_contra hni
      have hsub : S_idx ⊆ Finset.range i := by
        intro j hj
        rw [Finset.mem_range]
        by_contra hge
        exact hni (hdown i j hj (Nat.not_lt.mp hge))
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this; omega
  have hiff : ∀ i : Nat, i < rho.size → (toR (rho.getD i 0) < r ↔ i < m) := by
    intro i hi
    have hmem : i ∈ S_idx ↔ i < m := by rw [hS_eq, Finset.mem_range]
    rw [← hmem, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hr => ⟨hi, hr⟩, fun h => h.2⟩
  refine ⟨m, hm_le, hiff, ?_⟩
  unfold stepPot
  rw [Fin.sum_univ_eq_sum_range (fun i =>
      (toR (w.getD i 0) - toR (wPrev w i)) * if toR (rho.getD i 0) < r then 1 else 0)]
  have h1 : (∑ i ∈ Finset.range rho.size, (toR (w.getD i 0) - toR (wPrev w i)) *
      if toR (rho.getD i 0) < r then 1 else 0) =
      ∑ i ∈ S_idx, (toR (w.getD i 0) - toR (wPrev w i)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
  rw [h1, hS_eq, sum_dw_range]

/-- Soundness of integer `evalStepPot`: if `r ≤ toR m`, then `stepPot rho w r ≤ toR (evalStepPot rho w m)`. -/
lemma evalStepPotAux_eq {rho w : Array Int} (h : ValidStepPot rho w) (m : Int) :
    ∀ i : Nat, i ≤ rho.size →
      (∀ j : Nat, j < i → rho.getD j 0 < m) →
      evalStepPotAux rho w m i (if i = 0 then 0 else w.getD (i - 1) 0) =
        if ∃ k : Nat, k < rho.size ∧ rho.getD k 0 < m then
          w.getD (((Finset.range rho.size).filter fun k => rho.getD k 0 < m).card - 1) 0
        else 0 := by
  intro i hi hlt
  induction hn : rho.size - i generalizing i with
  | zero =>
    have hieq : i = rho.size := by omega
    subst hieq
    rw [evalStepPotAux, if_pos le_rfl]
    have hcard : ((Finset.range rho.size).filter fun k => rho.getD k 0 < m).card = rho.size := by
      rw [Finset.filter_true_of_mem (fun k hk => hlt k (Finset.mem_range.mp hk)), Finset.card_range]
    have hex : ∃ k : Nat, k < rho.size ∧ rho.getD k 0 < m := ⟨0, h.size_pos, hlt 0 h.size_pos⟩
    rw [if_pos hex, if_neg (Nat.ne_of_gt h.size_pos), hcard]
  | succ d ih =>
    have hilt : i < rho.size := by omega
    rw [evalStepPotAux, if_neg (by omega)]
    by_cases hgt : m > rho.getD i 0
    · rw [if_pos hgt]
      have hnext : (if i + 1 = 0 then 0 else w.getD (i + 1 - 1) 0) = w.getD i 0 := by simp
      rw [← hnext]
      refine ih (i + 1) (by omega) ?_ (by omega)
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h1 | rfl
      · exact hlt j h1
      · exact hgt
    · rw [if_neg hgt]
      have hfilt : ((Finset.range rho.size).filter fun k => rho.getD k 0 < m) = Finset.range i := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro ⟨hk, hkm⟩
          by_contra hge
          have hle : rho.getD i 0 ≤ rho.getD k 0 := h.rho_le_of_le (Nat.not_lt.mp hge) hk
          omega
        · intro hki
          exact ⟨by omega, hlt k hki⟩
      rw [hfilt, Finset.card_range]
      by_cases hi0 : i = 0
      · subst hi0
        have hno : ¬ ∃ k : Nat, k < rho.size ∧ rho.getD k 0 < m := by
          rintro ⟨k, hk, hkm⟩
          have : k ∈ Finset.range 0 := by
            rw [← hfilt]; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkm⟩
          simp at this
        rw [if_pos rfl, if_neg hno]
      · have hex : ∃ k : Nat, k < rho.size ∧ rho.getD k 0 < m := ⟨0, by omega, hlt 0 (by omega)⟩
        rw [if_neg hi0, if_pos hex]

lemma stepPot_le_evalStepPot {rho w : Array Int} (h : ValidStepPot rho w)
    {r : ℝ} {m : Int} (hrm : r ≤ toR m) :
    stepPot rho w r ≤ toR (evalStepPot rho w m) := by
  rcases stepPot_eq_prefix h r with ⟨k, hk_le, hiff, hval⟩
  rw [hval]
  unfold evalStepPot
  have hev := evalStepPotAux_eq h m 0 (Nat.zero_le _) (fun j hj => by omega)
  simp only [↓reduceIte] at hev
  rw [hev]
  by_cases hk0 : k = 0
  · subst hk0; simp only [↓reduceIte]
    split_ifs with hex
    · rcases hex with ⟨j, hj, _⟩
      have hcard_pos : 0 < ((Finset.range rho.size).filter fun l => rho.getD l 0 < m).card :=
        Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ‹_›⟩⟩
      have hcard_le : ((Finset.range rho.size).filter fun l => rho.getD l 0 < m).card ≤ rho.size :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
      exact toR_nonneg (h.w_nonneg (by omega))
    · rw [toR_zero]
  · simp only [hk0, ↓reduceIte]
    have hsub : Finset.range k ⊆ (Finset.range rho.size).filter (fun l => rho.getD l 0 < m) := by
      intro l hl
      rw [Finset.mem_range] at hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      have hlr : toR (rho.getD l 0) < r := (hiff l (by omega)).mpr hl
      have hlm : toR (rho.getD l 0) < toR m := lt_of_lt_of_le hlr hrm
      have : ((rho.getD l 0 : Int) : ℝ) < (m : ℝ) := (div_lt_div_iff_of_pos_right S_pos).mp hlm
      exact_mod_cast this
    have hex : ∃ l : Nat, l < rho.size ∧ rho.getD l 0 < m := by
      have h0 : 0 ∈ (Finset.range rho.size).filter (fun l => rho.getD l 0 < m) :=
        hsub (Finset.mem_range.mpr (by omega))
      rcases Finset.mem_filter.mp h0 with ⟨h1, h2⟩
      exact ⟨0, Finset.mem_range.mp h1, h2⟩
    rw [if_pos hex]
    have hcard_ge : k ≤ ((Finset.range rho.size).filter fun l => rho.getD l 0 < m).card := by
      simpa using Finset.card_le_card hsub
    have hcard_le : ((Finset.range rho.size).filter fun l => rho.getD l 0 < m).card ≤ rho.size :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    exact toR_le_toR (h.w_le_of_le (by omega) (by omega))

/-- **1D Abel Summation** for any function `f : ℝ → ℝ` with `f 0 = 0`:
`f (stepPot rho w r) = ∑ i, (f (w_i) - f (w_{i-1})) * 1_{ρ_i < r}`. -/
lemma stepPot_abel_1d {rho w : Array Int} (h : ValidStepPot rho w) (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (r : ℝ) :
    f (stepPot rho w r) =
      ∑ i : Fin rho.size, (f (toR (w.getD i.val 0)) - f (toR (wPrev w i.val))) *
        if toR (rho.getD i.val 0) < r then 1 else 0 := by
  rcases stepPot_eq_prefix h r with ⟨m, hm_le, hiff, hval⟩
  rw [hval, Fin.sum_univ_eq_sum_range (fun i =>
      (f (toR (w.getD i 0)) - f (toR (wPrev w i))) * if toR (rho.getD i 0) < r then 1 else 0)]
  have h1 : (∑ i ∈ Finset.range rho.size, (f (toR (w.getD i 0)) - f (toR (wPrev w i))) *
      if toR (rho.getD i 0) < r then 1 else 0) =
      ∑ i ∈ Finset.range m, (f (toR (w.getD i 0)) - f (toR (wPrev w i))) := by
    have hcongr : (∑ i ∈ Finset.range rho.size, (f (toR (w.getD i 0)) - f (toR (wPrev w i))) *
        if toR (rho.getD i 0) < r then 1 else 0) =
        ∑ i ∈ Finset.range rho.size, if i < m then (f (toR (w.getD i 0)) - f (toR (wPrev w i))) else 0 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hiff i (Finset.mem_range.mp hi)]
      split_ifs <;> ring
    rw [hcongr, ← Finset.sum_filter]
    congr 1
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h1]
  clear h1 hval hiff
  induction m with
  | zero => simp [hf0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih (by omega)]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hk : k = 0
    · subst hk; simp [wPrev, toR_zero, hf0]
    · simp only [hk, ↓reduceIte, wPrev]; ring

/-- **2D Abel Summation** for `g (x, y) = max 0 (x + y - d)` on `(stepPot r₁, stepPot r₂)`. -/
lemma stepPot_abel_2d {rho w : Array Int} (h : ValidStepPot rho w) (d r₁ r₂ : ℝ) (hd : 0 ≤ d) :
    max 0 (stepPot rho w r₁ + stepPot rho w r₂ - d) =
      (∑ i : Fin rho.size,
        (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
          if toR (rho.getD i.val 0) < r₁ then 1 else 0) +
      (∑ j : Fin rho.size,
        (max 0 (toR (w.getD j.val 0) - d) - max 0 (toR (wPrev w j.val) - d)) *
          if toR (rho.getD j.val 0) < r₂ then 1 else 0) +
      ∑ i : Fin rho.size, ∑ j : Fin rho.size,
        (max 0 (toR (w.getD i.val 0) + toR (w.getD j.val 0) - d) -
         max 0 (toR (wPrev w i.val) + toR (w.getD j.val 0) - d) -
         max 0 (toR (w.getD i.val 0) + toR (wPrev w j.val) - d) +
         max 0 (toR (wPrev w i.val) + toR (wPrev w j.val) - d)) *
          (if toR (rho.getD i.val 0) < r₁ then 1 else 0) *
          (if toR (rho.getD j.val 0) < r₂ then 1 else 0) := by
  have h0 : max 0 (0 - d) = 0 := max_eq_left (by linarith)
  -- Apply 1D Abel in `r₁` to `x ↦ max 0 (x + stepPot r₂ - d) - max 0 (stepPot r₂ - d)`
  let F : ℝ → ℝ := fun x => max 0 (x + stepPot rho w r₂ - d) - max 0 (stepPot rho w r₂ - d)
  have hF0 : F 0 = 0 := by simp [F]
  have hstep1 := stepPot_abel_1d h F hF0 r₁
  have hm2 := stepPot_abel_1d h (fun y => max 0 (y - d)) h0 r₂
  -- For each `i`, apply 1D Abel in `r₂` to `y ↦ max 0 (w_i + y - d) - max 0 (w_{i-1} + y - d) - (max 0 (w_i - d) - max 0 (w_{i-1} - d))`
  have hstep2 : ∀ i : Fin rho.size,
      F (toR (w.getD i.val 0)) - F (toR (wPrev w i.val)) =
        (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) +
        ∑ j : Fin rho.size,
          (max 0 (toR (w.getD i.val 0) + toR (w.getD j.val 0) - d) -
           max 0 (toR (wPrev w i.val) + toR (w.getD j.val 0) - d) -
           max 0 (toR (w.getD i.val 0) + toR (wPrev w j.val) - d) +
           max 0 (toR (wPrev w i.val) + toR (wPrev w j.val) - d)) *
            (if toR (rho.getD j.val 0) < r₂ then 1 else 0) := by
    intro i
    let Gi : ℝ → ℝ := fun y =>
      (max 0 (toR (w.getD i.val 0) + y - d) - max 0 (toR (wPrev w i.val) + y - d)) -
      (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d))
    have hGi0 : Gi 0 = 0 := by simp [Gi]
    have hab := stepPot_abel_1d h Gi hGi0 r₂
    have hGdiff : ∀ j : Fin rho.size,
        Gi (toR (w.getD j.val 0)) - Gi (toR (wPrev w j.val)) =
          max 0 (toR (w.getD i.val 0) + toR (w.getD j.val 0) - d) -
          max 0 (toR (wPrev w i.val) + toR (w.getD j.val 0) - d) -
          max 0 (toR (w.getD i.val 0) + toR (wPrev w j.val) - d) +
          max 0 (toR (wPrev w i.val) + toR (wPrev w j.val) - d) := fun j => by
      dsimp only [Gi]; ring
    simp_rw [hGdiff] at hab
    dsimp only [F, Gi] at hab ⊢
    linarith
  have hmain : max 0 (stepPot rho w r₁ + stepPot rho w r₂ - d) =
      F (stepPot rho w r₁) + max 0 (stepPot rho w r₂ - d) := by dsimp only [F]; ring
  rw [hmain, hstep1, hm2]
  simp_rw [hstep2]
  have hdist : ∀ i : Fin rho.size,
      ((max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) +
        ∑ j : Fin rho.size,
          (max 0 (toR (w.getD i.val 0) + toR (w.getD j.val 0) - d) -
           max 0 (toR (wPrev w i.val) + toR (w.getD j.val 0) - d) -
           max 0 (toR (w.getD i.val 0) + toR (wPrev w j.val) - d) +
           max 0 (toR (wPrev w i.val) + toR (wPrev w j.val) - d)) *
            (if toR (rho.getD j.val 0) < r₂ then 1 else 0)) *
        (if toR (rho.getD i.val 0) < r₁ then 1 else 0) =
      (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
        (if toR (rho.getD i.val 0) < r₁ then 1 else 0) +
      ∑ j : Fin rho.size,
        (max 0 (toR (w.getD i.val 0) + toR (w.getD j.val 0) - d) -
         max 0 (toR (wPrev w i.val) + toR (w.getD j.val 0) - d) -
         max 0 (toR (w.getD i.val 0) + toR (wPrev w j.val) - d) +
         max 0 (toR (wPrev w i.val) + toR (wPrev w j.val) - d)) *
          (if toR (rho.getD i.val 0) < r₁ then 1 else 0) *
          (if toR (rho.getD j.val 0) < r₂ then 1 else 0) := fun i => by
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hdist i, Finset.sum_add_distrib]
  ring

/-- Supermodularity of `t ↦ max 0 (t - d)`: for `a₁ ≤ a₂` and `b₁ ≤ b₂`,
`max 0 (a₂ + b₂ - d) - max 0 (a₁ + b₂ - d) - max 0 (a₂ + b₁ - d) + max 0 (a₁ + b₁ - d) ≥ 0`. -/
lemma max_zero_sub_supermod {a₁ a₂ b₁ b₂ d : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    0 ≤ max 0 (a₂ + b₂ - d) - max 0 (a₁ + b₂ - d) - max 0 (a₂ + b₁ - d) + max 0 (a₁ + b₁ - d) := by
  rcases le_total 0 (a₁ + b₂ - d) with h1 | h1 <;>
  rcases le_total 0 (a₂ + b₁ - d) with h2 | h2
  · rw [max_eq_right (by linarith), max_eq_right h1, max_eq_right h2]
    linarith [le_max_right (0 : ℝ) (a₁ + b₁ - d)]
  · rw [max_eq_right (by linarith), max_eq_right h1, max_eq_left h2]
    linarith [le_max_left (0 : ℝ) (a₁ + b₁ - d)]
  · rw [max_eq_right (by linarith), max_eq_left h1, max_eq_right h2]
    linarith [le_max_left (0 : ℝ) (a₁ + b₁ - d)]
  · rw [max_eq_left h1, max_eq_left h2]
    linarith [le_max_left (0 : ℝ) (a₂ + b₂ - d), le_max_left (0 : ℝ) (a₁ + b₁ - d)]

/-! ## Section 3: 1D Base Poisson Integral -/

/-- First-order 2-factor term `2 E[π(N₂(0))]`. -/
def baseTerm1 (rho w : Array Int) : ℝ :=
  2 * ∑ i : Fin rho.size,
    (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
      (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
      Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))

/-- Marginal pair-penalty term (Abel summation terms involving a single vertex potential). -/
def basePenMarg (rho w : Array Int) : ℝ :=
  ∑ i : Fin rho.size,
    2 * Real.pi *
      ∫ d in (0 : ℝ)..(toR (w.getD i.val 0)),
        d * (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
          (if d ≤ toR (rho.getD i.val 0) then
            Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
          else
            (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
              Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2)))

/-- Interaction pair-penalty coefficient `Δ_{ij}(d) ≥ 0`. -/
def baseInterCoeff (w : Array Int) (i j : Nat) (d : ℝ) : ℝ :=
  max 0 (toR (w.getD i 0) + toR (w.getD j 0) - d) -
  max 0 (toR (wPrev w i) + toR (w.getD j 0) - d) -
  max 0 (toR (w.getD i 0) + toR (wPrev w j) - d) +
  max 0 (toR (wPrev w i) + toR (wPrev w j) - d)

lemma baseInterCoeff_nonneg {rho w : Array Int} (h : ValidStepPot rho w)
    (i j : Fin rho.size) (d : ℝ) : 0 ≤ baseInterCoeff w i.val j.val d := by
  unfold baseInterCoeff
  have hi := stepPot_dw_nonneg h i
  have hj := stepPot_dw_nonneg h j
  exact max_zero_sub_supermod (by linarith) (by linarith)

lemma baseInterCoeff_symm (w : Array Int) (i j : Nat) (d : ℝ) :
    baseInterCoeff w i j d = baseInterCoeff w j i d := by
  unfold baseInterCoeff
  have h1 : toR (w.getD i 0) + toR (w.getD j 0) - d = toR (w.getD j 0) + toR (w.getD i 0) - d := by ring
  have h2 : toR (wPrev w i) + toR (w.getD j 0) - d = toR (w.getD j 0) + toR (wPrev w i) - d := by ring
  have h3 : toR (w.getD i 0) + toR (wPrev w j) - d = toR (wPrev w j) + toR (w.getD i 0) - d := by ring
  have h4 : toR (wPrev w i) + toR (wPrev w j) - d = toR (wPrev w j) + toR (wPrev w i) - d := by ring
  rw [h1, h2, h3, h4]; ring

/-- Interaction pair-penalty term (supermodular 2D Abel summation integral). -/
def basePenInter (rho w : Array Int) : ℝ :=
  Real.pi * ∫ d in (0 : ℝ)..(2 * toR (w.getD (rho.size - 1) 0)),
    d * ∑ i : Fin rho.size, ∑ j : Fin rho.size,
      baseInterCoeff w i.val j.val d *
        jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
          (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))

/-- Complete 1D base Poisson-limit integral `baseTerm1 - basePenMarg - basePenInter`. -/
def baseIntegral (rho w : Array Int) : ℝ :=
  baseTerm1 rho w - basePenMarg rho w - basePenInter rho w

/-! ## Section 4: Triangle-Moat Poisson Integral -/

/-- Canonical triangle vertices `![(0,0), (L,0), (L*pt.1, L*pt.2)]`. -/
def triVerts (L : ℝ) (pt : Pt) : Fin 3 → Pt :=
  ![((0 : ℝ), (0 : ℝ)), (L, 0), (L * pt.1, L * pt.2)]

/-- Union of the three radius-`r` disks centered at the triangle vertices. -/
def triUnion (P : Fin 3 → Pt) (r : ℝ) : Set Pt :=
  ⋃ u : Fin 3, disk (P u) r

/-- Number of triangle vertices inside `disk v ρ`. -/
def triHitCount (P : Fin 3 → Pt) (v : Pt) (ρ : ℝ) : Nat :=
  (Finset.univ.filter fun u : Fin 3 => euclidDist v (P u) ≤ ρ).card

/-- Exact Poisson survival probability `P(m + Poisson(V) ≤ 1)` for `N₂(v) > ρ`. -/
def extSurvProb (m : Nat) (V : ℝ) : ℝ :=
  if m ≥ 2 then 0
  else if m = 1 then Real.exp (-V)
  else (1 + V) * Real.exp (-V)

lemma extSurvProb_nonneg (m : Nat) {V : ℝ} (hV : 0 ≤ V) : 0 ≤ extSurvProb m V := by
  unfold extSurvProb
  split_ifs
  · exact le_rfl
  · exact Real.exp_nonneg _
  · exact mul_nonneg (by linarith) (Real.exp_nonneg _)

lemma extSurvProb_le_one (m : Nat) {V : ℝ} (hV : 0 ≤ V) : extSurvProb m V ≤ 1 := by
  unfold extSurvProb
  split_ifs
  · exact zero_le_one
  · exact Real.exp_le_one_iff.mpr (by linarith)
  · have h1 : 1 + V ≤ Real.exp V := by linarith [Real.add_one_le_exp V]
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos V)]
    exact h1

/-- `extSurvProb` is antitone in BOTH `m` and `V ≥ 0`! -/
lemma extSurvProb_antitone {m₁ m₂ : Nat} {V₁ V₂ : ℝ}
    (hm : m₁ ≤ m₂) (hV1 : 0 ≤ V₁) (hV : V₁ ≤ V₂) :
    extSurvProb m₂ V₂ ≤ extSurvProb m₁ V₁ := by
  have hexp_le : Real.exp (-V₂) ≤ Real.exp (-V₁) := Real.exp_le_exp.mpr (by linarith)
  have h1V_le : (1 + V₂) * Real.exp (-V₂) ≤ (1 + V₁) * Real.exp (-V₁) := by
    set δ := V₂ - V₁
    have hδ : 0 ≤ δ := by linarith
    have hexp_split : Real.exp (-V₂) = Real.exp (-δ) * Real.exp (-V₁) := by
      rw [← Real.exp_add]; congr 1; dsimp only [δ]; ring
    rw [hexp_split, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    have h1 : 1 + V₂ ≤ (1 + V₁) * (1 + δ) := by dsimp only [δ]; nlinarith
    have h2 : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
    have h3 : 1 + V₂ ≤ (1 + V₁) * Real.exp δ := h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos δ)]
    exact h3
  unfold extSurvProb
  split_ifs with h2_ge h2_1 h1_ge h1_1 h1_ge' h1_1'
  · exact le_rfl
  · exact Real.exp_nonneg _
  · exact mul_nonneg (by linarith) (Real.exp_nonneg _)
  · omega
  · exact hexp_le
  · calc Real.exp (-V₂) ≤ Real.exp (-V₁) := hexp_le
      _ ≤ (1 + V₁) * Real.exp (-V₁) := by nlinarith [Real.exp_pos (-V₁)]
  · omega
  · omega
  · exact h1V_le

/-- Deterministic vertex potential `p_u(L, pt)` of an isolated canonical triangle. -/
def triVertPot (rho w : Array Int) (L : ℝ) (pt : Pt) (u : Fin 3) : ℝ :=
  match u with
  | ⟨0, _⟩ => stepPot rho w L
  | ⟨1, _⟩ => stepPot rho w L
  | ⟨2, _⟩ => stepPot rho w (L * euclidNorm (1 - pt.1, pt.2))

/-- Incremental crossing coefficient for vertex `u`, step `k`, and external point `v` at level
`(yPrev, yj)`. -/
def triCrossCoeff (w : Array Int) (p yPrev yj d : ℝ) (k : Nat) : ℝ :=
  (max 0 (p + yj + toR (w.getD k 0) - d) - max 0 (p + yPrev + toR (w.getD k 0) - d)) -
  (max 0 (p + yj + toR (wPrev w k) - d) - max 0 (p + yPrev + toR (wPrev w k) - d))

/-- Abel-summation monotonicity of the external-point crossing expectation with respect to `p`:
whenever `p₁ ≤ p₂`, `yPrev ≤ yj`, `p₂ + yj ≤ d`, and `q` is antitone (`q₀ ≥ q₁ ≥ ... ≥ 0`),
`∑ k, triCrossCoeff p₁ * q k ≤ ∑ k, triCrossCoeff p₂ * q k`. -/
lemma sum_triCrossCoeff_mono_p {rho w : Array Int} (_h : ValidStepPot rho w)
    {p₁ p₂ yPrev yj d : ℝ} (hp : p₁ ≤ p₂) (hy : yPrev ≤ yj) (hclear : p₂ + yj ≤ d)
    {q : Nat → ℝ} (hq_nn : ∀ k < rho.size, 0 ≤ q k)
    (hq_anti : ∀ k, k + 1 < rho.size → q (k + 1) ≤ q k) :
    ∑ k : Fin rho.size, triCrossCoeff w p₁ yPrev yj d k.val * q k.val ≤
      ∑ k : Fin rho.size, triCrossCoeff w p₂ yPrev yj d k.val * q k.val := by
  let ψ : ℝ → ℝ → ℝ := fun p t => max 0 (p + yj + t - d) - max 0 (p + yPrev + t - d)
  have hψ0 : ∀ p ≤ p₂, ψ p 0 = 0 := fun p hp2 => by
    dsimp only [ψ]; rw [max_eq_left (by linarith), max_eq_left (by linarith), sub_self]
  have hψ_mono : ∀ t : ℝ, ψ p₁ t ≤ ψ p₂ t := fun t => by
    dsimp only [ψ]
    rcases le_total 0 (p₁ + yj + t - d) with h1 | h1 <;>
    rcases le_total 0 (p₂ + yPrev + t - d) with h2 | h2
    · rw [max_eq_right h1, max_eq_right (show 0 ≤ p₂ + yj + t - d by linarith), max_eq_right h2]
      linarith [le_max_right (0 : ℝ) (p₁ + yPrev + t - d)]
    · rw [max_eq_right h1, max_eq_right (show 0 ≤ p₂ + yj + t - d by linarith), max_eq_left h2]
      linarith [le_max_left (0 : ℝ) (p₁ + yPrev + t - d)]
    · rw [max_eq_left h1, max_eq_left (by linarith : p₁ + yPrev + t - d ≤ 0), sub_self]
      exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))
    · rw [max_eq_left h1, max_eq_left (by linarith : p₁ + yPrev + t - d ≤ 0), sub_self]
      exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))
  -- Rewrite BOTH sides by finite summation by parts!
  have hab : ∀ p ≤ p₂,
      ∑ k : Fin rho.size, triCrossCoeff w p yPrev yj d k.val * q k.val =
        ∑ k : Fin rho.size, ψ p (toR (w.getD k.val 0)) *
          (q k.val - if k.val + 1 < rho.size then q (k.val + 1) else 0) := by
    intro p hp2
    rw [Fin.sum_univ_eq_sum_range (fun k => triCrossCoeff w p yPrev yj d k * q k),
        Fin.sum_univ_eq_sum_range (fun k =>
          ψ p (toR (w.getD k 0)) * (q k - if k + 1 < rho.size then q (k + 1) else 0))]
    have hrec : ∀ m : Nat, m ≤ rho.size →
        ∑ k ∈ Finset.range m, triCrossCoeff w p yPrev yj d k * q k =
          (∑ k ∈ Finset.range m, ψ p (toR (w.getD k 0)) *
            (q k - if k + 1 < m then q (k + 1) else 0)) := by
      intro m _
      induction m with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih (by omega)]
        -- Expand `∑_{k < n + 1}` on RHS
        rw [Finset.sum_range_succ]
        simp only [lt_self_iff_false, ↓reduceIte, sub_zero]
        by_cases hn : n = 0
        · subst hn
          have h0 := hψ0 p hp2
          dsimp only [ψ] at h0
          simp only [add_zero] at h0
          simp only [Finset.range_zero, Finset.sum_empty, zero_add, triCrossCoeff, wPrev,
            ↓reduceIte, toR_zero, add_zero, ψ]
          rw [h0, sub_zero]
        · have hsplit : ∀ k ∈ Finset.range n,
              ψ p (toR (w.getD k 0)) * (q k - if k + 1 < n + 1 then q (k + 1) else 0) =
              ψ p (toR (w.getD k 0)) * (q k - if k + 1 < n then q (k + 1) else 0) -
              (if k = n - 1 then ψ p (toR (w.getD (n - 1) 0)) * q n else 0) := by
            intro k hk
            rw [Finset.mem_range] at hk
            by_cases hkn : k = n - 1
            · subst hkn
              have h3 : n - 1 + 1 = n := by omega
              rw [h3, if_pos (by omega : n < n + 1), if_neg (lt_irrefl n), if_pos rfl]
              ring
            · have h1 : k + 1 < n := by omega
              have h2 : k + 1 < n + 1 := by omega
              rw [if_pos h2, if_pos h1, if_neg hkn]; ring
          rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
          have hmem : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
          rw [Finset.sum_ite_eq' (Finset.range n) (n - 1), if_pos hmem]
          unfold triCrossCoeff wPrev
          simp only [hn, ↓reduceIte, ψ]
          ring
    exact hrec rho.size le_rfl
  rw [hab p₁ hp, hab p₂ le_rfl]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hψ_mono _) ?_
  split_ifs with hlt
  · linarith [hq_anti k.val hlt]
  · linarith [hq_nn k.val k.isLt]

/-- Exact Poisson crossing-penalty integral for a canonical triangle `(L, pt)` at level `(yPrev, rj, yj)`. -/
def levelCrossPen (rho w : Array Int) (yPrev rj yj : Int) (L : ℝ) (pt : Pt) : ℝ :=
  ∫ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
    ∑ u : Fin 3, ∑ k : Fin rho.size,
      triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
        (euclidDist v (triVerts L pt u)) k.val *
      extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
        (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal

/-- Exact Poisson net gain for one telescoping level `(rj, yj)` over a box `b`. -/
def levelGain (rho w : Array Int) (b : BoxCert) (yPrev rj yj : Int) : ℝ :=
  ∫ L in (toR b.l0)..(toR b.l1),
    ∫ x in (toR b.x0)..(toR b.x1),
      ∫ y in (toR b.y0)..(toR b.y1),
        (4 * Real.pi * L ^ 3) *
          Real.exp (-unionDiskArea (triVerts L (x, y)) (toR rj)) *
          (2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L (x, y))

/-- Sum of `levelGain` over all activated levels of a box `b` (according to mask `act`). -/
def boxLevelsIntegral (rho w : Array Int) (act : BoxCert → Int → Int → Int → Bool) (b : BoxCert) :
    List (Int × Int) → Int → ℝ
  | [], _ => 0
  | (rj, yj) :: rest, yPrev =>
    (if act b yPrev rj yj then levelGain rho w b yPrev rj yj else 0) +
      boxLevelsIntegral rho w act b rest yj

/-- Total Poisson-limit gain of a single certified box `b` under level mask `act`. -/
def boxIntegral (rho w : Array Int) (act : BoxCert → Int → Int → Int → Bool) (b : BoxCert) : ℝ :=
  boxLevelsIntegral rho w act b b.levels 0

/-- Total Poisson-limit triangle-moat gain across a list of pairwise-disjoint boxes. -/
def trianglePlanIntegral (rho w : Array Int) (act : BoxCert → Int → Int → Int → Bool)
    (boxes : List BoxCert) : ℝ :=
  (boxes.map (boxIntegral rho w act)).sum

lemma trianglePlanIntegral_nil (rho w : Array Int) (act : BoxCert → Int → Int → Int → Bool) :
    trianglePlanIntegral rho w act [] = 0 := rfl

lemma trianglePlanIntegral_cons (rho w : Array Int) (act : BoxCert → Int → Int → Int → Bool)
    (b : BoxCert) (bs : List BoxCert) :
    trianglePlanIntegral rho w act (b :: bs) =
      boxIntegral rho w act b + trianglePlanIntegral rho w act bs := rfl

lemma trianglePlanIntegral_append (rho w : Array Int) (act : BoxCert → Int → Int → Int → Bool)
    (xs ys : List BoxCert) :
    trianglePlanIntegral rho w act (xs ++ ys) =
      trianglePlanIntegral rho w act xs + trianglePlanIntegral rho w act ys := by
  unfold trianglePlanIntegral
  rw [List.map_append, List.sum_append]

end

end BHHBounds.Dual
