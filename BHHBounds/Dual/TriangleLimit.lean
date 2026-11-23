import BHHBounds.Dual.TriangleGeom
import BHHBounds.Dual.TriangleCond

/-!
# Limit of one triangle-moat level

`levelGain_tendsto`: the expected gain of one level of a box converges to `levelGain`, by
exchangeability, the three-point change of variables and dominated convergence.
-/

open MeasureTheory Set Real Filter Finset Topology
open scoped ENNReal Classical
open BHHBounds.Geometry
open BHHBounds.Cert

namespace BHHBounds.Dual

noncomputable section

/-! ## Section 1: Permutation Exchangeability of Ordered Distinct Triples -/

private lemma exists_perm_three {n : ℕ} (hn : 4 ≤ n) {u v t : Fin n}
    (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t) :
    ∃ σ : Equiv.Perm (Fin n),
      σ ⟨0, by omega⟩ = u ∧ σ ⟨1, by omega⟩ = v ∧ σ ⟨2, by omega⟩ = t := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  let σ₁ : Equiv.Perm (Fin n) := Equiv.swap i0 u
  let v' := σ₁.symm v
  have hv'0 : v' ≠ i0 := by
    intro h
    have : v = σ₁ i0 := by rw [← h]; simp [v']
    rw [Equiv.swap_apply_left] at this
    exact huv this.symm
  let σ₂ : Equiv.Perm (Fin n) := Equiv.swap i1 v'
  let t' := σ₂.symm (σ₁.symm t)
  have ht'0 : t' ≠ i0 := by
    intro h
    have h1 : σ₁.symm t = σ₂ i0 := by rw [← h]; simp [t']
    rw [Equiv.swap_apply_of_ne_of_ne h01 hv'0.symm] at h1
    have h2 : t = σ₁ i0 := by rw [← h1]; simp
    rw [Equiv.swap_apply_left] at h2
    exact hut h2.symm
  have ht'1 : t' ≠ i1 := by
    intro h
    have h1 : σ₁.symm t = σ₂ i1 := by rw [← h]; simp [t']
    rw [Equiv.swap_apply_left] at h1
    have h2 : t = v := σ₁.symm.injective h1
    exact hvt h2.symm
  let σ₃ : Equiv.Perm (Fin n) := Equiv.swap i2 t'
  refine ⟨σ₃.trans (σ₂.trans σ₁), ?_, ?_, ?_⟩
  · change σ₁ (σ₂ (σ₃ i0)) = u
    rw [Equiv.swap_apply_of_ne_of_ne h02 ht'0.symm,
        Equiv.swap_apply_of_ne_of_ne h01 hv'0.symm,
        Equiv.swap_apply_left]
  · change σ₁ (σ₂ (σ₃ i1)) = v
    rw [Equiv.swap_apply_of_ne_of_ne h12 ht'1.symm,
        Equiv.swap_apply_left]
    simp [v']
  · change σ₁ (σ₂ (σ₃ i2)) = t
    rw [Equiv.swap_apply_left]
    simp [t']

private lemma nn2_comp_perm_tri {n : ℕ} (hn : 3 ≤ n) (X : Fin n → Pt)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    nn2 hn (rescaledDist (X ∘ σ)) i = nn2 hn (rescaledDist X) (σ i) := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := (lt_nn2_iff hn (rescaledDist X) (σ i) (nn2 hn (rescaledDist (X ∘ σ)) i)).mp hlt
    have hcard : ((Finset.univ.erase i).filter fun j => rescaledDist (X ∘ σ) i j ≤ nn2 hn (rescaledDist (X ∘ σ)) i).card =
        ((Finset.univ.erase (σ i)).filter fun j => rescaledDist X (σ i) j ≤ nn2 hn (rescaledDist (X ∘ σ)) i).card := by
      refine Finset.card_bij (fun j _ => σ j) ?_ ?_ ?_
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hje, hjd⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
          ⟨fun he => Finset.ne_of_mem_erase hje (σ.injective he), Finset.mem_univ _⟩, hjd⟩
      · intro a _ b _ h; exact σ.injective h
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hje, hjd⟩
        refine ⟨σ.symm j, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
          ⟨fun he => Finset.ne_of_mem_erase hje (by rw [← he]; simp), Finset.mem_univ _⟩,
          by simpa [rescaledDist, Function.comp] using hjd⟩, by simp⟩
    have h2 : nn2 hn (rescaledDist (X ∘ σ)) i < nn2 hn (rescaledDist (X ∘ σ)) i :=
      (lt_nn2_iff hn (rescaledDist (X ∘ σ)) i _).mpr (by omega)
    exact lt_irrefl _ h2
  · have h1 := (lt_nn2_iff hn (rescaledDist (X ∘ σ)) i (nn2 hn (rescaledDist X) (σ i))).mp hgt
    have hcard : ((Finset.univ.erase i).filter fun j => rescaledDist (X ∘ σ) i j ≤ nn2 hn (rescaledDist X) (σ i)).card =
        ((Finset.univ.erase (σ i)).filter fun j => rescaledDist X (σ i) j ≤ nn2 hn (rescaledDist X) (σ i)).card := by
      refine Finset.card_bij (fun j _ => σ j) ?_ ?_ ?_
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hje, hjd⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
          ⟨fun he => Finset.ne_of_mem_erase hje (σ.injective he), Finset.mem_univ _⟩, hjd⟩
      · intro a _ b _ h; exact σ.injective h
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hje, hjd⟩
        refine ⟨σ.symm j, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
          ⟨fun he => Finset.ne_of_mem_erase hje (by rw [← he]; simp), Finset.mem_univ _⟩,
          by simpa [rescaledDist, Function.comp] using hjd⟩, by simp⟩
    have h2 : nn2 hn (rescaledDist X) (σ i) < nn2 hn (rescaledDist X) (σ i) :=
      (lt_nn2_iff hn (rescaledDist X) (σ i) _).mpr (by omega)
    exact lt_irrefl _ h2

private def triExpr {n : ℕ} (hn : 4 ≤ n) (rho w : Array Int) (b : BoxCert)
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

private lemma triExpr_comp_perm {n : ℕ} (hn : 4 ≤ n) (rho w : Array Int) (b : BoxCert)
    (yPrev rj yj : Int) (rBuf : ℝ) (σ : Equiv.Perm (Fin n)) (u v t : Fin n) (X : Fin n → Pt) :
    triExpr hn rho w b yPrev rj yj rBuf u v t (X ∘ σ) =
      triExpr hn rho w b yPrev rj yj rBuf (σ u) (σ v) (σ t) X := by
  unfold triExpr
  have hS : ({σ u, σ v, σ t} : Finset (Fin n)) = ({u, v, t} : Finset (Fin n)).image σ := by
    ext x; simp
  have hmatch : MatchesBox b rBuf (X ∘ σ) u v t ↔ MatchesBox b rBuf X (σ u) (σ v) (σ t) := by
    unfold MatchesBox
    simp only [Function.comp_apply, σ.injective.ne_iff]
  have hcl : (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
        toR rj < rescaledDist (X ∘ σ) x z) ↔
      (∀ x ∈ ({σ u, σ v, σ t} : Finset (Fin n)), ∀ z ∉ ({σ u, σ v, σ t} : Finset (Fin n)),
        toR rj < rescaledDist X x z) := by
    rw [hS]
    constructor
    · intro h x hx z hz
      rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
      have hz' : σ.symm z ∉ ({u, v, t} : Finset (Fin n)) := fun hm =>
        hz (Finset.mem_image.mpr ⟨σ.symm z, hm, by simp⟩)
      simpa [rescaledDist, Function.comp] using h x' hx' (σ.symm z) hz'
    · intro h x hx z hz
      have hx' : σ x ∈ ({u, v, t} : Finset (Fin n)).image σ := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hz' : σ z ∉ ({u, v, t} : Finset (Fin n)).image σ := fun hm => by
        rcases Finset.mem_image.mp hm with ⟨w, hw, hwz⟩
        exact hz (σ.injective hwz ▸ hw)
      exact h (σ x) hx' (σ z) hz'
  refine if_congr (and_congr hmatch hcl) ?_ rfl
  congr 1
  have hbij_outer : ∀ f : Fin n → ℝ,
      ∑ x ∈ ({u, v, t} : Finset (Fin n)), f (σ x) =
      ∑ x ∈ ({σ u, σ v, σ t} : Finset (Fin n)), f x := fun f => by
    rw [hS, Finset.sum_image (fun a _ b _ hab => σ.injective hab)]
  have hbij_inner : ∀ x : Fin n, ∀ f : Fin n → ℝ,
      ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)), f (σ z) =
      ∑ z ∈ Finset.univ \ ({σ u, σ v, σ t} : Finset (Fin n)), f z := fun _ f => by
    refine Finset.sum_bij (fun z _ => σ z) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro z hz
      rw [Finset.mem_sdiff] at hz ⊢
      refine ⟨Finset.mem_univ _, fun hm => hz.2 ?_⟩
      rw [hS] at hm; rcases Finset.mem_image.mp hm with ⟨w, hw, hwz⟩
      exact σ.injective hwz ▸ hw
    · intro a _ b _ hab; exact σ.injective hab
    · intro z hz
      rw [Finset.mem_sdiff] at hz
      refine ⟨σ.symm z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hm => hz.2 ?_⟩, by simp⟩
      rw [hS]; exact Finset.mem_image.mpr ⟨σ.symm z, hm, by simp⟩
  have hrew : ∀ x : Fin n,
      (∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
        (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (X ∘ σ)) x) + toR yj +
            stepPot rho w (nn2 (by omega) (rescaledDist (X ∘ σ)) z) - rescaledDist (X ∘ σ) x z) -
         max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (X ∘ σ)) x) + toR yPrev +
            stepPot rho w (nn2 (by omega) (rescaledDist (X ∘ σ)) z) - rescaledDist (X ∘ σ) x z))) =
      ∑ z ∈ Finset.univ \ ({σ u, σ v, σ t} : Finset (Fin n)),
        (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) (σ x)) + toR yj +
            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X (σ x) z) -
         max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) (σ x)) + toR yPrev +
            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X (σ x) z)) := fun x => by
    simp_rw [nn2_comp_perm_tri (by omega) X σ]
    exact hbij_inner x (fun z =>
      max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) (σ x)) + toR yj +
          stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X (σ x) z) -
       max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) (σ x)) + toR yPrev +
          stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X (σ x) z))
  simp_rw [hrew]
  exact hbij_outer (fun x => ∑ z ∈ Finset.univ \ ({σ u, σ v, σ t} : Finset (Fin n)),
    (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
        stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
     max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
        stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z)))

private lemma integrable_triExpr {n : ℕ} (hn : 4 ≤ n) (rho w : Array Int) (b : BoxCert)
    (yPrev rj yj : Int) (rBuf : ℝ) (u v t : Fin n) :
    Integrable (triExpr hn rho w b yPrev rj yj rBuf u v t) (unitSquarePi n) := by
  have hmeas : Measurable (triExpr hn rho w b yPrev rj yj rBuf u v t) := by
    unfold triExpr
    have hm_dist : ∀ a c : Fin n, Measurable (fun X : Fin n → Pt => rescaledDist X a c) := fun a c => by
      unfold rescaledDist
      have hpair : Measurable (fun X : Fin n → Pt => (X a, X c)) :=
        (measurable_pi_apply a).prodMk (measurable_pi_apply c)
      exact measurable_const.mul (measurable_euclidDist.comp hpair)
    have hm_nn2 : ∀ a : Fin n, Measurable (fun X : Fin n → Pt => nn2 (by omega) (rescaledDist X) a) := by
      intro a; unfold nn2
      have hinf : ∀ (s : Finset (Fin n × Fin n)) (hs : s.Nonempty) (f : (Fin n × Fin n) → (Fin n → Pt) → ℝ),
          (∀ p ∈ s, Measurable (f p)) → Measurable (fun X => s.inf' hs fun p => f p X) := by
        intro s
        induction s using Finset.cons_induction with
        | empty => intro hs; exact absurd hs Finset.not_nonempty_empty
        | cons p s' hp ih =>
          intro hs f hf
          by_cases hs' : s'.Nonempty
          · have : (fun X => (Finset.cons p s' hp).inf' hs fun q => f q X) =
                fun X => min (f p X) (s'.inf' hs' fun q => f q X) := by
              ext X; exact Finset.inf'_cons (f := fun q => f q X) hs'
            rw [this]
            exact (hf p (Finset.mem_cons_self p s')).min (ih hs' f fun q hq => hf q (Finset.mem_cons_of_mem hq))
          · have hem : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
            subst hem
            have : (fun X => (Finset.cons p ∅ hp).inf' hs fun q => f q X) = f p := by ext X; simp
            rw [this]; exact hf p (Finset.mem_cons_self p ∅)
      exact hinf _ _ _ fun p _ => (hm_dist a p.1).max (hm_dist a p.2)
    have hm_pot : Measurable (stepPot rho w) := by
      unfold stepPot
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul
        (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)
    have hm_match : MeasurableSet {X : Fin n → Pt | MatchesBox b rBuf X u v t} := by
      by_cases hne : u ≠ v ∧ u ≠ t ∧ v ≠ t
      · have heq : {X : Fin n → Pt | MatchesBox b rBuf X u v t} =
            {X : Fin n → Pt | X u ∈ interiorBox rBuf} ∩
            {X : Fin n → Pt | canonShape (Real.sqrt (n : ℝ) * (X u).1, Real.sqrt (n : ℝ) * (X u).2)
              (Real.sqrt (n : ℝ) * (X v).1, Real.sqrt (n : ℝ) * (X v).2)
              (Real.sqrt (n : ℝ) * (X t).1, Real.sqrt (n : ℝ) * (X t).2) ∈ boxRegion b} := by
          ext X; simp [MatchesBox, hne]
        rw [heq]
        have hsc : ∀ i : Fin n, Measurable (fun X : Fin n → Pt =>
            (Real.sqrt (n : ℝ) * (X i).1, Real.sqrt (n : ℝ) * (X i).2)) := fun i =>
          (measurable_const.mul (measurable_fst.comp (measurable_pi_apply i))).prodMk
            (measurable_const.mul (measurable_snd.comp (measurable_pi_apply i)))
        exact ((measurableSet_interiorBox rBuf).preimage (measurable_pi_apply u)).inter
          ((measurableSet_boxRegion b).preimage
            (measurable_canonShape.comp ((hsc u).prodMk ((hsc v).prodMk (hsc t)))))
      · have heq : {X : Fin n → Pt | MatchesBox b rBuf X u v t} = ∅ := by
          ext X; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro hm; exact hne ⟨hm.1, hm.2.1, hm.2.2.1⟩
        rw [heq]; exact MeasurableSet.empty
    have hm_cl : MeasurableSet {X : Fin n → Pt |
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
          measurableSet_lt measurable_const (hm_dist x z)
    refine Measurable.ite (hm_match.inter hm_cl) ?_ measurable_const
    refine measurable_const.sub (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun z _ => ?_)
    have hpx := hm_pot.comp (hm_nn2 x)
    have hpz := hm_pot.comp (hm_nn2 z)
    have hd := hm_dist x z
    exact (measurable_const.max (((hpx.add measurable_const).add hpz).sub hd)).sub
      (measurable_const.max (((hpx.add measurable_const).add hpz).sub hd))
  refine Integrable.of_bound hmeas.aestronglyMeasurable ((2 + 3 * (n : ℝ)) * |toR yj - toR yPrev|)
    (Eventually.of_forall fun X => ?_)
  unfold triExpr
  split_ifs with h
  · rw [Real.norm_eq_abs]
    have habs : ∀ a c : ℝ, |max 0 a - max 0 c| ≤ |a - c| := fun a c => by
      rw [abs_le]; simp only [max_def]; split_ifs <;>
        constructor <;> linarith [le_abs_self (a - c), neg_abs_le (a - c), abs_nonneg (a - c)]
    set S_sum := ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
        (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
         max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
    have hsum : |S_sum| ≤ (3 * (n : ℝ)) * |toR yj - toR yPrev| := by
      calc |S_sum|
          ≤ ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
              |toR yj - toR yPrev| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
            have h1 := habs
              (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
                stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z)
              (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
                stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z)
            have hd : (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
                  stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
                  stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) =
                toR yj - toR yPrev := by ring
            rwa [hd] at h1
        _ = (({u, v, t} : Finset (Fin n)).card : ℝ) *
              ((Finset.univ \ ({u, v, t} : Finset (Fin n))).card : ℝ) * |toR yj - toR yPrev| := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
        _ ≤ 3 * (n : ℝ) * |toR yj - toR yPrev| := by
            have hc1 : ({u, v, t} : Finset (Fin n)).card ≤ 3 :=
              (Finset.card_insert_le _ _).trans (by
                have := Finset.card_insert_le v {t}; simp at this; omega)
            have hc2 : (Finset.univ \ ({u, v, t} : Finset (Fin n))).card ≤ n :=
              (Finset.card_le_card Finset.sdiff_subset).trans (by simp)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul (by exact_mod_cast hc1) (by exact_mod_cast hc2) (Nat.cast_nonneg _) (by positivity))
              (abs_nonneg _)
    calc |2 * (toR yj - toR yPrev) - S_sum|
        ≤ |2 * (toR yj - toR yPrev)| + |S_sum| := abs_sub _ _
      _ = 2 * |toR yj - toR yPrev| + |S_sum| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
      _ ≤ 2 * |toR yj - toR yPrev| + (3 * (n : ℝ)) * |toR yj - toR yPrev| := add_le_add le_rfl hsum
      _ = (2 + 3 * (n : ℝ)) * |toR yj - toR yPrev| := by ring
  · rw [norm_zero]; positivity

private lemma integral_triExpr_sum_eq {n : ℕ} (hn : 4 ≤ n) (rho w : Array Int) (b : BoxCert)
    (yPrev rj yj : Int) (rBuf : ℝ) :
    ∫ X : Fin n → Pt,
      ((1 / (n : ℝ)) * ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
        triExpr hn rho w b yPrev rj yj rBuf u v t X) ∂(unitSquarePi n) =
    ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) *
      ∫ X : Fin n → Pt, triExpr hn rho w b yPrev rj yj rBuf ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ X
        ∂(unitSquarePi n) := by
  have hint : ∀ u v t : Fin n, Integrable (triExpr hn rho w b yPrev rj yj rBuf u v t) (unitSquarePi n) :=
    fun u v t => integrable_triExpr hn rho w b yPrev rj yj rBuf u v t
  rw [integral_const_mul,
      integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => integrable_finsetSum _ fun t _ => hint u v t]
  have hterm : ∀ u v t : Fin n,
      (∫ X : Fin n → Pt, triExpr hn rho w b yPrev rj yj rBuf u v t X ∂(unitSquarePi n)) =
      if u ≠ v ∧ u ≠ t ∧ v ≠ t then
        ∫ X : Fin n → Pt, triExpr hn rho w b yPrev rj yj rBuf ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ X
          ∂(unitSquarePi n)
      else 0 := by
    intro u v t
    by_cases hne : u ≠ v ∧ u ≠ t ∧ v ≠ t
    · rw [if_pos hne]
      obtain ⟨σ, h0, h1, h2⟩ := exists_perm_three hn hne.1 hne.2.1 hne.2.2
      have hmp := measurePreserving_perm_pi n σ.symm
      have hmap_int := integral_map (μ := unitSquarePi n) (φ := fun X : Fin n → Pt => X ∘ σ.symm)
        (f := triExpr hn rho w b yPrev rj yj rBuf u v t)
        hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact (hint u v t).aestronglyMeasurable)
      rw [hmp.map_eq] at hmap_int
      rw [hmap_int]
      refine integral_congr_ae (Eventually.of_forall fun X => ?_)
      have hperm := triExpr_comp_perm hn rho w b yPrev rj yj rBuf σ.symm u v t X
      have hs0 : σ.symm u = ⟨0, by omega⟩ := by rw [← h0]; simp
      have hs1 : σ.symm v = ⟨1, by omega⟩ := by rw [← h1]; simp
      have hs2 : σ.symm t = ⟨2, by omega⟩ := by rw [← h2]; simp
      rw [hs0, hs1, hs2] at hperm
      exact hperm
    · rw [if_neg hne]
      have h0 : triExpr hn rho w b yPrev rj yj rBuf u v t = fun _ => 0 := by
        ext X; unfold triExpr; rw [if_neg fun h => hne ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩]
      rw [h0, integral_zero]
  have hsum_u : ∀ u : Fin n,
      (∫ X : Fin n → Pt, (∑ v : Fin n, ∑ t : Fin n, triExpr hn rho w b yPrev rj yj rBuf u v t X) ∂(unitSquarePi n)) =
      ∑ v : Fin n, ∑ t : Fin n, ∫ X : Fin n → Pt, triExpr hn rho w b yPrev rj yj rBuf u v t X ∂(unitSquarePi n) := by
    intro u
    rw [integral_finsetSum _ fun v _ => integrable_finsetSum _ fun t _ => hint u v t]
    refine Finset.sum_congr rfl fun v _ => integral_finsetSum _ fun t _ => hint u v t
  have hsum_all : (∑ u : Fin n, ∫ X : Fin n → Pt,
        (∑ v : Fin n, ∑ t : Fin n, triExpr hn rho w b yPrev rj yj rBuf u v t X) ∂(unitSquarePi n)) =
      ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
        if u ≠ v ∧ u ≠ t ∧ v ≠ t then
          ∫ X : Fin n → Pt, triExpr hn rho w b yPrev rj yj rBuf ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ X
            ∂(unitSquarePi n)
        else 0 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hsum_u u]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun t _ => hterm u v t
  rw [hsum_all]
  -- Count ordered distinct triples `(u, v, t)` in `Fin n`: `n * (n - 1) * (n - 2)`
  set I0 := ∫ X : Fin n → Pt, triExpr hn rho w b yPrev rj yj rBuf ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ X
    ∂(unitSquarePi n)
  have hcount : ∀ u : Fin n,
      (∑ v : Fin n, ∑ t : Fin n, if u ≠ v ∧ u ≠ t ∧ v ≠ t then I0 else 0) =
      ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) * I0 := by
    intro u
    have hinner : ∀ v : Fin n,
        (∑ t : Fin n, if u ≠ v ∧ u ≠ t ∧ v ≠ t then I0 else 0) =
        if u ≠ v then ((n - 2 : ℕ) : ℝ) * I0 else 0 := by
      intro v
      by_cases huv : u ≠ v
      · rw [if_pos huv]
        have hrew : (∑ t : Fin n, if u ≠ v ∧ u ≠ t ∧ v ≠ t then I0 else 0) =
            ∑ _t ∈ (Finset.univ.erase u).erase v, I0 := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
          exact ⟨fun ⟨_, h1, h2⟩ => ⟨h2.symm, h1.symm⟩, fun ⟨h2, h1⟩ => ⟨huv, h1.symm, h2.symm⟩⟩
        rw [hrew, Finset.sum_const, nsmul_eq_mul,
            Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩),
            Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin, Nat.sub_sub]
      · rw [if_neg huv]; exact Finset.sum_eq_zero fun t _ => if_neg (fun h => huv h.1)
    simp_rw [hinner]
    have hrew2 : (∑ v : Fin n, if u ≠ v then ((n - 2 : ℕ) : ℝ) * I0 else 0) =
        ∑ _v ∈ Finset.univ.erase u, ((n - 2 : ℕ) : ℝ) * I0 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [hrew2, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, Fintype.card_fin, mul_assoc]
  simp_rw [hcount, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn_ne]

/-! ## Section 2: Splitting `unitSquarePi n` into `unitSquarePi 3 × unitSquarePi (n - 3)` -/

private def join3 {n : ℕ} (hn : 4 ≤ n) (p : (Fin 3 → Pt) × (Fin (n - 3) → Pt)) : Fin n → Pt :=
  fun i => (splitFinEquiv 3 (n - 3)).symm p (Fin.cast (by omega) i)

private lemma measurePreserving_join3 {n : ℕ} (hn : 4 ≤ n) :
    MeasurePreserving (join3 hn) ((unitSquarePi 3).prod (unitSquarePi (n - 3))) (unitSquarePi n) := by
  have hcast_mp : MeasurePreserving (fun X : Fin (3 + (n - 3)) → Pt => fun i : Fin n => X (Fin.cast (by omega) i))
      (unitSquarePi (3 + (n - 3))) (unitSquarePi n) := by
    have hmeas : Measurable (fun X : Fin (3 + (n - 3)) → Pt => fun i : Fin n => X (Fin.cast (by omega) i)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (Fin.cast (by omega) i)
    refine ⟨hmeas, ?_⟩
    symm
    unfold unitSquarePi
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    let s' : Fin (3 + (n - 3)) → Set Pt := fun j => s (Fin.cast (by omega) j)
    have hpre : (fun X : Fin (3 + (n - 3)) → Pt => fun i : Fin n => X (Fin.cast (by omega) i)) ⁻¹'
        Set.pi Set.univ s = Set.pi Set.univ s' := by
      ext X
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, s']
      constructor
      · intro h j
        have hj := h (Fin.cast (by omega) j)
        have hcast : Fin.cast (by omega : n = 3 + (n - 3)) (Fin.cast (by omega) j) = j := by ext; rfl
        rwa [hcast] at hj
      · intro h i
        have hi := h (Fin.cast (by omega) i)
        have hcast : Fin.cast (by omega : 3 + (n - 3) = n) (Fin.cast (by omega) i) = i := by ext; rfl
        rwa [hcast] at hi
    rw [hpre, Measure.pi_pi]
    refine Finset.prod_bij (fun i _ => Fin.cast (by omega) i) (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (by simpa [Fin.ext_iff] using h))
      (fun j _ => ⟨Fin.cast (by omega) j, Finset.mem_univ _, by ext; rfl⟩)
      (fun i _ => by simp [s'])
  exact hcast_mp.comp (measurePreserving_splitFinEquiv_symm 3 (n - 3))

/-! ## Section 3: Exact Finite-`n` Evaluation & Dominated Convergence (`levelGain_tendsto`) -/

/-- Exact Poisson limit of the finite-`n` expected net gain for a single telescoping level
`(yPrev, rj, yj)` of a certified box `b`. -/
theorem levelGain_tendsto {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) {yPrev rj yj : Int}
    (hyPrev_nn : 0 ≤ yPrev) (hy : yPrev < yj) (hrj_l1 : b.l1 < rj)
    (hhalf : 2 * (evalStepPot rho w b.l1 + yj) ≤ rj)
    {Rbuf : ℝ} (hRbuf_pos : 0 ≤ Rbuf)
    (hRbuf_r : toR b.l1 + toR rj ≤ Rbuf)
    (hRbuf_ext : ∀ i < rho.size,
      toR b.l1 + 2 * toR (w.getD (rho.size - 1) 0) + toR yj + toR (rho.getD i 0) ≤ Rbuf) :
    Tendsto (fun n : ℕ => if hn : 4 ≤ n then
      ∫ X : Fin n → Pt,
        ((1 / (n : ℝ)) * ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
          if MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t ∧
              (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                toR rj < rescaledDist X x z) then
            2 * (toR yj - toR yPrev) -
              ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yj +
                    stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                 max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR yPrev +
                    stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
          else 0) ∂(unitSquarePi n)
      else 0) atTop (nhds (levelGain rho w b yPrev rj yj)) := by
  obtain ⟨C, hC0, N0, hC⟩ := triCondVal_bound hpot hb hyPrev_nn hy hrj_l1 hhalf
  have hl0_pos : 0 < toR b.l0 := by
    have := div_lt_div_of_pos_right (by exact_mod_cast hb.l0_pos : (0 : ℝ) < (b.l0 : ℝ)) S_pos
    simpa [toR] using this
  have hl0_lt_l1 : toR b.l0 < toR b.l1 := div_lt_div_of_pos_right (by exact_mod_cast hb.l0_lt_l1) S_pos
  have hx0_lt_x1 : toR b.x0 < toR b.x1 := div_lt_div_of_pos_right (by exact_mod_cast hb.x0_lt_x1) S_pos
  have hy0_lt_y1 : toR b.y0 < toR b.y1 := div_lt_div_of_pos_right (by exact_mod_cast hb.y0_lt_y1) S_pos
  have hrj_pos : 0 < toR rj := lt_trans (lt_trans hl0_pos hl0_lt_l1)
    (div_lt_div_of_pos_right (by exact_mod_cast hrj_l1) S_pos)
  have hRbuf_l1 : toR b.l1 ≤ Rbuf := by linarith
  -- Choose `N1 ≥ max 5 N0` large enough that `Rbuf / √n ≤ 1 / 2` for all `n ≥ N1`
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, 5 ≤ N1 ∧ N0 ≤ N1 ∧ ∀ n ≥ N1, Rbuf / Real.sqrt (n : ℝ) ≤ 1 / 2 := by
    refine ⟨max (max 5 N0) (Nat.ceil ((2 * Rbuf) ^ 2) + 1), le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), fun n hn => ?_⟩
    have hn_ge : ((2 * Rbuf) ^ 2 : ℝ) < (n : ℝ) := by
      have h1 : Nat.ceil ((2 * Rbuf) ^ 2) + 1 ≤ n := le_trans (le_max_right _ _) hn
      have h2 : (2 * Rbuf) ^ 2 ≤ (Nat.ceil ((2 * Rbuf) ^ 2) : ℝ) := Nat.le_ceil _
      have h3 : (Nat.ceil ((2 * Rbuf) ^ 2) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
      linarith
    have hsqn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
    have h2R_le : 2 * Rbuf ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_sq (by linarith : 0 ≤ 2 * Rbuf)]
      exact Real.sqrt_le_sqrt (le_of_lt hn_ge)
    rw [div_le_iff₀ hsqn_pos]; linarith
  -- Exact evaluation for all `n ≥ N1`
  have heval : ∀ n ≥ N1,
      (if hn : 4 ≤ n then
        ∫ X : Fin n → Pt,
          ((1 / (n : ℝ)) * ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
            triExpr hn rho w b yPrev rj yj (Rbuf / Real.sqrt (n : ℝ)) u v t X) ∂(unitSquarePi n)
      else 0) =
      (((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) / (n : ℝ) ^ 2) *
      (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
      ∫ L in (toR b.l0)..(toR b.l1),
        ∫ x in (toR b.x0)..(toR b.x1),
          ∫ y in (toR b.y0)..(toR b.y1),
            (4 * Real.pi * L ^ 3) * triCondVal rho w yPrev rj yj n L (x, y) := by
    intro n hn
    have hn4 : 4 ≤ n := by omega
    have hn5 : 5 ≤ n := by omega
    rw [dif_pos hn4, integral_triExpr_sum_eq hn4]
    -- Split `unitSquarePi n` into `unitSquarePi 3 × unitSquarePi (n - 3)` via `join3`
    have hmp := measurePreserving_join3 hn4
    have hint0 := integrable_triExpr hn4 rho w b yPrev rj yj (Rbuf / Real.sqrt (n : ℝ))
      ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    have hmap_int := integral_map (μ := (unitSquarePi 3).prod (unitSquarePi (n - 3))) (φ := join3 hn4)
      (f := triExpr hn4 rho w b yPrev rj yj (Rbuf / Real.sqrt (n : ℝ))
        ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩)
      hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hint0.aestronglyMeasurable)
    rw [hmp.map_eq] at hmap_int
    rw [hmap_int]
    have hint_prod : Integrable (fun p : (Fin 3 → Pt) × (Fin (n - 3) → Pt) =>
        triExpr hn4 rho w b yPrev rj yj (Rbuf / Real.sqrt (n : ℝ))
          ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ (join3 hn4 p))
        ((unitSquarePi 3).prod (unitSquarePi (n - 3))) :=
      hmp.integrable_comp_of_integrable hint0
    rw [MeasureTheory.integral_prod _ hint_prod]
    -- Evaluate inner `Z`-integral for each `Y : Fin 3 → Pt`
    have hinner_Z : ∀ Y : Fin 3 → Pt,
        (∫ Z : Fin (n - 3) → Pt,
          triExpr hn4 rho w b yPrev rj yj (Rbuf / Real.sqrt (n : ℝ))
            ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ (join3 hn4 (Y, Z)) ∂(unitSquarePi (n - 3))) =
        if Y 0 ∈ interiorBox (Rbuf / Real.sqrt (n : ℝ)) ∧
            canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
              (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
              (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2) ∈ boxRegion b then
          triCondVal rho w yPrev rj yj n
            (canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
              (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
              (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2)).1
            (canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
              (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
              (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2)).2
        else 0 := by
      intro Y
      have hJ0 : ∀ Z, join3 hn4 (Y, Z) ⟨0, by omega⟩ = Y 0 := fun Z => by
        unfold join3 splitFinEquiv
        exact Fin.append_left Y Z (0 : Fin 3)
      have hJ1 : ∀ Z, join3 hn4 (Y, Z) ⟨1, by omega⟩ = Y 1 := fun Z => by
        unfold join3 splitFinEquiv
        exact Fin.append_left Y Z (1 : Fin 3)
      have hJ2 : ∀ Z, join3 hn4 (Y, Z) ⟨2, by omega⟩ = Y 2 := fun Z => by
        unfold join3 splitFinEquiv
        exact Fin.append_left Y Z (2 : Fin 3)
      have hmatch_iff : ∀ Z,
          MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) (join3 hn4 (Y, Z))
            ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ↔
          (Y 0 ∈ interiorBox (Rbuf / Real.sqrt (n : ℝ)) ∧
            canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
              (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
              (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2) ∈ boxRegion b) := fun Z => by
        unfold MatchesBox
        rw [hJ0 Z, hJ1 Z, hJ2 Z]
        simp [Fin.ext_iff]
      by_cases hY : Y 0 ∈ interiorBox (Rbuf / Real.sqrt (n : ℝ)) ∧
          canonShape (Real.sqrt (n : ℝ) * (Y 0).1, Real.sqrt (n : ℝ) * (Y 0).2)
            (Real.sqrt (n : ℝ) * (Y 1).1, Real.sqrt (n : ℝ) * (Y 1).2)
            (Real.sqrt (n : ℝ) * (Y 2).1, Real.sqrt (n : ℝ) * (Y 2).2) ∈ boxRegion b
      · rw [if_pos hY]
        have hcond := cond_integral_Z_eq_triCondVal hn5 hpot hb hyPrev_nn hy hrj_l1 hhalf
          hRbuf_pos hRbuf_r hRbuf_ext Y hY.1 hY.2
        rw [← hcond]
        refine integral_congr_ae (Eventually.of_forall fun Z => ?_)
        unfold triExpr
        refine if_congr (by rw [hmatch_iff Z]; exact ⟨fun h => h.2, fun h => ⟨hY, h⟩⟩) rfl rfl
      · rw [if_neg hY]
        have h0 : ∀ Z, triExpr hn4 rho w b yPrev rj yj (Rbuf / Real.sqrt (n : ℝ))
            ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ (join3 hn4 (Y, Z)) = 0 := fun Z => by
          unfold triExpr; exact if_neg (fun h => hY ((hmatch_iff Z).mp h.1))
        simp_rw [h0]; simp
    simp_rw [hinner_Z]
    rw [integral_unitSquarePi3_canonShape hb (by omega) hRbuf_pos hRbuf_l1 (hN1.2.2 n hn)
      (measurable_triCondVal rho w yPrev rj yj n) ⟨C, hC0, hC n (le_trans hN1.2.1 hn)⟩]
    ring
  -- Pass `n → ∞` using `Tendsto.congr'` + nested DCT on `Ioo`
  have htend_rhs : Tendsto (fun n : ℕ =>
      (((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) / (n : ℝ) ^ 2) *
      (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
      ∫ L in (toR b.l0)..(toR b.l1),
        ∫ x in (toR b.x0)..(toR b.x1),
          ∫ y in (toR b.y0)..(toR b.y1),
            (4 * Real.pi * L ^ 3) * triCondVal rho w yPrev rj yj n L (x, y)) atTop
      (nhds (levelGain rho w b yPrev rj yj)) := by
    -- 1. Prefactor `((n - 1) * (n - 2) / n^2) * (1 - 2 Rbuf / √n)^2 → 1 * 1 = 1`
    have hpre1 : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) / (n : ℝ) ^ 2) atTop (nhds 1) := by
      have h1 := tendsto_nat_sub_div_self 1
      have h2 := tendsto_nat_sub_div_self 2
      have hmul := h1.mul h2
      rw [one_mul] at hmul
      refine hmul.congr fun n => ?_; ring
    have hpre2 : Tendsto (fun n : ℕ => (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2) atTop (nhds 1) :=
      tendsto_one_sub_inv_sqrt_sq Rbuf
    -- 2. Triple integral converges to `levelGain rho w b yPrev rj yj` via nested DCT
    let G : ℕ → ℝ → Pt → ℝ := fun n L pt => (4 * Real.pi * L ^ 3) * triCondVal rho w yPrev rj yj n L pt
    let G_lim : ℝ → Pt → ℝ := fun L pt =>
      (4 * Real.pi * L ^ 3) *
        Real.exp (-unionDiskArea (triVerts L pt) (toR rj)) *
        (2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L pt)
    let B : ℝ := (4 * Real.pi * (toR b.l1) ^ 3) * C
    have hl1_pos : 0 < toR b.l1 := lt_trans hl0_pos hl0_lt_l1
    have hG_bdd : ∀ n ≥ N0, ∀ L pt, (L, pt) ∈ boxRegion b → ‖G n L pt‖ ≤ B := by
      intro n hn L pt hmem
      dsimp only [G, B]
      have hL0 : 0 ≤ L := le_of_lt (lt_trans hl0_pos hmem.1)
      have hL1 : L ≤ toR b.l1 := le_of_lt hmem.2.1
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL1 3) (by positivity))
        (hC n hn L pt hmem) (norm_nonneg _) (by positivity)
    -- Innermost `y`-integral DCT for fixed `(L, x) ∈ Ioo l0 l1 × Ioo x0 x1`
    have htend_y : ∀ L ∈ Ioo (toR b.l0) (toR b.l1), ∀ x ∈ Ioo (toR b.x0) (toR b.x1),
        Tendsto (fun n : ℕ => ∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y)) atTop
          (nhds (∫ y in Ioo (toR b.y0) (toR b.y1), G_lim L (x, y))) := by
      intro L hL x hx
      have hfin_y : volume (Ioo (toR b.y0) (toR b.y1)) < ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      haveI : IsFiniteMeasure (volume.restrict (Ioo (toR b.y0) (toR b.y1))) := ⟨by
        rw [Measure.restrict_apply_univ]; exact hfin_y⟩
      refine tendsto_integral_of_dominated_convergence (fun _ => B) ?_ (integrable_const B) ?_ ?_
      · intro n
        exact ((measurable_const.mul (measurable_triCondVal rho w yPrev rj yj (n + N0))).comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
      · intro n
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        exact hG_bdd (n + N0) (by omega) L (x, y) ⟨hL.1, hL.2, hx.1, hx.2, hy.1, hy.2⟩
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy_mem
        have ht := (tendsto_triCondVal hpot hb hyPrev_nn hy hrj_l1 hhalf (L := L) (pt := (x, y))
          ⟨hL.1, hL.2, hx.1, hx.2, hy_mem.1, hy_mem.2⟩).comp (tendsto_add_atTop_nat N0)
        have hmul := ht.const_mul (4 * Real.pi * L ^ 3)
        simpa [G, G_lim, mul_assoc] using hmul
    -- Middle `x`-integral DCT for fixed `L ∈ Ioo l0 l1`
    have hBy_bdd : ∀ n : ℕ, ∀ L ∈ Ioo (toR b.l0) (toR b.l1), ∀ x ∈ Ioo (toR b.x0) (toR b.x1),
        ‖∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y)‖ ≤ B * (toR b.y1 - toR b.y0) := by
      intro n L hL x hx
      have hfin_y : volume (Ioo (toR b.y0) (toR b.y1)) < ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      haveI : IsFiniteMeasure (volume.restrict (Ioo (toR b.y0) (toR b.y1))) := ⟨by
        rw [Measure.restrict_apply_univ]; exact hfin_y⟩
      have hint_y : IntegrableOn (fun y => G (n + N0) L (x, y)) (Ioo (toR b.y0) (toR b.y1)) volume := by
        refine Integrable.of_bound
          (((measurable_const.mul (measurable_triCondVal rho w yPrev rj yj (n + N0))).comp
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable) B ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        exact hG_bdd (n + N0) (by omega) L (x, y) ⟨hL.1, hL.2, hx.1, hx.2, hy.1, hy.2⟩
      calc ‖∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y)‖
          ≤ ∫ y in Ioo (toR b.y0) (toR b.y1), ‖G (n + N0) L (x, y)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ _ in Ioo (toR b.y0) (toR b.y1), B :=
            setIntegral_mono_on hint_y.norm (integrable_const B) measurableSet_Ioo fun y hy =>
              hG_bdd (n + N0) (by omega) L (x, y) ⟨hL.1, hL.2, hx.1, hx.2, hy.1, hy.2⟩
        _ = B * (toR b.y1 - toR b.y0) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
                ENNReal.toReal_ofReal (by linarith)]; ring
    have htend_x : ∀ L ∈ Ioo (toR b.l0) (toR b.l1),
        Tendsto (fun n : ℕ => ∫ x in Ioo (toR b.x0) (toR b.x1),
            ∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y)) atTop
          (nhds (∫ x in Ioo (toR b.x0) (toR b.x1),
            ∫ y in Ioo (toR b.y0) (toR b.y1), G_lim L (x, y))) := by
      intro L hL
      have hfin_x : volume (Ioo (toR b.x0) (toR b.x1)) < ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      haveI : IsFiniteMeasure (volume.restrict (Ioo (toR b.x0) (toR b.x1))) := ⟨by
        rw [Measure.restrict_apply_univ]; exact hfin_x⟩
      refine tendsto_integral_of_dominated_convergence (fun _ => B * (toR b.y1 - toR b.y0))
        ?_ (integrable_const _) ?_ ?_
      · intro n
        have hG_sm : StronglyMeasurable (fun q : ℝ × ℝ => G (n + N0) L (q.1, q.2)) :=
          ((measurable_const.mul (measurable_triCondVal rho w yPrev rj yj (n + N0))).comp
            (measurable_const.prodMk measurable_id)).stronglyMeasurable
        exact hG_sm.integral_prod_right'.aestronglyMeasurable
      · intro n
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact hBy_bdd n L hL x hx
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact htend_y L hL x hx
    -- Outer `L`-integral DCT
    have hBx_bdd : ∀ n : ℕ, ∀ L ∈ Ioo (toR b.l0) (toR b.l1),
        ‖∫ x in Ioo (toR b.x0) (toR b.x1), ∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y)‖ ≤
          B * (toR b.y1 - toR b.y0) * (toR b.x1 - toR b.x0) := by
      intro n L hL
      have hfin_x : volume (Ioo (toR b.x0) (toR b.x1)) < ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      haveI : IsFiniteMeasure (volume.restrict (Ioo (toR b.x0) (toR b.x1))) := ⟨by
        rw [Measure.restrict_apply_univ]; exact hfin_x⟩
      have hG_sm : StronglyMeasurable (fun q : ℝ × ℝ => G (n + N0) L (q.1, q.2)) :=
        ((measurable_const.mul (measurable_triCondVal rho w yPrev rj yj (n + N0))).comp
          (measurable_const.prodMk measurable_id)).stronglyMeasurable
      have hint_x : IntegrableOn (fun x => ∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y))
          (Ioo (toR b.x0) (toR b.x1)) volume := by
        refine Integrable.of_bound hG_sm.integral_prod_right'.aestronglyMeasurable (B * (toR b.y1 - toR b.y0)) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact hBy_bdd n L hL x hx
      calc ‖∫ x in Ioo (toR b.x0) (toR b.x1), ∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y)‖
          ≤ ∫ x in Ioo (toR b.x0) (toR b.x1), ‖∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ _ in Ioo (toR b.x0) (toR b.x1), B * (toR b.y1 - toR b.y0) :=
            setIntegral_mono_on hint_x.norm (integrable_const _) measurableSet_Ioo (hBy_bdd n L hL)
        _ = B * (toR b.y1 - toR b.y0) * (toR b.x1 - toR b.x0) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
                ENNReal.toReal_ofReal (by linarith)]; ring
    have htend_L_shift : Tendsto (fun n : ℕ =>
          ∫ L in Ioo (toR b.l0) (toR b.l1),
            ∫ x in Ioo (toR b.x0) (toR b.x1),
              ∫ y in Ioo (toR b.y0) (toR b.y1), G (n + N0) L (x, y)) atTop
        (nhds (∫ L in Ioo (toR b.l0) (toR b.l1),
            ∫ x in Ioo (toR b.x0) (toR b.x1),
              ∫ y in Ioo (toR b.y0) (toR b.y1), G_lim L (x, y))) := by
      have hfin_L : volume (Ioo (toR b.l0) (toR b.l1)) < ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      haveI : IsFiniteMeasure (volume.restrict (Ioo (toR b.l0) (toR b.l1))) := ⟨by
        rw [Measure.restrict_apply_univ]; exact hfin_L⟩
      refine tendsto_integral_of_dominated_convergence (fun _ => B * (toR b.y1 - toR b.y0) * (toR b.x1 - toR b.x0))
        ?_ (integrable_const _) ?_ ?_
      · intro n
        have hG_sm : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => G (n + N0) q.1.1 (q.1.2, q.2)) :=
          (((measurable_const.mul ((measurable_fst.comp measurable_fst).pow_const 3)).mul
            ((measurable_triCondVal rho w yPrev rj yj (n + N0)).comp
              ((measurable_fst.comp measurable_fst).prodMk
                ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))).stronglyMeasurable
        exact hG_sm.integral_prod_right'.integral_prod_right'.aestronglyMeasurable
      · intro n
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with L hL
        exact hBx_bdd n L hL
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with L hL
        exact htend_x L hL
    have htend_L : Tendsto (fun n : ℕ =>
          ∫ L in (toR b.l0)..(toR b.l1),
            ∫ x in (toR b.x0)..(toR b.x1),
              ∫ y in (toR b.y0)..(toR b.y1), G n L (x, y)) atTop
        (nhds (levelGain rho w b yPrev rj yj)) := by
      have hshift_back := (tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => ∫ L in Ioo (toR b.l0) (toR b.l1),
          ∫ x in Ioo (toR b.x0) (toR b.x1), ∫ y in Ioo (toR b.y0) (toR b.y1), G n L (x, y)) N0).mp htend_L_shift
      have hlim_eq : (∫ L in Ioo (toR b.l0) (toR b.l1),
            ∫ x in Ioo (toR b.x0) (toR b.x1),
              ∫ y in Ioo (toR b.y0) (toR b.y1), G_lim L (x, y)) = levelGain rho w b yPrev rj yj := by
        unfold levelGain
        rw [intervalIntegral.integral_of_le (le_of_lt hl0_lt_l1), MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun L _ => ?_
        rw [intervalIntegral.integral_of_le (le_of_lt hx0_lt_x1), MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
        rw [intervalIntegral.integral_of_le (le_of_lt hy0_lt_y1), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [hlim_eq] at hshift_back
      refine hshift_back.congr fun n => ?_
      rw [intervalIntegral.integral_of_le (le_of_lt hl0_lt_l1), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun L _ => ?_
      rw [intervalIntegral.integral_of_le (le_of_lt hx0_lt_x1), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
      rw [intervalIntegral.integral_of_le (le_of_lt hy0_lt_y1), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hprod := (hpre1.mul hpre2).mul htend_L
    simpa [G] using hprod
  refine htend_rhs.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop N1] with n hn
  exact (heval n hn).symm

end

end BHHBounds.Dual
