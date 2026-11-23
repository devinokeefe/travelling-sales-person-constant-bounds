import BHHBounds.Dual.FiniteN

/-!
# Finite-`n` to Poisson Convergence for the 1D Base Dual

Proves integrability and exact asymptotic bounds for the 2-factor base dual on `n` i.i.d.
uniform points in `[0, 1]²`:
1. `integrable_baseTerm1_integrand`, `integrable_basePen_integrand`: integrability of the
   first-order potential sum and the pair-penalty sum under `unitSquarePi n`.
2. `baseTerm1_lower_tendsto`: finite-`n` lower bound sequence converging to `baseTerm1 rho w`.
3. `basePen_upper_tendsto`: finite-`n` upper bound sequence converging to
   `basePenMarg rho w + basePenInter rho w`.
-/

open MeasureTheory Set Real Filter Finset Topology
open scoped ENNReal Classical
open BHHBounds.Geometry
open BHHBounds.Cert

namespace BHHBounds.Dual

noncomputable section

/-! ## Section 1: Measurability & Integrability -/

lemma measurable_rescaledDist {n : ℕ} (i j : Fin n) :
    Measurable (fun X : Fin n → Pt => rescaledDist X i j) := by
  unfold rescaledDist
  have hp : Measurable (fun X : Fin n → Pt => (X i, X j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hd : Measurable (fun X : Fin n → Pt => euclidDist (X i) (X j)) :=
    measurable_euclidDist.comp hp
  exact measurable_const.mul hd

lemma measurable_nn2 {n : ℕ} (hn : 3 ≤ n) (u : Fin n) :
    Measurable (fun X : Fin n → Pt => nn2 hn (rescaledDist X) u) := by
  unfold nn2
  have hpair : ∀ p : Fin n × Fin n,
      Measurable (fun X : Fin n → Pt => max (rescaledDist X u p.1) (rescaledDist X u p.2)) :=
    fun p => (measurable_rescaledDist u p.1).max (measurable_rescaledDist u p.2)
  have hinf : ∀ (s : Finset (Fin n × Fin n)) (hs : s.Nonempty),
      Measurable (fun X : Fin n → Pt =>
        s.inf' hs fun p => max (rescaledDist X u p.1) (rescaledDist X u p.2)) := by
    intro s
    refine Finset.induction_on s (fun hs => absurd hs (by simp)) fun a t hat ih _ => ?_
    by_cases ht : t.Nonempty
    · have hfn : (fun X : Fin n → Pt =>
          (insert a t).inf' (Finset.insert_nonempty a t)
            fun p => max (rescaledDist X u p.1) (rescaledDist X u p.2)) =
          fun X => min (max (rescaledDist X u a.1) (rescaledDist X u a.2))
            (t.inf' ht fun p => max (rescaledDist X u p.1) (rescaledDist X u p.2)) := by
        funext X; exact Finset.inf'_insert ht _
      rw [hfn]; exact (hpair a).min (ih ht)
    · have hte : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst hte
      simpa using hpair a
  exact hinf (neighborPairs u) (neighborPairs_nonempty hn u)

lemma measurable_stepPot (rho w : Array Int) : Measurable (stepPot rho w) := by
  unfold stepPot
  refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

lemma integrable_stepPot_nn2 {n : ℕ} (hn : 3 ≤ n) {rho w : Array Int}
    (hpot : ValidStepPot rho w) (u : Fin n) :
    Integrable (fun X : Fin n → Pt => stepPot rho w (nn2 hn (rescaledDist X) u))
      (unitSquarePi n) := by
  refine Integrable.of_bound
    ((measurable_stepPot rho w).comp (measurable_nn2 hn u)).aestronglyMeasurable
    (toR (w.getD (rho.size - 1) 0)) (Eventually.of_forall fun X => ?_)
  rw [Real.norm_of_nonneg (stepPot_nonneg hpot _)]
  exact stepPot_le_wMax hpot _

lemma integrable_pairPen_term {n : ℕ} (hn : 3 ≤ n) {rho w : Array Int}
    (hpot : ValidStepPot rho w) (u v : Fin n) :
    Integrable (fun X : Fin n → Pt =>
      max 0 (stepPot rho w (nn2 hn (rescaledDist X) u) +
        stepPot rho w (nn2 hn (rescaledDist X) v) - rescaledDist X u v))
      (unitSquarePi n) := by
  have hmeas : Measurable (fun X : Fin n → Pt =>
      max 0 (stepPot rho w (nn2 hn (rescaledDist X) u) +
        stepPot rho w (nn2 hn (rescaledDist X) v) - rescaledDist X u v)) :=
    measurable_const.max
      ((((measurable_stepPot rho w).comp (measurable_nn2 hn u)).add
        ((measurable_stepPot rho w).comp (measurable_nn2 hn v))).sub
        (measurable_rescaledDist u v))
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (2 * toR (w.getD (rho.size - 1) 0)) (Eventually.of_forall fun X => ?_)
  rw [Real.norm_of_nonneg (le_max_left _ _)]
  have hwMax_nn : 0 ≤ toR (w.getD (rho.size - 1) 0) :=
    toR_nonneg (hpot.w_nonneg (by have := hpot.size_pos; omega))
  exact max_le (by linarith) (by
    linarith [stepPot_le_wMax hpot (nn2 hn (rescaledDist X) u),
      stepPot_le_wMax hpot (nn2 hn (rescaledDist X) v),
      rescaledDist_nonneg X u v])

lemma integrable_baseTerm1_integrand {n : ℕ} (hn : 4 ≤ n)
    {rho w : Array Int} (hpot : ValidStepPot rho w) :
    Integrable (fun X : Fin n → Pt =>
      (2 / (n : ℝ)) * ∑ u : Fin n, stepPot rho w (nn2 (by omega) (rescaledDist X) u))
      (unitSquarePi n) :=
  (integrable_finsetSum _ fun u _ => integrable_stepPot_nn2 (by omega) hpot u).const_mul _

lemma integrable_basePen_integrand {n : ℕ} (hn : 4 ≤ n)
    {rho w : Array Int} (hpot : ValidStepPot rho w) :
    Integrable (fun X : Fin n → Pt =>
      (1 / (2 * (n : ℝ))) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u,
        max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
          stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v))
      (unitSquarePi n) :=
  (integrable_finsetSum _ fun u _ =>
    integrable_finsetSum _ fun v _ =>
      integrable_pairPen_term (by omega) hpot u v).const_mul _

/-! ## Section 2: Exchangeability & Coordinate Splitting -/

private lemma nn2_comp_perm {n : ℕ} (hn : 3 ≤ n) (X : Fin n → Pt)
    (σ : Equiv.Perm (Fin n)) (u : Fin n) :
    nn2 hn (rescaledDist (X ∘ σ)) u = nn2 hn (rescaledDist X) (σ u) := by
  unfold nn2
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    rintro ⟨a, b⟩ hab
    rcases Finset.mem_filter.mp hab with ⟨hprod, hne⟩
    rcases Finset.mem_product.mp hprod with ⟨ha, hb⟩
    have ha' : σ.symm a ∈ Finset.univ.erase u :=
      Finset.mem_erase.mpr ⟨fun he => Finset.ne_of_mem_erase ha (by rw [← he, σ.apply_symm_apply]),
        Finset.mem_univ _⟩
    have hb' : σ.symm b ∈ Finset.univ.erase u :=
      Finset.mem_erase.mpr ⟨fun he => Finset.ne_of_mem_erase hb (by rw [← he, σ.apply_symm_apply]),
        Finset.mem_univ _⟩
    have hmem : (σ.symm a, σ.symm b) ∈ neighborPairs u :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha', hb'⟩, fun he => hne (σ.symm.injective he)⟩
    refine (Finset.inf'_le _ hmem).trans ?_
    simp [rescaledDist]
  · rw [Finset.le_inf'_iff]
    rintro ⟨a, b⟩ hab
    rcases Finset.mem_filter.mp hab with ⟨hprod, hne⟩
    rcases Finset.mem_product.mp hprod with ⟨ha, hb⟩
    have ha' : σ a ∈ Finset.univ.erase (σ u) :=
      Finset.mem_erase.mpr ⟨fun he => Finset.ne_of_mem_erase ha (σ.injective he), Finset.mem_univ _⟩
    have hb' : σ b ∈ Finset.univ.erase (σ u) :=
      Finset.mem_erase.mpr ⟨fun he => Finset.ne_of_mem_erase hb (σ.injective he), Finset.mem_univ _⟩
    have hmem : (σ a, σ b) ∈ neighborPairs (σ u) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha', hb'⟩, fun he => hne (σ.injective he)⟩
    refine (Finset.inf'_le _ hmem).trans ?_
    simp [rescaledDist]

private lemma integral_baseTerm1_eq_single {n : ℕ} (hn : 4 ≤ n)
    {rho w : Array Int} (hpot : ValidStepPot rho w) :
    ∫ X : Fin n → Pt,
        ((2 / (n : ℝ)) * ∑ u : Fin n, stepPot rho w (nn2 (by omega) (rescaledDist X) u))
        ∂(unitSquarePi n) =
      2 * ∫ X : Fin n → Pt,
        stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩)
        ∂(unitSquarePi n) := by
  rw [integral_const_mul, integral_finsetSum _ fun u _ => integrable_stepPot_nn2 (by omega) hpot u]
  have hsym : ∀ u : Fin n,
      ∫ X : Fin n → Pt, stepPot rho w (nn2 (by omega) (rescaledDist X) u) ∂(unitSquarePi n) =
      ∫ X : Fin n → Pt, stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩)
        ∂(unitSquarePi n) := by
    intro u
    let σ : Equiv.Perm (Fin n) := Equiv.swap ⟨0, by omega⟩ u
    have hmp := measurePreserving_perm_pi n σ
    have hmeas : AEStronglyMeasurable
        (fun X : Fin n → Pt => stepPot rho w (nn2 (by omega) (rescaledDist X) u))
        ((unitSquarePi n).map (fun X => X ∘ σ)) := by
      rw [hmp.map_eq]
      exact (integrable_stepPot_nn2 (by omega) hpot u).aestronglyMeasurable
    conv_lhs => rw [← hmp.map_eq]
    rw [integral_map hmp.measurable.aemeasurable hmeas]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    dsimp only
    rw [nn2_comp_perm (by omega) X σ u]
    have hσu : σ u = ⟨0, by omega⟩ := Equiv.swap_apply_right _ _
    rw [hσu]
  simp_rw [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn0]

private lemma integral_basePen_eq_pair {n : ℕ} (hn : 4 ≤ n)
    {rho w : Array Int} (hpot : ValidStepPot rho w) :
    ∫ X : Fin n → Pt,
        ((1 / (2 * (n : ℝ))) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u,
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
            stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v))
        ∂(unitSquarePi n) =
      (((n - 1 : ℕ) : ℝ) / 2) * ∫ X : Fin n → Pt,
        max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩) +
          stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨1, by omega⟩) -
          rescaledDist X ⟨0, by omega⟩ ⟨1, by omega⟩)
        ∂(unitSquarePi n) := by
  rw [integral_const_mul,
    integral_finsetSum _ fun u _ =>
      integrable_finsetSum _ fun v _ => integrable_pairPen_term (by omega) hpot u v]
  have hinner : ∀ u : Fin n,
      ∫ X : Fin n → Pt, (∑ v ∈ Finset.univ.erase u,
        max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
          stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v))
        ∂(unitSquarePi n) =
      ((n - 1 : ℕ) : ℝ) * ∫ X : Fin n → Pt,
        max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩) +
          stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨1, by omega⟩) -
          rescaledDist X ⟨0, by omega⟩ ⟨1, by omega⟩)
        ∂(unitSquarePi n) := by
    intro u
    rw [integral_finsetSum _ fun v _ => integrable_pairPen_term (by omega) hpot u v]
    have hsym : ∀ v ∈ Finset.univ.erase u,
        ∫ X : Fin n → Pt,
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
            stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v)
          ∂(unitSquarePi n) =
        ∫ X : Fin n → Pt,
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩) +
            stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨1, by omega⟩) -
            rescaledDist X ⟨0, by omega⟩ ⟨1, by omega⟩)
          ∂(unitSquarePi n) := by
      intro v hv
      have hvu : v ≠ u := Finset.ne_of_mem_erase hv
      let i0 : Fin n := ⟨0, by omega⟩
      let i1 : Fin n := ⟨1, by omega⟩
      have h01 : i0 ≠ i1 := by intro h; simp [i0, i1] at h
      let τ₁ : Equiv.Perm (Fin n) := Equiv.swap i0 u
      let w₁ : Fin n := τ₁.symm v
      have hw₁_ne : w₁ ≠ i0 := by
        intro h
        have hv' : v = τ₁ i0 := by rw [← h, τ₁.apply_symm_apply]
        rw [Equiv.swap_apply_left] at hv'
        exact hvu hv'
      let τ₂ : Equiv.Perm (Fin n) := Equiv.swap i1 w₁
      let σ : Equiv.Perm (Fin n) := τ₁ * τ₂
      have hσ0 : σ i0 = u := by
        change τ₁ (τ₂ i0) = u
        rw [Equiv.swap_apply_of_ne_of_ne h01 hw₁_ne.symm]
        exact Equiv.swap_apply_left i0 u
      have hσ1 : σ i1 = v := by
        change τ₁ (τ₂ i1) = v
        rw [Equiv.swap_apply_left]
        exact τ₁.apply_symm_apply v
      have hσu : σ.symm u = i0 := σ.symm_apply_eq.mpr hσ0.symm
      have hσv : σ.symm v = i1 := σ.symm_apply_eq.mpr hσ1.symm
      have hmp := measurePreserving_perm_pi n σ.symm
      have hmeas : AEStronglyMeasurable (fun X : Fin n → Pt =>
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
            stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v))
          ((unitSquarePi n).map (fun X => X ∘ σ.symm)) := by
        rw [hmp.map_eq]
        exact (integrable_pairPen_term (by omega) hpot u v).aestronglyMeasurable
      conv_lhs => rw [← hmp.map_eq]
      rw [integral_map hmp.measurable.aemeasurable hmeas]
      refine integral_congr_ae (Eventually.of_forall fun X => ?_)
      dsimp only
      have h1 : nn2 (by omega) (rescaledDist (X ∘ σ.symm)) u = nn2 (by omega) (rescaledDist X) i0 := by
        rw [nn2_comp_perm (by omega) X σ.symm u, hσu]
      have h2 : nn2 (by omega) (rescaledDist (X ∘ σ.symm)) v = nn2 (by omega) (rescaledDist X) i1 := by
        rw [nn2_comp_perm (by omega) X σ.symm v, hσv]
      have h3 : rescaledDist (X ∘ σ.symm) u v = rescaledDist X i0 i1 := by
        simp [rescaledDist, hσu, hσv]
      rw [h1, h2, h3]
    rw [Finset.sum_congr rfl hsym, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn0]

/-- Prepend a single point `x₀` to `Z : Fin (n - 1) → Pt` to form `Fin n → Pt`. -/
private def consPt {n : ℕ} (hn : 1 ≤ n) (x₀ : Pt) (Z : Fin (n - 1) → Pt) : Fin n → Pt :=
  fun i => if h : i.val = 0 then x₀ else Z ⟨i.val - 1, by omega⟩

private lemma measurable_consPt {n : ℕ} (hn : 1 ≤ n) :
    Measurable (fun p : Pt × (Fin (n - 1) → Pt) => consPt hn p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h0 : i.val = 0
  · simp only [consPt, dif_pos h0]; exact measurable_fst
  · simp only [consPt, dif_neg h0]; exact (measurable_pi_apply _).comp measurable_snd

private lemma measurePreserving_consPt {n : ℕ} (hn : 1 ≤ n) :
    MeasurePreserving (fun p : Pt × (Fin (n - 1) → Pt) => consPt hn p.1 p.2)
      (unitSquareMeasure.prod (unitSquarePi (n - 1))) (unitSquarePi n) := by
  refine ⟨measurable_consPt hn, ?_⟩
  symm
  unfold unitSquarePi
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_consPt hn) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : Pt × (Fin (n - 1) → Pt) => consPt hn p.1 p.2) ⁻¹' Set.pi Set.univ s =
      s ⟨0, by omega⟩ ×ˢ Set.pi Set.univ (fun j : Fin (n - 1) => s ⟨j.val + 1, by omega⟩) := by
    ext ⟨x₀, Z⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨?_, fun j => ?_⟩
      · simpa [consPt] using h ⟨0, by omega⟩
      · have hj := h ⟨j.val + 1, by omega⟩
        simpa [consPt] using hj
    · rintro ⟨hx, hZ⟩ i
      by_cases h0 : i.val = 0
      · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
        rw [hi]; simpa [consPt] using hx
      · have hZ' := hZ ⟨i.val - 1, by omega⟩
        have hi : (⟨i.val - 1 + 1, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
        rw [hi] at hZ'
        simpa [consPt, h0] using hZ'
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun i : Fin n => unitSquareMeasure (s i))
    (Finset.mem_univ ⟨0, by omega⟩)]
  congr 1
  refine Finset.prod_bij (fun j _ => (⟨j.val + 1, by omega⟩ : Fin n))
    (fun j _ => Finset.mem_erase.mpr ⟨by intro h; simp [Fin.ext_iff] at h, Finset.mem_univ _⟩)
    (fun j₁ _ j₂ _ he => Fin.ext (by have := congrArg Fin.val he; dsimp at this; omega))
    (fun i hi => by
      have hne : i.val ≠ 0 := fun h => Finset.ne_of_mem_erase hi (Fin.ext h)
      have := i.isLt
      exact ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, Fin.ext (by simp; omega)⟩)
    (fun _ _ => rfl)

/-- Prepend two points `(x₀, x₁)` to `Z : Fin (n - 2) → Pt` to form `Fin n → Pt`. -/
private def consTwoPt {n : ℕ} (hn : 2 ≤ n) (x₀ x₁ : Pt) (Z : Fin (n - 2) → Pt) : Fin n → Pt :=
  fun i => if h0 : i.val = 0 then x₀ else if h1 : i.val = 1 then x₁ else Z ⟨i.val - 2, by omega⟩

private lemma consTwoPt_zero {n : ℕ} (hn : 2 ≤ n) (x₀ x₁ : Pt) (Z : Fin (n - 2) → Pt) :
    consTwoPt hn x₀ x₁ Z ⟨0, by omega⟩ = x₀ := by
  simp [consTwoPt]

private lemma consTwoPt_one {n : ℕ} (hn : 2 ≤ n) (x₀ x₁ : Pt) (Z : Fin (n - 2) → Pt) :
    consTwoPt hn x₀ x₁ Z ⟨1, by omega⟩ = x₁ := by
  simp [consTwoPt]

private lemma consTwoPt_rest {n : ℕ} (hn : 2 ≤ n) (x₀ x₁ : Pt) (Z : Fin (n - 2) → Pt)
    (j : Fin (n - 2)) :
    consTwoPt hn x₀ x₁ Z ⟨j.val + 2, by omega⟩ = Z j := by
  simp [consTwoPt]

private lemma measurable_consTwoPt {n : ℕ} (hn : 2 ≤ n) :
    Measurable (fun p : Pt × (Pt × (Fin (n - 2) → Pt)) => consTwoPt hn p.1 p.2.1 p.2.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h0 : i.val = 0
  · simp only [consTwoPt, dif_pos h0]; exact measurable_fst
  · by_cases h1 : i.val = 1
    · simp only [consTwoPt, dif_neg h0, dif_pos h1]; exact measurable_fst.comp measurable_snd
    · simp only [consTwoPt, dif_neg h0, dif_neg h1]
      exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)

private lemma measurePreserving_consTwoPt {n : ℕ} (hn : 2 ≤ n) :
    MeasurePreserving (fun p : Pt × (Pt × (Fin (n - 2) → Pt)) => consTwoPt hn p.1 p.2.1 p.2.2)
      (unitSquareMeasure.prod (unitSquareMeasure.prod (unitSquarePi (n - 2)))) (unitSquarePi n) := by
  refine ⟨measurable_consTwoPt hn, ?_⟩
  symm
  unfold unitSquarePi
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_consTwoPt hn) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : Pt × (Pt × (Fin (n - 2) → Pt)) => consTwoPt hn p.1 p.2.1 p.2.2) ⁻¹'
        Set.pi Set.univ s =
      s ⟨0, by omega⟩ ×ˢ (s ⟨1, by omega⟩ ×ˢ
        Set.pi Set.univ (fun j : Fin (n - 2) => s ⟨j.val + 2, by omega⟩)) := by
    ext ⟨x₀, x₁, Z⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨?_, ?_, fun j => ?_⟩
      · simpa [consTwoPt] using h ⟨0, by omega⟩
      · simpa [consTwoPt] using h ⟨1, by omega⟩
      · simpa [consTwoPt] using h ⟨j.val + 2, by omega⟩
    · rintro ⟨hx₀, hx₁, hZ⟩ i
      by_cases h0 : i.val = 0
      · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
        rw [hi]; simpa [consTwoPt] using hx₀
      · by_cases h1 : i.val = 1
        · have hi : i = ⟨1, by omega⟩ := Fin.ext h1
          rw [hi]; simpa [consTwoPt] using hx₁
        · have hZ' := hZ ⟨i.val - 2, by have := i.isLt; omega⟩
          have hi : (⟨i.val - 2 + 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
          rw [hi] at hZ'
          simpa [consTwoPt, h0, h1] using hZ'
  rw [hpre, Measure.prod_prod, Measure.prod_prod, Measure.pi_pi]
  have h01 : (⟨1, by omega⟩ : Fin n) ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin n) :=
    Finset.mem_erase.mpr ⟨by intro h; simp [Fin.ext_iff] at h, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun i : Fin n => unitSquareMeasure (s i))
      (Finset.mem_univ ⟨0, by omega⟩),
    ← Finset.mul_prod_erase (Finset.univ.erase ⟨0, by omega⟩)
      (fun i : Fin n => unitSquareMeasure (s i)) h01]
  congr 2
  refine Finset.prod_bij (fun j _ => (⟨j.val + 2, by omega⟩ : Fin n))
    (fun j _ => Finset.mem_erase.mpr ⟨by intro h; simp [Fin.ext_iff] at h,
      Finset.mem_erase.mpr ⟨by intro h; simp [Fin.ext_iff] at h, Finset.mem_univ _⟩⟩)
    (fun j₁ _ j₂ _ he => Fin.ext (by have := congrArg Fin.val he; dsimp at this; omega))
    (fun i hi => by
      have h1 : i.val ≠ 1 := fun h => Finset.ne_of_mem_erase hi (Fin.ext h)
      have h0 : i.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi) (Fin.ext h)
      have := i.isLt
      exact ⟨⟨i.val - 2, by omega⟩, Finset.mem_univ _, Fin.ext (by simp; omega)⟩)
    (fun _ _ => rfl)

private lemma lt_nn2_consPt_iff {n : ℕ} (hn : 4 ≤ n) (x₀ : Pt) (Z : Fin (n - 1) → Pt)
    {r : ℝ} (hr : 0 ≤ r) :
    r < nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩ ↔
      hitCount Z (disk x₀ (r / Real.sqrt (n : ℝ))) ≤ 1 := by
  rw [lt_nn2_iff]
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hcard : ((Finset.univ.erase (⟨0, by omega⟩ : Fin n)).filter fun j =>
      rescaledDist (consPt (by omega) x₀ Z) ⟨0, by omega⟩ j ≤ r).card =
      hitCount Z (disk x₀ (r / Real.sqrt (n : ℝ))) := by
    unfold hitCount
    refine Finset.card_bij (fun j _ => (⟨j.val - 1, by omega⟩ : Fin (n - 1))) ?_ ?_ ?_
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hj_er, hj_le⟩
      have hj0 : j.val ≠ 0 := fun h => Finset.ne_of_mem_erase hj_er (Fin.ext h)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hX0 : consPt (by omega) x₀ Z ⟨0, by omega⟩ = x₀ := by simp [consPt]
      have hXj : consPt (by omega) x₀ Z j = Z ⟨j.val - 1, by omega⟩ := by simp [consPt, hj0]
      unfold rescaledDist at hj_le
      rw [hX0, hXj, euclidDist_symm] at hj_le
      have hle : euclidDist (Z ⟨j.val - 1, by omega⟩) x₀ ≤ r / Real.sqrt (n : ℝ) := by
        rw [le_div_iff₀ hsn]; linarith
      exact (euclidDist_le_iff (div_nonneg hr (le_of_lt hsn))).mp hle
    · intro j₁ hj₁ j₂ hj₂ he
      have h1 : j₁.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp hj₁).1 (Fin.ext h)
      have h2 : j₂.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp hj₂).1 (Fin.ext h)
      have hv := congrArg Fin.val he; dsimp at hv
      exact Fin.ext (by omega)
    · intro k hk
      have hk_mem := (Finset.mem_filter.mp hk).2
      refine ⟨⟨k.val + 1, by omega⟩, ?_, Fin.ext (by simp)⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by intro h; simp [Fin.ext_iff] at h,
        Finset.mem_univ _⟩, ?_⟩
      unfold rescaledDist
      have hX0 : consPt (by omega) x₀ Z ⟨0, by omega⟩ = x₀ := by simp [consPt]
      have hXk : consPt (by omega) x₀ Z ⟨k.val + 1, by omega⟩ = Z k := by simp [consPt]
      rw [hX0, hXk, euclidDist_symm]
      have hle : euclidDist (Z k) x₀ ≤ r / Real.sqrt (n : ℝ) :=
        (euclidDist_le_iff (div_nonneg hr (le_of_lt hsn))).mpr hk_mem
      rw [le_div_iff₀ hsn] at hle; linarith
  rw [hcard]

private lemma lt_nn2_consTwoPt_zero_iff {n : ℕ} (hn : 4 ≤ n) (x₀ x₁ : Pt) (Z : Fin (n - 2) → Pt)
    {r : ℝ} (hr : 0 ≤ r) :
    r < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩ ↔
      (if Real.sqrt (n : ℝ) * euclidDist x₀ x₁ ≤ r then 1 else 0) +
        hitCount Z (disk x₀ (r / Real.sqrt (n : ℝ))) ≤ 1 := by
  rw [lt_nn2_iff]
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  let S := (Finset.univ.erase (⟨0, by omega⟩ : Fin n)).filter fun j =>
    rescaledDist (consTwoPt (by omega) x₀ x₁ Z) ⟨0, by omega⟩ j ≤ r
  let i1 : Fin n := ⟨1, by omega⟩
  have hsplit : S.card = (if i1 ∈ S then 1 else 0) + (S.erase i1).card := by
    by_cases h1 : i1 ∈ S
    · rw [if_pos h1, Finset.card_erase_of_mem h1]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i1, h1⟩
      omega
    · rw [if_neg h1, Finset.erase_eq_of_notMem h1, zero_add]
  have hi1_iff : i1 ∈ S ↔ Real.sqrt (n : ℝ) * euclidDist x₀ x₁ ≤ r := by
    simp only [S, i1, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      rescaledDist, consTwoPt_zero, consTwoPt_one]
    exact and_iff_right (by intro h; simp [Fin.ext_iff] at h)
  have hrest : (S.erase i1).card = hitCount Z (disk x₀ (r / Real.sqrt (n : ℝ))) := by
    unfold hitCount
    refine Finset.card_bij (fun j _ => (⟨j.val - 2, by omega⟩ : Fin (n - 2))) ?_ ?_ ?_
    · intro j hj
      have hj1 : j ≠ i1 := Finset.ne_of_mem_erase hj
      rcases Finset.mem_filter.mp (Finset.mem_of_mem_erase hj) with ⟨hj_er, hj_le⟩
      have hj0 : j.val ≠ 0 := fun h => Finset.ne_of_mem_erase hj_er (Fin.ext h)
      have hj1' : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hXj : consTwoPt (by omega) x₀ x₁ Z j = Z ⟨j.val - 2, by omega⟩ := by
        have he : j = ⟨(j.val - 2) + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        conv_lhs => rw [he]
        exact consTwoPt_rest (by omega) x₀ x₁ Z ⟨j.val - 2, by omega⟩
      unfold rescaledDist at hj_le
      rw [consTwoPt_zero, hXj, euclidDist_symm] at hj_le
      have hle : euclidDist (Z ⟨j.val - 2, by omega⟩) x₀ ≤ r / Real.sqrt (n : ℝ) := by
        rw [le_div_iff₀ hsn]; linarith
      exact (euclidDist_le_iff (div_nonneg hr (le_of_lt hsn))).mp hle
    · intro j₁ hj₁ j₂ hj₂ he
      have h10 : j₁.val ≠ 0 := fun h =>
        Finset.ne_of_mem_erase (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj₁)).1 (Fin.ext h)
      have h11 : j₁.val ≠ 1 := fun h => Finset.ne_of_mem_erase hj₁ (Fin.ext h)
      have h20 : j₂.val ≠ 0 := fun h =>
        Finset.ne_of_mem_erase (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj₂)).1 (Fin.ext h)
      have h21 : j₂.val ≠ 1 := fun h => Finset.ne_of_mem_erase hj₂ (Fin.ext h)
      have hv := congrArg Fin.val he; dsimp at hv
      exact Fin.ext (by omega)
    · intro k hk
      have hk_mem := (Finset.mem_filter.mp hk).2
      refine ⟨⟨k.val + 2, by omega⟩, ?_, Fin.ext (by simp)⟩
      refine Finset.mem_erase.mpr ⟨by intro h; simp [i1, Fin.ext_iff] at h,
        Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by intro h; simp [Fin.ext_iff] at h,
          Finset.mem_univ _⟩, ?_⟩⟩
      unfold rescaledDist
      rw [consTwoPt_zero, consTwoPt_rest, euclidDist_symm]
      have hle : euclidDist (Z k) x₀ ≤ r / Real.sqrt (n : ℝ) :=
        (euclidDist_le_iff (div_nonneg hr (le_of_lt hsn))).mpr hk_mem
      rw [le_div_iff₀ hsn] at hle; linarith
  change S.card ≤ 1 ↔ _
  simp only [hsplit, hrest, hi1_iff]

private lemma lt_nn2_consTwoPt_one_iff {n : ℕ} (hn : 4 ≤ n) (x₀ x₁ : Pt) (Z : Fin (n - 2) → Pt)
    {r : ℝ} (hr : 0 ≤ r) :
    r < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩ ↔
      (if Real.sqrt (n : ℝ) * euclidDist x₀ x₁ ≤ r then 1 else 0) +
        hitCount Z (disk x₁ (r / Real.sqrt (n : ℝ))) ≤ 1 := by
  rw [lt_nn2_iff]
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  let S := (Finset.univ.erase (⟨1, by omega⟩ : Fin n)).filter fun j =>
    rescaledDist (consTwoPt (by omega) x₀ x₁ Z) ⟨1, by omega⟩ j ≤ r
  let i0 : Fin n := ⟨0, by omega⟩
  have hsplit : S.card = (if i0 ∈ S then 1 else 0) + (S.erase i0).card := by
    by_cases h0 : i0 ∈ S
    · rw [if_pos h0, Finset.card_erase_of_mem h0]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i0, h0⟩
      omega
    · rw [if_neg h0, Finset.erase_eq_of_notMem h0, zero_add]
  have hi0_iff : i0 ∈ S ↔ Real.sqrt (n : ℝ) * euclidDist x₀ x₁ ≤ r := by
    simp only [S, i0, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      rescaledDist, consTwoPt_zero, consTwoPt_one, euclidDist_symm x₁ x₀]
    exact and_iff_right (by intro h; simp [Fin.ext_iff] at h)
  have hrest : (S.erase i0).card = hitCount Z (disk x₁ (r / Real.sqrt (n : ℝ))) := by
    unfold hitCount
    refine Finset.card_bij (fun j _ => (⟨j.val - 2, by omega⟩ : Fin (n - 2))) ?_ ?_ ?_
    · intro j hj
      have hj0 : j ≠ i0 := Finset.ne_of_mem_erase hj
      rcases Finset.mem_filter.mp (Finset.mem_of_mem_erase hj) with ⟨hj_er, hj_le⟩
      have hj1 : j.val ≠ 1 := fun h => Finset.ne_of_mem_erase hj_er (Fin.ext h)
      have hj0' : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hXj : consTwoPt (by omega) x₀ x₁ Z j = Z ⟨j.val - 2, by omega⟩ := by
        have he : j = ⟨(j.val - 2) + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        conv_lhs => rw [he]
        exact consTwoPt_rest (by omega) x₀ x₁ Z ⟨j.val - 2, by omega⟩
      unfold rescaledDist at hj_le
      rw [consTwoPt_one, hXj, euclidDist_symm] at hj_le
      have hle : euclidDist (Z ⟨j.val - 2, by omega⟩) x₁ ≤ r / Real.sqrt (n : ℝ) := by
        rw [le_div_iff₀ hsn]; linarith
      exact (euclidDist_le_iff (div_nonneg hr (le_of_lt hsn))).mp hle
    · intro j₁ hj₁ j₂ hj₂ he
      have h11 : j₁.val ≠ 1 := fun h =>
        Finset.ne_of_mem_erase (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj₁)).1 (Fin.ext h)
      have h10 : j₁.val ≠ 0 := fun h => Finset.ne_of_mem_erase hj₁ (Fin.ext h)
      have h21 : j₂.val ≠ 1 := fun h =>
        Finset.ne_of_mem_erase (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj₂)).1 (Fin.ext h)
      have h20 : j₂.val ≠ 0 := fun h => Finset.ne_of_mem_erase hj₂ (Fin.ext h)
      have hv := congrArg Fin.val he; dsimp at hv
      exact Fin.ext (by omega)
    · intro k hk
      have hk_mem := (Finset.mem_filter.mp hk).2
      refine ⟨⟨k.val + 2, by omega⟩, ?_, Fin.ext (by simp)⟩
      refine Finset.mem_erase.mpr ⟨by intro h; simp [i0, Fin.ext_iff] at h,
        Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by intro h; simp [Fin.ext_iff] at h,
          Finset.mem_univ _⟩, ?_⟩⟩
      unfold rescaledDist
      rw [consTwoPt_one, consTwoPt_rest, euclidDist_symm]
      have hle : euclidDist (Z k) x₁ ≤ r / Real.sqrt (n : ℝ) :=
        (euclidDist_le_iff (div_nonneg hr (le_of_lt hsn))).mpr hk_mem
      rw [le_div_iff₀ hsn] at hle; linarith
  change S.card ≤ 1 ↔ _
  simp only [hsplit, hrest, hi0_iff]

/-! ## Section 3: First-Order Base Term Lower Limit -/

/-- Explicit finite-`n` lower bound sequence for the first-order 2-factor base term. -/
private def baseTerm1Lower (rho w : Array Int) (Rbuf : ℝ) (n : ℕ) : ℝ :=
  if 4 ≤ n ∧ Rbuf / Real.sqrt (n : ℝ) ≤ 1 / 2 then
    2 * (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
      ∑ i : Fin rho.size,
        (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
          ((1 - Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) ^ (n - 1) +
            ((n - 1 : ℕ) : ℝ) * (Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) *
              (1 - Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) ^ (n - 2))
  else 0

theorem baseTerm1_lower_tendsto {rho w : Array Int} (hpot : ValidStepPot rho w)
    {Rbuf : ℝ} (hRbuf_pos : 0 ≤ Rbuf)
    (hRbuf : ∀ i < rho.size, toR (rho.getD i 0) ≤ Rbuf) :
    ∃ f : ℕ → ℝ,
      (∀ n : ℕ, (hn : 4 ≤ n) →
        f n ≤ ∫ X : Fin n → Pt,
          ((2 / (n : ℝ)) * ∑ u : Fin n, stepPot rho w (nn2 (by omega) (rescaledDist X) u))
          ∂(unitSquarePi n)) ∧
      Tendsto f atTop (nhds (baseTerm1 rho w)) := by
  refine ⟨baseTerm1Lower rho w Rbuf, ?_, ?_⟩
  · intro n hn
    rw [integral_baseTerm1_eq_single hn hpot]
    unfold baseTerm1Lower
    by_cases hcond : 4 ≤ n ∧ Rbuf / Real.sqrt (n : ℝ) ≤ 1 / 2
    · rw [if_pos hcond]
      have hsn_pos : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      have hmp := measurePreserving_consPt (n := n) (by omega)
      have hint_orig := integrable_stepPot_nn2 (n := n) (by omega) hpot ⟨0, by omega⟩
      have hcomp_int : Integrable (fun p : Pt × (Fin (n - 1) → Pt) =>
          stepPot rho w (nn2 (by omega) (rescaledDist (consPt (by omega) p.1 p.2)) ⟨0, by omega⟩))
          (unitSquareMeasure.prod (unitSquarePi (n - 1))) := by
        refine Integrable.of_bound
          (((measurable_stepPot rho w).comp
            ((measurable_nn2 (by omega) ⟨0, by omega⟩).comp hmp.measurable)).aestronglyMeasurable)
          (toR (w.getD (rho.size - 1) 0)) (Eventually.of_forall fun p => ?_)
        rw [Real.norm_of_nonneg (stepPot_nonneg hpot _)]
        exact stepPot_le_wMax hpot _
      have hsplit_eq : ∫ X : Fin n → Pt,
            stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩) ∂(unitSquarePi n) =
          ∫ x₀ : Pt, (∫ Z : Fin (n - 1) → Pt,
            stepPot rho w (nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩)
            ∂(unitSquarePi (n - 1))) ∂unitSquareMeasure := by
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
          (by rw [hmp.map_eq]; exact hint_orig.aestronglyMeasurable),
          MeasureTheory.integral_prod _ hcomp_int]
      rw [hsplit_eq]
      let rBuf := Rbuf / Real.sqrt (n : ℝ)
      let B := interiorBox rBuf
      have hB_meas : MeasurableSet B := measurableSet_interiorBox rBuf
      have hinner_int : Integrable (fun x₀ : Pt => ∫ Z : Fin (n - 1) → Pt,
          stepPot rho w (nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩)
          ∂(unitSquarePi (n - 1))) unitSquareMeasure := hcomp_int.integral_prod_left
      have hge_B : ∫ x₀ in B, (∫ Z : Fin (n - 1) → Pt,
            stepPot rho w (nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩)
            ∂(unitSquarePi (n - 1))) ∂unitSquareMeasure ≤
          ∫ x₀ : Pt, (∫ Z : Fin (n - 1) → Pt,
            stepPot rho w (nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩)
            ∂(unitSquarePi (n - 1))) ∂unitSquareMeasure :=
        setIntegral_le_integral hinner_int
          (Eventually.of_forall fun x₀ => integral_nonneg fun Z => stepPot_nonneg hpot _)
      have hval_on_B : ∀ x₀ ∈ B,
          ∫ Z : Fin (n - 1) → Pt,
            stepPot rho w (nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩)
            ∂(unitSquarePi (n - 1)) =
          ∑ i : Fin rho.size,
            (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
              ((1 - Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) ^ (n - 1) +
                ((n - 1 : ℕ) : ℝ) * (Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) *
                  (1 - Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) ^ (n - 2)) := by
        intro x₀ hx₀
        unfold stepPot
        have hterm_int : ∀ i : Fin rho.size,
            Integrable (fun Z : Fin (n - 1) → Pt =>
              (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
                if toR (rho.getD i.val 0) <
                  nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩
                then 1 else 0) (unitSquarePi (n - 1)) := by
          intro i
          have hmeas_nn2 : Measurable (fun Z : Fin (n - 1) → Pt =>
              nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩) :=
            (measurable_nn2 (by omega) ⟨0, by omega⟩).comp
              ((measurable_consPt (by omega)).comp (measurable_const.prodMk measurable_id))
          refine (Integrable.of_bound
            (Measurable.ite (measurableSet_lt measurable_const hmeas_nn2)
              measurable_const measurable_const).aestronglyMeasurable
            1 (Eventually.of_forall fun Z => by split_ifs <;> norm_num)).const_mul _
        rw [integral_finsetSum _ fun i _ => hterm_int i]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul]
        congr 1
        have hρ_nn : 0 ≤ toR (rho.getD i.val 0) := toR_nonneg (hpot.rho_nonneg i.isLt)
        have hcongr : (fun Z : Fin (n - 1) → Pt =>
            if toR (rho.getD i.val 0) <
              nn2 (by omega) (rescaledDist (consPt (by omega) x₀ Z)) ⟨0, by omega⟩
            then (1 : ℝ) else 0) =
            fun Z => if hitCount Z (disk x₀ (toR (rho.getD i.val 0) / Real.sqrt (n : ℝ))) ≤ 1
              then 1 else 0 := by
          funext Z
          exact if_congr (lt_nn2_consPt_iff hn x₀ Z hρ_nn) rfl rfl
        rw [hcongr, prob_hitCount_le_one (n - 1) (measurableSet_disk _ _)]
        have hvol : (unitSquareMeasure (disk x₀ (toR (rho.getD i.val 0) / Real.sqrt (n : ℝ)))).toReal =
            Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ) := by
          rw [unitSquareMeasure_disk_of_mem_interiorBox hx₀ (div_nonneg hρ_nn (le_of_lt hsn_pos))
            (div_le_div_of_nonneg_right (hRbuf i.val i.isLt) (le_of_lt hsn_pos)),
            div_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_div_assoc]
        rw [hvol, show n - 1 - 1 = n - 2 by omega]
      rw [setIntegral_congr_fun hB_meas hval_on_B, setIntegral_const, smul_eq_mul, Measure.real,
        unitSquareMeasure_interiorBox (div_nonneg hRbuf_pos (le_of_lt hsn_pos)) hcond.2] at hge_B
      have hmul_eq : (1 - 2 * (Rbuf / Real.sqrt (n : ℝ))) ^ 2 =
          (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 := by ring
      rw [hmul_eq] at hge_B
      linarith
    · rw [if_neg hcond]
      exact mul_nonneg (by norm_num) (integral_nonneg fun X => stepPot_nonneg hpot _)
  · have hlim_main : Tendsto (fun n : ℕ =>
        2 * (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
          ∑ i : Fin rho.size,
            (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
              ((1 - Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) ^ (n - 1) +
                ((n - 1 : ℕ) : ℝ) * (Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) *
                  (1 - Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) ^ (n - 2)))
        atTop (nhds (baseTerm1 rho w)) := by
      have hbox := tendsto_one_sub_inv_sqrt_sq Rbuf
      have hsum : Tendsto (fun n : ℕ =>
          ∑ i : Fin rho.size,
            (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
              ((1 - Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) ^ (n - 1) +
                ((n - 1 : ℕ) : ℝ) * (Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) *
                  (1 - Real.pi * (toR (rho.getD i.val 0)) ^ 2 / (n : ℝ)) ^ (n - 2)))
          atTop (nhds (∑ i : Fin rho.size,
            (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
              ((1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
                Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))))) := by
        refine tendsto_finsetSum _ fun i _ => ?_
        set a := Real.pi * (toR (rho.getD i.val 0)) ^ 2
        have h1 := tendsto_one_sub_div_pow a 1
        have h2 := tendsto_binom_one a a 1
        have hadd : Tendsto (fun n : ℕ =>
            (1 - a / (n : ℝ)) ^ (n - 1) +
              ((n - 1 : ℕ) : ℝ) * (a / (n : ℝ)) * (1 - a / (n : ℝ)) ^ (n - 2))
            atTop (nhds ((1 + a) * Real.exp (-a))) := by
          have h12 := h1.add h2
          rw [show Real.exp (-a) + a * Real.exp (-a) = (1 + a) * Real.exp (-a) by ring] at h12
          refine h12.congr fun n => ?_
          rw [show n - 1 - 1 = n - 2 by omega]
        exact tendsto_const_nhds.mul hadd
      have hprod := (tendsto_const_nhds (x := (2 : ℝ)).mul hbox).mul hsum
      have htarget : 2 * 1 * ∑ i : Fin rho.size,
            (toR (w.getD i.val 0) - toR (wPrev w i.val)) *
              ((1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
                Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))) =
          baseTerm1 rho w := by
        unfold baseTerm1
        rw [mul_one]
        congr 1
        refine Finset.sum_congr rfl fun i _ => by ring
      rwa [htarget] at hprod
    refine hlim_main.congr' ?_
    have hdiv0 : Tendsto (fun n : ℕ => Rbuf / Real.sqrt (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hev_half : ∀ᶠ n : ℕ in atTop, Rbuf / Real.sqrt (n : ℝ) ≤ 1 / 2 :=
      (hdiv0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => le_of_lt h
    filter_upwards [Filter.eventually_ge_atTop 4, hev_half] with n hn4 hhalf
    unfold baseTerm1Lower
    rw [if_pos ⟨hn4, hhalf⟩]

/-! ## Section 4: Two-Disk Scaling, Finite-`n` Survival Functions, and Radial Integration -/

private lemma diskInterArea_scale {c d r₁ r₂ : ℝ} (hc : 0 < c)
    (hd : 0 ≤ d) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    diskInterArea (c * d) (c * r₁) (c * r₂) = c ^ 2 * diskInterArea d r₁ r₂ := by
  have hmeas : MeasurableSet (disk (0 : Pt) r₁ ∩ disk (d, 0) r₂) :=
    (measurableSet_disk _ _).inter (measurableSet_disk _ _)
  have himg : scaleLinearEquiv (ne_of_gt hc) '' (disk (0 : Pt) r₁ ∩ disk (d, 0) r₂) =
      disk (0 : Pt) (c * r₁) ∩ disk (c * d, 0) (c * r₂) := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff, disk, sqDist, Set.mem_setOf_eq,
      Prod.fst_zero, Prod.snd_zero, sub_zero, scaleLinearEquiv, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
      exact ⟨by nlinarith [sq_nonneg c], by
        have : (c * w.1 - c * d) ^ 2 + (c * w.2) ^ 2 = c ^ 2 * ((w.1 - d) ^ 2 + w.2 ^ 2) := by ring
        rw [this]; nlinarith [sq_nonneg c]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(c⁻¹ * z.1, c⁻¹ * z.2), ⟨?_, ?_⟩, ?_⟩
      · have hsq : (c⁻¹ * z.1) ^ 2 + (c⁻¹ * z.2) ^ 2 = (c ^ 2)⁻¹ * (z.1 ^ 2 + z.2 ^ 2) := by
          field_simp [ne_of_gt hc]
        rw [hsq, inv_mul_le_iff₀ (sq_pos_of_pos hc)]
        nlinarith
      · have hsq : (c⁻¹ * z.1 - d) ^ 2 + (c⁻¹ * z.2) ^ 2 =
            (c ^ 2)⁻¹ * ((z.1 - c * d) ^ 2 + z.2 ^ 2) := by
          field_simp [ne_of_gt hc]
        rw [hsq, inv_mul_le_iff₀ (sq_pos_of_pos hc)]
        nlinarith
      · ext <;> dsimp <;> field_simp [ne_of_gt hc]
  have hvol := volume_image_scale hc hmeas
  rw [himg, volume_disk_inter_axis (mul_nonneg (le_of_lt hc) hd) (mul_nonneg (le_of_lt hc) hr₁)
      (mul_nonneg (le_of_lt hc) hr₂),
    volume_disk_inter_axis hd hr₁ hr₂, ← ENNReal.ofReal_mul (sq_nonneg c)] at hvol
  exact (ENNReal.ofReal_eq_ofReal_iff (diskInterArea_nonneg _ _ _)
    (mul_nonneg (sq_nonneg c) (diskInterArea_nonneg _ _ _))).mp hvol

private lemma continuous_segArea : Continuous segArea := by
  unfold segArea
  have hprim : Continuous (fun c : ℝ => ∫ t in (1 : ℝ)..c, Real.sqrt (1 - t ^ 2)) :=
    intervalIntegral.continuous_primitive
      (fun a b => (by fun_prop : Continuous fun t : ℝ => Real.sqrt (1 - t ^ 2)).intervalIntegrable a b) 1
  have heq : (fun c : ℝ => 2 * ∫ t in c..(1 : ℝ), Real.sqrt (1 - t ^ 2)) =
      fun c => -(2 * ∫ t in (1 : ℝ)..c, Real.sqrt (1 - t ^ 2)) := by
    funext c
    rw [intervalIntegral.integral_symm 1 c]; ring
  rw [heq]
  exact (continuous_const.mul hprim).neg

private lemma measurable_diskInterArea (r₁ r₂ : ℝ) :
    Measurable (fun d : ℝ => diskInterArea d r₁ r₂) := by
  unfold diskInterArea
  have h1 : MeasurableSet {d : ℝ | r₁ ≤ 0 ∨ r₂ ≤ 0 ∨ r₁ + r₂ ≤ d} :=
    (MeasurableSet.const _).union ((MeasurableSet.const _).union
      (measurableSet_le measurable_const measurable_id))
  have h2 : MeasurableSet {d : ℝ | d ≤ |r₁ - r₂|} :=
    measurableSet_le measurable_id measurable_const
  refine Measurable.ite h1 measurable_const (Measurable.ite h2 measurable_const ?_)
  have hc1 : Measurable (fun d : ℝ => (d ^ 2 + r₁ ^ 2 - r₂ ^ 2) / (2 * d * r₁)) := by fun_prop
  have hc2 : Measurable (fun d : ℝ => (d ^ 2 + r₂ ^ 2 - r₁ ^ 2) / (2 * d * r₂)) := by fun_prop
  exact (measurable_const.mul (continuous_segArea.measurable.comp hc1)).add
    (measurable_const.mul (continuous_segArea.measurable.comp hc2))

/-- Exact `unitSquareMeasure` values of `A, B, A ∩ B, A \ B, B \ A, A ∪ B` for two disks
contained in `[0, 1]²`. -/
private lemma unitSquareMeasure_twoDisks {n : ℕ} (hn : 1 ≤ n) {x₀ x₁ : Pt} {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hA_sub : disk x₀ (r₁ / Real.sqrt (n : ℝ)) ⊆ unitSquare)
    (hB_sub : disk x₁ (r₂ / Real.sqrt (n : ℝ)) ⊆ unitSquare) :
    let A := disk x₀ (r₁ / Real.sqrt (n : ℝ))
    let B := disk x₁ (r₂ / Real.sqrt (n : ℝ))
    let d := Real.sqrt (n : ℝ) * euclidDist x₀ x₁
    (unitSquareMeasure A).toReal = Real.pi * r₁ ^ 2 / (n : ℝ) ∧
    (unitSquareMeasure B).toReal = Real.pi * r₂ ^ 2 / (n : ℝ) ∧
    (unitSquareMeasure (A ∩ B)).toReal = diskInterArea d r₁ r₂ / (n : ℝ) ∧
    (unitSquareMeasure (A \ B)).toReal = (Real.pi * r₁ ^ 2 - diskInterArea d r₁ r₂) / (n : ℝ) ∧
    (unitSquareMeasure (B \ A)).toReal = (Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂) / (n : ℝ) ∧
    (unitSquareMeasure (A ∪ B)).toReal =
      (Real.pi * r₁ ^ 2 + Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂) / (n : ℝ) := by
  intro A B d
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hA_meas : MeasurableSet A := measurableSet_disk _ _
  have hB_meas : MeasurableSet B := measurableSet_disk _ _
  have hA_val : (unitSquareMeasure A).toReal = Real.pi * r₁ ^ 2 / (n : ℝ) := by
    rw [unitSquareMeasure_eq_volume_of_subset hA_sub,
      volume_disk x₀ (div_nonneg hr₁ (le_of_lt hsn)), ENNReal.toReal_ofReal (by positivity),
      div_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_div_assoc]
  have hB_val : (unitSquareMeasure B).toReal = Real.pi * r₂ ^ 2 / (n : ℝ) := by
    rw [unitSquareMeasure_eq_volume_of_subset hB_sub,
      volume_disk x₁ (div_nonneg hr₂ (le_of_lt hsn)), ENNReal.toReal_ofReal (by positivity),
      div_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_div_assoc]
  have hI_val : (unitSquareMeasure (A ∩ B)).toReal = diskInterArea d r₁ r₂ / (n : ℝ) := by
    rw [unitSquareMeasure_eq_volume_of_subset (Set.inter_subset_left.trans hA_sub),
      volume_disk_inter x₀ x₁ (div_nonneg hr₁ (le_of_lt hsn)) (div_nonneg hr₂ (le_of_lt hsn)),
      ENNReal.toReal_ofReal (diskInterArea_nonneg _ _ _)]
    have hscale := diskInterArea_scale (c := (Real.sqrt (n : ℝ))⁻¹) (inv_pos.mpr hsn)
      (mul_nonneg (le_of_lt hsn) (euclidDist_nonneg x₀ x₁)) hr₁ hr₂
    have hd_eq : (Real.sqrt (n : ℝ))⁻¹ * d = euclidDist x₀ x₁ := by
      dsimp only [d]; field_simp [ne_of_gt hsn]
    rw [hd_eq, inv_mul_eq_div, inv_mul_eq_div, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n),
      inv_mul_eq_div] at hscale
    exact hscale
  have hAB_sdiff : (unitSquareMeasure (A \ B)).toReal =
      (Real.pi * r₁ ^ 2 - diskInterArea d r₁ r₂) / (n : ℝ) := by
    have heq : A \ B = A \ (A ∩ B) := by ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
    rw [heq, measure_sdiff Set.inter_subset_left (hA_meas.inter hB_meas).nullMeasurableSet
        (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono Set.inter_subset_left) (measure_ne_top _ _),
      hA_val, hI_val, sub_div]
  have hBA_sdiff : (unitSquareMeasure (B \ A)).toReal =
      (Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂) / (n : ℝ) := by
    have heq : B \ A = B \ (A ∩ B) := by ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
    rw [heq, measure_sdiff Set.inter_subset_right (hA_meas.inter hB_meas).nullMeasurableSet
        (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono Set.inter_subset_right) (measure_ne_top _ _),
      hB_val, hI_val, sub_div]
  have hU_val : (unitSquareMeasure (A ∪ B)).toReal =
      (Real.pi * r₁ ^ 2 + Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂) / (n : ℝ) := by
    have hadd := measure_union_add_inter (μ := unitSquareMeasure) A hB_meas
    have htoReal := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      hA_val, hB_val, hI_val] at htoReal
    have : (unitSquareMeasure (A ∪ B)).toReal =
        Real.pi * r₁ ^ 2 / (n : ℝ) + Real.pi * r₂ ^ 2 / (n : ℝ) -
        diskInterArea d r₁ r₂ / (n : ℝ) := by linarith
    rw [this]; ring
  exact ⟨hA_val, hB_val, hI_val, hAB_sdiff, hBA_sdiff, hU_val⟩

/-- Exact finite-`n` marginal survival probability given pair distance `d` and knot radius `r`. -/
private def finiteMargSurv (n : ℕ) (d r : ℝ) : ℝ :=
  let a := Real.pi * r ^ 2
  let m := n - 2
  if d ≤ r then
    (1 - a / (n : ℝ)) ^ m
  else
    (1 - a / (n : ℝ)) ^ m +
      (m : ℝ) * (a / (n : ℝ)) * (1 - a / (n : ℝ)) ^ (m - 1)

/-- Exact finite-`n` joint survival probability given pair distance `d`, radii `r₁, r₂`,
and strict-comparison flags `(k₁, k₂)`. -/
private def finiteJointSurv (n : ℕ) (d r₁ r₂ : ℝ) (k₁ k₂ : Bool) : ℝ :=
  let a₁ := Real.pi * r₁ ^ 2
  let a₂ := Real.pi * r₂ ^ 2
  let I := diskInterArea d r₁ r₂
  let a10 := a₁ - I
  let a01 := a₂ - I
  let au := a₁ + a₂ - I
  let m := n - 2
  match k₁, k₂ with
  | false, false => (1 - au / (n : ℝ)) ^ m
  | true, false =>
      (1 - au / (n : ℝ)) ^ m +
        (m : ℝ) * (a10 / (n : ℝ)) * (1 - au / (n : ℝ)) ^ (m - 1)
  | false, true =>
      (1 - au / (n : ℝ)) ^ m +
        (m : ℝ) * (a01 / (n : ℝ)) * (1 - au / (n : ℝ)) ^ (m - 1)
  | true, true =>
      (1 - au / (n : ℝ)) ^ m +
        (m : ℝ) * (au / (n : ℝ)) * (1 - au / (n : ℝ)) ^ (m - 1) +
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (a10 / (n : ℝ)) * (a01 / (n : ℝ)) *
          (1 - au / (n : ℝ)) ^ (m - 2)

private lemma measurable_finiteMargSurv (n : ℕ) (r : ℝ) :
    Measurable (fun d : ℝ => finiteMargSurv n d r) := by
  unfold finiteMargSurv
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

private lemma measurable_finiteJointSurv (n : ℕ) (r₁ r₂ : ℝ) :
    Measurable (fun d : ℝ =>
      finiteJointSurv n d r₁ r₂ (decide (r₁ < d)) (decide (r₂ < d))) := by
  have hI : Measurable (fun d : ℝ => diskInterArea d r₁ r₂) := measurable_diskInterArea r₁ r₂
  have hbranch : ∀ k₁ k₂ : Bool,
      Measurable (fun d : ℝ => finiteJointSurv n d r₁ r₂ k₁ k₂) := by
    intro k₁ k₂
    cases k₁ <;> cases k₂ <;> unfold finiteJointSurv <;> dsimp only
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
  have heq : (fun d : ℝ => finiteJointSurv n d r₁ r₂ (decide (r₁ < d)) (decide (r₂ < d))) =
      fun d =>
        if r₁ < d then
          (if r₂ < d then finiteJointSurv n d r₁ r₂ true true
           else finiteJointSurv n d r₁ r₂ true false)
        else
          (if r₂ < d then finiteJointSurv n d r₁ r₂ false true
           else finiteJointSurv n d r₁ r₂ false false) := by
    funext d
    by_cases h1 : r₁ < d <;> by_cases h2 : r₂ < d <;> simp [h1, h2]
  rw [heq]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (hbranch true true) (hbranch true false))
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (hbranch false true) (hbranch false false))

private lemma tendsto_finiteMargSurv (d r : ℝ) :
    Tendsto (fun n : ℕ => finiteMargSurv n d r) atTop
      (nhds (if d ≤ r then Real.exp (-(Real.pi * r ^ 2))
             else (1 + Real.pi * r ^ 2) * Real.exp (-(Real.pi * r ^ 2)))) := by
  unfold finiteMargSurv
  by_cases h : d ≤ r
  · simp only [h, ↓reduceIte]
    exact tendsto_one_sub_div_pow (Real.pi * r ^ 2) 2
  · simp only [h, ↓reduceIte]
    set a := Real.pi * r ^ 2
    have h1 := tendsto_one_sub_div_pow a 2
    have h2 := tendsto_binom_one a a 2
    have h12 := h1.add h2
    rw [show Real.exp (-a) + a * Real.exp (-a) = (1 + a) * Real.exp (-a) by ring] at h12
    exact h12

private lemma tendsto_finiteJointSurv (d r₁ r₂ : ℝ) (k₁ k₂ : Bool) :
    Tendsto (fun n : ℕ => finiteJointSurv n d r₁ r₂ k₁ k₂) atTop
      (nhds (jointSurvReal d r₁ r₂ k₁ k₂)) := by
  unfold finiteJointSurv jointSurvReal jointSurvCore
  set a₁ := Real.pi * r₁ ^ 2
  set a₂ := Real.pi * r₂ ^ 2
  set I := diskInterArea d r₁ r₂
  set a10 := a₁ - I
  set a01 := a₂ - I
  set au := a₁ + a₂ - I
  cases k₁ <;> cases k₂ <;> dsimp only
  · exact tendsto_one_sub_div_pow au 2
  · have h1 := tendsto_one_sub_div_pow au 2
    have h2 := tendsto_binom_one au a01 2
    have h12 := h1.add h2
    rw [show Real.exp (-au) + a01 * Real.exp (-au) = (1 + a01) * Real.exp (-au) by ring] at h12
    exact h12
  · have h1 := tendsto_one_sub_div_pow au 2
    have h2 := tendsto_binom_one au a10 2
    have h12 := h1.add h2
    rw [show Real.exp (-au) + a10 * Real.exp (-au) = (1 + a10) * Real.exp (-au) by ring] at h12
    exact h12
  · have h1 := tendsto_one_sub_div_pow au 2
    have h2 := tendsto_binom_one au au 2
    have h3 := tendsto_binom_two a10 a01 au 2
    have h123 := (h1.add h2).add h3
    have hlim : Real.exp (-au) + au * Real.exp (-au) + a10 * a01 * Real.exp (-au) =
        ((1 + a10) * (1 + a01) + I) * Real.exp (-au) := by
      dsimp only [au, a10, a01]; ring
    rw [hlim] at h123
    refine h123.congr fun n => ?_
    dsimp only [a₁, a₂, I, a10, a01, au]
    simp only [show n - 2 - 1 = n - (2 + 1) by omega, show n - 2 - 2 = n - (2 + 2) by omega]

private lemma prob_consTwoPt_marg_zero {n : ℕ} (hn : 4 ≤ n) {x₀ x₁ : Pt} {r : ℝ}
    (hr : 0 ≤ r) (hA_sub : disk x₀ (r / Real.sqrt (n : ℝ)) ⊆ unitSquare) :
    ∫ Z : Fin (n - 2) → Pt,
        (if r < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
          then (1 : ℝ) else 0) ∂(unitSquarePi (n - 2)) =
      finiteMargSurv n (Real.sqrt (n : ℝ) * euclidDist x₀ x₁) r := by
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  let A := disk x₀ (r / Real.sqrt (n : ℝ))
  have hvol : (unitSquareMeasure A).toReal = Real.pi * r ^ 2 / (n : ℝ) := by
    rw [unitSquareMeasure_eq_volume_of_subset hA_sub,
      volume_disk x₀ (div_nonneg hr (le_of_lt hsn)), ENNReal.toReal_ofReal (by positivity),
      div_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_div_assoc]
  unfold finiteMargSurv
  by_cases hd : Real.sqrt (n : ℝ) * euclidDist x₀ x₁ ≤ r
  · rw [if_pos hd]
    have hcongr : (fun Z : Fin (n - 2) → Pt =>
        if r < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
        then (1 : ℝ) else 0) =
        fun Z => if hitCount Z A = 0 then 1 else 0 := by
      funext Z
      refine if_congr ?_ rfl rfl
      rw [lt_nn2_consTwoPt_zero_iff hn x₀ x₁ Z hr, if_pos hd]
      dsimp only [A]; omega
    rw [hcongr, prob_hitCount_eq_zero (n - 2) (measurableSet_disk _ _), hvol]
  · rw [if_neg hd]
    have hcongr : (fun Z : Fin (n - 2) → Pt =>
        if r < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
        then (1 : ℝ) else 0) =
        fun Z => if hitCount Z A ≤ 1 then 1 else 0 := by
      funext Z
      refine if_congr ?_ rfl rfl
      rw [lt_nn2_consTwoPt_zero_iff hn x₀ x₁ Z hr, if_neg hd, zero_add]
    rw [hcongr, prob_hitCount_le_one (n - 2) (measurableSet_disk _ _), hvol]

private lemma prob_consTwoPt_marg_one {n : ℕ} (hn : 4 ≤ n) {x₀ x₁ : Pt} {r : ℝ}
    (hr : 0 ≤ r) (hB_sub : disk x₁ (r / Real.sqrt (n : ℝ)) ⊆ unitSquare) :
    ∫ Z : Fin (n - 2) → Pt,
        (if r < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
          then (1 : ℝ) else 0) ∂(unitSquarePi (n - 2)) =
      finiteMargSurv n (Real.sqrt (n : ℝ) * euclidDist x₀ x₁) r := by
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  let B := disk x₁ (r / Real.sqrt (n : ℝ))
  have hvol : (unitSquareMeasure B).toReal = Real.pi * r ^ 2 / (n : ℝ) := by
    rw [unitSquareMeasure_eq_volume_of_subset hB_sub,
      volume_disk x₁ (div_nonneg hr (le_of_lt hsn)), ENNReal.toReal_ofReal (by positivity),
      div_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_div_assoc]
  unfold finiteMargSurv
  by_cases hd : Real.sqrt (n : ℝ) * euclidDist x₀ x₁ ≤ r
  · rw [if_pos hd]
    have hcongr : (fun Z : Fin (n - 2) → Pt =>
        if r < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
        then (1 : ℝ) else 0) =
        fun Z => if hitCount Z B = 0 then 1 else 0 := by
      funext Z
      refine if_congr ?_ rfl rfl
      rw [lt_nn2_consTwoPt_one_iff hn x₀ x₁ Z hr, if_pos hd]
      dsimp only [B]; omega
    rw [hcongr, prob_hitCount_eq_zero (n - 2) (measurableSet_disk _ _), hvol]
  · rw [if_neg hd]
    have hcongr : (fun Z : Fin (n - 2) → Pt =>
        if r < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
        then (1 : ℝ) else 0) =
        fun Z => if hitCount Z B ≤ 1 then 1 else 0 := by
      funext Z
      refine if_congr ?_ rfl rfl
      rw [lt_nn2_consTwoPt_one_iff hn x₀ x₁ Z hr, if_neg hd, zero_add]
    rw [hcongr, prob_hitCount_le_one (n - 2) (measurableSet_disk _ _), hvol]

private lemma prob_consTwoPt_joint {n : ℕ} (hn : 4 ≤ n) {x₀ x₁ : Pt} {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hA_sub : disk x₀ (r₁ / Real.sqrt (n : ℝ)) ⊆ unitSquare)
    (hB_sub : disk x₁ (r₂ / Real.sqrt (n : ℝ)) ⊆ unitSquare) :
    let d := Real.sqrt (n : ℝ) * euclidDist x₀ x₁
    ∫ Z : Fin (n - 2) → Pt,
        ((if r₁ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
            then (1 : ℝ) else 0) *
         (if r₂ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
            then (1 : ℝ) else 0)) ∂(unitSquarePi (n - 2)) =
      finiteJointSurv n d r₁ r₂ (decide (r₁ < d)) (decide (r₂ < d)) := by
  intro d
  let A := disk x₀ (r₁ / Real.sqrt (n : ℝ))
  let B := disk x₁ (r₂ / Real.sqrt (n : ℝ))
  have hA : MeasurableSet A := measurableSet_disk _ _
  have hB : MeasurableSet B := measurableSet_disk _ _
  have hvols := unitSquareMeasure_twoDisks (by omega) hr₁ hr₂ hA_sub hB_sub
  rcases hvols with ⟨_, _, _, hAB_vol, hBA_vol, hU_vol⟩
  have hmul_ite : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
      (if P then (1 : ℝ) else 0) * (if Q then (1 : ℝ) else 0) = if P ∧ Q then 1 else 0 := by
    intro P Q _ _; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  simp_rw [hmul_ite]
  by_cases h1 : r₁ < d <;> by_cases h2 : r₂ < d
  · -- `r₁ < d` and `r₂ < d`: `hitCount Z A ≤ 1 ∧ hitCount Z B ≤ 1`
    have hd1 : ¬ d ≤ r₁ := not_le.mpr h1
    have hd2 : ¬ d ≤ r₂ := not_le.mpr h2
    have hcongr : (fun Z : Fin (n - 2) → Pt =>
        if r₁ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩ ∧
           r₂ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
        then (1 : ℝ) else 0) =
        fun Z => if hitCount Z A ≤ 1 ∧ hitCount Z B ≤ 1 then 1 else 0 := by
      funext Z
      refine if_congr ?_ rfl rfl
      rw [lt_nn2_consTwoPt_zero_iff hn x₀ x₁ Z hr₁, lt_nn2_consTwoPt_one_iff hn x₀ x₁ Z hr₂,
        if_neg hd1, if_neg hd2, zero_add, zero_add]
    rw [hcongr, prob_twoSet_le_one (n - 2) hA hB, hAB_vol, hBA_vol, hU_vol]
    simp [finiteJointSurv, h1, h2]; rfl
  · -- `r₁ < d` and `d ≤ r₂`: `hitCount Z B = 0 ∧ hitCount Z (A \ B) ≤ 1`
    have hd1 : ¬ d ≤ r₁ := not_le.mpr h1
    have hd2 : d ≤ r₂ := not_lt.mp h2
    have hcongr : (fun Z : Fin (n - 2) → Pt =>
        if r₁ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩ ∧
           r₂ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
        then (1 : ℝ) else 0) =
        fun Z => if hitCount Z B = 0 ∧ hitCount Z (A \ B) ≤ 1 then 1 else 0 := by
      funext Z
      refine if_congr ?_ rfl rfl
      rw [lt_nn2_consTwoPt_zero_iff hn x₀ x₁ Z hr₁, lt_nn2_consTwoPt_one_iff hn x₀ x₁ Z hr₂,
        if_neg hd1, if_pos hd2, zero_add]
      have hB0_eq : hitCount Z B = 0 → hitCount Z A = hitCount Z (A \ B) := by
        intro hB0
        unfold hitCount at hB0 ⊢
        congr 1; ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_sdiff]
        have hkB : Z k ∉ B := fun hk => by
          have : 0 < (Finset.univ.filter fun i => Z i ∈ B).card :=
            Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
          omega
        tauto
      constructor
      · intro ⟨hA1, hB1⟩
        have hB0 : hitCount Z B = 0 := by dsimp only [B]; omega
        exact ⟨hB0, by rw [← hB0_eq hB0]; exact hA1⟩
      · intro ⟨hB0, hAB1⟩
        exact ⟨by rw [hB0_eq hB0]; exact hAB1, by dsimp only [B] at hB0; omega⟩
    have hdisj : Disjoint B (A \ B) := Set.disjoint_left.mpr fun _ hB' hAB' => hAB'.2 hB'
    have hunion : B ∪ (A \ B) = A ∪ B := by
      ext z; simp only [Set.mem_union, Set.mem_sdiff]; tauto
    rw [hcongr, prob_disjoint_zero_le_one (n - 2) hB (hA.diff hB) hdisj, hunion, hAB_vol, hU_vol]
    simp [finiteJointSurv, h1, h2]; rfl
  · -- `d ≤ r₁` and `r₂ < d`: `hitCount Z A = 0 ∧ hitCount Z (B \ A) ≤ 1`
    have hd1 : d ≤ r₁ := not_lt.mp h1
    have hd2 : ¬ d ≤ r₂ := not_le.mpr h2
    have hcongr : (fun Z : Fin (n - 2) → Pt =>
        if r₁ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩ ∧
           r₂ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
        then (1 : ℝ) else 0) =
        fun Z => if hitCount Z A = 0 ∧ hitCount Z (B \ A) ≤ 1 then 1 else 0 := by
      funext Z
      refine if_congr ?_ rfl rfl
      rw [lt_nn2_consTwoPt_zero_iff hn x₀ x₁ Z hr₁, lt_nn2_consTwoPt_one_iff hn x₀ x₁ Z hr₂,
        if_pos hd1, if_neg hd2, zero_add]
      have hA0_eq : hitCount Z A = 0 → hitCount Z B = hitCount Z (B \ A) := by
        intro hA0
        unfold hitCount at hA0 ⊢
        congr 1; ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_sdiff]
        have hkA : Z k ∉ A := fun hk => by
          have : 0 < (Finset.univ.filter fun i => Z i ∈ A).card :=
            Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
          omega
        tauto
      constructor
      · intro ⟨hA1, hB1⟩
        have hA0 : hitCount Z A = 0 := by dsimp only [A]; omega
        exact ⟨hA0, by rw [← hA0_eq hA0]; exact hB1⟩
      · intro ⟨hA0, hBA1⟩
        exact ⟨by dsimp only [A] at hA0; omega, by rw [hA0_eq hA0]; exact hBA1⟩
    have hdisj : Disjoint A (B \ A) := Set.disjoint_left.mpr fun _ hA' hBA' => hBA'.2 hA'
    have hunion : A ∪ (B \ A) = A ∪ B := by
      ext z; simp only [Set.mem_union, Set.mem_sdiff]; tauto
    rw [hcongr, prob_disjoint_zero_le_one (n - 2) hA (hB.diff hA) hdisj, hunion, hBA_vol, hU_vol]
    simp [finiteJointSurv, h1, h2]; rfl
  · -- `d ≤ r₁` and `d ≤ r₂`: `hitCount Z (A ∪ B) = 0`
    have hd1 : d ≤ r₁ := not_lt.mp h1
    have hd2 : d ≤ r₂ := not_lt.mp h2
    have hcongr : (fun Z : Fin (n - 2) → Pt =>
        if r₁ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩ ∧
           r₂ < nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
        then (1 : ℝ) else 0) =
        fun Z => if hitCount Z (A ∪ B) = 0 then 1 else 0 := by
      funext Z
      refine if_congr ?_ rfl rfl
      rw [lt_nn2_consTwoPt_zero_iff hn x₀ x₁ Z hr₁, lt_nn2_consTwoPt_one_iff hn x₀ x₁ Z hr₂,
        if_pos hd1, if_pos hd2]
      have hU0 : hitCount Z (A ∪ B) = 0 ↔ hitCount Z A = 0 ∧ hitCount Z B = 0 := by
        simp only [hitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
          forall_true_left, Set.mem_union, not_or, forall_and]
      rw [hU0]; dsimp only [A, B]; omega
    rw [hcongr, prob_hitCount_eq_zero (n - 2) (hA.union hB), hU_vol]
    simp [finiteJointSurv, h1, h2]; rfl

/-- Radial change of variables on `[0, 1]²` for a compactly supported nonnegative radial
function centered at an interior point `x₀ ∈ interiorBox (Rbuf / √n)`. -/
private lemma integral_unitSquare_radial_rescaled {n : ℕ} (hn : 1 ≤ n)
    {x₀ : Pt} {R Rbuf : ℝ} (hR : 0 ≤ R) (hR_le : R ≤ Rbuf)
    (hx₀ : x₀ ∈ interiorBox (Rbuf / Real.sqrt (n : ℝ)))
    {H : ℝ → ℝ} (hH_meas : Measurable H) (hH_nn : ∀ d, 0 ≤ H d)
    (hH_supp : ∀ d, R < d → H d = 0) :
    ∫ x₁ : Pt, H (Real.sqrt (n : ℝ) * euclidDist x₀ x₁) ∂unitSquareMeasure =
      (1 / (n : ℝ)) * ∫ d in (0 : ℝ)..R, (2 * Real.pi * d) * H d := by
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hvanish : ∀ x₁ ∉ unitSquare, H (Real.sqrt (n : ℝ) * euclidDist x₀ x₁) = 0 := by
    intro x₁ hx₁
    apply hH_supp
    by_contra hle; push Not at hle
    have hdisk : x₁ ∈ disk x₀ (Rbuf / Real.sqrt (n : ℝ)) := by
      refine (euclidDist_le_iff (div_nonneg (hR.trans hR_le) (le_of_lt hsn))).mp ?_
      rw [euclidDist_symm, le_div_iff₀ hsn]; linarith
    exact hx₁ (disk_subset_unitSquare hx₀ (div_nonneg (hR.trans hR_le) (le_of_lt hsn)) le_rfl hdisk)
  rw [← restrict_unitSquare_eq, setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
  -- Translate by `x₀`: `x₁ = x₀ + y`
  have htrans : ∫ x₁ : Pt, H (Real.sqrt (n : ℝ) * euclidDist x₀ x₁) =
      ∫ y : Pt, H (Real.sqrt (n : ℝ) * euclidNorm y) := by
    rw [← MeasureTheory.integral_add_left_eq_self
      (fun y : Pt => H (Real.sqrt (n : ℝ) * euclidDist x₀ y)) x₀]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hdist : euclidDist x₀ (x₀ + y) = euclidNorm y := by
      unfold euclidDist euclidNorm sqDist
      congr 1; dsimp; ring
    dsimp only; rw [hdist]
  have hrad := integral_radial_eq (h := fun r : ℝ => H (Real.sqrt (n : ℝ) * r))
    (hH_meas.comp (measurable_const.mul measurable_id)) (fun r => hH_nn _)
  rw [htrans, hrad]
  -- Truncate `Ioi 0` to `Ioc 0 (R / √n)`
  have htrunc : ∫ r in Ioi (0 : ℝ), (2 * Real.pi * r) * H (Real.sqrt (n : ℝ) * r) =
      ∫ r in Ioc (0 : ℝ) (R / Real.sqrt (n : ℝ)), (2 * Real.pi * r) * H (Real.sqrt (n : ℝ) * r) := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      Set.Ioc_subset_Ioi_self ?_
    refine Eventually.of_forall fun r hr => ?_
    have hgt : R / Real.sqrt (n : ℝ) < r := by
      rcases hr with ⟨hr0, hnot⟩
      by_contra hle
      exact hnot ⟨hr0, not_lt.mp hle⟩
    have hgt' : R < Real.sqrt (n : ℝ) * r := by
      rw [div_lt_iff₀ hsn] at hgt; linarith
    rw [hH_supp _ hgt', mul_zero]
  rw [htrunc, ← intervalIntegral.integral_of_le (div_nonneg hR (le_of_lt hsn))]
  -- 1D change of variables `d = √n * r`
  have hcov := intervalIntegral.integral_comp_mul_left
    (f := fun d : ℝ => (2 * Real.pi * d) * H d)
    (a := (0 : ℝ)) (b := R / Real.sqrt (n : ℝ)) (c := Real.sqrt (n : ℝ)) (ne_of_gt hsn)
  rw [mul_zero, mul_div_cancel₀ R (ne_of_gt hsn), smul_eq_mul] at hcov
  have hpull : ∫ r in (0 : ℝ)..(R / Real.sqrt (n : ℝ)),
      (2 * Real.pi * (Real.sqrt (n : ℝ) * r)) * H (Real.sqrt (n : ℝ) * r) =
      Real.sqrt (n : ℝ) * ∫ r in (0 : ℝ)..(R / Real.sqrt (n : ℝ)),
        (2 * Real.pi * r) * H (Real.sqrt (n : ℝ) * r) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun r _ => by ring
  rw [hpull] at hcov
  have hn_eq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hsn_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsn
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hstep : (n : ℝ) * ∫ r in (0 : ℝ)..(R / Real.sqrt (n : ℝ)),
      (2 * Real.pi * r) * H (Real.sqrt (n : ℝ) * r) =
      ∫ d in (0 : ℝ)..R, (2 * Real.pi * d) * H d := by
    have := congrArg (Real.sqrt (n : ℝ) * ·) hcov
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hsn_ne, one_mul, hn_eq] at this
    exact this
  rw [← hstep, one_div, ← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul]

/-! ## Section 5: Pair-Penalty Upper Limit -/

private def finitePenRadIntegrand (rho w : Array Int) (n : ℕ) (d : ℝ) : ℝ :=
  2 * (∑ i : Fin rho.size,
    (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
      finiteMargSurv n d (toR (rho.getD i.val 0))) +
  ∑ i : Fin rho.size, ∑ j : Fin rho.size,
    baseInterCoeff w i.val j.val d *
      finiteJointSurv n d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
        (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))

private def limPenRadIntegrand (rho w : Array Int) (d : ℝ) : ℝ :=
  2 * (∑ i : Fin rho.size,
    (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
      (if d ≤ toR (rho.getD i.val 0) then
        Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
      else
        (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
          Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2)))) +
  ∑ i : Fin rho.size, ∑ j : Fin rho.size,
    baseInterCoeff w i.val j.val d *
      jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
        (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))

private lemma measurable_finitePenRadIntegrand (rho w : Array Int) (n : ℕ) :
    Measurable (finitePenRadIntegrand rho w n) := by
  unfold finitePenRadIntegrand
  refine (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)).add
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  · exact ((measurable_const.max (measurable_const.sub measurable_id)).sub
      (measurable_const.max (measurable_const.sub measurable_id))).mul
      (measurable_finiteMargSurv n _)
  · have hcoeff : Measurable (fun d : ℝ => baseInterCoeff w i.val j.val d) := by
      unfold baseInterCoeff; fun_prop
    exact hcoeff.mul (measurable_finiteJointSurv n _ _)

private lemma marg_coeff_nonneg {rho w : Array Int} (hpot : ValidStepPot rho w)
    (i : Fin rho.size) (d : ℝ) :
    0 ≤ max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d) := by
  have hdw := stepPot_dw_nonneg hpot i
  exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))

private lemma finitePenRadIntegrand_eq_zero_of_gt {rho w : Array Int} (hpot : ValidStepPot rho w)
    (n : ℕ) {d : ℝ} (hd : 2 * toR (w.getD (rho.size - 1) 0) < d) :
    finitePenRadIntegrand rho w n d = 0 := by
  have hwMax_nn : 0 ≤ toR (w.getD (rho.size - 1) 0) :=
    toR_nonneg (hpot.w_nonneg (by have := hpot.size_pos; omega))
  have hwi : ∀ i : Fin rho.size, toR (w.getD i.val 0) ≤ toR (w.getD (rho.size - 1) 0) := fun i =>
    toR_le_toR (hpot.w_le_of_le (by omega) (by have := hpot.size_pos; omega))
  have hwpi : ∀ i : Fin rho.size, toR (wPrev w i.val) ≤ toR (w.getD i.val 0) := fun i => by
    linarith [stepPot_dw_nonneg hpot i]
  unfold finitePenRadIntegrand
  have h1 : ∑ i : Fin rho.size,
      (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
        finiteMargSurv n d (toR (rho.getD i.val 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [max_eq_left (by linarith [hwi i]), max_eq_left (by linarith [hwi i, hwpi i]),
      sub_self, zero_mul]
  have h2 : ∑ i : Fin rho.size, ∑ j : Fin rho.size,
      baseInterCoeff w i.val j.val d *
        finiteJointSurv n d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
          (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have hc0 : baseInterCoeff w i.val j.val d = 0 := by
      unfold baseInterCoeff
      rw [max_eq_left (by linarith [hwi i, hwi j]),
        max_eq_left (by linarith [hwi i, hwi j, hwpi i]),
        max_eq_left (by linarith [hwi i, hwi j, hwpi j]),
        max_eq_left (by linarith [hwi i, hwi j, hwpi i, hwpi j])]
      ring
    rw [hc0, zero_mul]
  rw [h1, h2]; ring

private lemma finiteMargSurv_bounds {n : ℕ} (hn : 4 ≤ n) {d r Rbuf : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ Rbuf) (hnR : 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ)) :
    0 ≤ finiteMargSurv n d r ∧ finiteMargSurv n d r ≤ 1 + Real.pi * Rbuf ^ 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have ha_nn : 0 ≤ Real.pi * r ^ 2 := by positivity
  have ha_le : Real.pi * r ^ 2 ≤ Real.pi * Rbuf ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) (le_of_lt Real.pi_pos)
  have hfrac_le : Real.pi * r ^ 2 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn_pos]; nlinarith [Real.pi_pos, sq_nonneg Rbuf]
  have h1m_nn : 0 ≤ 1 - Real.pi * r ^ 2 / (n : ℝ) := by linarith
  have h1m_le : 1 - Real.pi * r ^ 2 / (n : ℝ) ≤ 1 := by linarith [div_nonneg ha_nn (le_of_lt hn_pos)]
  have hm_le : ((n - 2 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn_pos]; exact_mod_cast Nat.sub_le n 2
  unfold finiteMargSurv
  split_ifs
  · refine ⟨pow_nonneg h1m_nn _, (pow_le_one₀ h1m_nn h1m_le).trans ?_⟩
    linarith [ha_nn, ha_le]
  · refine ⟨add_nonneg (pow_nonneg h1m_nn _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg ha_nn (le_of_lt hn_pos)))
        (pow_nonneg h1m_nn _)), ?_⟩
    have hp1 : (1 - Real.pi * r ^ 2 / (n : ℝ)) ^ (n - 2) ≤ 1 := pow_le_one₀ h1m_nn h1m_le
    have hp2 : (1 - Real.pi * r ^ 2 / (n : ℝ)) ^ (n - 2 - 1) ≤ 1 := pow_le_one₀ h1m_nn h1m_le
    have ht2 : ((n - 2 : ℕ) : ℝ) * (Real.pi * r ^ 2 / (n : ℝ)) *
        (1 - Real.pi * r ^ 2 / (n : ℝ)) ^ (n - 2 - 1) ≤ Real.pi * Rbuf ^ 2 := by
      have hrew : ((n - 2 : ℕ) : ℝ) * (Real.pi * r ^ 2 / (n : ℝ)) =
          (((n - 2 : ℕ) : ℝ) / (n : ℝ)) * (Real.pi * r ^ 2) := by ring
      rw [hrew]
      calc (((n - 2 : ℕ) : ℝ) / (n : ℝ)) * (Real.pi * r ^ 2) *
              (1 - Real.pi * r ^ 2 / (n : ℝ)) ^ (n - 2 - 1)
          ≤ 1 * (Real.pi * Rbuf ^ 2) * 1 := by
            refine mul_le_mul (mul_le_mul hm_le ha_le ha_nn zero_le_one) hp2
              (pow_nonneg h1m_nn _) (by positivity)
        _ = Real.pi * Rbuf ^ 2 := by ring
    linarith

private lemma finiteJointSurv_bounds {n : ℕ} (hn : 4 ≤ n) {d r₁ r₂ Rbuf : ℝ}
    (hd : 0 ≤ d) (hr₁0 : 0 ≤ r₁) (hr₂0 : 0 ≤ r₂)
    (hr₁ : r₁ ≤ Rbuf) (hr₂ : r₂ ≤ Rbuf) (hnR : 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ))
    (k₁ k₂ : Bool) :
    0 ≤ finiteJointSurv n d r₁ r₂ k₁ k₂ ∧
      finiteJointSurv n d r₁ r₂ k₁ k₂ ≤
        1 + 2 * Real.pi * Rbuf ^ 2 + (Real.pi * Rbuf ^ 2) ^ 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  set a₁ := Real.pi * r₁ ^ 2
  set a₂ := Real.pi * r₂ ^ 2
  set I := diskInterArea d r₁ r₂
  set a10 := a₁ - I
  set a01 := a₂ - I
  set au := a₁ + a₂ - I
  have hI_nn : 0 ≤ I := diskInterArea_nonneg d r₁ r₂
  have hI_min : I ≤ Real.pi * (min r₁ r₂) ^ 2 := diskInterArea_le_min_disk hd hr₁0 hr₂0
  have hI_le1 : I ≤ a₁ :=
    hI_min.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_min hr₁0 hr₂0) (min_le_left _ _) 2) (le_of_lt Real.pi_pos))
  have hI_le2 : I ≤ a₂ :=
    hI_min.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_min hr₁0 hr₂0) (min_le_right _ _) 2) (le_of_lt Real.pi_pos))
  have ha1_le : a₁ ≤ Real.pi * Rbuf ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₁0 hr₁ 2) (le_of_lt Real.pi_pos)
  have ha2_le : a₂ ≤ Real.pi * Rbuf ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₂0 hr₂ 2) (le_of_lt Real.pi_pos)
  have ha10_nn : 0 ≤ a10 := by dsimp only [a10]; linarith
  have ha01_nn : 0 ≤ a01 := by dsimp only [a01]; linarith
  have ha10_le : a10 ≤ Real.pi * Rbuf ^ 2 := by dsimp only [a10]; linarith
  have ha01_le : a01 ≤ Real.pi * Rbuf ^ 2 := by dsimp only [a01]; linarith
  have hau_nn : 0 ≤ au := by dsimp only [au]; linarith
  have hau_le : au ≤ 2 * Real.pi * Rbuf ^ 2 := by dsimp only [au]; linarith
  have hfrac_le : au / (n : ℝ) ≤ 1 := by rw [div_le_one hn_pos]; linarith
  have h1m_nn : 0 ≤ 1 - au / (n : ℝ) := by linarith
  have h1m_le : 1 - au / (n : ℝ) ≤ 1 := by linarith [div_nonneg hau_nn (le_of_lt hn_pos)]
  have hm_le : ((n - 2 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn_pos]; exact_mod_cast Nat.sub_le n 2
  have hm1_le : ((n - 2 - 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn_pos]; exact_mod_cast Nat.sub_le n 3
  have hp0 : (1 - au / (n : ℝ)) ^ (n - 2) ≤ 1 := pow_le_one₀ h1m_nn h1m_le
  have hp1 : (1 - au / (n : ℝ)) ^ (n - 2 - 1) ≤ 1 := pow_le_one₀ h1m_nn h1m_le
  have hp2 : (1 - au / (n : ℝ)) ^ (n - 2 - 2) ≤ 1 := pow_le_one₀ h1m_nn h1m_le
  have hR_nn : 0 ≤ Real.pi * Rbuf ^ 2 := by positivity
  have hterm1 : ∀ x : ℝ, 0 ≤ x → x ≤ 2 * Real.pi * Rbuf ^ 2 →
      ((n - 2 : ℕ) : ℝ) * (x / (n : ℝ)) * (1 - au / (n : ℝ)) ^ (n - 2 - 1) ≤
        2 * Real.pi * Rbuf ^ 2 := by
    intro x hx0 hx
    have hrew : ((n - 2 : ℕ) : ℝ) * (x / (n : ℝ)) = (((n - 2 : ℕ) : ℝ) / (n : ℝ)) * x := by ring
    rw [hrew]
    calc (((n - 2 : ℕ) : ℝ) / (n : ℝ)) * x * (1 - au / (n : ℝ)) ^ (n - 2 - 1)
        ≤ 1 * (2 * Real.pi * Rbuf ^ 2) * 1 :=
          mul_le_mul (mul_le_mul hm_le hx hx0 zero_le_one) hp1 (pow_nonneg h1m_nn _) (by positivity)
      _ = 2 * Real.pi * Rbuf ^ 2 := by ring
  cases k₁ <;> cases k₂ <;> unfold finiteJointSurv <;> dsimp only
  · refine ⟨pow_nonneg h1m_nn _, ?_⟩
    nlinarith [sq_nonneg (Real.pi * Rbuf ^ 2)]
  · refine ⟨add_nonneg (pow_nonneg h1m_nn _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg ha01_nn (le_of_lt hn_pos)))
        (pow_nonneg h1m_nn _)), ?_⟩
    have ht := hterm1 a01 ha01_nn (by linarith)
    nlinarith [sq_nonneg (Real.pi * Rbuf ^ 2)]
  · refine ⟨add_nonneg (pow_nonneg h1m_nn _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg ha10_nn (le_of_lt hn_pos)))
        (pow_nonneg h1m_nn _)), ?_⟩
    have ht := hterm1 a10 ha10_nn (by linarith)
    nlinarith [sq_nonneg (Real.pi * Rbuf ^ 2)]
  · refine ⟨add_nonneg
      (add_nonneg (pow_nonneg h1m_nn _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hau_nn (le_of_lt hn_pos)))
          (pow_nonneg h1m_nn _)))
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (div_nonneg ha10_nn (le_of_lt hn_pos))) (div_nonneg ha01_nn (le_of_lt hn_pos)))
        (pow_nonneg h1m_nn _)), ?_⟩
    have ht1 := hterm1 au hau_nn hau_le
    have ht2 : ((n - 2 : ℕ) : ℝ) * ((n - 2 - 1 : ℕ) : ℝ) * (a10 / (n : ℝ)) * (a01 / (n : ℝ)) *
        (1 - au / (n : ℝ)) ^ (n - 2 - 2) ≤ (Real.pi * Rbuf ^ 2) ^ 2 := by
      have hrew : ((n - 2 : ℕ) : ℝ) * ((n - 2 - 1 : ℕ) : ℝ) * (a10 / (n : ℝ)) * (a01 / (n : ℝ)) =
          ((((n - 2 : ℕ) : ℝ) / (n : ℝ)) * a10) * ((((n - 2 - 1 : ℕ) : ℝ) / (n : ℝ)) * a01) := by
        ring
      rw [hrew, sq]
      have hA : (((n - 2 : ℕ) : ℝ) / (n : ℝ)) * a10 ≤ Real.pi * Rbuf ^ 2 := by
        calc (((n - 2 : ℕ) : ℝ) / (n : ℝ)) * a10 ≤ 1 * (Real.pi * Rbuf ^ 2) :=
              mul_le_mul hm_le ha10_le ha10_nn zero_le_one
          _ = Real.pi * Rbuf ^ 2 := one_mul _
      have hB : (((n - 2 - 1 : ℕ) : ℝ) / (n : ℝ)) * a01 ≤ Real.pi * Rbuf ^ 2 := by
        calc (((n - 2 - 1 : ℕ) : ℝ) / (n : ℝ)) * a01 ≤ 1 * (Real.pi * Rbuf ^ 2) :=
              mul_le_mul hm1_le ha01_le ha01_nn zero_le_one
          _ = Real.pi * Rbuf ^ 2 := one_mul _
      have hAB : ((((n - 2 : ℕ) : ℝ) / (n : ℝ)) * a10) *
          ((((n - 2 - 1 : ℕ) : ℝ) / (n : ℝ)) * a01) ≤
          (Real.pi * Rbuf ^ 2) * (Real.pi * Rbuf ^ 2) :=
        mul_le_mul hA hB (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos)) ha01_nn) hR_nn
      calc ((((n - 2 : ℕ) : ℝ) / (n : ℝ)) * a10) * ((((n - 2 - 1 : ℕ) : ℝ) / (n : ℝ)) * a01) *
            (1 - au / (n : ℝ)) ^ (n - 2 - 2)
          ≤ ((Real.pi * Rbuf ^ 2) * (Real.pi * Rbuf ^ 2)) * 1 :=
            mul_le_mul hAB hp2 (pow_nonneg h1m_nn _) (mul_nonneg hR_nn hR_nn)
        _ = (Real.pi * Rbuf ^ 2) * (Real.pi * Rbuf ^ 2) := mul_one _
    linarith

private lemma finitePenRadIntegrand_nonneg {rho w : Array Int} (hpot : ValidStepPot rho w)
    {Rbuf : ℝ} (hRbuf_r : ∀ i < rho.size, toR (rho.getD i 0) ≤ Rbuf)
    {n : ℕ} (hn : 4 ≤ n) (hnR : 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ)) {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ finitePenRadIntegrand rho w n d := by
  unfold finitePenRadIntegrand
  refine add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_))
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  · exact mul_nonneg (marg_coeff_nonneg hpot i d)
      (finiteMargSurv_bounds hn (toR_nonneg (hpot.rho_nonneg i.isLt)) (hRbuf_r i.val i.isLt) hnR).1
  · exact mul_nonneg (baseInterCoeff_nonneg hpot i j d)
      (finiteJointSurv_bounds hn hd (toR_nonneg (hpot.rho_nonneg i.isLt))
        (toR_nonneg (hpot.rho_nonneg j.isLt)) (hRbuf_r i.val i.isLt) (hRbuf_r j.val j.isLt) hnR _ _).1

private lemma integral_limPenRadIntegrand_eq {rho w : Array Int} (hpot : ValidStepPot rho w) :
    Real.pi * ∫ d in (0 : ℝ)..(2 * toR (w.getD (rho.size - 1) 0)),
        d * limPenRadIntegrand rho w d =
      basePenMarg rho w + basePenInter rho w := by
  set wMax := toR (w.getD (rho.size - 1) 0)
  have hwMax_nn : 0 ≤ wMax := toR_nonneg (hpot.w_nonneg (by have := hpot.size_pos; omega))
  have hmarg_int : ∀ i : Fin rho.size, ∀ a b : ℝ, a ≤ b →
      IntervalIntegrable (fun d : ℝ =>
        d * ((max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
          (if d ≤ toR (rho.getD i.val 0) then
            Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
          else
            (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
              Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))))) volume a b := by
    intro i a b hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hmeas : Measurable (fun d : ℝ =>
        d * ((max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
          (if d ≤ toR (rho.getD i.val 0) then
            Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
          else
            (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
              Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))))) :=
      measurable_id.mul (((measurable_const.max (measurable_const.sub measurable_id)).sub
        (measurable_const.max (measurable_const.sub measurable_id))).mul
        (Measurable.ite (measurableSet_le measurable_id measurable_const)
          measurable_const measurable_const))
    have hC : ∃ C : ℝ, ∀ d ∈ Ioc a b,
        ‖d * ((max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
          (if d ≤ toR (rho.getD i.val 0) then
            Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
          else
            (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
              Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))))‖ ≤ C := by
      let M := max |a| |b|
      let K := (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
        Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
      refine ⟨M * ((|toR (w.getD i.val 0)| + |toR (wPrev w i.val)| + 2 * M) * K), fun d hd => ?_⟩
      have hd_abs : |d| ≤ M := by
        rcases le_total 0 d with h0 | h0
        · rw [abs_of_nonneg h0]; exact (hd.2.trans (le_abs_self b)).trans (le_max_right _ _)
        · rw [abs_of_nonpos h0]
          have : -d ≤ -a := by linarith [hd.1]
          exact (this.trans (neg_le_abs a)).trans (le_max_left _ _)
      have hK_nn : 0 ≤ K := by positivity
      have hite_abs : |if d ≤ toR (rho.getD i.val 0) then
            Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
          else K| ≤ K := by
        split_ifs
        · rw [abs_of_nonneg (Real.exp_nonneg _)]
          dsimp only [K]
          have h1 : 1 ≤ 1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2 := by
            nlinarith [Real.pi_pos, sq_nonneg (toR (rho.getD i.val 0))]
          exact le_mul_of_one_le_left (Real.exp_nonneg _) h1
        · rw [abs_of_nonneg hK_nn]
      have hdiff_abs : |max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)| ≤
          |toR (w.getD i.val 0)| + |toR (wPrev w i.val)| + 2 * M := by
        have h1 : |max 0 (toR (w.getD i.val 0) - d)| ≤ |toR (w.getD i.val 0)| + M := by
          rw [abs_of_nonneg (le_max_left _ _)]
          exact max_le (by positivity) (by linarith [le_abs_self (toR (w.getD i.val 0)), neg_le_abs d])
        have h2 : |max 0 (toR (wPrev w i.val) - d)| ≤ |toR (wPrev w i.val)| + M := by
          rw [abs_of_nonneg (le_max_left _ _)]
          exact max_le (by positivity) (by linarith [le_abs_self (toR (wPrev w i.val)), neg_le_abs d])
        linarith [abs_sub (max 0 (toR (w.getD i.val 0) - d)) (max 0 (toR (wPrev w i.val) - d))]
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul hd_abs
        (mul_le_mul hdiff_abs hite_abs (abs_nonneg _) (by positivity))
        (by positivity) (by positivity)
    rcases hC with ⟨C, hC⟩
    exact Measure.integrableOn_of_bounded (by simp [Real.volume_Ioc]) hmeas.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono hC)
  have hinter_int : IntervalIntegrable (fun d : ℝ =>
      d * ∑ i : Fin rho.size, ∑ j : Fin rho.size,
        baseInterCoeff w i.val j.val d *
          jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
            (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)))
      volume 0 (2 * wMax) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    have hmeas_js : ∀ r₁ r₂ : ℝ,
        Measurable (fun d : ℝ => jointSurvReal d r₁ r₂ (decide (r₁ < d)) (decide (r₂ < d))) := by
      intro r₁ r₂
      have hI := measurable_diskInterArea r₁ r₂
      have hbr : ∀ k₁ k₂ : Bool, Measurable (fun d : ℝ => jointSurvReal d r₁ r₂ k₁ k₂) := by
        intro k₁ k₂
        cases k₁ <;> cases k₂ <;> unfold jointSurvReal jointSurvCore <;> dsimp only <;> fun_prop
      have heq : (fun d : ℝ => jointSurvReal d r₁ r₂ (decide (r₁ < d)) (decide (r₂ < d))) =
          fun d => if r₁ < d then (if r₂ < d then jointSurvReal d r₁ r₂ true true
              else jointSurvReal d r₁ r₂ true false)
            else (if r₂ < d then jointSurvReal d r₁ r₂ false true
              else jointSurvReal d r₁ r₂ false false) := by
        funext d; by_cases h1 : r₁ < d <;> by_cases h2 : r₂ < d <;> simp [h1, h2]
      rw [heq]
      exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
        (Measurable.ite (measurableSet_lt measurable_const measurable_id)
          (hbr true true) (hbr true false))
        (Measurable.ite (measurableSet_lt measurable_const measurable_id)
          (hbr false true) (hbr false false))
    have hmeas : Measurable (fun d : ℝ =>
        d * ∑ i : Fin rho.size, ∑ j : Fin rho.size,
          baseInterCoeff w i.val j.val d *
            jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
              (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))) :=
      measurable_id.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        (by unfold baseInterCoeff; fun_prop : Measurable fun d => baseInterCoeff w i.val j.val d).mul
          (hmeas_js _ _))
    -- Uniform bound on `Ioc 0 (2 * wMax)`
    let Rmax : ℝ := ∑ i : Fin rho.size, toR (rho.getD i.val 0)
    have hRmax : ∀ i : Fin rho.size, toR (rho.getD i.val 0) ≤ Rmax := fun i =>
      Finset.single_le_sum (fun j _ => toR_nonneg (hpot.rho_nonneg j.isLt)) (Finset.mem_univ i)
    have hRmax_nn : 0 ≤ Rmax := Finset.sum_nonneg fun j _ => toR_nonneg (hpot.rho_nonneg j.isLt)
    let Bjs := (1 + Real.pi * Rmax ^ 2) * (1 + Real.pi * Rmax ^ 2) + Real.pi * Rmax ^ 2
    let C := (2 * wMax) * ((rho.size : ℝ) * (rho.size : ℝ) * (4 * wMax * Bjs))
    refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun d hd => ?_)
    have hd0 : 0 ≤ d := le_of_lt hd.1
    have hd2 : d ≤ 2 * wMax := hd.2
    have hjs_le : ∀ i j : Fin rho.size,
        0 ≤ jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
              (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) ∧
        jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
              (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) ≤ Bjs := by
      intro i j
      set r₁ := toR (rho.getD i.val 0)
      set r₂ := toR (rho.getD j.val 0)
      have hr1 : 0 ≤ r₁ := toR_nonneg (hpot.rho_nonneg i.isLt)
      have hr2 : 0 ≤ r₂ := toR_nonneg (hpot.rho_nonneg j.isLt)
      have hI0 : 0 ≤ diskInterArea d r₁ r₂ := diskInterArea_nonneg d r₁ r₂
      have hIm := diskInterArea_le_min_disk hd0 hr1 hr2
      have hI1 : diskInterArea d r₁ r₂ ≤ Real.pi * r₁ ^ 2 :=
        hIm.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_min hr1 hr2) (min_le_left _ _) 2) (le_of_lt Real.pi_pos))
      have hI2 : diskInterArea d r₁ r₂ ≤ Real.pi * r₂ ^ 2 :=
        hIm.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_min hr1 hr2) (min_le_right _ _) 2) (le_of_lt Real.pi_pos))
      have ha1 : Real.pi * r₁ ^ 2 ≤ Real.pi * Rmax ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr1 (hRmax i) 2) (le_of_lt Real.pi_pos)
      have ha2 : Real.pi * r₂ ^ 2 ≤ Real.pi * Rmax ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr2 (hRmax j) 2) (le_of_lt Real.pi_pos)
      have hexp_le : Real.exp (-(Real.pi * r₁ ^ 2 + Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have hexp_nn : 0 ≤ Real.exp (-(Real.pi * r₁ ^ 2 + Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂)) :=
        Real.exp_nonneg _
      unfold jointSurvReal jointSurvCore
      cases decide (r₁ < d) <;> cases decide (r₂ < d) <;> dsimp only
      · refine ⟨hexp_nn, hexp_le.trans ?_⟩
        dsimp only [Bjs]; nlinarith [Real.pi_pos, sq_nonneg Rmax]
      · refine ⟨mul_nonneg (by linarith) hexp_nn, ?_⟩
        dsimp only [Bjs]
        nlinarith [Real.pi_pos, sq_nonneg Rmax, mul_le_mul_of_nonneg_left hexp_le (by linarith : 0 ≤ 1 + (Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂))]
      · refine ⟨mul_nonneg (by linarith) hexp_nn, ?_⟩
        dsimp only [Bjs]
        nlinarith [Real.pi_pos, sq_nonneg Rmax, mul_le_mul_of_nonneg_left hexp_le (by linarith : 0 ≤ 1 + (Real.pi * r₁ ^ 2 - diskInterArea d r₁ r₂))]
      · have hfac_nn : 0 ≤ (1 + (Real.pi * r₁ ^ 2 - diskInterArea d r₁ r₂)) *
            (1 + (Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂)) + diskInterArea d r₁ r₂ := by nlinarith
        have hfac_le : (1 + (Real.pi * r₁ ^ 2 - diskInterArea d r₁ r₂)) *
            (1 + (Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂)) + diskInterArea d r₁ r₂ ≤ Bjs := by
          dsimp only [Bjs]; nlinarith
        refine ⟨mul_nonneg hfac_nn hexp_nn, ?_⟩
        calc ((1 + (Real.pi * r₁ ^ 2 - diskInterArea d r₁ r₂)) *
              (1 + (Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂)) + diskInterArea d r₁ r₂) *
              Real.exp (-(Real.pi * r₁ ^ 2 + Real.pi * r₂ ^ 2 - diskInterArea d r₁ r₂))
            ≤ Bjs * 1 := mul_le_mul hfac_le hexp_le hexp_nn (by positivity)
          _ = Bjs := mul_one _
    have hcoeff_le : ∀ i j : Fin rho.size, baseInterCoeff w i.val j.val d ≤ 4 * wMax := by
      intro i j
      have hwi : toR (w.getD i.val 0) ≤ wMax :=
        toR_le_toR (hpot.w_le_of_le (by omega) (by have := hpot.size_pos; omega))
      have hwj : toR (w.getD j.val 0) ≤ wMax :=
        toR_le_toR (hpot.w_le_of_le (by omega) (by have := hpot.size_pos; omega))
      have hwpi : toR (wPrev w i.val) ≤ wMax := by linarith [stepPot_dw_nonneg hpot i]
      have hwpj : toR (wPrev w j.val) ≤ wMax := by linarith [stepPot_dw_nonneg hpot j]
      unfold baseInterCoeff
      have h1 : max 0 (toR (w.getD i.val 0) + toR (w.getD j.val 0) - d) ≤ 2 * wMax :=
        max_le (by linarith) (by linarith)
      have h4 : max 0 (toR (wPrev w i.val) + toR (wPrev w j.val) - d) ≤ 2 * wMax :=
        max_le (by linarith) (by linarith)
      linarith [le_max_left (0 : ℝ) (toR (wPrev w i.val) + toR (w.getD j.val 0) - d),
        le_max_left (0 : ℝ) (toR (w.getD i.val 0) + toR (wPrev w j.val) - d)]
    have hsum_nn : 0 ≤ ∑ i : Fin rho.size, ∑ j : Fin rho.size,
        baseInterCoeff w i.val j.val d *
          jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
            (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (baseInterCoeff_nonneg hpot i j d) (hjs_le i j).1
    rw [Real.norm_of_nonneg (mul_nonneg hd0 hsum_nn)]
    have hsum_le : ∑ i : Fin rho.size, ∑ j : Fin rho.size,
        baseInterCoeff w i.val j.val d *
          jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
            (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) ≤
        (rho.size : ℝ) * (rho.size : ℝ) * (4 * wMax * Bjs) := by
      calc ∑ i : Fin rho.size, ∑ j : Fin rho.size,
            baseInterCoeff w i.val j.val d *
              jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))
          ≤ ∑ _i : Fin rho.size, ∑ _j : Fin rho.size, (4 * wMax * Bjs) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              mul_le_mul (hcoeff_le i j) (hjs_le i j).2 (hjs_le i j).1 (by linarith)
        _ = (rho.size : ℝ) * (rho.size : ℝ) * (4 * wMax * Bjs) := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    exact mul_le_mul hd2 hsum_le hsum_nn (by linarith)
  have hsplit : (fun d : ℝ => d * limPenRadIntegrand rho w d) =
      fun d =>
        (2 * ∑ i : Fin rho.size,
          d * ((max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
            (if d ≤ toR (rho.getD i.val 0) then
              Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
            else
              (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
                Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))))) +
        d * ∑ i : Fin rho.size, ∑ j : Fin rho.size,
          baseInterCoeff w i.val j.val d *
            jointSurvReal d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
              (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) := by
    funext d
    unfold limPenRadIntegrand
    rw [mul_add, ← mul_assoc, mul_comm d 2, mul_assoc, Finset.mul_sum]
  have hmarg_sum_int : IntervalIntegrable (fun d : ℝ =>
      2 * ∑ i : Fin rho.size,
        d * ((max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
          (if d ≤ toR (rho.getD i.val 0) then
            Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
          else
            (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
              Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2)))))
      volume 0 (2 * wMax) := by
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum Finset.univ fun i _ => hmarg_int i 0 (2 * wMax) (by linarith)).const_mul 2
  rw [hsplit, intervalIntegral.integral_add hmarg_sum_int hinter_int,
    mul_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum fun i _ => hmarg_int i 0 (2 * wMax) (by linarith)]
  congr 1
  · rw [← mul_assoc, Finset.mul_sum]
    unfold basePenMarg
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm Real.pi 2]
    congr 1
    have hwi_nn : 0 ≤ toR (w.getD i.val 0) := toR_nonneg (hpot.w_nonneg i.isLt)
    have hwi_le : toR (w.getD i.val 0) ≤ 2 * wMax := by
      have h1 : toR (w.getD i.val 0) ≤ wMax :=
        toR_le_toR (hpot.w_le_of_le (i := i.val) (j := rho.size - 1) (by omega)
          (by have := hpot.size_pos; omega))
      linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hmarg_int i 0 (toR (w.getD i.val 0)) hwi_nn)
      (hmarg_int i (toR (w.getD i.val 0)) (2 * wMax) hwi_le)]
    have htail : ∫ d in (toR (w.getD i.val 0))..(2 * wMax),
        d * ((max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
          (if d ≤ toR (rho.getD i.val 0) then
            Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2))
          else
            (1 + Real.pi * (toR (rho.getD i.val 0)) ^ 2) *
              Real.exp (-(Real.pi * (toR (rho.getD i.val 0)) ^ 2)))) = 0 := by
      rw [intervalIntegral.integral_of_le hwi_le]
      refine setIntegral_eq_zero_of_forall_eq_zero fun d hd => ?_
      have hgt : toR (w.getD i.val 0) < d := hd.1
      have hwp : toR (wPrev w i.val) ≤ toR (w.getD i.val 0) := by
        linarith [stepPot_dw_nonneg hpot i]
      rw [max_eq_left (by linarith), max_eq_left (by linarith), sub_self, zero_mul, mul_zero]
    rw [htail, add_zero]
    exact intervalIntegral.integral_congr fun d _ => by ring

private lemma tendsto_integral_finitePenRadIntegrand {rho w : Array Int} (hpot : ValidStepPot rho w)
    {Rbuf : ℝ} (hRbuf_r : ∀ i < rho.size, toR (rho.getD i 0) ≤ Rbuf) :
    Tendsto (fun n : ℕ =>
      if 4 ≤ n ∧ 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ) then
        Real.pi * ∫ d in (0 : ℝ)..(2 * toR (w.getD (rho.size - 1) 0)),
          d * finitePenRadIntegrand rho w n d
      else 0)
      atTop (nhds (basePenMarg rho w + basePenInter rho w)) := by
  set wMax := toR (w.getD (rho.size - 1) 0)
  have hwMax_nn : 0 ≤ wMax := toR_nonneg (hpot.w_nonneg (by have := hpot.size_pos; omega))
  let G : ℕ → ℝ → ℝ := fun n d =>
    if 4 ≤ n ∧ 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ) then
      d * finitePenRadIntegrand rho w n d
    else 0
  have hG_meas : ∀ n, AEStronglyMeasurable (G n) (volume.restrict (Ioc 0 (2 * wMax))) := by
    intro n
    dsimp only [G]
    split_ifs
    · exact (measurable_id.mul (measurable_finitePenRadIntegrand rho w n)).aestronglyMeasurable
    · exact aestronglyMeasurable_const
  let Bjs := 1 + 2 * Real.pi * Rbuf ^ 2 + (Real.pi * Rbuf ^ 2) ^ 2
  let C : ℝ := (2 * wMax) *
    (2 * (rho.size : ℝ) * (wMax * (1 + Real.pi * Rbuf ^ 2)) +
      (rho.size : ℝ) * (rho.size : ℝ) * (4 * wMax * Bjs))
  have hG_bound : ∀ n, ∀ᵐ d ∂(volume.restrict (Ioc 0 (2 * wMax))), ‖G n d‖ ≤ C := by
    intro n
    refine (ae_restrict_mem measurableSet_Ioc).mono fun d hd => ?_
    have hd0 : 0 ≤ d := le_of_lt hd.1
    have hd2 : d ≤ 2 * wMax := hd.2
    dsimp only [G]
    split_ifs with hcond
    · have hnn := finitePenRadIntegrand_nonneg hpot hRbuf_r hcond.1 hcond.2 hd0
      rw [Real.norm_of_nonneg (mul_nonneg hd0 hnn)]
      have hwi : ∀ i : Fin rho.size, toR (w.getD i.val 0) ≤ wMax := fun i =>
        toR_le_toR (hpot.w_le_of_le (by omega) (by have := hpot.size_pos; omega))
      have hwpi : ∀ i : Fin rho.size, toR (wPrev w i.val) ≤ wMax := fun i => by
        linarith [stepPot_dw_nonneg hpot i, hwi i]
      have hpart1 : ∑ i : Fin rho.size,
          (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
            finiteMargSurv n d (toR (rho.getD i.val 0)) ≤
          (rho.size : ℝ) * (wMax * (1 + Real.pi * Rbuf ^ 2)) := by
        calc ∑ i : Fin rho.size,
              (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
                finiteMargSurv n d (toR (rho.getD i.val 0))
            ≤ ∑ _i : Fin rho.size, (wMax * (1 + Real.pi * Rbuf ^ 2)) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have hms := finiteMargSurv_bounds hcond.1 (d := d)
                (toR_nonneg (hpot.rho_nonneg i.isLt)) (hRbuf_r i.val i.isLt) hcond.2
              have hmc : max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d) ≤ wMax := by
                have h1 : max 0 (toR (w.getD i.val 0) - d) ≤ wMax :=
                  max_le hwMax_nn (by linarith [hwi i, hd0])
                linarith [le_max_left (0 : ℝ) (toR (wPrev w i.val) - d)]
              exact mul_le_mul hmc hms.2 hms.1 hwMax_nn
          _ = (rho.size : ℝ) * (wMax * (1 + Real.pi * Rbuf ^ 2)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      have hpart2 : ∑ i : Fin rho.size, ∑ j : Fin rho.size,
          baseInterCoeff w i.val j.val d *
            finiteJointSurv n d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
              (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) ≤
          (rho.size : ℝ) * (rho.size : ℝ) * (4 * wMax * Bjs) := by
        calc ∑ i : Fin rho.size, ∑ j : Fin rho.size,
              baseInterCoeff w i.val j.val d *
                finiteJointSurv n d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                  (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))
            ≤ ∑ _i : Fin rho.size, ∑ _j : Fin rho.size, (4 * wMax * Bjs) := by
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
              have hjs := finiteJointSurv_bounds hcond.1 hd0
                (toR_nonneg (hpot.rho_nonneg i.isLt)) (toR_nonneg (hpot.rho_nonneg j.isLt))
                (hRbuf_r i.val i.isLt) (hRbuf_r j.val j.isLt) hcond.2
                (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d))
              have hic : baseInterCoeff w i.val j.val d ≤ 4 * wMax := by
                unfold baseInterCoeff
                have h1 : max 0 (toR (w.getD i.val 0) + toR (w.getD j.val 0) - d) ≤ 2 * wMax :=
                  max_le (by linarith) (by linarith [hwi i, hwi j])
                have h4 : max 0 (toR (wPrev w i.val) + toR (wPrev w j.val) - d) ≤ 2 * wMax :=
                  max_le (by linarith) (by linarith [hwpi i, hwpi j])
                linarith [le_max_left (0 : ℝ) (toR (wPrev w i.val) + toR (w.getD j.val 0) - d),
                  le_max_left (0 : ℝ) (toR (w.getD i.val 0) + toR (wPrev w j.val) - d)]
              exact mul_le_mul hic hjs.2 hjs.1 (by linarith)
          _ = (rho.size : ℝ) * (rho.size : ℝ) * (4 * wMax * Bjs) := by
              simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      have htot : finitePenRadIntegrand rho w n d ≤
          2 * (rho.size : ℝ) * (wMax * (1 + Real.pi * Rbuf ^ 2)) +
            (rho.size : ℝ) * (rho.size : ℝ) * (4 * wMax * Bjs) := by
        unfold finitePenRadIntegrand; linarith
      exact mul_le_mul hd2 htot hnn (by positivity)
    · rw [norm_zero]
      dsimp only [C, Bjs]; positivity
  have hG_lim : ∀ᵐ d ∂(volume.restrict (Ioc 0 (2 * wMax))),
      Tendsto (fun n => G n d) atTop (nhds (d * limPenRadIntegrand rho w d)) := by
    refine Eventually.of_forall fun d => ?_
    have hmain : Tendsto (fun n => d * finitePenRadIntegrand rho w n d) atTop
        (nhds (d * limPenRadIntegrand rho w d)) := by
      refine tendsto_const_nhds.mul ?_
      unfold finitePenRadIntegrand limPenRadIntegrand
      refine (tendsto_const_nhds.mul (tendsto_finsetSum _ fun i _ =>
        tendsto_const_nhds.mul (tendsto_finiteMargSurv d _))).add
        (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
          tendsto_const_nhds.mul (tendsto_finiteJointSurv d _ _ _ _))
    refine hmain.congr' ?_
    have hev_R : ∀ᶠ n : ℕ in atTop, 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop _)
    filter_upwards [Filter.eventually_ge_atTop 4, hev_R] with n hn4 hnR
    simp [G, hn4, hnR]
  have hbound_int : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc 0 (2 * wMax))) := by
    rw [← IntegrableOn]
    exact integrableOn_const measure_Ioc_lt_top.ne
  have hdct := tendsto_integral_of_dominated_convergence (fun _ => C)
    hG_meas hbound_int hG_bound hG_lim
  have hmul := tendsto_const_nhds (x := Real.pi).mul hdct
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * wMax),
    integral_limPenRadIntegrand_eq hpot] at hmul
  refine hmul.congr fun n => ?_
  dsimp only [G]
  split_ifs
  · rw [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * wMax)]
  · simp

/-- Explicit finite-`n` upper bound sequence for the pair-penalty expectation. -/
private def basePenUpper (rho w : Array Int) (Rbuf : ℝ) (n : ℕ) : ℝ :=
  let wMax := toR (w.getD (rho.size - 1) 0)
  if 4 ≤ n ∧ Rbuf / Real.sqrt (n : ℝ) ≤ 1 / 2 ∧ 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ) then
    (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
      (Real.pi * ∫ d in (0 : ℝ)..(2 * wMax), d * finitePenRadIntegrand rho w n d) +
    (((n - 1 : ℕ) : ℝ) / (2 * (n : ℝ))) * (1 - (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2) *
      (2 * wMax * (Real.pi * (2 * wMax) ^ 2))
  else
    (n : ℝ) * wMax

theorem basePen_upper_tendsto {rho w : Array Int} (hpot : ValidStepPot rho w)
    {Rbuf : ℝ} (hRbuf_pos : 0 ≤ Rbuf)
    (hRbuf_w : 2 * toR (w.getD (rho.size - 1) 0) ≤ Rbuf)
    (hRbuf_r : ∀ i < rho.size, 2 * toR (w.getD (rho.size - 1) 0) + toR (rho.getD i 0) ≤ Rbuf) :
    ∃ g : ℕ → ℝ,
      (∀ n : ℕ, (hn : 4 ≤ n) →
        ∫ X : Fin n → Pt,
          ((1 / (2 * (n : ℝ))) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u,
            max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
              stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v))
          ∂(unitSquarePi n) ≤ g n) ∧
      Tendsto g atTop (nhds (basePenMarg rho w + basePenInter rho w)) := by
  set wMax := toR (w.getD (rho.size - 1) 0)
  have hwMax_nn : 0 ≤ wMax := toR_nonneg (hpot.w_nonneg (by have := hpot.size_pos; omega))
  have hRbuf_r' : ∀ i < rho.size, toR (rho.getD i 0) ≤ Rbuf := fun i hi => by
    linarith [hRbuf_r i hi]
  refine ⟨basePenUpper rho w Rbuf, ?_, ?_⟩
  · intro n hn
    rw [integral_basePen_eq_pair hn hpot]
    unfold basePenUpper
    dsimp only
    by_cases hcond : 4 ≤ n ∧ Rbuf / Real.sqrt (n : ℝ) ≤ 1 / 2 ∧ 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ)
    · rw [if_pos hcond]
      have hsn_pos : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hmp := measurePreserving_consTwoPt (n := n) (by omega)
      have hint_orig := integrable_pairPen_term (n := n) (by omega) hpot ⟨0, by omega⟩ ⟨1, by omega⟩
      have hcomp_int : Integrable (fun p : Pt × (Pt × (Fin (n - 2) → Pt)) =>
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2)) ⟨0, by omega⟩) +
            stepPot rho w (nn2 (by omega) (rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2)) ⟨1, by omega⟩) -
            rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2) ⟨0, by omega⟩ ⟨1, by omega⟩))
          (unitSquareMeasure.prod (unitSquareMeasure.prod (unitSquarePi (n - 2)))) := by
        have hmeas_c : Measurable (fun p : Pt × (Pt × (Fin (n - 2) → Pt)) =>
            max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2)) ⟨0, by omega⟩) +
              stepPot rho w (nn2 (by omega) (rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2)) ⟨1, by omega⟩) -
              rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2) ⟨0, by omega⟩ ⟨1, by omega⟩)) :=
          measurable_const.max ((((measurable_stepPot rho w).comp
            ((measurable_nn2 (by omega) ⟨0, by omega⟩).comp hmp.measurable)).add
            ((measurable_stepPot rho w).comp
              ((measurable_nn2 (by omega) ⟨1, by omega⟩).comp hmp.measurable))).sub
            ((measurable_rescaledDist ⟨0, by omega⟩ ⟨1, by omega⟩).comp hmp.measurable))
        refine Integrable.of_bound hmeas_c.aestronglyMeasurable (2 * wMax)
          (Eventually.of_forall fun p => ?_)
        rw [Real.norm_of_nonneg (le_max_left _ _)]
        exact max_le (by linarith) (by
          linarith [stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2)) ⟨0, by omega⟩),
            stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2)) ⟨1, by omega⟩),
            rescaledDist_nonneg (consTwoPt (by omega) p.1 p.2.1 p.2.2) ⟨0, by omega⟩ ⟨1, by omega⟩])
      let F : Pt → Pt → (Fin (n - 2) → Pt) → ℝ := fun x₀ x₁ Z =>
        max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩) +
          stepPot rho w (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩) -
          Real.sqrt (n : ℝ) * euclidDist x₀ x₁)
      have hF_eq : ∀ p : Pt × (Pt × (Fin (n - 2) → Pt)),
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2)) ⟨0, by omega⟩) +
            stepPot rho w (nn2 (by omega) (rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2)) ⟨1, by omega⟩) -
            rescaledDist (consTwoPt (by omega) p.1 p.2.1 p.2.2) ⟨0, by omega⟩ ⟨1, by omega⟩) =
          F p.1 p.2.1 p.2.2 := by
        intro p
        simp only [F, rescaledDist, consTwoPt_zero, consTwoPt_one]
      have hF_int : Integrable (fun p : Pt × (Pt × (Fin (n - 2) → Pt)) => F p.1 p.2.1 p.2.2)
          (unitSquareMeasure.prod (unitSquareMeasure.prod (unitSquarePi (n - 2)))) := by
        simpa only [hF_eq] using hcomp_int
      have hF_int_inner : ∀ x₀ : Pt,
          Integrable (fun q : Pt × (Fin (n - 2) → Pt) => F x₀ q.1 q.2)
            (unitSquareMeasure.prod (unitSquarePi (n - 2))) := by
        intro x₀
        have hmeas_q : Measurable (fun q : Pt × (Fin (n - 2) → Pt) => F x₀ q.1 q.2) := by
          have hc : Measurable (fun q : Pt × (Fin (n - 2) → Pt) => consTwoPt (by omega) x₀ q.1 q.2) :=
            hmp.measurable.comp (measurable_const.prodMk measurable_id)
          refine measurable_const.max ((((measurable_stepPot rho w).comp
            ((measurable_nn2 (by omega) ⟨0, by omega⟩).comp hc)).add
            ((measurable_stepPot rho w).comp
              ((measurable_nn2 (by omega) ⟨1, by omega⟩).comp hc))).sub
            (measurable_const.mul (measurable_euclidDist.comp (measurable_const.prodMk measurable_fst))))
        refine Integrable.of_bound hmeas_q.aestronglyMeasurable (2 * wMax)
          (Eventually.of_forall fun q => ?_)
        rw [Real.norm_of_nonneg (le_max_left _ _)]
        exact max_le (by linarith) (by
          linarith [stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ q.1 q.2)) ⟨0, by omega⟩),
            stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ q.1 q.2)) ⟨1, by omega⟩),
            mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (euclidDist_nonneg x₀ q.1)])
      let Φ : Pt → ℝ := fun x₀ =>
        ∫ x₁ : Pt, (∫ Z : Fin (n - 2) → Pt, F x₀ x₁ Z ∂(unitSquarePi (n - 2))) ∂unitSquareMeasure
      have hsplit_eq : ∫ X : Fin n → Pt,
            max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩) +
              stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨1, by omega⟩) -
              rescaledDist X ⟨0, by omega⟩ ⟨1, by omega⟩) ∂(unitSquarePi n) =
          ∫ x₀ : Pt, Φ x₀ ∂unitSquareMeasure := by
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
          (by rw [hmp.map_eq]; exact hint_orig.aestronglyMeasurable)]
        simp_rw [hF_eq]
        rw [MeasureTheory.integral_prod _ hF_int]
        refine integral_congr_ae (Eventually.of_forall fun x₀ => ?_)
        exact MeasureTheory.integral_prod _ (hF_int_inner x₀)
      rw [hsplit_eq]
      let B := interiorBox (Rbuf / Real.sqrt (n : ℝ))
      have hB_meas : MeasurableSet B := measurableSet_interiorBox _
      have hΦ_int : Integrable Φ unitSquareMeasure := by
        have h1 := hF_int.integral_prod_left
        refine h1.congr (Eventually.of_forall fun x₀ => ?_)
        exact MeasureTheory.integral_prod _ (hF_int_inner x₀)
      rw [← integral_add_compl hB_meas hΦ_int]
      -- (A) Exact evaluation of `Φ x₀` for `x₀ ∈ B`
      have hΦ_on_B : ∀ x₀ ∈ B,
          Φ x₀ = (1 / (n : ℝ)) * ∫ d in (0 : ℝ)..(2 * wMax),
            (2 * Real.pi * d) * finitePenRadIntegrand rho w n d := by
        intro x₀ hx₀
        have hinner_eq : ∀ x₁ : Pt,
            ∫ Z : Fin (n - 2) → Pt, F x₀ x₁ Z ∂(unitSquarePi (n - 2)) =
              finitePenRadIntegrand rho w n (Real.sqrt (n : ℝ) * euclidDist x₀ x₁) := by
          intro x₁
          set d := Real.sqrt (n : ℝ) * euclidDist x₀ x₁
          have hd_nn : 0 ≤ d := mul_nonneg (le_of_lt hsn_pos) (euclidDist_nonneg x₀ x₁)
          by_cases hd_gt : 2 * wMax < d
          · rw [finitePenRadIntegrand_eq_zero_of_gt hpot n hd_gt]
            have hFz : ∀ Z : Fin (n - 2) → Pt, F x₀ x₁ Z = 0 := fun Z => by
              dsimp only [F]
              exact max_eq_left (by
                linarith [stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩),
                  stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩)])
            simp_rw [hFz, integral_zero]
          · push Not at hd_gt
            have hA_sub : ∀ i : Fin rho.size,
                disk x₀ (toR (rho.getD i.val 0) / Real.sqrt (n : ℝ)) ⊆ unitSquare := fun i =>
              disk_subset_unitSquare hx₀
                (div_nonneg (toR_nonneg (hpot.rho_nonneg i.isLt)) (le_of_lt hsn_pos))
                (div_le_div_of_nonneg_right (hRbuf_r' i.val i.isLt) (le_of_lt hsn_pos))
            have hB_sub : ∀ i : Fin rho.size,
                disk x₁ (toR (rho.getD i.val 0) / Real.sqrt (n : ℝ)) ⊆ unitSquare := by
              intro i z hz
              have hρ_nn := toR_nonneg (hpot.rho_nonneg i.isLt)
              have hzx1 : euclidDist z x₁ ≤ toR (rho.getD i.val 0) / Real.sqrt (n : ℝ) :=
                (euclidDist_le_iff (div_nonneg hρ_nn (le_of_lt hsn_pos))).mpr hz
              have hx1x0 : euclidDist x₁ x₀ ≤ 2 * wMax / Real.sqrt (n : ℝ) := by
                rw [euclidDist_symm, le_div_iff₀ hsn_pos]; linarith
              have hzx0 : euclidDist z x₀ ≤ Rbuf / Real.sqrt (n : ℝ) := by
                calc euclidDist z x₀ ≤ euclidDist z x₁ + euclidDist x₁ x₀ := euclidDist_triangle z x₁ x₀
                  _ ≤ toR (rho.getD i.val 0) / Real.sqrt (n : ℝ) + 2 * wMax / Real.sqrt (n : ℝ) :=
                      add_le_add hzx1 hx1x0
                  _ = (2 * wMax + toR (rho.getD i.val 0)) / Real.sqrt (n : ℝ) := by ring
                  _ ≤ Rbuf / Real.sqrt (n : ℝ) :=
                      div_le_div_of_nonneg_right (hRbuf_r i.val i.isLt) (le_of_lt hsn_pos)
              exact disk_subset_unitSquare hx₀ (div_nonneg hRbuf_pos (le_of_lt hsn_pos)) le_rfl
                ((euclidDist_le_iff (div_nonneg hRbuf_pos (le_of_lt hsn_pos))).mp hzx0)
            have hmeas_nn2 : ∀ u : Fin n, Measurable (fun Z : Fin (n - 2) → Pt =>
                nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) u) := fun u =>
              (measurable_nn2 (by omega) u).comp
                (hmp.measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
            have hint_ind0 : ∀ i : Fin rho.size, Integrable (fun Z : Fin (n - 2) → Pt =>
                if toR (rho.getD i.val 0) <
                  nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                then (1 : ℝ) else 0) (unitSquarePi (n - 2)) := fun i =>
              Integrable.of_bound
                (Measurable.ite (measurableSet_lt measurable_const (hmeas_nn2 ⟨0, by omega⟩))
                  measurable_const measurable_const).aestronglyMeasurable
                1 (Eventually.of_forall fun _ => by split_ifs <;> norm_num)
            have hint_ind1 : ∀ j : Fin rho.size, Integrable (fun Z : Fin (n - 2) → Pt =>
                if toR (rho.getD j.val 0) <
                  nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                then (1 : ℝ) else 0) (unitSquarePi (n - 2)) := fun j =>
              Integrable.of_bound
                (Measurable.ite (measurableSet_lt measurable_const (hmeas_nn2 ⟨1, by omega⟩))
                  measurable_const measurable_const).aestronglyMeasurable
                1 (Eventually.of_forall fun _ => by split_ifs <;> norm_num)
            have hint_joint : ∀ i j : Fin rho.size, Integrable (fun Z : Fin (n - 2) → Pt =>
                baseInterCoeff w i.val j.val d *
                  (if toR (rho.getD i.val 0) <
                    nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                  then (1 : ℝ) else 0) *
                  (if toR (rho.getD j.val 0) <
                    nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                  then (1 : ℝ) else 0)) (unitSquarePi (n - 2)) := by
              intro i j
              have hmul : (fun Z : Fin (n - 2) → Pt =>
                  baseInterCoeff w i.val j.val d *
                    (if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then (1 : ℝ) else 0) *
                    (if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then (1 : ℝ) else 0)) =
                  fun Z => baseInterCoeff w i.val j.val d *
                    ((if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then (1 : ℝ) else 0) *
                    (if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then (1 : ℝ) else 0)) := by funext Z; ring
              rw [hmul]
              refine (Integrable.of_bound ?_ 1 (Eventually.of_forall fun _ => by
                split_ifs <;> norm_num)).const_mul _
              exact ((Measurable.ite (measurableSet_lt measurable_const (hmeas_nn2 ⟨0, by omega⟩))
                measurable_const measurable_const).mul
                (Measurable.ite (measurableSet_lt measurable_const (hmeas_nn2 ⟨1, by omega⟩))
                  measurable_const measurable_const)).aestronglyMeasurable
            have habel : ∀ Z : Fin (n - 2) → Pt, F x₀ x₁ Z =
                (∑ i : Fin rho.size,
                  (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
                    if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then 1 else 0) +
                (∑ j : Fin rho.size,
                  (max 0 (toR (w.getD j.val 0) - d) - max 0 (toR (wPrev w j.val) - d)) *
                    if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then 1 else 0) +
                ∑ i : Fin rho.size, ∑ j : Fin rho.size,
                  baseInterCoeff w i.val j.val d *
                    (if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then 1 else 0) *
                    (if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then 1 else 0) := fun Z =>
              stepPot_abel_2d hpot d _ _ hd_nn
            simp_rw [habel]
            have hintS1 : Integrable (fun Z : Fin (n - 2) → Pt =>
                ∑ i : Fin rho.size,
                  (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
                    if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then 1 else 0) (unitSquarePi (n - 2)) :=
              integrable_finsetSum _ fun i _ => (hint_ind0 i).const_mul _
            have hintS2 : Integrable (fun Z : Fin (n - 2) → Pt =>
                ∑ j : Fin rho.size,
                  (max 0 (toR (w.getD j.val 0) - d) - max 0 (toR (wPrev w j.val) - d)) *
                    if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then 1 else 0) (unitSquarePi (n - 2)) :=
              integrable_finsetSum _ fun j _ => (hint_ind1 j).const_mul _
            have hintS3 : Integrable (fun Z : Fin (n - 2) → Pt =>
                ∑ i : Fin rho.size, ∑ j : Fin rho.size,
                  baseInterCoeff w i.val j.val d *
                    (if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then 1 else 0) *
                    (if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then 1 else 0)) (unitSquarePi (n - 2)) :=
              integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_joint i j
            have hintS12 : Integrable (fun Z : Fin (n - 2) → Pt =>
                (∑ i : Fin rho.size,
                  (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
                    if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then 1 else 0) +
                ∑ j : Fin rho.size,
                  (max 0 (toR (w.getD j.val 0) - d) - max 0 (toR (wPrev w j.val) - d)) *
                    if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then 1 else 0) (unitSquarePi (n - 2)) :=
              hintS1.add hintS2
            rw [integral_add hintS12 hintS3,
              integral_add hintS1 hintS2,
              integral_finsetSum _ fun i _ => (hint_ind0 i).const_mul _,
              integral_finsetSum _ fun j _ => (hint_ind1 j).const_mul _,
              integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_joint i j]
            have hS1 : ∑ i : Fin rho.size,
                ∫ Z : Fin (n - 2) → Pt,
                  (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
                    (if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then 1 else 0) ∂(unitSquarePi (n - 2)) =
                ∑ i : Fin rho.size,
                  (max 0 (toR (w.getD i.val 0) - d) - max 0 (toR (wPrev w i.val) - d)) *
                    finiteMargSurv n d (toR (rho.getD i.val 0)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [integral_const_mul,
                prob_consTwoPt_marg_zero hn (toR_nonneg (hpot.rho_nonneg i.isLt)) (hA_sub i)]
            have hS2 : ∑ j : Fin rho.size,
                ∫ Z : Fin (n - 2) → Pt,
                  (max 0 (toR (w.getD j.val 0) - d) - max 0 (toR (wPrev w j.val) - d)) *
                    (if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then 1 else 0) ∂(unitSquarePi (n - 2)) =
                ∑ j : Fin rho.size,
                  (max 0 (toR (w.getD j.val 0) - d) - max 0 (toR (wPrev w j.val) - d)) *
                    finiteMargSurv n d (toR (rho.getD j.val 0)) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [integral_const_mul,
                prob_consTwoPt_marg_one hn (toR_nonneg (hpot.rho_nonneg j.isLt)) (hB_sub j)]
            have hS3 : ∑ i : Fin rho.size,
                ∫ Z : Fin (n - 2) → Pt, (∑ j : Fin rho.size,
                  baseInterCoeff w i.val j.val d *
                    (if toR (rho.getD i.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩
                    then 1 else 0) *
                    (if toR (rho.getD j.val 0) <
                      nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩
                    then 1 else 0)) ∂(unitSquarePi (n - 2)) =
                ∑ i : Fin rho.size, ∑ j : Fin rho.size,
                  baseInterCoeff w i.val j.val d *
                    finiteJointSurv n d (toR (rho.getD i.val 0)) (toR (rho.getD j.val 0))
                      (decide (toR (rho.getD i.val 0) < d)) (decide (toR (rho.getD j.val 0) < d)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [integral_finsetSum _ fun j _ => hint_joint i j]
              refine Finset.sum_congr rfl fun j _ => ?_
              simp_rw [mul_assoc]
              rw [integral_const_mul,
                prob_consTwoPt_joint hn (toR_nonneg (hpot.rho_nonneg i.isLt))
                  (toR_nonneg (hpot.rho_nonneg j.isLt)) (hA_sub i) (hB_sub j)]
            rw [hS1, hS2, hS3]
            unfold finitePenRadIntegrand; ring
        dsimp only [Φ]
        simp_rw [hinner_eq]
        let H : ℝ → ℝ := fun d => if 0 ≤ d then finitePenRadIntegrand rho w n d else 0
        have hH_eq : ∀ x₁ : Pt,
            finitePenRadIntegrand rho w n (Real.sqrt (n : ℝ) * euclidDist x₀ x₁) =
              H (Real.sqrt (n : ℝ) * euclidDist x₀ x₁) := fun x₁ => by
          dsimp only [H]
          rw [if_pos (mul_nonneg (le_of_lt hsn_pos) (euclidDist_nonneg x₀ x₁))]
        simp_rw [hH_eq]
        have hH_meas : Measurable H :=
          Measurable.ite (measurableSet_le measurable_const measurable_id)
            (measurable_finitePenRadIntegrand rho w n) measurable_const
        have hH_nn : ∀ d, 0 ≤ H d := fun d => by
          dsimp only [H]; split_ifs with hd0
          · exact finitePenRadIntegrand_nonneg hpot hRbuf_r' hcond.1 hcond.2.2 hd0
          · exact le_rfl
        have hH_supp : ∀ d, 2 * wMax < d → H d = 0 := fun d hd => by
          dsimp only [H]; split_ifs
          · exact finitePenRadIntegrand_eq_zero_of_gt hpot n hd
          · rfl
        rw [integral_unitSquare_radial_rescaled (by omega) (by linarith : 0 ≤ 2 * wMax) hRbuf_w hx₀
          (H := H) hH_meas hH_nn hH_supp]
        congr 1
        refine intervalIntegral.integral_congr fun d hd => ?_
        have hd0 : 0 ≤ d := by
          rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 2 * wMax)] at hd; exact hd.1
        simp only [H, if_pos hd0]
      have hB_int_eq : ∫ x₀ in B, Φ x₀ ∂unitSquareMeasure =
          (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
            ((1 / (n : ℝ)) * ∫ d in (0 : ℝ)..(2 * wMax),
              (2 * Real.pi * d) * finitePenRadIntegrand rho w n d) := by
        rw [setIntegral_congr_fun hB_meas hΦ_on_B, setIntegral_const, smul_eq_mul, Measure.real,
          unitSquareMeasure_interiorBox (div_nonneg hRbuf_pos (le_of_lt hsn_pos)) hcond.2.1]
        congr 1; ring
      -- (B) Upper bound on `Φ x₀` for `x₀ ∈ Bᶜ`
      have hΦ_le : ∀ x₀ : Pt, Φ x₀ ≤ 2 * wMax * (Real.pi * (2 * wMax) ^ 2 / (n : ℝ)) := by
        intro x₀
        dsimp only [Φ]
        let D := disk x₀ (2 * wMax / Real.sqrt (n : ℝ))
        have hD_meas : MeasurableSet D := measurableSet_disk _ _
        have hpt : ∀ x₁ : Pt,
            ∫ Z : Fin (n - 2) → Pt, F x₀ x₁ Z ∂(unitSquarePi (n - 2)) ≤
              (2 * wMax) * if x₁ ∈ D then (1 : ℝ) else 0 := by
          intro x₁
          by_cases hx₁ : x₁ ∈ D
          · rw [if_pos hx₁, mul_one]
            calc ∫ Z : Fin (n - 2) → Pt, F x₀ x₁ Z ∂(unitSquarePi (n - 2))
                ≤ ∫ _ : Fin (n - 2) → Pt, (2 * wMax) ∂(unitSquarePi (n - 2)) := by
                  refine integral_mono ?_ (integrable_const _) fun Z => ?_
                  · refine Integrable.of_bound ?_ (2 * wMax) (Eventually.of_forall fun Z => ?_)
                    · have hc : Measurable (fun Z : Fin (n - 2) → Pt =>
                          consTwoPt (by omega) x₀ x₁ Z) :=
                        hmp.measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
                      exact (measurable_const.max ((((measurable_stepPot rho w).comp
                        ((measurable_nn2 (by omega) ⟨0, by omega⟩).comp hc)).add
                        ((measurable_stepPot rho w).comp
                          ((measurable_nn2 (by omega) ⟨1, by omega⟩).comp hc))).sub
                        measurable_const)).aestronglyMeasurable
                    · rw [Real.norm_of_nonneg (le_max_left _ _)]
                      exact max_le (by linarith) (by
                        linarith [stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩),
                          stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩),
                          mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (euclidDist_nonneg x₀ x₁)])
                  · exact max_le (by linarith) (by
                      linarith [stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩),
                        stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩),
                        mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (euclidDist_nonneg x₀ x₁)])
              _ = 2 * wMax := by simp [Measure.real]
          · rw [if_neg hx₁, mul_zero]
            have hgt : 2 * wMax < Real.sqrt (n : ℝ) * euclidDist x₀ x₁ := by
              by_contra hle; push Not at hle
              apply hx₁
              refine (euclidDist_le_iff (div_nonneg (by linarith) (le_of_lt hsn_pos))).mp ?_
              rw [euclidDist_symm, le_div_iff₀ hsn_pos]; linarith
            have hFz : ∀ Z, F x₀ x₁ Z = 0 := fun Z => max_eq_left (by
              linarith [stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨0, by omega⟩),
                stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist (consTwoPt (by omega) x₀ x₁ Z)) ⟨1, by omega⟩)])
            simp_rw [hFz, integral_zero]; exact le_rfl
        calc ∫ x₁ : Pt, (∫ Z : Fin (n - 2) → Pt, F x₀ x₁ Z ∂(unitSquarePi (n - 2))) ∂unitSquareMeasure
            ≤ ∫ x₁ : Pt, ((2 * wMax) * if x₁ ∈ D then (1 : ℝ) else 0) ∂unitSquareMeasure :=
              integral_mono (hF_int_inner x₀).integral_prod_left
                ((integrable_indicator_one_unitSquare hD_meas).const_mul _) hpt
          _ = (2 * wMax) * (unitSquareMeasure D).toReal := by
              rw [integral_const_mul, integral_indicator_one_unitSquare hD_meas]
          _ ≤ (2 * wMax) * (volume D).toReal := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              have hfin : volume D ≠ ⊤ := by
                rw [volume_disk x₀ (div_nonneg (by linarith) (le_of_lt hsn_pos))]
                exact ENNReal.ofReal_ne_top
              exact ENNReal.toReal_mono hfin (unitSquareMeasure_le_volume D)
          _ = 2 * wMax * (Real.pi * (2 * wMax) ^ 2 / (n : ℝ)) := by
              rw [volume_disk x₀ (div_nonneg (by linarith) (le_of_lt hsn_pos)),
                ENNReal.toReal_ofReal (by positivity), div_pow,
                Real.sq_sqrt (Nat.cast_nonneg n), mul_div_assoc]
      have hBc_int_le : ∫ x₀ in Bᶜ, Φ x₀ ∂unitSquareMeasure ≤
          (1 - (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2) *
            (2 * wMax * (Real.pi * (2 * wMax) ^ 2 / (n : ℝ))) := by
        calc ∫ x₀ in Bᶜ, Φ x₀ ∂unitSquareMeasure
            ≤ ∫ _ in Bᶜ, (2 * wMax * (Real.pi * (2 * wMax) ^ 2 / (n : ℝ))) ∂unitSquareMeasure :=
              setIntegral_mono_on hΦ_int.integrableOn (integrable_const _).integrableOn hB_meas.compl
                fun x₀ _ => hΦ_le x₀
          _ = (unitSquareMeasure Bᶜ).toReal *
                (2 * wMax * (Real.pi * (2 * wMax) ^ 2 / (n : ℝ))) := by
              rw [setIntegral_const, smul_eq_mul, Measure.real]
          _ = (1 - (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2) *
                (2 * wMax * (Real.pi * (2 * wMax) ^ 2 / (n : ℝ))) := by
              rw [unitSquareMeasure_compl_toReal hB_meas,
                unitSquareMeasure_interiorBox (div_nonneg hRbuf_pos (le_of_lt hsn_pos)) hcond.2.1]
              congr 2; ring
      -- Combine interior and boundary bounds
      have hpull_2pi : ∫ d in (0 : ℝ)..(2 * wMax),
            (2 * Real.pi * d) * finitePenRadIntegrand rho w n d =
          2 * (Real.pi * ∫ d in (0 : ℝ)..(2 * wMax), d * finitePenRadIntegrand rho w n d) := by
        have hrew : (fun d : ℝ => (2 * Real.pi * d) * finitePenRadIntegrand rho w n d) =
            fun d => (2 * Real.pi) * (d * finitePenRadIntegrand rho w n d) := by
          funext d; ring
        rw [hrew, intervalIntegral.integral_const_mul]; ring
      rw [hB_int_eq, hpull_2pi]
      have hcomb : (((n - 1 : ℕ) : ℝ) / 2) *
          ((1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
            ((1 / (n : ℝ)) *
              (2 * (Real.pi * ∫ d in (0 : ℝ)..(2 * wMax), d * finitePenRadIntegrand rho w n d))) +
            ∫ x₀ in Bᶜ, Φ x₀ ∂unitSquareMeasure) ≤
          (((n - 1 : ℕ) : ℝ) / 2) *
          ((1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
            ((1 / (n : ℝ)) *
              (2 * (Real.pi * ∫ d in (0 : ℝ)..(2 * wMax), d * finitePenRadIntegrand rho w n d))) +
            (1 - (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2) *
              (2 * wMax * (Real.pi * (2 * wMax) ^ 2 / (n : ℝ)))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hBc_int_le) (by positivity)
      refine hcomb.trans (le_of_eq ?_)
      ring
    · -- Fallback bound when `¬ hcond`
      rw [if_neg hcond]
      have hint_le : ∫ X : Fin n → Pt,
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩) +
            stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨1, by omega⟩) -
            rescaledDist X ⟨0, by omega⟩ ⟨1, by omega⟩) ∂(unitSquarePi n) ≤ 2 * wMax := by
        calc ∫ X : Fin n → Pt,
              max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩) +
                stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨1, by omega⟩) -
                rescaledDist X ⟨0, by omega⟩ ⟨1, by omega⟩) ∂(unitSquarePi n)
            ≤ ∫ _ : Fin n → Pt, (2 * wMax) ∂(unitSquarePi n) :=
              integral_mono (integrable_pairPen_term (by omega) hpot ⟨0, by omega⟩ ⟨1, by omega⟩)
                (integrable_const _) fun X =>
                  max_le (by linarith) (by
                    linarith [stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩),
                      stepPot_le_wMax hpot (nn2 (by omega) (rescaledDist X) ⟨1, by omega⟩),
                      rescaledDist_nonneg X ⟨0, by omega⟩ ⟨1, by omega⟩])
          _ = 2 * wMax := by simp [Measure.real]
      have hnm1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
      calc (((n - 1 : ℕ) : ℝ) / 2) * ∫ X : Fin n → Pt,
            max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨0, by omega⟩) +
              stepPot rho w (nn2 (by omega) (rescaledDist X) ⟨1, by omega⟩) -
              rescaledDist X ⟨0, by omega⟩ ⟨1, by omega⟩) ∂(unitSquarePi n)
          ≤ (((n - 1 : ℕ) : ℝ) / 2) * (2 * wMax) :=
            mul_le_mul_of_nonneg_left hint_le (by positivity)
        _ = ((n - 1 : ℕ) : ℝ) * wMax := by ring
        _ ≤ (n : ℝ) * wMax := mul_le_mul_of_nonneg_right hnm1 hwMax_nn
  · -- Convergence `basePenUpper rho w Rbuf n → basePenMarg rho w + basePenInter rho w`
    have hnat1 := tendsto_nat_sub_div_self 1
    have hbox := tendsto_one_sub_inv_sqrt_sq Rbuf
    have hint_lim := tendsto_integral_finitePenRadIntegrand hpot hRbuf_r'
    have hpart1 : Tendsto (fun n : ℕ =>
        (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2 *
          (if 4 ≤ n ∧ 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ) then
            Real.pi * ∫ d in (0 : ℝ)..(2 * wMax), d * finitePenRadIntegrand rho w n d
          else 0))
        atTop (nhds (1 * 1 * (basePenMarg rho w + basePenInter rho w))) :=
      (hnat1.mul hbox).mul hint_lim
    simp only [one_mul] at hpart1
    have hpart2 : Tendsto (fun n : ℕ =>
        (((n - 1 : ℕ) : ℝ) / (2 * (n : ℝ))) * (1 - (1 - 2 * Rbuf / Real.sqrt (n : ℝ)) ^ 2) *
          (2 * wMax * (Real.pi * (2 * wMax) ^ 2)))
        atTop (nhds ((1 / 2) * (1 - 1) * (2 * wMax * (Real.pi * (2 * wMax) ^ 2)))) := by
      have hhalf : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (2 * (n : ℝ))) atTop (nhds (1 / 2)) := by
        have h := hnat1.div_const 2
        refine h.congr fun n => ?_; ring
      exact (hhalf.mul (tendsto_const_nhds.sub hbox)).mul tendsto_const_nhds
    simp only [sub_self, mul_zero, zero_mul] at hpart2
    have hsum := hpart1.add hpart2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    have hdiv0 : Tendsto (fun n : ℕ => Rbuf / Real.sqrt (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hev_half : ∀ᶠ n : ℕ in atTop, Rbuf / Real.sqrt (n : ℝ) ≤ 1 / 2 :=
      (hdiv0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => le_of_lt h
    have hev_R : ∀ᶠ n : ℕ in atTop, 2 * Real.pi * Rbuf ^ 2 ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop _)
    filter_upwards [Filter.eventually_ge_atTop 4, hev_half, hev_R] with n hn4 hhalf hnR
    unfold basePenUpper
    simp only [hn4, hhalf, hnR, and_self, ↓reduceIte]
    rfl

end

end BHHBounds.Dual
