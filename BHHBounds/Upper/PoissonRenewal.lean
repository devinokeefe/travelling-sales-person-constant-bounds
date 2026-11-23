import BHHBounds.Upper.StripDPBound
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Poisson Renewal Order Statistics and Multi-Strip Superposition

Proves:
1. Basic properties of `finTourLen` (`finTourLen_continuous`, `finTourLen_perm`,
   `finTourLen_mono_castLE`, `expectedTourLen`, `expectedTourLen_mono`).
2. Elementary Poisson probability identities (`hasSum_poissonProb`, `poisson_chebyshev`,
   `poisson_chernoff_upper`).
3. 1D renewal order-statistic Jacobian (`lintegral_gapSimplex_eq_orderedSimplex`) by induction on `k`
   and `k!`-simplex symmetry (`lintegral_orderedSimplex_mul_factorial`).
4. Single-strip renewal identity (`single_strip_renewal_lintegral`).
-/

namespace BHHBounds.Upper

open MeasureTheory Set Finset BigOperators
open scoped ENNReal NNReal

/-! ## Section 1: `finTourLen` Measurability, Symmetry, Integrability & Monotonicity -/

/-- `finTourLen x` as a finite infimum over `Equiv.Perm (Fin n)`. -/
lemma finTourLen_eq_inf' {n : ℕ} (x : Fin n → ℝ × ℝ) :
    finTourLen x = (Finset.univ : Finset (Equiv.Perm (Fin n))).inf' Finset.univ_nonempty
      (fun σ => ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i)))) := by
  unfold finTourLen
  apply le_antisymm
  · exact le_inf' _ _ fun σ _ => finTourLen_le_perm x σ
  · refine le_ciInf fun σ => ?_
    exact inf'_le _ (Finset.mem_univ σ)

lemma continuous_ptDist : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ptDist p.1 p.2) := by
  unfold ptDist; fun_prop

lemma finTourLen_continuous (n : ℕ) : Continuous (finTourLen (n := n)) := by
  have hfun : (finTourLen (n := n)) = fun x =>
      (Finset.univ : Finset (Equiv.Perm (Fin n))).inf' Finset.univ_nonempty
        (fun σ => ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i)))) := by
    funext x; exact finTourLen_eq_inf' x
  rw [hfun]
  have hmem : ∀ s : Finset (Equiv.Perm (Fin n)), (hs : s.Nonempty) →
      Continuous (fun x : Fin n → ℝ × ℝ =>
        s.inf' hs (fun σ => ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i))))) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => intro hs; exact absurd hs Finset.not_nonempty_empty
    | cons a s' ha ih =>
      intro _
      by_cases hne : s'.Nonempty
      · have heq : (fun x : Fin n → ℝ × ℝ =>
            (Finset.cons a s' ha).inf' (Finset.cons_nonempty _)
              (fun σ => ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i))))) =
            fun x => min (∑ i : Fin n, ptDist (x (a i)) (x (a (finRotate n i))))
              (s'.inf' hne (fun σ => ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i))))) := by
          funext x
          exact Finset.inf'_cons (f := fun σ : Equiv.Perm (Fin n) =>
            ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i)))) hne
        rw [heq]
        refine Continuous.min ?_ (ih hne)
        exact continuous_finsetSum _ fun i _ =>
          continuous_ptDist.comp (f := fun x : Fin n → ℝ × ℝ => (x (a i), x (a (finRotate n i))))
            ((continuous_apply (a i)).prodMk (continuous_apply (a (finRotate n i))))
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        have heq : (fun x : Fin n → ℝ × ℝ =>
            (Finset.cons a ∅ ha).inf' (Finset.cons_nonempty _)
              (fun σ => ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i))))) =
            fun x => ∑ i : Fin n, ptDist (x (a i)) (x (a (finRotate n i))) := by
          funext x; simp
        rw [heq]
        exact continuous_finsetSum _ fun i _ =>
          continuous_ptDist.comp (f := fun x : Fin n → ℝ × ℝ => (x (a i), x (a (finRotate n i))))
            ((continuous_apply (a i)).prodMk (continuous_apply (a (finRotate n i))))
  exact hmem Finset.univ Finset.univ_nonempty

lemma finTourLen_perm {n : ℕ} (x : Fin n → ℝ × ℝ) (τ : Equiv.Perm (Fin n)) :
    finTourLen (x ∘ τ) = finTourLen x := by
  apply le_antisymm
  · refine le_ciInf fun σ => ?_
    have h := finTourLen_le_perm (x ∘ τ) (τ⁻¹ * σ)
    refine h.trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    simp [Function.comp]
  · refine le_ciInf fun σ => ?_
    have h := finTourLen_le_perm x (τ * σ)
    refine h.trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    simp [Function.comp]

lemma finTourLen_mono_castLE {n r : ℕ} (h : n ≤ r) (x : Fin r → ℝ × ℝ) :
    finTourLen (fun i : Fin n => x (Fin.castLE h i)) ≤ finTourLen x := by
  refine le_ciInf fun σ => ?_
  let L : List (ℝ × ℝ) := (List.finRange r).map (x ∘ σ)
  have hlen : L.length = r := by simp [L]
  let f : Fin n → Fin L.length := fun i => Fin.cast hlen.symm (σ⁻¹ (Fin.castLE h i))
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : σ⁻¹ (Fin.castLE h i) = σ⁻¹ (Fin.castLE h j) := by
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa [f] using this)
    have h2 := σ⁻¹.injective h1
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  have hval : ∀ i : Fin n, L[f i] = x (Fin.castLE h i) := by
    intro i
    simp [L, f]
  calc finTourLen (fun i : Fin n => x (Fin.castLE h i))
      ≤ cycleLen L := finTourLen_le_cycleLen_of_inj _ L f hf hval
    _ = ∑ i : Fin r, ptDist (x (σ i)) (x (σ (finRotate r i))) := cycleLen_finRange r (x ∘ σ)

/-- Uniform probability measure on `[0,1]²`. -/
noncomputable def unitSquareMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))

instance isProbabilityMeasure_unitSquareMeasure : IsProbabilityMeasure unitSquareMeasure := by
  unfold unitSquareMeasure
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
    constructor; simp [Real.volume_Icc]
  infer_instance

/-- `n`-fold product of `unitSquareMeasure` on `Fin n → ℝ × ℝ`. -/
noncomputable def unitSquarePi (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun _ : Fin n => unitSquareMeasure

instance isProbabilityMeasure_unitSquarePi (n : ℕ) : IsProbabilityMeasure (unitSquarePi n) := by
  unfold unitSquarePi; infer_instance

/-- Expected optimal TSP tour length of `n` i.i.d. uniform points in `[0,1]²`. -/
noncomputable def expectedTourLen (n : ℕ) : ℝ :=
  ∫ x : Fin n → ℝ × ℝ, finTourLen x ∂(unitSquarePi n)

/-- General coordinate-projection measure-preserving lemma for `Measure.pi`. -/
lemma measurePreserving_pi_emb_gen {α : Type*} [MeasurableSpace α] {k n : ℕ}
    (μ : Fin n → Measure α) [∀ j, IsProbabilityMeasure (μ j)] (emb : Fin k ↪ Fin n) :
    MeasurePreserving (fun x : Fin n → α => fun i : Fin k => x (emb i))
      (Measure.pi μ) (Measure.pi fun i : Fin k => μ (emb i)) := by
  have hmeas : Measurable (fun x : Fin n → α => fun i : Fin k => x (emb i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (emb i)
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  let t : Fin n → Set α := fun j =>
    if h : ∃ i : Fin k, emb i = j then s h.choose else Set.univ
  have hpre : (fun x : Fin n → α => fun i : Fin k => x (emb i)) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx j
      dsimp only [t]
      split_ifs with h
      · have h1 := hx h.choose; rwa [h.choose_spec] at h1
      · trivial
    · intro hx i
      have hj := hx (emb i)
      have hex : ∃ i' : Fin k, emb i' = emb i := ⟨i, rfl⟩
      dsimp only [t] at hj
      rw [dif_pos hex] at hj
      have heq : hex.choose = i := emb.injective hex.choose_spec
      rwa [heq] at hj
  rw [hpre, Measure.pi_pi]
  have hprod : ∏ j : Fin n, μ j (t j) = ∏ j ∈ Finset.univ.image emb, μ j (t j) := by
    symm
    refine Finset.prod_subset (Finset.subset_univ _) fun j _ hj => ?_
    have hnot : ¬∃ i : Fin k, emb i = j := fun ⟨i, hi⟩ =>
      hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    dsimp only [t]; rw [dif_neg hnot]; exact measure_univ
  rw [hprod, Finset.prod_image (fun i _ j _ hij => emb.injective hij)]
  apply Finset.prod_congr rfl
  intro i _
  have hex : ∃ i' : Fin k, emb i' = emb i := ⟨i, rfl⟩
  dsimp only [t]; rw [dif_pos hex]
  have heq : hex.choose = i := emb.injective hex.choose_spec
  rw [heq]

/-- General coordinate-reindexing measure-preserving lemma for `Measure.pi`. -/
lemma measurePreserving_pi_equiv {α : Type*} [MeasurableSpace α] {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂] (e : ι₁ ≃ ι₂) (μ : ι₂ → Measure α)
    [∀ j, SigmaFinite (μ j)] :
    MeasurePreserving (fun x : ι₂ → α => fun i : ι₁ => x (e i))
      (Measure.pi μ) (Measure.pi fun i : ι₁ => μ (e i)) := by
  have hmeas : Measurable (fun x : ι₂ → α => fun i : ι₁ => x (e i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ι₂ → α => fun i : ι₁ => x (e i)) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun j => s (e.symm j)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx j; simpa using hx (e.symm j)
    · intro hx i; simpa using hx (e i)
  rw [hpre, Measure.pi_pi]
  exact (Fintype.prod_equiv e (fun i => μ (e i) (s i)) (fun j => μ j (s (e.symm j)))
    (fun i => by simp)).symm

lemma ae_mem_unitSquareMeasure :
    ∀ᵐ p ∂unitSquareMeasure, p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  unfold unitSquareMeasure
  have h1 : ∀ᵐ x : ℝ ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).mpr
    (h1.mono fun x hx => h1.mono fun y hy => ⟨hx, hy⟩)

lemma ae_mem_unitSquarePi (n : ℕ) :
    ∀ᵐ x ∂(unitSquarePi n), ∀ i : Fin n, x i ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  have h : ∀ i : Fin n, ∀ᵐ x ∂(unitSquarePi n), x i ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro i
    have hmp : MeasurePreserving (fun x : Fin n → ℝ × ℝ => x i) (unitSquarePi n) unitSquareMeasure :=
      measurePreserving_eval (fun _ : Fin n => unitSquareMeasure) i
    exact hmp.quasiMeasurePreserving.ae ae_mem_unitSquareMeasure
  exact ae_all_iff.mpr h

lemma finTourLen_integrable (n : ℕ) : Integrable (finTourLen (n := n)) (unitSquarePi n) := by
  refine Integrable.mono' (integrable_const (4 * Real.sqrt (n : ℝ) + 4))
    (finTourLen_continuous n).aestronglyMeasurable ?_
  filter_upwards [ae_mem_unitSquarePi n] with x hx
  rw [Real.norm_of_nonneg (finTourLen_nonneg x)]
  exact finTourLen_unitSquare_le x hx

lemma expectedTourLen_mono {n r : ℕ} (h : n ≤ r) :
    expectedTourLen n ≤ expectedTourLen r := by
  unfold expectedTourLen
  let emb : Fin n ↪ Fin r := ⟨Fin.castLE h, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩
  have hmp : MeasurePreserving (fun x : Fin r → ℝ × ℝ => fun i : Fin n => x (emb i))
      (unitSquarePi r) (unitSquarePi n) :=
    measurePreserving_pi_emb_gen (fun _ : Fin r => unitSquareMeasure) emb
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (finTourLen_continuous n).aestronglyMeasurable]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => finTourLen_nonneg _)
    (finTourLen_integrable r) (ae_of_all _ fun x => finTourLen_mono_castLE h x)

/-! ## Section 2: Elementary Poisson Probabilities, Chebyshev & Chernoff Tails -/

noncomputable def poissonProb (lam : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-lam) * lam ^ k / (k.factorial : ℝ)

lemma poissonProb_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) : 0 ≤ poissonProb lam k := by
  unfold poissonProb; positivity

lemma hasSum_poissonProb (lam : ℝ) : HasSum (poissonProb lam) 1 := by
  have hexp : HasSum (fun k : ℕ => lam ^ k / (k.factorial : ℝ)) (Real.exp lam) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [smul_eq_mul, div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp lam
  have h := hexp.mul_left (Real.exp (-lam))
  have h1 : Real.exp (-lam) * Real.exp lam = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [h1] at h
  exact h.congr_fun fun k => by unfold poissonProb; ring

lemma summable_poissonProb (lam : ℝ) : Summable (poissonProb lam) :=
  (hasSum_poissonProb lam).summable

lemma sum_poissonProb_le_one {lam : ℝ} (hlam : 0 ≤ lam) (s : Finset ℕ) :
    ∑ k ∈ s, poissonProb lam k ≤ 1 := by
  rw [← (hasSum_poissonProb lam).tsum_eq]
  exact (summable_poissonProb lam).sum_le_tsum s (fun k _ => poissonProb_nonneg hlam k)

lemma hasSum_mul_poissonProb (lam : ℝ) :
    HasSum (fun k : ℕ => (k : ℝ) * poissonProb lam k) lam := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  have h : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * poissonProb lam (k + 1)) =
      fun k : ℕ => lam * poissonProb lam k := by
    funext k
    unfold poissonProb
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hne : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    field_simp
  rw [h]
  simpa using (hasSum_poissonProb lam).mul_left lam

lemma hasSum_mul_pred_poissonProb (lam : ℝ) :
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * poissonProb lam k) (lam ^ 2) := by
  rw [← hasSum_nat_add_iff' 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, zero_mul,
    Nat.cast_one, sub_self, mul_zero, zero_add, sub_zero]
  have h : (fun k : ℕ => ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1) * poissonProb lam (k + 2)) =
      fun k : ℕ => lam ^ 2 * poissonProb lam k := by
    funext k
    unfold poissonProb
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul, pow_succ, pow_succ]
    have h1 : ((k + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsub : ((k + 2 : ℕ) : ℝ) - 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hsub]
    field_simp
  rw [h]
  simpa using (hasSum_poissonProb lam).mul_left (lam ^ 2)

lemma hasSum_sq_sub_poissonProb (lam : ℝ) :
    HasSum (fun k : ℕ => ((k : ℝ) - lam) ^ 2 * poissonProb lam k) lam := by
  have h1 := hasSum_mul_pred_poissonProb lam
  have h2 := (hasSum_mul_poissonProb lam).mul_left (1 - 2 * lam)
  have h3 := (hasSum_poissonProb lam).mul_left (lam ^ 2)
  have hcomb := (h1.add h2).add h3
  have hval : lam ^ 2 + (1 - 2 * lam) * lam + lam ^ 2 * 1 = lam := by ring
  rw [hval] at hcomb
  convert hcomb using 1
  funext k; ring

/-- Chebyshev bound for the Poisson distribution outside `[n, R]`. -/
lemma poisson_chebyshev {lam d : ℝ} (hlam : 0 ≤ lam) (hd : 0 < d) {n R : ℕ}
    (hn : (n : ℝ) ≤ lam - d) (hR : lam + d ≤ (R : ℝ)) :
    1 - ∑ k ∈ Finset.Icc n R, poissonProb lam k ≤ lam / d ^ 2 := by
  have hsq := hasSum_sq_sub_poissonProb lam
  have hle : ∀ k : ℕ, (if k ∈ Finset.Icc n R then (0 : ℝ) else d ^ 2 * poissonProb lam k) ≤
      ((k : ℝ) - lam) ^ 2 * poissonProb lam k := by
    intro k
    split_ifs with hk
    · exact mul_nonneg (sq_nonneg _) (poissonProb_nonneg hlam k)
    · refine mul_le_mul_of_nonneg_right ?_ (poissonProb_nonneg hlam k)
      simp only [Finset.mem_Icc, not_and_or, not_le] at hk
      rcases hk with hlt | hgt
      · have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hlt
        nlinarith
      · have hkR : (R : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_of_lt hgt
        nlinarith
  have hind_sum : HasSum (fun k : ℕ => if k ∈ Finset.Icc n R then (0 : ℝ) else poissonProb lam k)
      (1 - ∑ k ∈ Finset.Icc n R, poissonProb lam k) := by
    have hfin : HasSum (fun k : ℕ => if k ∈ Finset.Icc n R then poissonProb lam k else 0)
        (∑ k ∈ Finset.Icc n R, poissonProb lam k) := by
      have h0 : HasSum (fun k : ℕ => if k ∈ Finset.Icc n R then poissonProb lam k else 0)
          (∑ k ∈ Finset.Icc n R, (if k ∈ Finset.Icc n R then poissonProb lam k else 0)) :=
        hasSum_sum_of_ne_finset_zero (fun k hk => if_neg hk)
      have hsum_eq : ∑ k ∈ Finset.Icc n R, (if k ∈ Finset.Icc n R then poissonProb lam k else 0) =
          ∑ k ∈ Finset.Icc n R, poissonProb lam k :=
        Finset.sum_congr rfl fun k hk => if_pos hk
      rwa [hsum_eq] at h0
    have hdiff := (hasSum_poissonProb lam).sub hfin
    exact hdiff.congr_fun fun k => by split_ifs <;> ring
  have hmul := hind_sum.mul_left (d ^ 2)
  have hbound : d ^ 2 * (1 - ∑ k ∈ Finset.Icc n R, poissonProb lam k) ≤ lam := by
    have hmul' : HasSum (fun k : ℕ => if k ∈ Finset.Icc n R then (0 : ℝ) else d ^ 2 * poissonProb lam k)
        (d ^ 2 * (1 - ∑ k ∈ Finset.Icc n R, poissonProb lam k)) :=
      hmul.congr_fun fun k => by split_ifs <;> ring
    exact hasSum_le hle hmul' hsq
  rw [le_div_iff₀ (sq_pos_of_pos hd)]
  linarith

/-- Elementary inequality `e^t ≤ 1 + t + t^2` for `0 ≤ t ≤ 1/2`. -/
lemma exp_le_one_add_add_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp t ≤ 1 + t + t ^ 2 := by
  have he_lt4 : Real.exp 1 < 4 := by
    have hb := Real.exp_bound (x := (1 : ℝ)) (n := 2) (by norm_num) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, Nat.factorial_one, abs_one, one_pow, Nat.factorial_two,
      Nat.cast_ofNat, zero_add] at hb
    rw [abs_le] at hb
    linarith [hb.2]
  have hexp_le2 : ∀ x ∈ Icc (0 : ℝ) (1 / 2), Real.exp x ≤ 2 := by
    intro x hx
    have hsq : Real.exp x ^ 2 ≤ 4 := by
      rw [← Real.exp_nat_mul]
      calc Real.exp ((2 : ℕ) * x) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by push_cast; linarith [hx.2])
        _ ≤ 4 := le_of_lt he_lt4
    nlinarith [Real.exp_pos x]
  let g : ℝ → ℝ := fun x => 1 + 2 * x - Real.exp x
  have hg_mono : MonotoneOn g (Icc 0 (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
      (by unfold g; fun_prop) (by unfold g; fun_prop) ?_
    intro x hx
    have hderiv : HasDerivAt g (2 - Real.exp x) x := by
      have h1 : HasDerivAt (fun x : ℝ => (1 : ℝ) + 2 * x) 2 x := by
        simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).const_add (1 : ℝ)
      exact h1.sub (Real.hasDerivAt_exp x)
    rw [hderiv.deriv]
    have hx' : x ∈ Icc (0 : ℝ) (1 / 2) := interior_subset hx
    linarith [hexp_le2 x hx']
  let f : ℝ → ℝ := fun x => 1 + x + x ^ 2 - Real.exp x
  have hf_mono : MonotoneOn f (Icc 0 (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
      (by unfold f; fun_prop) (by unfold f; fun_prop) ?_
    intro x hx
    have hderiv : HasDerivAt f (1 + 2 * x - Real.exp x) x := by
      have h1 : HasDerivAt (fun x : ℝ => (1 : ℝ) + x + x ^ 2) (1 + 2 * x) x := by
        have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have hlin : HasDerivAt (fun x : ℝ => (1 : ℝ) + x) 1 x := (hasDerivAt_id x).const_add (1 : ℝ)
        exact hlin.add hp
      exact h1.sub (Real.hasDerivAt_exp x)
    rw [hderiv.deriv]
    have hx' : x ∈ Icc (0 : ℝ) (1 / 2) := interior_subset hx
    have h0 : g 0 ≤ g x := hg_mono ⟨le_rfl, by norm_num⟩ hx' hx'.1
    simpa [g] using h0
  have h0 : f 0 ≤ f t := hf_mono ⟨le_rfl, by norm_num⟩ ⟨ht0, ht1⟩ ht0
  simp only [f, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.exp_zero,
    sub_self] at h0
  linarith

/-- Chernoff upper tail for `Pois(μ)` on `[N₀, R]`. -/
lemma poisson_chernoff_upper {μ δ : ℝ} (hμ : 0 < μ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {N₀ R : ℕ} (hN : (1 + δ) * μ ≤ (N₀ : ℝ)) :
    ∑ k ∈ Finset.Icc N₀ R, poissonProb μ k ≤ Real.exp (-μ * δ ^ 2 / 4) := by
  let t : ℝ := δ / 2
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 2 := by dsimp only [t]; linarith
  have hstep1 : Real.exp (t * (N₀ : ℝ)) * ∑ k ∈ Finset.Icc N₀ R, poissonProb μ k ≤
      Real.exp (μ * (Real.exp t - 1)) := by
    rw [Finset.mul_sum]
    have hterm : ∀ k ∈ Finset.Icc N₀ R,
        Real.exp (t * (N₀ : ℝ)) * poissonProb μ k ≤
          Real.exp (μ * (Real.exp t - 1)) * poissonProb (μ * Real.exp t) k := by
      intro k hk
      have hkN : (N₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hexp_le : Real.exp (t * (N₀ : ℝ)) ≤ Real.exp (t * (k : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkN ht0)
      have hpow : Real.exp (t * (k : ℝ)) = Real.exp t ^ k := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      have hrhs : Real.exp (μ * (Real.exp t - 1)) * poissonProb (μ * Real.exp t) k =
          Real.exp t ^ k * poissonProb μ k := by
        unfold poissonProb
        rw [mul_pow]
        have hcomb : Real.exp (μ * (Real.exp t - 1)) * Real.exp (-(μ * Real.exp t)) = Real.exp (-μ) := by
          rw [← Real.exp_add]; congr 1; ring
        calc Real.exp (μ * (Real.exp t - 1)) * (Real.exp (-(μ * Real.exp t)) * (μ ^ k * Real.exp t ^ k) / (k.factorial : ℝ))
            = (Real.exp (μ * (Real.exp t - 1)) * Real.exp (-(μ * Real.exp t))) * (μ ^ k * Real.exp t ^ k) / (k.factorial : ℝ) := by ring
          _ = Real.exp (-μ) * (μ ^ k * Real.exp t ^ k) / (k.factorial : ℝ) := by rw [hcomb]
          _ = Real.exp t ^ k * (Real.exp (-μ) * μ ^ k / (k.factorial : ℝ)) := by ring
      rw [hrhs, ← hpow]
      exact mul_le_mul_of_nonneg_right hexp_le (poissonProb_nonneg (le_of_lt hμ) k)
    calc ∑ k ∈ Finset.Icc N₀ R, Real.exp (t * (N₀ : ℝ)) * poissonProb μ k
        ≤ ∑ k ∈ Finset.Icc N₀ R, Real.exp (μ * (Real.exp t - 1)) * poissonProb (μ * Real.exp t) k :=
          Finset.sum_le_sum hterm
      _ = Real.exp (μ * (Real.exp t - 1)) * ∑ k ∈ Finset.Icc N₀ R, poissonProb (μ * Real.exp t) k := by
          rw [← Finset.mul_sum]
      _ ≤ Real.exp (μ * (Real.exp t - 1)) * 1 :=
          mul_le_mul_of_nonneg_left (sum_poissonProb_le_one (by positivity) _) (le_of_lt (Real.exp_pos _))
      _ = Real.exp (μ * (Real.exp t - 1)) := mul_one _
  have hdiv : ∑ k ∈ Finset.Icc N₀ R, poissonProb μ k ≤ Real.exp (μ * (Real.exp t - 1) - t * (N₀ : ℝ)) := by
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
    linarith
  refine hdiv.trans (Real.exp_le_exp.mpr ?_)
  have hexp_t : Real.exp t - 1 ≤ t + t ^ 2 := by linarith [exp_le_one_add_add_sq ht0 ht1]
  have h1 : μ * (Real.exp t - 1) ≤ μ * (t + t ^ 2) := mul_le_mul_of_nonneg_left hexp_t (le_of_lt hμ)
  have h2 : t * ((1 + δ) * μ) ≤ t * (N₀ : ℝ) := mul_le_mul_of_nonneg_left hN ht0
  dsimp only [t] at h1 h2 ⊢
  nlinarith

/-! ## Section 3: 1D Renewal Order Statistics & `k!`-Simplex Symmetry -/

/-- Ordered simplex `0 < t 0 < t 1 < ... < t (k-1) ≤ 1`. -/
def orderedSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {t | (∀ i, 0 < t i ∧ t i ≤ 1) ∧ StrictMono t}

/-- Gap simplex `e i > 0` and `∑ e i ≤ μ`. -/
def gapSimplex (k : ℕ) (μ : ℝ) : Set (Fin k → ℝ) :=
  {e | (∀ i, 0 < e i) ∧ ∑ i, e i ≤ μ}

/-- Partial sums divided by `μ`. -/
noncomputable def partialSumsDiv (k : ℕ) (μ : ℝ) (e : Fin k → ℝ) : Fin k → ℝ :=
  fun i => (∑ j : Fin k, if j ≤ i then e j else 0) / μ

lemma measurableSet_orderedSimplex (k : ℕ) : MeasurableSet (orderedSimplex k) := by
  have heq : orderedSimplex k =
      (⋂ i : Fin k, {t : Fin k → ℝ | 0 < t i ∧ t i ≤ 1}) ∩
      (⋂ p : {p : Fin k × Fin k // p.1 < p.2}, {t : Fin k → ℝ | t p.1.1 < t p.1.2}) := by
    ext t; simp [orderedSimplex, StrictMono]
  rw [heq]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_le (measurable_pi_apply i) measurable_const)
  · exact MeasurableSet.iInter fun p =>
      measurableSet_lt (measurable_pi_apply p.1.1) (measurable_pi_apply p.1.2)

lemma measurableSet_gapSimplex (k : ℕ) (μ : ℝ) : MeasurableSet (gapSimplex k μ) := by
  have heq : gapSimplex k μ =
      (⋂ i : Fin k, {e : Fin k → ℝ | 0 < e i}) ∩ {e : Fin k → ℝ | ∑ i : Fin k, e i ≤ μ} := by
    ext e; simp [gapSimplex]
  rw [heq]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)) ?_
  exact measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const

lemma measurable_partialSumsDiv (k : ℕ) (μ : ℝ) : Measurable (partialSumsDiv k μ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Measurable.div_const ?_ μ
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases h : j ≤ i
  · simp [h]; exact measurable_pi_apply j
  · simp [h]

/-- 1D scaling of Lebesgue `lintegral` on `ℝ` by `a > 0`. -/
lemma lintegral_comp_mul_left_pos {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x : ℝ, f (a * x) = ENNReal.ofReal a⁻¹ * ∫⁻ y : ℝ, f y := by
  have hmap : (volume : Measure ℝ).map (fun x : ℝ => a * x) = ENNReal.ofReal a⁻¹ • (volume : Measure ℝ) := by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul a) hs, Measure.smul_apply, smul_eq_mul]
    rw [Real.volume_preimage_mul_left (ne_of_gt ha) s, abs_of_pos (inv_pos.mpr ha)]
  rw [← lintegral_map hf (measurable_const_mul a), hmap, lintegral_smul_measure, smul_eq_mul]

/-- 1D change of variables `u = (S + e) / μ` on `Ioc 0 (μ - S)`. -/
lemma lintegral_Ioc_shift_div {μ S : ℝ} (hμ : 0 < μ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ e in Ioc (0 : ℝ) (μ - S), g ((S + e) / μ) =
      ENNReal.ofReal μ * ∫⁻ u in Ioc (S / μ) 1, g u := by
  have h1 : ∀ u : ℝ, (S + (μ * u - S)) / μ = u := fun u => by field_simp; ring
  have hmap : ∫⁻ u in Ioc (S / μ) 1, g u =
      ∫⁻ x, (Ioc (S / μ) 1).indicator g x := (lintegral_indicator measurableSet_Ioc g).symm
  have hmap2 : ∫⁻ e in Ioc (0 : ℝ) (μ - S), g ((S + e) / μ) =
      ∫⁻ e, (Ioc (0 : ℝ) (μ - S)).indicator (fun e => g ((S + e) / μ)) e :=
    (lintegral_indicator measurableSet_Ioc _).symm
  rw [hmap, hmap2]
  have hf_meas : Measurable (fun y : ℝ =>
      (Ioc (0 : ℝ) (μ - S)).indicator (fun e => g ((S + e) / μ)) (y - S)) :=
    ((hg.comp (by fun_prop)).indicator measurableSet_Ioc).comp (measurable_id.sub_const S)
  have hadd := lintegral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun e : ℝ =>
    (Ioc (0 : ℝ) (μ - S)).indicator (fun e => g ((S + e) / μ)) e) (-S)
  have hcomb : ∫⁻ e, (Ioc (0 : ℝ) (μ - S)).indicator (fun e => g ((S + e) / μ)) e =
      ENNReal.ofReal μ * ∫⁻ u, (Ioc (0 : ℝ) (μ - S)).indicator (fun e => g ((S + e) / μ)) (μ * u - S) := by
    rw [← hadd]
    have hsub : (fun y : ℝ => (Ioc (0 : ℝ) (μ - S)).indicator (fun e => g ((S + e) / μ)) (y + -S)) =
        fun y => (Ioc (0 : ℝ) (μ - S)).indicator (fun e => g ((S + e) / μ)) (y - S) := by
      funext y; simp [sub_eq_add_neg]
    rw [hsub]
    have hmul := lintegral_comp_mul_left_pos hμ _ hf_meas
    rw [hmul, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hμ),
      mul_inv_cancel₀ (ne_of_gt hμ), ENNReal.ofReal_one, one_mul]
  rw [hcomb]
  congr 1
  apply lintegral_congr
  intro u
  have hiff : μ * u - S ∈ Ioc (0 : ℝ) (μ - S) ↔ u ∈ Ioc (S / μ) 1 := by
    simp only [Set.mem_Ioc, div_lt_iff₀ hμ]
    constructor <;> intro ⟨ha, hb⟩ <;> constructor <;> nlinarith
  by_cases hu : u ∈ Ioc (S / μ) 1
  · rw [Set.indicator_of_mem (hiff.mpr hu), Set.indicator_of_mem hu, h1 u]
  · rw [Set.indicator_of_notMem (mt hiff.mp hu), Set.indicator_of_notMem hu]

private lemma splitLast_last {k : ℕ} (x : ℝ) (v : Fin k → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm (x, v) (Fin.last k) = x := by
  simp

private lemma splitLast_castSucc {k : ℕ} (x : ℝ) (v : Fin k → ℝ) (i : Fin k) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm (x, v) i.castSucc = v i := by
  have hcast : i.castSucc = (Fin.last k).succAbove i := (congrFun Fin.succAbove_last i).symm
  rw [hcast]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

/-- Inductive Jacobian formula for partial sums of positive gaps:
`∫⁻_{e > 0, ∑ e ≤ μ} f(partialSumsDiv e) = μ^k * ∫⁻_{0 < t_0 < ... < t_{k-1} ≤ 1} f(t)`. -/
lemma lintegral_gapSimplex_eq_orderedSimplex :
    ∀ (k : ℕ) {μ : ℝ} (_ : 0 < μ) (f : (Fin k → ℝ) → ℝ≥0∞), Measurable f →
      ∫⁻ e in gapSimplex k μ, f (partialSumsDiv k μ e) =
        ENNReal.ofReal (μ ^ k) * ∫⁻ t in orderedSimplex k, f t
  | 0, μ, hμ, f, _ => by
    have hgap : gapSimplex 0 μ = Set.univ := by
      ext e; simp [gapSimplex, le_of_lt hμ]
    have hord : orderedSimplex 0 = Set.univ := by
      ext t; simp [orderedSimplex, StrictMono]
    rw [hgap, hord, pow_zero, ENNReal.ofReal_one, one_mul]
    simp only [Measure.restrict_univ]
    have huniq : ∀ e : Fin 0 → ℝ, partialSumsDiv 0 μ e = e := fun e => by funext i; exact Fin.elim0 i
    simp_rw [huniq]
  | k + 1, μ, hμ, f, hf => by
    -- Split off the last coordinate `Fin.last k` via `volume_preserving_piFinSuccAbove`
    have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
    let splitEquiv : (Fin (k + 1) → ℝ) ≃ᵐ ℝ × (Fin k → ℝ) :=
      MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last k)
    -- Rewrite LHS as integral over `(e_last, e') : ℝ × (Fin k → ℝ)`
    have hlhs : ∫⁻ e in gapSimplex (k + 1) μ, f (partialSumsDiv (k + 1) μ e) =
        ∫⁻ e' : Fin k → ℝ, ∫⁻ e_last : ℝ,
          (gapSimplex (k + 1) μ).indicator (fun e => f (partialSumsDiv (k + 1) μ e))
            (splitEquiv.symm (e_last, e')) := by
      rw [← lintegral_indicator (measurableSet_gapSimplex (k + 1) μ)]
      have hmeas_ind : Measurable ((gapSimplex (k + 1) μ).indicator
          (fun e => f (partialSumsDiv (k + 1) μ e))) :=
        (hf.comp (measurable_partialSumsDiv (k + 1) μ)).indicator (measurableSet_gapSimplex (k + 1) μ)
      rw [← hmp.symm.lintegral_comp hmeas_ind]
      rw [Measure.volume_eq_prod, MeasureTheory.lintegral_prod_symm]
      exact (hmeas_ind.comp splitEquiv.symm.measurable).aemeasurable
    -- Rewrite RHS similarly
    have hrhs : ∫⁻ t in orderedSimplex (k + 1), f t =
        ∫⁻ t' : Fin k → ℝ, ∫⁻ t_last : ℝ,
          (orderedSimplex (k + 1)).indicator f (splitEquiv.symm (t_last, t')) := by
      rw [← lintegral_indicator (measurableSet_orderedSimplex (k + 1))]
      have hmeas_ind : Measurable ((orderedSimplex (k + 1)).indicator f) :=
        hf.indicator (measurableSet_orderedSimplex (k + 1))
      rw [← hmp.symm.lintegral_comp hmeas_ind]
      rw [Measure.volume_eq_prod, MeasureTheory.lintegral_prod_symm]
      exact (hmeas_ind.comp splitEquiv.symm.measurable).aemeasurable
    rw [hlhs, hrhs]
    -- Helper: how `partialSumsDiv (k + 1)` acts on `splitEquiv.symm (e_last, e')`
    have hps_snoc : ∀ (e_last : ℝ) (e' : Fin k → ℝ),
        partialSumsDiv (k + 1) μ (splitEquiv.symm (e_last, e')) =
          splitEquiv.symm (((∑ i : Fin k, e' i) + e_last) / μ, partialSumsDiv k μ e') := by
      intro e_last e'
      funext i
      dsimp only [splitEquiv]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [splitLast_last]
        simp only [partialSumsDiv, Fin.le_last, ↓reduceIte, Fin.sum_univ_castSucc,
          splitLast_castSucc, splitLast_last]
      · rw [splitLast_castSucc]
        simp only [partialSumsDiv, Fin.sum_univ_castSucc, splitLast_castSucc]
        have hnot : ¬(Fin.last k ≤ j.castSucc) := not_le.mpr j.castSucc_lt_last
        simp only [hnot, ↓reduceIte, add_zero, Fin.castSucc_le_castSucc_iff]
    -- Simplify the inner integral over `e_last` for each `e' : Fin k → ℝ`
    have hinner : ∀ e' : Fin k → ℝ,
        ∫⁻ e_last : ℝ,
          (gapSimplex (k + 1) μ).indicator (fun e => f (partialSumsDiv (k + 1) μ e))
            (splitEquiv.symm (e_last, e')) =
        ENNReal.ofReal μ *
          (gapSimplex k μ).indicator (fun e' =>
            ∫⁻ t_last : ℝ,
              (orderedSimplex (k + 1)).indicator f
                (splitEquiv.symm (t_last, partialSumsDiv k μ e'))) e' := by
      intro e'
      by_cases he' : e' ∈ gapSimplex k μ
      · rw [Set.indicator_of_mem he']
        have hmem_iff : ∀ e_last : ℝ,
            splitEquiv.symm (e_last, e') ∈ gapSimplex (k + 1) μ ↔
              e_last ∈ Ioc (0 : ℝ) (μ - ∑ i : Fin k, e' i) := by
          intro e_last
          dsimp only [splitEquiv]
          simp only [gapSimplex, Set.mem_setOf_eq, Set.mem_Ioc, Fin.forall_fin_succ',
            Fin.sum_univ_castSucc, splitLast_castSucc, splitLast_last]
          constructor
          · rintro ⟨⟨_, hpos⟩, hsum⟩; exact ⟨hpos, by linarith⟩
          · rintro ⟨hpos, hle⟩; exact ⟨⟨he'.1, hpos⟩, by linarith⟩
        have hcongr1 : ∀ e_last : ℝ,
            (gapSimplex (k + 1) μ).indicator (fun e => f (partialSumsDiv (k + 1) μ e))
              (splitEquiv.symm (e_last, e')) =
            (Ioc (0 : ℝ) (μ - ∑ i : Fin k, e' i)).indicator
              (fun e_last => f (splitEquiv.symm (((∑ i : Fin k, e' i) + e_last) / μ, partialSumsDiv k μ e'))) e_last := by
          intro e_last
          by_cases h : e_last ∈ Ioc (0 : ℝ) (μ - ∑ i : Fin k, e' i)
          · rw [Set.indicator_of_mem ((hmem_iff e_last).mpr h), Set.indicator_of_mem h, hps_snoc]
          · rw [Set.indicator_of_notMem (mt (hmem_iff e_last).mp h), Set.indicator_of_notMem h]
        simp_rw [hcongr1]
        rw [lintegral_indicator measurableSet_Ioc,
            lintegral_Ioc_shift_div hμ (fun u => f (splitEquiv.symm (u, partialSumsDiv k μ e')))
              (hf.comp (splitEquiv.symm.measurable.comp (measurable_id.prodMk measurable_const)))]
        congr 1
        rw [← lintegral_indicator measurableSet_Ioc]
        apply lintegral_congr
        intro t_last
        have hord_e' : partialSumsDiv k μ e' ∈ orderedSimplex k := by
          refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
          · unfold partialSumsDiv
            refine div_pos ?_ hμ
            have hle : e' i ≤ ∑ j : Fin k, if j ≤ i then e' j else 0 := by
              have h1 := Finset.single_le_sum (f := fun j : Fin k => if j ≤ i then e' j else 0)
                (fun j _ => by split_ifs <;> linarith [he'.1 j]) (Finset.mem_univ i)
              simpa using h1
            linarith [he'.1 i]
          · unfold partialSumsDiv
            rw [div_le_one hμ]
            calc ∑ j : Fin k, (if j ≤ i then e' j else 0)
                ≤ ∑ j : Fin k, e' j := Finset.sum_le_sum fun j _ => by split_ifs <;> linarith [he'.1 j]
              _ ≤ μ := he'.2
          · unfold partialSumsDiv
            refine div_lt_div_of_pos_right ?_ hμ
            refine Finset.sum_lt_sum (fun m _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
            · split_ifs with h1 h2
              · exact le_rfl
              · exact absurd (le_trans h1 (le_of_lt hij)) h2
              · exact le_of_lt (he'.1 m)
              · exact le_rfl
            · have hnot : ¬(j ≤ i) := not_le.mpr hij
              simp [hnot, he'.1 j]
        have hord_iff : splitEquiv.symm (t_last, partialSumsDiv k μ e') ∈ orderedSimplex (k + 1) ↔
            t_last ∈ Ioc ((∑ i : Fin k, e' i) / μ) 1 := by
          simp only [orderedSimplex, Set.mem_setOf_eq, Set.mem_Ioc]
          constructor
          · rintro ⟨hbnd, hsm⟩
            have hle1 : t_last ≤ 1 := by
              have h := (hbnd (Fin.last k)).2
              rwa [splitLast_last] at h
            cases k with
            | zero =>
              have hpos : 0 < t_last := by
                have h := (hbnd (Fin.last 0)).1
                rwa [splitLast_last] at h
              simpa using ⟨hpos, hle1⟩
            | succ k' =>
              have hlt := hsm (Fin.castSucc_lt_last (Fin.last k'))
              rw [splitLast_castSucc, splitLast_last] at hlt
              have hsum_eq : partialSumsDiv (k' + 1) μ e' (Fin.last k') = (∑ i : Fin (k' + 1), e' i) / μ := by
                simp [partialSumsDiv, Fin.le_last]
              rw [hsum_eq] at hlt
              exact ⟨hlt, hle1⟩
          · rintro ⟨hgt, hle1⟩
            have hpos_sum : 0 ≤ (∑ i : Fin k, e' i) / μ :=
              div_nonneg (Finset.sum_nonneg fun i _ => le_of_lt (he'.1 i)) (le_of_lt hμ)
            refine ⟨fun i => Fin.lastCases (by rw [splitLast_last]; exact ⟨lt_of_le_of_lt hpos_sum hgt, hle1⟩)
              (fun j => by rw [splitLast_castSucc]; exact hord_e'.1 j) i, ?_⟩
            intro a b
            refine Fin.lastCases (fun hab => absurd hab (not_lt.mpr (Fin.le_last b))) (fun a' => ?_) a
            refine Fin.lastCases (fun _ => ?_) (fun b' hab => ?_) b
            · rw [splitLast_castSucc, splitLast_last]
              refine lt_of_le_of_lt ?_ hgt
              unfold partialSumsDiv
              refine div_le_div_of_nonneg_right ?_ (le_of_lt hμ)
              exact Finset.sum_le_sum fun j _ => by split_ifs <;> linarith [he'.1 j]
            · rw [splitLast_castSucc, splitLast_castSucc]
              exact hord_e'.2 (Fin.castSucc_lt_castSucc_iff.mp hab)
        by_cases ht : t_last ∈ Ioc ((∑ i : Fin k, e' i) / μ) 1
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hord_iff.mpr ht)]
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (mt hord_iff.mp ht)]
      · rw [Set.indicator_of_notMem he', mul_zero]
        have hzero : ∀ e_last : ℝ, splitEquiv.symm (e_last, e') ∉ gapSimplex (k + 1) μ := by
          intro e_last hmem
          apply he'
          dsimp only [splitEquiv] at hmem
          refine ⟨fun i => by have := hmem.1 i.castSucc; rwa [splitLast_castSucc] at this, ?_⟩
          have hsum := hmem.2
          rw [Fin.sum_univ_castSucc] at hsum
          simp_rw [splitLast_castSucc, splitLast_last] at hsum
          have hlast_pos : 0 < e_last := by
            have := hmem.1 (Fin.last k)
            rwa [splitLast_last] at this
          linarith
        simp [Set.indicator_of_notMem (hzero _)]
    simp_rw [hinner]
    rw [lintegral_const_mul _]
    · let g : (Fin k → ℝ) → ℝ≥0∞ := fun t' =>
        ∫⁻ t_last : ℝ, (orderedSimplex (k + 1)).indicator f (splitEquiv.symm (t_last, t'))
      have hg_meas : Measurable g := by
        refine Measurable.lintegral_prod_left ?_
        exact ((hf.indicator (measurableSet_orderedSimplex (k + 1))).comp splitEquiv.symm.measurable)
      rw [lintegral_indicator (measurableSet_gapSimplex k μ)]
      have hih := lintegral_gapSimplex_eq_orderedSimplex k hμ g hg_meas
      rw [hih, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hμ), ← pow_succ']
      congr 1
      rw [← lintegral_indicator (measurableSet_orderedSimplex k)]
      apply lintegral_congr
      intro t'
      by_cases ht' : t' ∈ orderedSimplex k
      · rw [Set.indicator_of_mem ht']
      · rw [Set.indicator_of_notMem ht']
        symm
        have hzero : ∀ t_last : ℝ, splitEquiv.symm (t_last, t') ∉ orderedSimplex (k + 1) := by
          intro t_last hmem
          apply ht'
          exact ⟨fun i => by have := hmem.1 i.castSucc; rwa [splitLast_castSucc] at this,
            fun i j hij => by
              have h := hmem.2 (show i.castSucc < j.castSucc by exact_mod_cast hij)
              rwa [splitLast_castSucc, splitLast_castSucc] at h⟩
        simp [Set.indicator_of_notMem (hzero _)]
    · refine Measurable.indicator ?_ (measurableSet_gapSimplex k μ)
      have hg_meas : Measurable (fun t' : Fin k → ℝ =>
          ∫⁻ t_last : ℝ, (orderedSimplex (k + 1)).indicator f (splitEquiv.symm (t_last, t'))) :=
        Measurable.lintegral_prod_left
          ((hf.indicator (measurableSet_orderedSimplex (k + 1))).comp splitEquiv.symm.measurable)
      exact hg_meas.comp (measurable_partialSumsDiv k μ)

/-- The set of points in `Fin k → ℝ` with two equal coordinates has Lebesgue measure `0`. -/
lemma volume_not_injective_eq_zero : ∀ (k : ℕ),
    volume {t : Fin k → ℝ | ¬Function.Injective t} = 0
  | 0 => by
    have hempty : {t : Fin 0 → ℝ | ¬Function.Injective t} = ∅ := by
      ext t; simp [Function.Injective]
    rw [hempty, measure_empty]
  | k' + 1 => by
    have hsub : {t : Fin (k' + 1) → ℝ | ¬Function.Injective t} ⊆
        ⋃ p : {p : Fin (k' + 1) × Fin (k' + 1) // p.1 ≠ p.2},
          {t : Fin (k' + 1) → ℝ | t p.1.1 = t p.1.2} := by
      intro t ht
      simp only [Function.Injective, not_forall] at ht
      obtain ⟨i, j, hij, hne⟩ := ht
      exact Set.mem_iUnion.mpr ⟨⟨(i, j), hne⟩, hij⟩
    refine measure_mono_null hsub (measure_iUnion_null fun ⟨⟨i, j⟩, hne⟩ => ?_)
    have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (k' + 1) => ℝ) i
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k' + 1) => ℝ) i
    have hmeas_eq : MeasurableSet {t : Fin (k' + 1) → ℝ | t i = t j} :=
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
    rw [← lintegral_indicator_one hmeas_eq]
    change ∫⁻ a : Fin (k' + 1) → ℝ, {t | t i = t j}.indicator (fun _ => (1 : ℝ≥0∞)) a = 0
    rw [← hmp.symm.lintegral_comp (measurable_const.indicator hmeas_eq)]
    have hm_ind : Measurable (fun a : ℝ × (Fin k' → ℝ) =>
        {t : Fin (k' + 1) → ℝ | t i = t j}.indicator (fun _ => (1 : ℝ≥0∞)) (e.symm a)) :=
      (measurable_const.indicator hmeas_eq).comp e.symm.measurable
    rw [Measure.volume_eq_prod, MeasureTheory.lintegral_prod_symm
      (f := fun a : ℝ × (Fin k' → ℝ) => {t | t i = t j}.indicator (fun _ => (1 : ℝ≥0∞)) (e.symm a))
      hm_ind.aemeasurable]
    obtain ⟨j', hj'⟩ : ∃ j' : Fin k', i.succAbove j' = j := Fin.exists_succAbove_eq hne.symm
    have hinner : ∀ y : Fin k' → ℝ,
        ∫⁻ x : ℝ, {t : Fin (k' + 1) → ℝ | t i = t j}.indicator (fun _ => (1 : ℝ≥0∞)) (e.symm (x, y)) = 0 := by
      intro y
      have hset : (fun x : ℝ => {t : Fin (k' + 1) → ℝ | t i = t j}.indicator
            (fun _ => (1 : ℝ≥0∞)) (e.symm (x, y))) = ({y j'} : Set ℝ).indicator 1 := by
        funext x
        have hmem : e.symm (x, y) ∈ {t : Fin (k' + 1) → ℝ | t i = t j} ↔ x = y j' := by
          simp only [Set.mem_setOf_eq, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same, ← hj',
            Fin.insertNth_apply_succAbove]
        by_cases hx : x = y j'
        · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem (Set.mem_singleton_iff.mpr hx)]; rfl
        · rw [Set.indicator_of_notMem (mt hmem.mp hx), Set.indicator_of_notMem (mt Set.mem_singleton_iff.mp hx)]
      rw [hset, lintegral_indicator_one (measurableSet_singleton _), Real.volume_singleton]
    simp [hinner]

/-- `k!`-simplex permutation symmetry for Lebesgue `lintegral` on `(0, 1]^k`. -/
lemma lintegral_orderedSimplex_mul_factorial (k : ℕ) (f : (Fin k → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hsym : ∀ σ : Equiv.Perm (Fin k), ∀ t, f (t ∘ σ) = f t) :
    (k.factorial : ℝ≥0∞) * ∫⁻ t in orderedSimplex k, f t =
      ∫⁻ t in Set.pi Set.univ (fun _ : Fin k => Ioc (0 : ℝ) 1), f t := by
  let S (σ : Equiv.Perm (Fin k)) : Set (Fin k → ℝ) :=
    {t | (∀ i, 0 < t i ∧ t i ≤ 1) ∧ StrictMono (t ∘ σ)}
  have hS_meas : ∀ σ, MeasurableSet (S σ) := fun σ => by
    have hpre : S σ = (fun t : Fin k → ℝ => t ∘ σ) ⁻¹' orderedSimplex k := by
      ext t
      simp only [S, orderedSimplex, Set.mem_preimage, Set.mem_setOf_eq, Function.comp]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun i => h1 (σ i), h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun i => by simpa using h1 (σ⁻¹ i), h2⟩
    rw [hpre]
    exact (measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)) (measurableSet_orderedSimplex k)
  have hS_disj : Pairwise (Function.onFun Disjoint S) := by
    intro σ₁ σ₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro t ht1 ht2
    apply hne
    have hbij : ∀ i : Fin k, σ₁ i = σ₂ i := by
      -- Two strictly monotone functions with the same finite range are equal
      have heq_fn : t ∘ σ₁ = t ∘ σ₂ := by
        have hrange : Set.range (t ∘ σ₁) = Set.range (t ∘ σ₂) := by
          ext y; simp only [Set.mem_range, Function.comp]
          constructor
          · rintro ⟨i, rfl⟩; exact ⟨σ₂⁻¹ (σ₁ i), by simp⟩
          · rintro ⟨i, rfl⟩; exact ⟨σ₁⁻¹ (σ₂ i), by simp⟩
        -- Standard order-isomorphism uniqueness on `Fin k`
        let e1 : Fin k ≃o Set.range (t ∘ σ₁) :=
          StrictMono.orderIsoOfSurjective (fun i => ⟨(t ∘ σ₁) i, ⟨i, rfl⟩⟩)
            (fun a b hab => ht1.2 hab) (fun ⟨y, i, hi⟩ => ⟨i, Subtype.ext hi⟩)
        let e2 : Fin k ≃o Set.range (t ∘ σ₁) :=
          StrictMono.orderIsoOfSurjective (fun i => ⟨(t ∘ σ₂) i, hrange.symm ▸ ⟨i, rfl⟩⟩)
            (fun a b hab => ht2.2 hab) (fun ⟨y, hy⟩ => by
              rw [hrange] at hy; obtain ⟨i, hi⟩ := hy; exact ⟨i, Subtype.ext hi⟩)
        have hcomp : e1.trans e2.symm = OrderIso.refl (Fin k) := Subsingleton.elim _ _
        funext i
        have hi := congrArg (fun e : Fin k ≃o Fin k => e2 (e i)) hcomp
        simpa [e1, e2] using hi
      have hinj : Function.Injective t := by
        intro a b hab
        have h1 := ht1.2.injective (show (t ∘ σ₁) (σ₁⁻¹ a) = (t ∘ σ₁) (σ₁⁻¹ b) by simpa using hab)
        simpa using congrArg σ₁ h1
      intro i
      exact hinj (congrFun heq_fn i)
    exact Equiv.ext hbij
  have hS_int : ∀ σ : Equiv.Perm (Fin k), ∫⁻ t in S σ, f t = ∫⁻ t in orderedSimplex k, f t := by
    intro σ
    have hmp : MeasurePreserving (fun t : Fin k → ℝ => t ∘ σ) volume volume := by
      have : (volume : Measure (Fin k → ℝ)) = Measure.pi fun _ : Fin k => (volume : Measure ℝ) := rfl
      rw [this]
      exact measurePreserving_pi_equiv σ (fun _ : Fin k => (volume : Measure ℝ))
    have hpre : S σ = (fun t : Fin k → ℝ => t ∘ σ) ⁻¹' orderedSimplex k := by
      ext t
      simp only [S, orderedSimplex, Set.mem_preimage, Set.mem_setOf_eq, Function.comp]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun i => h1 (σ i), h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun i => by simpa using h1 (σ⁻¹ i), h2⟩
    rw [hpre, ← lintegral_indicator (measurableSet_orderedSimplex k),
        ← lintegral_indicator (hpre ▸ hS_meas σ)]
    have hfun : ((fun t : Fin k → ℝ => t ∘ σ) ⁻¹' orderedSimplex k).indicator f =
        fun t => (orderedSimplex k).indicator f (t ∘ σ) := by
      funext t
      by_cases ht : t ∘ σ ∈ orderedSimplex k
      · have ht' : t ∈ (fun t : Fin k → ℝ => t ∘ σ) ⁻¹' orderedSimplex k := ht
        rw [Set.indicator_of_mem ht', Set.indicator_of_mem ht, hsym σ t]
      · rw [Set.indicator_of_notMem (show t ∉ (fun t : Fin k → ℝ => t ∘ σ) ⁻¹' orderedSimplex k from ht),
            Set.indicator_of_notMem ht]
    rw [hfun]
    exact hmp.lintegral_comp (hf.indicator (measurableSet_orderedSimplex k))
  -- Show `⋃ σ, S σ` agrees a.e. with `(0, 1]^k`
  let box : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k => Ioc (0 : ℝ) 1)
  have hunion_sub : (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))), S σ) ⊆ box := by
    intro t ht
    simp only [Set.mem_iUnion, Finset.mem_univ] at ht
    obtain ⟨σ, _, hσ⟩ := ht
    intro i _; exact hσ.1 i
  have hdiff_null : volume (box \ ⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))), S σ) = 0 := by
    refine measure_mono_null (fun t ht => ?_) (volume_not_injective_eq_zero k)
    intro hinj
    apply ht.2
    refine Set.mem_iUnion₂.mpr ⟨Tuple.sort t, Finset.mem_univ _, ?_⟩
    exact ⟨fun i => ht.1 i (Set.mem_univ i), (Tuple.monotone_sort t).strictMono_of_injective (hinj.comp (Tuple.sort t).injective)⟩
  have hae : (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))), S σ) =ᵐ[volume] box :=
    Filter.EventuallyEq.symm (ae_eq_set.mpr ⟨hdiff_null,
      measure_mono_null (Set.sdiff_eq_empty.mpr hunion_sub).subset (by simp)⟩)
  rw [← setLIntegral_congr hae, lintegral_biUnion_finset (fun σ₁ _ σ₂ _ hne => hS_disj hne) (fun σ _ => hS_meas σ)]
  simp_rw [hS_int]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-! ## Section 4: Single-Strip Renewal Identity -/

/-- Rescaled point `i` in strip `s : Fin M` of `[0, 1]²`. -/
noncomputable def stripUnitPt (M : ℕ) (s : Fin M) {m : ℕ}
    (E : Fin (7 + m) → ℝ) (Y : Fin (8 + m) → ℝ) (i : ℕ) : ℝ × ℝ :=
  ((stripPt E Y i).1 / ((M : ℝ) * (11 / 5 : ℝ)),
   ((s.val : ℝ) + (stripPt E Y i).2 / (11 / 5 : ℝ)) / (M : ℝ))

lemma ptDist_stripUnitPt {M : ℕ} (hM : 0 < M) (s : Fin M) {m : ℕ}
    (E : Fin (7 + m) → ℝ) (Y : Fin (8 + m) → ℝ) (a b : ℕ) :
    ptDist (stripUnitPt M s E Y a) (stripUnitPt M s E Y b) =
      ptDist (stripPt E Y a) (stripPt E Y b) / ((M : ℝ) * (11 / 5 : ℝ)) := by
  have hpos : (0 : ℝ) < (M : ℝ) * (11 / 5 : ℝ) := by positivity
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let c : ℝ := ((M : ℝ) * (11 / 5 : ℝ))⁻¹
  let t : ℝ × ℝ := (0, (s.val : ℝ) / (M : ℝ))
  let pa : ℝ × ℝ := (c * (stripPt E Y a).1, c * (stripPt E Y a).2)
  let pb : ℝ × ℝ := (c * (stripPt E Y b).1, c * (stripPt E Y b).2)
  have h1 : stripUnitPt M s E Y a = (pa.1 + t.1, pa.2 + t.2) := by
    unfold stripUnitPt; dsimp only [pa, t, c]; apply Prod.ext <;> (field_simp; ring)
  have h2 : stripUnitPt M s E Y b = (pb.1 + t.1, pb.2 + t.2) := by
    unfold stripUnitPt; dsimp only [pa, pb, t, c]; apply Prod.ext <;> (field_simp; ring)
  rw [h1, h2, ptDist_translate t pa pb]
  dsimp only [pa, pb]
  rw [ptDist_scale (by positivity : 0 ≤ c)]
  dsimp only [c]; rw [inv_mul_eq_div]

/-- Lebesgue measure restricted to strip `s`: `(0, 1] × (s/M, (s+1)/M]`. -/
noncomputable def stripBoxMeasure (M : ℕ) (s : Fin M) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) 1)).prod
    (volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))))

instance isFiniteMeasure_stripBoxMeasure (M : ℕ) (s : Fin M) :
    IsFiniteMeasure (stripBoxMeasure M s) := by
  unfold stripBoxMeasure
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor; simp [Real.volume_Ioc]
  haveI : IsFiniteMeasure (volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
    constructor; simp [Real.volume_Ioc]
  infer_instance

lemma stripBoxMeasure_univ {M : ℕ} (hM : 0 < M) (s : Fin M) :
    stripBoxMeasure M s Set.univ = ((M : ℝ≥0∞)⁻¹) := by
  unfold stripBoxMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, one_mul]
  have hsub : ((s.val : ℝ) + 1) / (M : ℝ) - (s.val : ℝ) / (M : ℝ) = ((M : ℝ))⁻¹ := by
    have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp; ring
  rw [hsub, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hM), ENNReal.ofReal_natCast]

/-- Pushing `unifHMeasure` forward by `y ↦ (s + y / (11/5)) / M` gives `M • volume.restrict (Ioc (s/M) ((s+1)/M))`. -/
lemma map_unifHMeasure_stripY {M : ℕ} (hM : 0 < M) (s : Fin M) :
    unifHMeasure.map (fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) =
      (M : ℝ≥0∞) • volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))) := by
  have hmeas : Measurable (fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) := by fun_prop
  ext A hA
  rw [Measure.map_apply hmeas hA, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
  unfold unifHMeasure heightBinMeasure
  rw [withDensity_apply _ (hmeas hA), ← lintegral_indicator (hmeas hA)]
  -- Change variables `u = (s + y / (11/5)) / M`, i.e., `y = (M * (11/5)) * u - s * (11/5)`
  let a : ℝ := (M : ℝ) * (11 / 5 : ℝ)
  let b : ℝ := (s.val : ℝ) * (11 / 5 : ℝ)
  have ha : 0 < a := by positivity
  have hadd := lintegral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun y : ℝ =>
    ((fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) ⁻¹' A).indicator
      (fun y => (heightBinDensityNN 1 (11 / 5) 0 y : ℝ≥0∞)) y) (-b)
  rw [← hadd]
  have hmeas_z : Measurable (fun z : ℝ =>
      ((fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) ⁻¹' A).indicator
        (fun y => (heightBinDensityNN 1 (11 / 5) 0 y : ℝ≥0∞)) (z + -b)) := by
    have hm1 : Measurable (fun y : ℝ => (heightBinDensityNN 1 (11 / 5) 0 y : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp (measurable_heightBinDensityNN 1 (11 / 5) 0)
    exact (hm1.indicator (hmeas hA)).comp (measurable_id.add_const (-b))
  have hmul := lintegral_comp_mul_left_pos ha _ hmeas_z
  have hstep : ∫⁻ z : ℝ, ((fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) ⁻¹' A).indicator
        (fun y => (heightBinDensityNN 1 (11 / 5) 0 y : ℝ≥0∞)) (z + -b) =
      ENNReal.ofReal a * ∫⁻ u : ℝ,
        ((fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) ⁻¹' A).indicator
          (fun y => (heightBinDensityNN 1 (11 / 5) 0 y : ℝ≥0∞)) (a * u + -b) := by
    rw [hmul, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt ha),
      mul_inv_cancel₀ (ne_of_gt ha), ENNReal.ofReal_one, one_mul]
  rw [hstep]
  have hinv_fn : ∀ u : ℝ, ((s.val : ℝ) + (a * u + -b) / (11 / 5 : ℝ)) / (M : ℝ) = u := fun u => by
    have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp only [a, b]; field_simp; ring
  have hmem_bin : ∀ u : ℝ,
      a * u + -b ∈ heightBinSet 1 (11 / 5) 0 ↔
        u ∈ Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)) := fun u => by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    simp only [heightBinSet, Set.mem_Ioc, Nat.cast_zero, zero_mul, zero_add,
      Nat.cast_one, one_mul, div_one, div_lt_iff₀ hM0, le_div_iff₀ hM0]
    dsimp only [a, b]
    constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> nlinarith
  have hcongr : ∀ u : ℝ,
      ((fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) ⁻¹' A).indicator
        (fun y => (heightBinDensityNN 1 (11 / 5) 0 y : ℝ≥0∞)) (a * u + -b) =
      (A ∩ Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))).indicator
        (fun _ => ENNReal.ofReal (5 / 11 : ℝ)) u := by
    intro u
    by_cases hAu : u ∈ A
    · have hpre : a * u + -b ∈ (fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) ⁻¹' A := by
        simpa [hinv_fn u] using hAu
      rw [Set.indicator_of_mem hpre]
      by_cases hIu : u ∈ Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))
      · have hAI : u ∈ A ∩ Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)) := ⟨hAu, hIu⟩
        rw [Set.indicator_of_mem hAI]
        simp only [heightBinDensityNN, Set.indicator_of_mem ((hmem_bin u).mpr hIu),
          ENNReal.ofReal]
        congr 1; ext; simp
      · rw [Set.indicator_of_notMem (fun h => hIu h.2)]
        simp [heightBinDensityNN, Set.indicator_of_notMem (mt (hmem_bin u).mp hIu)]
    · have hpre : a * u + -b ∉ (fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) ⁻¹' A := by
        simpa [hinv_fn u] using hAu
      rw [Set.indicator_of_notMem hpre, Set.indicator_of_notMem (fun h => hAu h.1)]
  simp_rw [hcongr]
  rw [lintegral_indicator_const (hA.inter measurableSet_Ioc), ← mul_assoc]
  have hprod_const : ENNReal.ofReal a * ENNReal.ofReal (5 / 11 : ℝ) = (M : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul (le_of_lt ha)]
    have hval : a * (5 / 11 : ℝ) = (M : ℝ) := by dsimp only [a]; ring
    rw [hval, ENNReal.ofReal_natCast]
  rw [hprod_const]

/-- Arrival event for strip `s`: exactly `k` arrivals among `1..4+m` fall in `(0, 1]`. -/
def stripArrivalEvent (M m k : ℕ) (hk : k < 4 + m) :
    Set ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) :=
  {p | (∀ j, 0 < p.1 j) ∧
       (∑ j : Fin k, p.1 ⟨j.val + 3, by omega⟩) ≤ (M : ℝ) * (11 / 5 : ℝ) ^ 2 ∧
       (M : ℝ) * (11 / 5 : ℝ) ^ 2 < ∑ j : Fin (k + 1), p.1 ⟨j.val + 3, by omega⟩}

lemma measurableSet_stripArrivalEvent (M m k : ℕ) (hk : k < 4 + m) :
    MeasurableSet (stripArrivalEvent M m k hk) := by
  have heq : stripArrivalEvent M m k hk =
      (⋂ j : Fin (7 + m), {p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) | 0 < p.1 j}) ∩
      ({p | (∑ j : Fin k, p.1 ⟨j.val + 3, by omega⟩) ≤ (M : ℝ) * (11 / 5 : ℝ) ^ 2} ∩
       {p | (M : ℝ) * (11 / 5 : ℝ) ^ 2 < ∑ j : Fin (k + 1), p.1 ⟨j.val + 3, by omega⟩}) := by
    ext p; simp [stripArrivalEvent]
  rw [heq]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)) ?_
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le (Finset.measurable_sum _ fun j _ => (measurable_pi_apply _).comp measurable_fst) measurable_const
  · exact measurableSet_lt measurable_const (Finset.measurable_sum _ fun j _ => (measurable_pi_apply _).comp measurable_fst)

lemma stripArrivalEvent_pairwiseDisjoint (M m : ℕ) :
    Pairwise (fun (k₁ k₂ : Fin (4 + m)) =>
      Disjoint (stripArrivalEvent M m k₁.val k₁.isLt) (stripArrivalEvent M m k₂.val k₂.isLt)) := by
  intro k₁ k₂ hne
  rw [Set.disjoint_left]
  intro p hp1 hp2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · -- `k₁ + 1 ≤ k₂`, so `∑_{< k₁+1} ≤ ∑_{< k₂} ≤ μ`, contradicting `μ < ∑_{< k₁+1}`
    have hsum_le : ∑ j : Fin (k₁.val + 1), p.1 ⟨j.val + 3, by omega⟩ ≤
        ∑ j : Fin k₂.val, p.1 ⟨j.val + 3, by omega⟩ := by
      let emb : Fin (k₁.val + 1) ↪ Fin k₂.val :=
        ⟨fun j => ⟨j.val, by omega⟩, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩
      calc ∑ j : Fin (k₁.val + 1), p.1 ⟨j.val + 3, by omega⟩
          = ∑ j ∈ Finset.univ.map emb, p.1 ⟨j.val + 3, by omega⟩ := by
              rw [Finset.sum_map]; rfl
        _ ≤ ∑ j : Fin k₂.val, p.1 ⟨j.val + 3, by omega⟩ :=
              Finset.sum_le_univ_sum_of_nonneg fun j => le_of_lt (hp1.1 _)
    linarith [hp1.2.2, hp2.2.1]
  · have hsum_le : ∑ j : Fin (k₂.val + 1), p.1 ⟨j.val + 3, by omega⟩ ≤
        ∑ j : Fin k₁.val, p.1 ⟨j.val + 3, by omega⟩ := by
      let emb : Fin (k₂.val + 1) ↪ Fin k₁.val :=
        ⟨fun j => ⟨j.val, by omega⟩, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩
      calc ∑ j : Fin (k₂.val + 1), p.1 ⟨j.val + 3, by omega⟩
          = ∑ j ∈ Finset.univ.map emb, p.1 ⟨j.val + 3, by omega⟩ := by
              rw [Finset.sum_map]; rfl
        _ ≤ ∑ j : Fin k₁.val, p.1 ⟨j.val + 3, by omega⟩ :=
              Finset.sum_le_univ_sum_of_nonneg fun j => le_of_lt (hp2.1 _)
    linarith [hp2.2.2, hp1.2.1]

/-- The `k` arrival points in strip `s` (`stripUnitPt M s E Y 1, ..., stripUnitPt M s E Y k`). -/
noncomputable def stripArrPts (M m k : ℕ) (s : Fin M)
    (p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) : Fin k → ℝ × ℝ :=
  fun i => stripUnitPt M s p.1 p.2 (i.val + 1)

lemma measurable_stripArrPts (M m k : ℕ) (s : Fin M) : Measurable (stripArrPts M m k s) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold stripArrPts stripUnitPt stripPt
  refine Measurable.prodMk ?_ ?_
  · refine Measurable.div_const (Measurable.div_const ?_ _) _
    refine Finset.measurable_sum _ fun j _ => ?_
    split_ifs
    · exact (measurable_pi_apply j).comp measurable_fst
    · exact measurable_const
  · refine Measurable.div_const (Measurable.const_add (Measurable.div_const ?_ _) _) _
    split_ifs
    · exact (measurable_pi_apply _).comp measurable_snd
    · exact measurable_const

/-- Tail probability of `exp1Measure`: `exp1Measure (Ioi a) = ENNReal.ofReal (Real.exp (-a))` for `a ≥ 0`. -/
lemma exp1Measure_Ioi {a : ℝ} (ha : 0 ≤ a) :
    exp1Measure (Ioi a) = ENNReal.ofReal (Real.exp (-a)) := by
  unfold exp1Measure
  rw [withDensity_apply _ measurableSet_Ioi]
  have hcongr : ∀ x ∈ Ioi a, (exp1DensityNN x : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-x)) := by
    intro x hx
    have hx0 : x ∈ Ioi (0 : ℝ) := lt_of_le_of_lt ha hx
    simp [exp1DensityNN, Set.indicator_of_mem hx0, ENNReal.ofReal]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi a) :=
    integrableOn_exp_neg_Ioi a
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => le_of_lt (Real.exp_pos _))]
  rw [integral_Ioi_exp_neg a]

local instance : IsProbabilityMeasure exp1Measure := isProbabilityMeasure_exp1Measure
local instance : IsProbabilityMeasure unifHMeasure := isProbabilityMeasure_unifHMeasure

/-- **Single-Strip Renewal Identity:** Integrating a symmetric measurable function `F` of the `k`
arrival points in strip `s` over `stripArrivalEvent M m k` equals
`poissonProb μ k * M^k * ∫⁻ x, F x ∂(stripBoxMeasure M s)^k`. -/
theorem single_strip_renewal_lintegral {M : ℕ} (hM : 0 < M) (m k : ℕ) (hk : k < 4 + m)
    (s : Fin M) (F : (Fin k → ℝ × ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hFsym : ∀ σ : Equiv.Perm (Fin k), ∀ x, F (x ∘ σ) = F x) :
    ∫⁻ p in stripArrivalEvent M m k hk, F (stripArrPts M m k s p) ∂(stripFullMeasure m) =
      ENNReal.ofReal (poissonProb ((M : ℝ) * (11 / 5 : ℝ) ^ 2) k * (M : ℝ) ^ k) *
        ∫⁻ x : Fin k → ℝ × ℝ, F x ∂(Measure.pi fun _ : Fin k => stripBoxMeasure M s) := by
  set μ : ℝ := (M : ℝ) * (11 / 5 : ℝ) ^ 2
  have hμ : 0 < μ := by positivity
  -- Step 1: Project `E` onto the `k + 1` active gaps `(e : Fin k → ℝ, e_last : ℝ)` and `Y` onto `k` active heights
  let embE : Fin (k + 1) ↪ Fin (7 + m) :=
    ⟨fun i => ⟨i.val + 3, by omega⟩, fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simp at this; omega)⟩
  let embY : Fin k ↪ Fin (8 + m) :=
    ⟨fun i => ⟨i.val + 4, by omega⟩, fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simp at this; omega)⟩
  have hmpE : MeasurePreserving (fun E : Fin (7 + m) → ℝ => fun i : Fin (k + 1) => E (embE i))
      (Measure.pi fun _ : Fin (7 + m) => exp1Measure) (Measure.pi fun _ : Fin (k + 1) => exp1Measure) :=
    measurePreserving_pi_emb_gen (fun _ => exp1Measure) embE
  have hmpY : MeasurePreserving (fun Y : Fin (8 + m) → ℝ => fun i : Fin k => Y (embY i))
      (Measure.pi fun _ : Fin (8 + m) => unifHMeasure) (Measure.pi fun _ : Fin k => unifHMeasure) :=
    measurePreserving_pi_emb_gen (fun _ => unifHMeasure) embY
  have hmp : MeasurePreserving (fun p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) =>
      ((fun i : Fin (k + 1) => p.1 (embE i)), (fun i : Fin k => p.2 (embY i))))
      (stripFullMeasure m)
      ((Measure.pi fun _ : Fin (k + 1) => exp1Measure).prod (Measure.pi fun _ : Fin k => unifHMeasure)) :=
    hmpE.prod hmpY
  -- On `stripFullMeasure m`, `∀ j, 0 < p.1 j` holds a.e.
  have hae_pos : ∀ᵐ p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) ∂(stripFullMeasure m), ∀ j, 0 < p.1 j := by
    have h1 : ∀ j : Fin (7 + m), ∀ᵐ E ∂(Measure.pi fun _ : Fin (7 + m) => exp1Measure), 0 < E j := by
      intro j
      have hm := measurePreserving_eval (fun _ : Fin (7 + m) => exp1Measure) j
      have hpos1 : ∀ᵐ x : ℝ ∂exp1Measure, 0 < x := by
        unfold exp1Measure
        rw [ae_withDensity_iff (f := fun x : ℝ => (exp1DensityNN x : ℝ≥0∞))
          (measurable_coe_nnreal_ennreal.comp measurable_exp1DensityNN)]
        refine ae_of_all _ fun x hx => ?_
        by_contra hnot
        have hmem : x ∉ Ioi (0 : ℝ) := hnot
        simp [exp1DensityNN, Set.indicator_of_notMem hmem] at hx
      exact hm.quasiMeasurePreserving.ae hpos1
    have hall := ae_all_iff.mpr h1
    exact measurePreserving_fst.quasiMeasurePreserving.ae hall
  -- Express the integrand as a function of the projected `(E', Y')`
  let A' : Set (Fin (k + 1) → ℝ) :=
    {E' | (∀ i, 0 < E' i) ∧ (∑ i : Fin k, E' i.castSucc) ≤ μ ∧ μ < ∑ i : Fin (k + 1), E' i}
  have hA'_meas : MeasurableSet A' := by
    have heq : A' = (⋂ i : Fin (k + 1), {E' | 0 < E' i}) ∩
        ({E' | (∑ i : Fin k, E' i.castSucc) ≤ μ} ∩ {E' | μ < ∑ i : Fin (k + 1), E' i}) := by
      ext E'; simp [A']
    rw [heq]
    exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      ((measurableSet_le (Finset.measurable_sum _ fun i : Fin k => fun _ => measurable_pi_apply i.castSucc) measurable_const).inter
       (measurableSet_lt measurable_const (Finset.measurable_sum _ fun i : Fin (k + 1) => fun _ => measurable_pi_apply i)))
  let mapY : (Fin k → ℝ) → (Fin k → ℝ) := fun Y' i => ((s.val : ℝ) + Y' i / (11 / 5 : ℝ)) / (M : ℝ)
  let G : (Fin (k + 1) → ℝ) × (Fin k → ℝ) → ℝ≥0∞ := fun q =>
    A'.indicator (fun E' => F (fun i => (partialSumsDiv k μ (fun j => E' j.castSucc) i, mapY q.2 i))) q.1
  have hG_meas : Measurable G := by
    have hpair : Measurable (fun q : (Fin (k + 1) → ℝ) × (Fin k → ℝ) =>
        fun i : Fin k => (partialSumsDiv k μ (fun j => q.1 j.castSucc) i, mapY q.2 i)) := by
      refine measurable_pi_lambda _ fun i => Measurable.prodMk ?_ ?_
      · exact ((measurable_pi_apply i).comp (measurable_partialSumsDiv k μ)).comp
          (measurable_pi_lambda _ fun j => (measurable_pi_apply j.castSucc).comp measurable_fst)
      · exact (by fun_prop : Measurable fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)).comp
          ((measurable_pi_apply i).comp measurable_snd)
    have hcomp := hF.comp hpair
    exact hcomp.indicator (hA'_meas.prod MeasurableSet.univ) |> fun hm => by
      convert hm using 1
      funext ⟨E', Y'⟩
      dsimp only [G]
      by_cases h : E' ∈ A'
      · have hmemP : (E', Y') ∈ A' ×ˢ (Set.univ : Set (Fin k → ℝ)) := ⟨h, Set.mem_univ Y'⟩
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hmemP]; rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h hc.1)]
  -- Show our LHS equals `∫⁻ q, G q ∂((exp1Measure^(k+1)).prod (unifHMeasure^k))`
  have hlhs_eq : ∫⁻ p in stripArrivalEvent M m k hk, F (stripArrPts M m k s p) ∂(stripFullMeasure m) =
      ∫⁻ q, G q ∂((Measure.pi fun _ : Fin (k + 1) => exp1Measure).prod
        (Measure.pi fun _ : Fin k => unifHMeasure)) := by
    rw [← lintegral_indicator (measurableSet_stripArrivalEvent M m k hk)]
    rw [← hmp.lintegral_comp hG_meas]
    refine lintegral_congr_ae ?_
    filter_upwards [hae_pos] with ⟨E, Y⟩ hpos
    have hmem_iff : (E, Y) ∈ stripArrivalEvent M m k hk ↔ (fun i : Fin (k + 1) => E (embE i)) ∈ A' := by
      simp only [stripArrivalEvent, A', Set.mem_setOf_eq, embE, Function.Embedding.coeFn_mk,
        Fin.val_castSucc]
      exact ⟨fun h => ⟨fun _ => hpos _, h.2⟩, fun h => ⟨hpos, h.2⟩⟩
    by_cases hp : (E, Y) ∈ stripArrivalEvent M m k hk
    · rw [Set.indicator_of_mem hp]
      dsimp only [G]
      rw [Set.indicator_of_mem (hmem_iff.mp hp)]
      congr 1; funext i
      unfold stripArrPts stripUnitPt stripPt partialSumsDiv mapY
      have hlt : i.val + 1 + 3 < 8 + m := by omega
      simp only [hlt, ↓reduceDIte]
      apply Prod.ext
      · have hsum_eq : (∑ j : Fin (7 + m), if 3 ≤ j.val ∧ j.val < i.val + 1 + 3 then E j else 0) =
            ∑ j : Fin k, if j ≤ i then E ⟨j.val + 3, by omega⟩ else 0 := by
          rw [← Finset.sum_filter, ← Finset.sum_filter]
          refine Finset.sum_bij (fun j hj => ⟨j.val - 3, by
              have h1 := (Finset.mem_filter.mp hj).2; omega⟩) ?_ ?_ ?_ ?_
          · intro j hj
            have h1 := (Finset.mem_filter.mp hj).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Fin.le_iff_val_le_val]; omega⟩
          · intro j1 hj1 j2 hj2 heq
            have h1 := (Finset.mem_filter.mp hj1).2
            have h2 := (Finset.mem_filter.mp hj2).2
            have hv := congrArg Fin.val heq; simp at hv
            exact Fin.ext (by omega)
          · intro j hj
            have h1 := (Finset.mem_filter.mp hj).2
            refine ⟨⟨j.val + 3, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp; omega⟩, ?_⟩
            apply Fin.ext; simp
          · intro j hj
            have h1 := (Finset.mem_filter.mp hj).2
            congr 1; apply Fin.ext; simp; omega
        rw [hsum_eq, div_div]
        have hμ_eq : (11 / 5 : ℝ) * ((M : ℝ) * (11 / 5 : ℝ)) = μ := by dsimp only [μ]; ring
        rw [hμ_eq]
        rfl
      · have hYeq : Y ⟨i.val + 1 + 3, hlt⟩ = Y (embY i) :=
          congrArg Y (Fin.ext (by simp only [embY, Function.Embedding.coeFn_mk]))
        rw [hYeq]
    · rw [Set.indicator_of_notMem hp]
      dsimp only [G]
      rw [Set.indicator_of_notMem (mt hmem_iff.mpr hp)]
  rw [hlhs_eq]
  -- Step 2: Use Fubini to put the `Y'` integral on the outside and `E'` on the inside
  rw [MeasureTheory.lintegral_prod_symm _ hG_meas.aemeasurable]
  -- Step 3: For each fixed `Y' : Fin k → ℝ`, evaluate the `E'`-integral to `exp(-μ) * μ^k * ∫⁻ t in orderedSimplex k, ...`
  have hE_eval : ∀ Y' : Fin k → ℝ,
      ∫⁻ E' : Fin (k + 1) → ℝ, G (E', Y') ∂(Measure.pi fun _ : Fin (k + 1) => exp1Measure) =
        ENNReal.ofReal (Real.exp (-μ) * μ ^ k) *
          ∫⁻ t in orderedSimplex k, F (fun i => (t i, mapY Y' i)) := by
    intro Y'
    -- Split `E' : Fin (k + 1) → ℝ` into `(e_last, e)` via `MeasurableEquiv.piFinSuccAbove`
    let splitE := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
    have hmpS : MeasurePreserving splitE (Measure.pi fun _ : Fin (k + 1) => exp1Measure)
        (exp1Measure.prod (Measure.pi fun _ : Fin k => exp1Measure)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => exp1Measure) (Fin.last k)
    have hmeas_gE : Measurable (fun E' : Fin (k + 1) → ℝ => G (E', Y')) :=
      hG_meas.comp (measurable_id.prodMk measurable_const)
    rw [← hmpS.symm.lintegral_comp hmeas_gE]
    rw [MeasureTheory.lintegral_prod_symm (f := fun a : ℝ × (Fin k → ℝ) => G (splitE.symm a, Y'))
      (hmeas_gE.comp splitE.symm.measurable).aemeasurable]
    -- Inner integral over `e_last : ℝ` against `exp1Measure`:
    have hinnerE : ∀ e : Fin k → ℝ,
        ∫⁻ e_last : ℝ, G (splitE.symm (e_last, e), Y') ∂exp1Measure =
          (gapSimplex k μ).indicator (fun e =>
            ENNReal.ofReal (Real.exp (-(μ - ∑ i : Fin k, e i))) *
              F (fun i => (partialSumsDiv k μ e i, mapY Y' i))) e := by
      intro e
      have hcast_any : ∀ (e_last : ℝ) (i : Fin k), splitE.symm (e_last, e) i.castSucc = e i :=
        fun e_last i => splitLast_castSucc e_last e i
      have hlast_any : ∀ e_last : ℝ, splitE.symm (e_last, e) (Fin.last k) = e_last :=
        fun e_last => splitLast_last e_last e
      by_cases he : e ∈ gapSimplex k μ
      · rw [Set.indicator_of_mem he]
        have hmem_e : ∀ e_last : ℝ,
            splitE.symm (e_last, e) ∈ A' ↔ e_last ∈ Ioi (μ - ∑ i : Fin k, e i) := by
          intro e_last
          simp only [A', Set.mem_setOf_eq, Set.mem_Ioi, Fin.forall_fin_succ',
            Fin.sum_univ_castSucc, hcast_any, hlast_any]
          constructor
          · rintro ⟨_, _, hgt⟩; linarith
          · intro hgt
            have hpos : 0 < e_last := by linarith [he.2]
            exact ⟨⟨he.1, hpos⟩, he.2, by linarith⟩
        have hcongr_e : ∀ e_last : ℝ,
            G (splitE.symm (e_last, e), Y') =
              (Ioi (μ - ∑ i : Fin k, e i)).indicator
                (fun _ => F (fun i => (partialSumsDiv k μ e i, mapY Y' i))) e_last := by
          intro e_last
          dsimp only [G]
          have hfn : (fun j : Fin k => splitE.symm (e_last, e) j.castSucc) = e := funext (hcast_any e_last)
          by_cases hl : e_last ∈ Ioi (μ - ∑ i : Fin k, e i)
          · rw [Set.indicator_of_mem ((hmem_e e_last).mpr hl), Set.indicator_of_mem hl, hfn]
          · rw [Set.indicator_of_notMem (mt (hmem_e e_last).mp hl), Set.indicator_of_notMem hl]
        simp_rw [hcongr_e]
        rw [lintegral_indicator_const measurableSet_Ioi,
            exp1Measure_Ioi (by linarith [he.2]), mul_comm]
      · rw [Set.indicator_of_notMem he]
        have hzero : ∀ e_last : ℝ, splitE.symm (e_last, e) ∉ A' := by
          intro e_last hm
          apply he
          simp only [A', Set.mem_setOf_eq, Fin.forall_fin_succ', hcast_any] at hm
          exact ⟨hm.1.1, hm.2.1⟩
        simp [G, Set.indicator_of_notMem (hzero _)]
    simp_rw [hinnerE]
    have hpi_dens : ∀ (h : (Fin k → ℝ) → ℝ≥0∞), Measurable h →
        ∫⁻ e : Fin k → ℝ, h e ∂(Measure.pi fun _ : Fin k => exp1Measure) =
          ∫⁻ e : Fin k → ℝ, (∏ i : Fin k, (exp1DensityNN (e i) : ℝ≥0∞)) * h e := by
      have hgen : ∀ (n : ℕ) (h : (Fin n → ℝ) → ℝ≥0∞), Measurable h →
          ∫⁻ e : Fin n → ℝ, h e ∂(Measure.pi fun _ : Fin n => exp1Measure) =
            ∫⁻ e : Fin n → ℝ, (∏ i : Fin n, (exp1DensityNN (e i) : ℝ≥0∞)) * h e := by
        intro n
        induction n with
        | zero =>
          intro h _
          simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
          have heq : (Measure.pi fun _ : Fin 0 => exp1Measure) = (volume : Measure (Fin 0 → ℝ)) := by
            refine Measure.pi_eq fun s _ => ?_
            have hvol : (volume : Measure (Fin 0 → ℝ)) = Measure.pi fun _ : Fin 0 => (volume : Measure ℝ) := rfl
            rw [hvol, Measure.pi_pi]; simp
          rw [heq]
        | succ n' ih =>
          intro h hh
          let sp := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n' + 1) => ℝ) 0
          have hmp1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n' + 1) => exp1Measure) 0
          have hmp2 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n' + 1) => ℝ) 0
          rw [← hmp1.symm.lintegral_comp hh]
          rw [MeasureTheory.lintegral_prod (f := fun a : ℝ × (Fin n' → ℝ) => h (sp.symm a))
            (hh.comp sp.symm.measurable).aemeasurable]
          have hstep1 : ∀ x : ℝ, ∫⁻ y : Fin n' → ℝ, h (sp.symm (x, y)) ∂(Measure.pi fun _ : Fin n' => exp1Measure) =
              ∫⁻ y : Fin n' → ℝ, (∏ i : Fin n', (exp1DensityNN (y i) : ℝ≥0∞)) * h (sp.symm (x, y)) := fun x =>
            ih _ (hh.comp (sp.symm.measurable.comp (measurable_const.prodMk measurable_id)))
          simp_rw [hstep1]
          unfold exp1Measure
          rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun x : ℝ => (exp1DensityNN x : ℝ≥0∞))
            (measurable_coe_nnreal_ennreal.comp measurable_exp1DensityNN)]
          · have hmul_in : ∀ x : ℝ,
                (exp1DensityNN x : ℝ≥0∞) * ∫⁻ y : Fin n' → ℝ, (∏ i : Fin n', (exp1DensityNN (y i) : ℝ≥0∞)) * h (sp.symm (x, y)) =
                ∫⁻ y : Fin n' → ℝ, (exp1DensityNN x : ℝ≥0∞) * ((∏ i : Fin n', (exp1DensityNN (y i) : ℝ≥0∞)) * h (sp.symm (x, y))) := by
              intro x
              have hm : Measurable (fun y : Fin n' → ℝ =>
                  (∏ i : Fin n', (exp1DensityNN (y i) : ℝ≥0∞)) * h (sp.symm (x, y))) := by
                refine Measurable.mul ?_ (hh.comp (sp.symm.measurable.comp (measurable_const.prodMk measurable_id)))
                exact Finset.measurable_prod _ fun i _ =>
                  (measurable_coe_nnreal_ennreal.comp measurable_exp1DensityNN).comp (measurable_pi_apply i)
              exact (lintegral_const_mul _ hm).symm
            have hstep2 : (∫⁻ x : ℝ, (exp1DensityNN x : ℝ≥0∞) *
                  ∫⁻ y : Fin n' → ℝ, (∏ i : Fin n', (exp1DensityNN (y i) : ℝ≥0∞)) * h (sp.symm (x, y))) =
                ∫⁻ x : ℝ, ∫⁻ y : Fin n' → ℝ,
                  (exp1DensityNN x : ℝ≥0∞) * ((∏ i : Fin n', (exp1DensityNN (y i) : ℝ≥0∞)) * h (sp.symm (x, y))) :=
              lintegral_congr hmul_in
            change (∫⁻ x : ℝ, (exp1DensityNN x : ℝ≥0∞) *
                ∫⁻ y : Fin n' → ℝ, (∏ i : Fin n', (exp1DensityNN (y i) : ℝ≥0∞)) * h (sp.symm (x, y))) = _
            rw [hstep2]
            have hmeas_prod : Measurable (fun p : ℝ × (Fin n' → ℝ) =>
                (exp1DensityNN p.1 : ℝ≥0∞) * ((∏ i : Fin n', (exp1DensityNN (p.2 i) : ℝ≥0∞)) * h (sp.symm p))) := by
              refine Measurable.mul ((measurable_coe_nnreal_ennreal.comp measurable_exp1DensityNN).comp measurable_fst) ?_
              refine Measurable.mul ?_ (hh.comp sp.symm.measurable)
              exact Finset.measurable_prod _ fun i _ =>
                (measurable_coe_nnreal_ennreal.comp measurable_exp1DensityNN).comp ((measurable_pi_apply i).comp measurable_snd)
            rw [← MeasureTheory.lintegral_prod _ hmeas_prod.aemeasurable]
            have hcongr : (fun p : ℝ × (Fin n' → ℝ) =>
                (exp1DensityNN p.1 : ℝ≥0∞) * ((∏ i : Fin n', (exp1DensityNN (p.2 i) : ℝ≥0∞)) * h (sp.symm p))) =
                fun p => ((∏ i : Fin (n' + 1), (exp1DensityNN (sp.symm p i) : ℝ≥0∞)) * h (sp.symm p)) := by
              funext ⟨x, y⟩
              rw [← mul_assoc, Fin.prod_univ_succ]
              congr 2
            rw [hcongr]
            have hmeas_full : Measurable (fun e : Fin (n' + 1) → ℝ =>
                (∏ i : Fin (n' + 1), (exp1DensityNN (e i) : ℝ≥0∞)) * h e) :=
              (Finset.measurable_prod _ fun i _ =>
                (measurable_coe_nnreal_ennreal.comp measurable_exp1DensityNN).comp (measurable_pi_apply i)).mul hh
            rw [← Measure.volume_eq_prod]
            exact hmp2.symm.lintegral_comp hmeas_full
          · exact Measurable.lintegral_prod_right'
              (f := fun p : ℝ × (Fin n' → ℝ) => (∏ i : Fin n', (exp1DensityNN (p.2 i) : ℝ≥0∞)) * h (sp.symm p))
              ((Finset.measurable_prod _ fun i _ =>
                (measurable_coe_nnreal_ennreal.comp measurable_exp1DensityNN).comp
                  ((measurable_pi_apply i).comp measurable_snd)).mul (hh.comp sp.symm.measurable))
      exact hgen k
    have hmeas_inner : Measurable ((gapSimplex k μ).indicator (fun e =>
        ENNReal.ofReal (Real.exp (-(μ - ∑ i : Fin k, e i))) *
          F (fun i => (partialSumsDiv k μ e i, mapY Y' i)))) := by
      refine Measurable.indicator (Measurable.mul ?_ ?_) (measurableSet_gapSimplex k μ)
      · exact ENNReal.measurable_ofReal.comp
          (Real.continuous_exp.measurable.comp
            (measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)).neg)
      · refine hF.comp (measurable_pi_lambda _ fun i => Measurable.prodMk ?_ measurable_const)
        exact (measurable_pi_apply i).comp (measurable_partialSumsDiv k μ)
    rw [hpi_dens _ hmeas_inner]
    have hcancel : ∀ e : Fin k → ℝ,
        (∏ i : Fin k, (exp1DensityNN (e i) : ℝ≥0∞)) *
          (gapSimplex k μ).indicator (fun e =>
            ENNReal.ofReal (Real.exp (-(μ - ∑ i : Fin k, e i))) *
              F (fun i => (partialSumsDiv k μ e i, mapY Y' i))) e =
        ENNReal.ofReal (Real.exp (-μ)) *
          (gapSimplex k μ).indicator (fun e => F (fun i => (partialSumsDiv k μ e i, mapY Y' i))) e := by
      intro e
      by_cases he : e ∈ gapSimplex k μ
      · rw [Set.indicator_of_mem he, Set.indicator_of_mem he, ← mul_assoc]
        congr 1
        have hprod : ∏ i : Fin k, (exp1DensityNN (e i) : ℝ≥0∞) =
            ENNReal.ofReal (Real.exp (-(∑ i : Fin k, e i))) := by
          have h1 : ∀ i : Fin k, (exp1DensityNN (e i) : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-(e i))) := fun i => by
            simp [exp1DensityNN, Set.indicator_of_mem (show e i ∈ Ioi (0 : ℝ) from he.1 i), ENNReal.ofReal]
          simp_rw [h1]
          rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => le_of_lt (Real.exp_pos _)),
              ← Real.exp_sum, Finset.sum_neg_distrib]
        rw [hprod, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), ← Real.exp_add]
        congr 2; ring
      · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he, mul_zero, mul_zero]
    simp_rw [hcancel]
    have hF_t_meas : Measurable (fun t : Fin k → ℝ => F (fun i => (t i, mapY Y' i))) :=
      hF.comp (measurable_pi_lambda _ fun i => (measurable_pi_apply i).prodMk measurable_const)
    have hF_e_meas : Measurable ((gapSimplex k μ).indicator (fun e => F (fun i => (partialSumsDiv k μ e i, mapY Y' i)))) :=
      (hF_t_meas.comp (measurable_partialSumsDiv k μ)).indicator (measurableSet_gapSimplex k μ)
    rw [lintegral_const_mul _ hF_e_meas]
    rw [lintegral_indicator (measurableSet_gapSimplex k μ)]
    rw [lintegral_gapSimplex_eq_orderedSimplex k hμ _ hF_t_meas, ← mul_assoc,
        ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  -- Step 4: Swap `Y'` inside and apply `k!`-simplex symmetry to `H(t) := ∫⁻ Y', F(t, mapY Y')`
  simp_rw [hE_eval]
  have hF_tY_meas : Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => F (fun i => (p.1 i, mapY p.2 i))) := by
    refine hF.comp (measurable_pi_lambda _ fun i => Measurable.prodMk ?_ ?_)
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (by fun_prop : Measurable fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)).comp
        ((measurable_pi_apply i).comp measurable_snd)
  have hF_Yt_meas : Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => F (fun i => (p.2 i, mapY p.1 i))) :=
    hF_tY_meas.comp measurable_swap
  have hmeas_ord : Measurable (fun Y' : Fin k → ℝ =>
      ∫⁻ t in orderedSimplex k, F (fun i => (t i, mapY Y' i))) :=
    Measurable.lintegral_prod_left hF_tY_meas
  rw [lintegral_const_mul _ hmeas_ord]
  rw [MeasureTheory.lintegral_lintegral_swap hF_Yt_meas.aemeasurable]
  let H : (Fin k → ℝ) → ℝ≥0∞ := fun t =>
    ∫⁻ Y' : Fin k → ℝ, F (fun i => (t i, mapY Y' i)) ∂(Measure.pi fun _ : Fin k => unifHMeasure)
  have hH_meas : Measurable H := Measurable.lintegral_prod_right' hF_tY_meas
  have hH_sym : ∀ σ : Equiv.Perm (Fin k), ∀ t, H (t ∘ σ) = H t := by
    intro σ t
    dsimp only [H, Function.comp]
    have hmpσ : MeasurePreserving (fun Y' : Fin k → ℝ => Y' ∘ σ)
        (Measure.pi fun _ : Fin k => unifHMeasure) (Measure.pi fun _ : Fin k => unifHMeasure) :=
      measurePreserving_pi_equiv σ (fun _ => unifHMeasure)
    rw [← hmpσ.lintegral_comp (f := fun Y' => F (fun i => (t (σ i), mapY Y' i)))
      (hF_tY_meas.comp (measurable_const.prodMk measurable_id))]
    apply lintegral_congr
    intro Y'
    have heq : (fun i : Fin k => (t (σ i), mapY (Y' ∘ σ) i)) = (fun i => (t i, mapY Y' i)) ∘ σ := by
      funext i; rfl
    rw [heq, hFsym σ]
  have hfact_ne0 : (k.factorial : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hfact_top : (k.factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsym_eq : ∫⁻ t in orderedSimplex k, H t =
      ((k.factorial : ℝ≥0∞)⁻¹) * ∫⁻ t in Set.pi Set.univ (fun _ : Fin k => Ioc (0 : ℝ) 1), H t := by
    rw [← lintegral_orderedSimplex_mul_factorial k H hH_meas hH_sym, ← mul_assoc,
        ENNReal.inv_mul_cancel hfact_ne0 hfact_top, one_mul]
  change ENNReal.ofReal (Real.exp (-μ) * μ ^ k) * (∫⁻ t in orderedSimplex k, H t) = _
  rw [hsym_eq, ← mul_assoc]
  -- Step 5: Push `unifHMeasure^k` forward by `mapY` to `M^k • (volume.restrict (Ioc (s/M) ((s+1)/M)))^k`
  have hmapY_pi : (Measure.pi fun _ : Fin k => unifHMeasure).map mapY =
      ((M : ℝ≥0∞) ^ k) • Measure.pi (fun _ : Fin k =>
        volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
    have hmeas_mY : Measurable mapY := measurable_pi_lambda _ fun i =>
      (by fun_prop : Measurable fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)).comp (measurable_pi_apply i)
    have hsmul_pi : Measure.pi (fun _ : Fin k =>
        (M : ℝ≥0∞) • volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) =
        ((M : ℝ≥0∞) ^ k) • Measure.pi (fun _ : Fin k =>
          volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
      haveI : IsFiniteMeasure (volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
        constructor; simp [Real.volume_Ioc]
      haveI : IsFiniteMeasure ((M : ℝ≥0∞) • volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
        constructor
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top M) (measure_lt_top _ _)
      refine Measure.pi_eq fun A hA => ?_
      simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← hsmul_pi]
    haveI : IsFiniteMeasure ((M : ℝ≥0∞) • volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top M) (by simp [Real.volume_Ioc])
    symm
    refine Measure.pi_eq fun A hA => ?_
    rw [Measure.map_apply hmeas_mY (MeasurableSet.univ_pi hA)]
    have hpre : mapY ⁻¹' Set.pi Set.univ A =
        Set.pi Set.univ (fun i => (fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)) ⁻¹' A i) := by
      ext Y'; simp [mapY]
    rw [hpre, Measure.pi_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [← map_unifHMeasure_stripY hM s, Measure.map_apply (by fun_prop) (hA i)]
  have hH_eq : ∀ t : Fin k → ℝ, H t =
      ((M : ℝ≥0∞) ^ k) * ∫⁻ y : Fin k → ℝ, F (fun i => (t i, y i))
        ∂(Measure.pi fun _ : Fin k => volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
    intro t
    dsimp only [H]
    have hmeas_mY : Measurable mapY := measurable_pi_lambda _ fun i =>
      (by fun_prop : Measurable fun y : ℝ => ((s.val : ℝ) + y / (11 / 5 : ℝ)) / (M : ℝ)).comp (measurable_pi_apply i)
    have hmeas_Ft : Measurable (fun y : Fin k → ℝ => F (fun i => (t i, y i))) :=
      hF.comp (measurable_pi_lambda _ fun i => measurable_const.prodMk (measurable_pi_apply i))
    rw [← lintegral_map hmeas_Ft hmeas_mY, hmapY_pi, lintegral_smul_measure, smul_eq_mul]
  simp_rw [hH_eq]
  have hF_ty_meas : Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => F (fun i => (p.1 i, p.2 i))) :=
    hF.comp (measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  rw [lintegral_const_mul _ (Measurable.lintegral_prod_right' hF_ty_meas)]
  -- Combine constants: `exp(-μ) * μ^k * (k!)⁻¹ * M^k = poissonProb μ k * M^k`
  have hconst : ENNReal.ofReal (Real.exp (-μ) * μ ^ k) * ((k.factorial : ℝ≥0∞)⁻¹) * ((M : ℝ≥0∞) ^ k) =
      ENNReal.ofReal (poissonProb μ k * (M : ℝ) ^ k) := by
    rw [← ENNReal.ofReal_natCast (k.factorial), ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.factorial_pos k),
        ← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_pow (Nat.cast_nonneg M),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
  rw [← mul_assoc, hconst]
  congr 1
  -- Identify `(volume.restrict (Ioc 0 1))^k × (volume.restrict (Ioc (s / M) ((s + 1) / M)))^k` with `(stripBoxMeasure M s)^k`.
  have hrestrict_pi : volume.restrict (Set.pi Set.univ fun _ : Fin k => Ioc (0 : ℝ) 1) =
      Measure.pi (fun _ : Fin k => volume.restrict (Ioc (0 : ℝ) 1)) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by constructor; simp [Real.volume_Ioc]
    symm
    refine Measure.pi_eq fun A hA => ?_
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hA), ← Set.pi_inter_distrib]
    have hvol : (volume : Measure (Fin k → ℝ)) = Measure.pi (fun _ : Fin k => (volume : Measure ℝ)) := rfl
    rw [hvol, Measure.pi_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [Measure.restrict_apply (hA i)]
  rw [hrestrict_pi]
  let pairFun : ∀ (n : ℕ), ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ × ℝ) :=
    fun _ p i => (p.1 i, p.2 i)
  have hmp_pair_gen : ∀ (n : ℕ) (ν₁ ν₂ : Measure ℝ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂],
      MeasurePreserving (pairFun n)
        ((Measure.pi fun _ : Fin n => ν₁).prod (Measure.pi fun _ : Fin n => ν₂))
        (Measure.pi fun _ : Fin n => ν₁.prod ν₂) := by
    intro n ν₁ ν₂ _ _
    induction n with
    | zero =>
      have hmeas0 : Measurable (pairFun 0) :=
        measurable_pi_lambda _ fun i => Fin.elim0 i
      refine ⟨hmeas0, ?_⟩
      symm
      refine Measure.pi_eq fun A _ => ?_
      rw [Measure.map_apply hmeas0 (MeasurableSet.univ_pi fun i => Fin.elim0 i)]
      have hpre : pairFun 0 ⁻¹' Set.pi Set.univ A = Set.univ ×ˢ Set.univ := by
        ext ⟨a, b⟩; simp
      rw [hpre, Measure.prod_prod]
      have h1 : (Measure.pi fun _ : Fin 0 => ν₁) Set.univ = 1 := by
        rw [← Set.pi_univ, Measure.pi_pi]; simp
      have h2 : (Measure.pi fun _ : Fin 0 => ν₂) Set.univ = 1 := by
        rw [← Set.pi_univ, Measure.pi_pi]; simp
      simp [h1, h2]
    | succ n' ih =>
      let s1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n' + 1) => ν₁) 0
      let s2 := measurePreserving_piFinSuccAbove (fun _ : Fin (n' + 1) => ν₂) 0
      let s12 := measurePreserving_piFinSuccAbove (fun _ : Fin (n' + 1) => ν₁.prod ν₂) 0
      let sw : MeasurePreserving
          (fun p : (ℝ × (Fin n' → ℝ)) × (ℝ × (Fin n' → ℝ)) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
          ((ν₁.prod (Measure.pi fun _ : Fin n' => ν₁)).prod (ν₂.prod (Measure.pi fun _ : Fin n' => ν₂)))
          ((ν₁.prod ν₂).prod ((Measure.pi fun _ : Fin n' => ν₁).prod (Measure.pi fun _ : Fin n' => ν₂))) := by
        have hcomp := (measurePreserving_prodAssoc (μa := ν₁) (μb := ν₂)
            (μc := (Measure.pi fun _ : Fin n' => ν₁).prod (Measure.pi fun _ : Fin n' => ν₂))).symm.comp
          ((MeasurePreserving.id ν₁).prod
            ((measurePreserving_prodAssoc (μa := ν₂) (μb := Measure.pi fun _ : Fin n' => ν₁)
                (μc := Measure.pi fun _ : Fin n' => ν₂)).comp
              (((Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin n' => ν₁) (ν := ν₂)).prod
                  (MeasurePreserving.id (Measure.pi fun _ : Fin n' => ν₂))).comp
                ((measurePreserving_prodAssoc (μa := Measure.pi fun _ : Fin n' => ν₁) (μb := ν₂)
                    (μc := Measure.pi fun _ : Fin n' => ν₂)).symm))))
        have hcomp2 := hcomp.comp (measurePreserving_prodAssoc (μa := ν₁)
          (μb := Measure.pi fun _ : Fin n' => ν₁) (μc := ν₂.prod (Measure.pi fun _ : Fin n' => ν₂)))
        convert hcomp2 using 1
        funext ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
      have htot := s12.symm.comp (((MeasurePreserving.id (ν₁.prod ν₂)).prod ih).comp (sw.comp (s1.prod s2)))
      convert htot using 1
      funext ⟨a, b⟩; funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pairFun]
      · simp [pairFun, Fin.tail]
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by constructor; simp [Real.volume_Ioc]
  haveI : IsFiniteMeasure (volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
    constructor; simp [Real.volume_Ioc]
  have hmp_pair := hmp_pair_gen k (volume.restrict (Ioc (0 : ℝ) 1))
    (volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))))
  rw [← MeasureTheory.lintegral_prod _ hF_ty_meas.aemeasurable]
  exact hmp_pair.lintegral_comp hF

end BHHBounds.Upper

