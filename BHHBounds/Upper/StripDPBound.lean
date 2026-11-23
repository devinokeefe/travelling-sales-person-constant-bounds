import BHHBounds.Upper.CostTableSound
import BHHBounds.Upper.TourHelpers

/-!
# Expected path length in one strip

`strip_expected_path_le`: if `dpOp automaton4 edgeCost4 V ≤ V + uBound`, there is a constant
`C_strip` such that, for i.i.d. `Exp(1)` gaps and uniform heights in `(0, 11/5]`, the points
`0, ..., 4 + m` of a strip have a Hamiltonian path from `0` to `4 + m` of expected length at most
`m * uBound + C_strip`.
-/

namespace BHHBounds.Upper

open MeasureTheory Set Real Filter Finset
open scoped ENNReal NNReal BigOperators

/-! ## Section 1: Standard `Exp(1)` and `Unif(0, 11/5]` Measures and Quantile Decomposition -/

noncomputable def exp1DensityNN (x : ℝ) : ℝ≥0 :=
  (Ioi (0 : ℝ)).indicator (fun t => Real.toNNReal (Real.exp (-t))) x

lemma measurable_exp1DensityNN : Measurable exp1DensityNN :=
  (Measurable.real_toNNReal (by fun_prop)).indicator measurableSet_Ioi

noncomputable def exp1Measure : Measure ℝ :=
  volume.withDensity fun x => (exp1DensityNN x : ℝ≥0∞)

lemma exp1DensityNN_coe (x : ℝ) :
    ((exp1DensityNN x : ℝ≥0) : ℝ) = (Ioi (0 : ℝ)).indicator (fun t => Real.exp (-t)) x := by
  unfold exp1DensityNN
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp [Set.indicator_of_mem hx, Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _))]
  · simp [Set.indicator_of_notMem hx]

lemma isProbabilityMeasure_exp1Measure : IsProbabilityMeasure exp1Measure := by
  constructor
  unfold exp1Measure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfun : (fun x => (exp1DensityNN x : ℝ≥0∞)) =
      (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (Real.exp (-t))) := by
    funext x; unfold exp1DensityNN
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp [Set.indicator_of_mem hx, ENNReal.ofReal]
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, lintegral_indicator measurableSet_Ioi]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
    (ae_of_all _ fun t => le_of_lt (Real.exp_pos _))]
  rw [integral_Ioi_exp_neg 0]
  simp

lemma integral_exp1Measure (f : ℝ → ℝ) :
    ∫ x, f x ∂exp1Measure = ∫ x in Ioi (0 : ℝ), f x * Real.exp (-x) := by
  unfold exp1Measure
  rw [integral_withDensity_eq_integral_smul measurable_exp1DensityNN]
  have hfun : (fun x => exp1DensityNN x • f x) =
      (Ioi (0 : ℝ)).indicator (fun x => f x * Real.exp (-x)) := by
    funext x
    change ((exp1DensityNN x : ℝ≥0) : ℝ) * f x = _
    rw [exp1DensityNN_coe]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem hx]; ring
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, integral_indicator measurableSet_Ioi]

lemma integrable_exp1Measure_iff {f : ℝ → ℝ} :
    Integrable f exp1Measure ↔ IntegrableOn (fun x => f x * Real.exp (-x)) (Ioi (0 : ℝ)) volume := by
  unfold exp1Measure
  rw [integrable_withDensity_iff_integrable_smul₀ measurable_exp1DensityNN.aemeasurable]
  have hfun : (fun x => exp1DensityNN x • f x) =
      (Ioi (0 : ℝ)).indicator (fun x => f x * Real.exp (-x)) := by
    funext x
    change ((exp1DensityNN x : ℝ≥0) : ℝ) * f x = _
    rw [exp1DensityNN_coe]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem hx]; ring
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, integrable_indicator_iff measurableSet_Ioi]

lemma integrable_id_exp1Measure : Integrable (fun x : ℝ => x) exp1Measure :=
  integrable_exp1Measure_iff.mpr (integrableOn_mul_exp_neg_Ioi le_rfl)

lemma integrable_sq_exp1Measure : Integrable (fun x : ℝ => x ^ 2) exp1Measure :=
  integrable_exp1Measure_iff.mpr (integrableOn_sq_mul_exp_neg_Ioi 0)

lemma integral_id_exp1Measure : ∫ x, x ∂exp1Measure = 1 := by
  rw [integral_exp1Measure, integral_Ioi_mul_exp_neg le_rfl]; simp

lemma integral_sq_exp1Measure : ∫ x, x ^ 2 ∂exp1Measure = 2 := by
  rw [integral_exp1Measure, integral_Ioi_sq_mul_exp_neg 0]; simp

lemma Ioi_zero_eq_expBinSet_union :
    Ioi (0 : ℝ) = ⋃ g : Fin 4, expBinSet 4 g.val := by
  ext x
  simp only [mem_iUnion, Set.mem_Ioi]
  have h0 : expCut 4 0 = 0 := by unfold expCut; simp
  constructor
  · intro hx
    by_cases h1 : x ≤ expCut 4 1
    · exact ⟨0, by unfold expBinSet; simp [h0, hx, h1]⟩
    · by_cases h2 : x ≤ expCut 4 2
      · exact ⟨1, by unfold expBinSet; simp; exact ⟨lt_of_not_ge h1, h2⟩⟩
      · by_cases h3 : x ≤ expCut 4 3
        · exact ⟨2, by unfold expBinSet; simp; exact ⟨lt_of_not_ge h2, h3⟩⟩
        · exact ⟨3, by unfold expBinSet; simp; exact lt_of_not_ge h3⟩
  · rintro ⟨g, hg⟩
    have hge : 0 ≤ expCut 4 g.val := expCut_nonneg g.isLt
    unfold expBinSet at hg
    split_ifs at hg
    · exact lt_of_le_of_lt hge hg.1
    · exact lt_of_le_of_lt hge hg

lemma expBinSet4_pairwiseDisjoint :
    ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).Pairwise
      (Function.onFun Disjoint (fun g : Fin 4 => expBinSet 4 g.val)) := by
  intro g1 _ g2 _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx1 hx2
  have hord : ∀ a b : Fin 4, a.val < b.val →
      x ∈ expBinSet 4 a.val → x ∈ expBinSet 4 b.val → False := by
    intro a b hab hxa hxb
    have hlta : a.val + 1 < 4 := by have := b.isLt; omega
    unfold expBinSet at hxa hxb
    simp only [hlta, ↓reduceIte] at hxa
    have hmono : expCut 4 (a.val + 1) ≤ expCut 4 b.val := expCut_mono_le (by omega) b.isLt
    have hlt_b : expCut 4 b.val < x := by split_ifs at hxb <;> [exact hxb.1; exact hxb]
    linarith [hxa.2]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact hord g1 g2 h hx1 hx2
  · exact hord g2 g1 h hx2 hx1

/-- Exact 4-bin decomposition of `exp1Measure`. -/
lemma exp1Measure_eq_avg_bins :
    exp1Measure = (1 / 4 : ℝ≥0∞) • ∑ g : Fin 4, expBinMeasure 4 g.val := by
  ext s hs
  simp only [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  unfold exp1Measure expBinMeasure
  rw [withDensity_apply _ hs]
  simp_rw [withDensity_apply _ hs]
  have hfun1 : (fun x => (exp1DensityNN x : ℝ≥0∞)) =
      fun x => ∑ g : Fin 4, (expBinSet 4 g.val).indicator (fun t => ENNReal.ofReal (Real.exp (-t))) x := by
    funext x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · have hmem : x ∈ ⋃ g : Fin 4, expBinSet 4 g.val := by rw [← Ioi_zero_eq_expBinSet_union]; exact hx
      obtain ⟨g0, hg0⟩ := mem_iUnion.mp hmem
      have hother : ∀ g : Fin 4, g ≠ g0 → x ∉ expBinSet 4 g.val := fun g hne hmem' =>
        Set.disjoint_left.mp (expBinSet4_pairwiseDisjoint (Finset.mem_univ g) (Finset.mem_univ g0) hne) hmem' hg0
      rw [Finset.sum_eq_single g0 (fun g _ hne => Set.indicator_of_notMem (hother g hne) _) (fun h => absurd (Finset.mem_univ g0) h)]
      simp [exp1DensityNN, Set.indicator_of_mem hx, Set.indicator_of_mem hg0, ENNReal.ofReal]
    · have hnone : ∀ g : Fin 4, x ∉ expBinSet 4 g.val := fun g hmem => by
        have : x ∈ Ioi (0 : ℝ) := by rw [Ioi_zero_eq_expBinSet_union]; exact mem_iUnion.mpr ⟨g, hmem⟩
        exact hx this
      simp [exp1DensityNN, Set.indicator_of_notMem hx, Set.indicator_of_notMem (hnone _)]
  rw [hfun1, lintegral_finsetSum _ (fun g _ => (Measurable.ennreal_ofReal (by fun_prop)).indicator (measurableSet_expBinSet 4 g.val))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [← lintegral_const_mul' (1 / 4 : ℝ≥0∞) _ (by simp)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ expBinSet 4 g.val
  · simp only [Set.indicator_of_mem hx, expBinDensityNN]
    have h14 : (1 / 4 : ℝ≥0∞) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by norm_num
    rw [ENNReal.ofReal, h14, ← ENNReal.coe_mul]
    congr 1; ext
    simp [Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _)),
      Real.coe_toNNReal _ (by positivity : 0 ≤ (4 : ℝ) * Real.exp (-x))]
  · simp [Set.indicator_of_notMem hx, expBinDensityNN]

/-- Exact 6-bin decomposition of `unifHMeasure := heightBinMeasure 1 (11/5) 0`. -/
noncomputable def unifHMeasure : Measure ℝ := heightBinMeasure 1 (11 / 5) 0

lemma isProbabilityMeasure_unifHMeasure : IsProbabilityMeasure unifHMeasure :=
  isProbabilityMeasure_heightBinMeasure (by norm_num) (by norm_num) 0

lemma heightBinSet1_eq_union6 :
    heightBinSet 1 (11 / 5) 0 = ⋃ b : Fin 6, heightBinSet 6 (11 / 5) b.val := by
  ext y
  simp only [heightBinSet, mem_iUnion, Set.mem_Ioc]
  constructor
  · rintro ⟨hy1, hy2⟩
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, one_mul, div_one] at hy1 hy2
    by_cases h1 : y ≤ 1 * (11 / 5 : ℝ) / 6
    · exact ⟨0, by simp [hy1]; linarith⟩
    · by_cases h2 : y ≤ 2 * (11 / 5 : ℝ) / 6
      · exact ⟨1, by simp; constructor <;> linarith⟩
      · by_cases h3 : y ≤ 3 * (11 / 5 : ℝ) / 6
        · exact ⟨2, by simp; constructor <;> linarith⟩
        · by_cases h4 : y ≤ 4 * (11 / 5 : ℝ) / 6
          · exact ⟨3, by change (3 : ℝ) * (11 / 5) / 6 < y ∧ y ≤ ((3 + 1 : ℕ) : ℝ) * (11 / 5) / 6; push_cast; constructor <;> linarith⟩
          · by_cases h5 : y ≤ 5 * (11 / 5 : ℝ) / 6
            · exact ⟨4, by change (4 : ℝ) * (11 / 5) / 6 < y ∧ y ≤ ((4 + 1 : ℕ) : ℝ) * (11 / 5) / 6; push_cast; constructor <;> linarith⟩
            · exact ⟨5, by change (5 : ℝ) * (11 / 5) / 6 < y ∧ y ≤ ((5 + 1 : ℕ) : ℝ) * (11 / 5) / 6; push_cast; constructor <;> linarith⟩
  · rintro ⟨b, hb1, hb2⟩
    have hb0 : (0 : ℝ) ≤ (b.val : ℝ) := Nat.cast_nonneg _
    have hb6 : (b.val : ℝ) + 1 ≤ 6 := by exact_mod_cast b.isLt
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, one_mul, div_one]
    push_cast at hb1 hb2
    constructor <;> linarith

lemma heightBinSet6_pairwiseDisjoint :
    ((Finset.univ : Finset (Fin 6)) : Set (Fin 6)).Pairwise
      (Function.onFun Disjoint (fun b : Fin 6 => heightBinSet 6 (11 / 5) b.val)) := by
  intro b1 _ b2 _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro y hy1 hy2
  simp only [heightBinSet, Set.mem_Ioc] at hy1 hy2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have hle : (b1.val : ℝ) + 1 ≤ (b2.val : ℝ) := by exact_mod_cast hlt
    push_cast at hy1 hy2; linarith
  · have hle : (b2.val : ℝ) + 1 ≤ (b1.val : ℝ) := by exact_mod_cast hlt
    push_cast at hy1 hy2; linarith

lemma unifHMeasure_eq_avg_bins :
    unifHMeasure = (1 / 6 : ℝ≥0∞) • ∑ b : Fin 6, heightBinMeasure 6 (11 / 5) b.val := by
  ext s hs
  simp only [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  unfold unifHMeasure heightBinMeasure
  rw [withDensity_apply _ hs]
  simp_rw [withDensity_apply _ hs]
  have hfun1 : (fun y => (heightBinDensityNN 1 (11 / 5) 0 y : ℝ≥0∞)) =
      fun y => ∑ b : Fin 6, (heightBinSet 6 (11 / 5) b.val).indicator
        (fun _ => ENNReal.ofReal (1 / (11 / 5 : ℝ))) y := by
    funext y
    by_cases hy : y ∈ heightBinSet 1 (11 / 5) 0
    · have hmem : y ∈ ⋃ b : Fin 6, heightBinSet 6 (11 / 5) b.val := by
        rw [← heightBinSet1_eq_union6]; exact hy
      obtain ⟨b0, hb0⟩ := mem_iUnion.mp hmem
      have hother : ∀ b : Fin 6, b ≠ b0 → y ∉ heightBinSet 6 (11 / 5) b.val := fun b hne hmem' =>
        Set.disjoint_left.mp (heightBinSet6_pairwiseDisjoint (Finset.mem_univ b) (Finset.mem_univ b0) hne) hmem' hb0
      rw [Finset.sum_eq_single b0 (fun b _ hne => Set.indicator_of_notMem (hother b hne) _) (fun h => absurd (Finset.mem_univ b0) h)]
      simp [heightBinDensityNN, Set.indicator_of_mem hy, Set.indicator_of_mem hb0, ENNReal.ofReal]
    · have hnone : ∀ b : Fin 6, y ∉ heightBinSet 6 (11 / 5) b.val := fun b hmem => by
        have : y ∈ heightBinSet 1 (11 / 5) 0 := by rw [heightBinSet1_eq_union6]; exact mem_iUnion.mpr ⟨b, hmem⟩
        exact hy this
      simp [heightBinDensityNN, Set.indicator_of_notMem hy, Set.indicator_of_notMem (hnone _)]
  rw [hfun1, lintegral_finsetSum _ (fun b _ => measurable_const.indicator (measurableSet_heightBinSet 6 (11 / 5) b.val))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← lintegral_const_mul' (1 / 6 : ℝ≥0∞) _ (by simp)]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ heightBinSet 6 (11 / 5) b.val
  · simp only [Set.indicator_of_mem hy, heightBinDensityNN]
    have h16 : (1 / 6 : ℝ≥0∞) = ((1 / 6 : ℝ≥0) : ℝ≥0∞) := by norm_num
    rw [ENNReal.ofReal, h16, ← ENNReal.coe_mul]
    congr 1; ext
    simp
    norm_num
  · simp [Set.indicator_of_notMem hy, heightBinDensityNN]

/-! ## Section 2: General Product-of-Mixtures Decomposition & Sub-Coordinate Projection -/

/-- A product of uniform finite mixtures of measures equals the uniform mixture of product measures. -/
lemma pi_avg_eq_sum {k M : ℕ} (hM : 0 < M) (ν : Fin M → Measure ℝ)
    [∀ j, IsProbabilityMeasure (ν j)] :
    Measure.pi (fun _ : Fin k => ((M : ℝ≥0∞)⁻¹) • ∑ j : Fin M, ν j) =
      (((M ^ k : ℕ) : ℝ≥0∞)⁻¹) • ∑ c : Fin k → Fin M, Measure.pi (fun i => ν (c i)) := by
  haveI : IsProbabilityMeasure (((M : ℝ≥0∞)⁻¹) • ∑ j : Fin M, ν j) := by
    constructor
    simp only [Measure.smul_apply, Measure.finsetSum_apply, measure_univ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : M ≠ 0)) (ENNReal.natCast_ne_top M)
  haveI : ∀ c : Fin k → Fin M, IsProbabilityMeasure (Measure.pi fun i => ν (c i)) :=
    fun _ => inferInstance
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul, Measure.pi_pi]
  have hrhs : ∏ i : Fin k, (((M : ℝ≥0∞)⁻¹) * ∑ j : Fin M, ν j (s i)) =
      (((M ^ k : ℕ) : ℝ≥0∞)⁻¹) * ∏ i : Fin k, ∑ j : Fin M, ν j (s i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← ENNReal.inv_pow, Nat.cast_pow]
  rw [hrhs, Fintype.prod_sum]

/-- Projecting `Measure.pi μ` onto an injective subset of coordinates `emb : Fin k ↪ Fin n`
is measure-preserving whenever all coordinates are probability measures. -/
lemma measurePreserving_pi_emb {k n : ℕ} (μ : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (emb : Fin k ↪ Fin n) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i : Fin k => x (emb i))
      (Measure.pi μ) (Measure.pi fun i : Fin k => μ (emb i)) := by
  have hmeas : Measurable (fun x : Fin n → ℝ => fun i : Fin k => x (emb i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (emb i)
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  classical
  let t : Fin n → Set ℝ := fun j =>
    if h : ∃ i : Fin k, emb i = j then s h.choose else Set.univ
  have hpre : (fun x : Fin n → ℝ => fun i : Fin k => x (emb i)) ⁻¹' Set.univ.pi s = Set.univ.pi t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx j
      dsimp only [t]
      split_ifs with h
      · have h1 := hx h.choose
        rwa [h.choose_spec] at h1
      · trivial
    · intro hx i
      have hj := hx (emb i)
      dsimp only [t] at hj
      have hex : ∃ i' : Fin k, emb i' = emb i := ⟨i, rfl⟩
      rw [dif_pos hex] at hj
      rwa [emb.injective hex.choose_spec] at hj
  rw [hpre, Measure.pi_pi]
  have hprod : ∏ j : Fin n, μ j (t j) = ∏ j ∈ Finset.univ.image emb, μ j (t j) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro j _ hnot
    dsimp only [t]
    have hnot' : ¬∃ i : Fin k, emb i = j := fun ⟨i, hi⟩ =>
      hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    rw [dif_neg hnot', measure_univ]
  rw [hprod, Finset.prod_image (fun a _ b _ h => emb.injective h)]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [t]
  have hex : ∃ i' : Fin k, emb i' = emb i := ⟨i, rfl⟩
  rw [dif_pos hex, emb.injective hex.choose_spec]

/-! ## Section 3: Exact Bin-Indexed Strip Coordinates & Expected Hamiltonian Path Length -/

/-- Global gap bin at index `j : Fin (7 + m)` determined by `(z₀, w)`. -/
def gapBinAt {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) (j : Fin (7 + m)) : Fin 4 :=
  if h : j.val < 3 then z₀.1 ⟨j.val, h⟩
  else (w ⟨j.val - 3, by omega⟩).1

/-- Global height bin at index `j : Fin (8 + m)` determined by `(z₀, w)`. -/
def heightBinAt {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) (j : Fin (8 + m)) : Fin 6 :=
  if h : j.val < 4 then z₀.2 ⟨j.val, h⟩
  else (w ⟨j.val - 4, by omega⟩).2

/-- Bijection between `(Window 3 4 6 × (Fin (4 + m) → Label 4 6))` and
`(Fin (7 + m) → Fin 4) × (Fin (8 + m) → Fin 6)`. -/
def labelSeqEquiv (m : ℕ) :
    (Window 3 4 6 × (Fin (4 + m) → Label 4 6)) ≃ ((Fin (7 + m) → Fin 4) × (Fin (8 + m) → Fin 6)) where
  toFun p := (gapBinAt p.1 p.2, heightBinAt p.1 p.2)
  invFun q :=
    (((fun i : Fin 3 => q.1 ⟨i.val, by omega⟩), (fun i : Fin 4 => q.2 ⟨i.val, by omega⟩)),
      fun t : Fin (4 + m) => (q.1 ⟨t.val + 3, by omega⟩, q.2 ⟨t.val + 4, by omega⟩))
  left_inv := by
    rintro ⟨⟨zg, zy⟩, w⟩
    apply Prod.ext
    · apply Prod.ext <;> funext i <;> simp [gapBinAt, heightBinAt, i.isLt]
    · funext t
      apply Prod.ext <;> simp [gapBinAt, heightBinAt]
  right_inv := by
    rintro ⟨gs, ys⟩
    apply Prod.ext <;> funext j
    · dsimp only [gapBinAt]; split_ifs with h
      · rfl
      · congr 1; apply Fin.ext; simp; omega
    · dsimp only [heightBinAt]; split_ifs with h
      · rfl
      · congr 1; apply Fin.ext; simp; omega

/-- Rescaled strip point `k` (`0 ≤ k ≤ 4 + m`) generated by gaps `E : Fin (7 + m) → ℝ` and
heights `Y : Fin (8 + m) → ℝ`. Vertex `0` is at `(0, Y 3)`; vertex `k` has x-coordinate
`(E 3 + ... + E (k + 2)) / (11 / 5)` and y-coordinate `Y (k + 3)`. -/
noncomputable def stripPt {m : ℕ} (E : Fin (7 + m) → ℝ) (Y : Fin (8 + m) → ℝ) (k : ℕ) : ℝ × ℝ :=
  ((∑ j : Fin (7 + m), if 3 ≤ j.val ∧ j.val < k + 3 then E j else 0) / (11 / 5 : ℝ),
   if h : k + 3 < 8 + m then Y ⟨k + 3, h⟩ else 0)

/-- The `t`-th sliding window along `(z₀, w)` matches `gapBinAt` and `heightBinAt`. -/
lemma runWindow_take_eq {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) :
    ∀ (t : ℕ) (ht : t ≤ 4 + m),
      let wt : Fin t → Label 4 6 := fun i => w ⟨i.val, by omega⟩
      let zt := runWindow z₀ wt
      (∀ i : Fin 3, zt.1 i = gapBinAt z₀ w ⟨t + i.val, by omega⟩) ∧
      (∀ i : Fin 4, zt.2 i = heightBinAt z₀ w ⟨t + i.val, by omega⟩) := by
  intro t
  induction t with
  | zero =>
    intro _
    constructor
    · intro i; simp [runWindow, gapBinAt, i.isLt]
    · intro i; simp [runWindow, heightBinAt, i.isLt]
  | succ t ih =>
    intro ht
    obtain ⟨ihg, ihy⟩ := ih (by omega)
    have hstep : runWindow z₀ (fun i : Fin (t + 1) => w ⟨i.val, by omega⟩) =
        advanceWindow (runWindow z₀ (fun i : Fin t => w ⟨i.val, by omega⟩)) (w ⟨t, by omega⟩) := rfl
    dsimp only
    rw [hstep]
    constructor
    · intro i
      dsimp only [advanceWindow, fullGaps]
      by_cases hi : i.val + 1 < 3
      · have hcast : i.succ = (⟨i.val + 1, hi⟩ : Fin 3).castSucc := Fin.ext rfl
        rw [hcast, snocND_castSucc, ihg ⟨i.val + 1, hi⟩]
        congr 1; apply Fin.ext; simp; omega
      · have hlast : i.succ = Fin.last 3 := Fin.ext (by simp; omega)
        rw [hlast, snocND_last]
        have hi2 : i.val = 2 := by omega
        unfold gapBinAt
        have hge : ¬(t + 1 + i.val < 3) := by omega
        simp only [hge, ↓reduceDIte]
        congr 1; congr 1; apply Fin.ext; simp; omega
    · intro i
      dsimp only [advanceWindow, fullHeights]
      by_cases hi : i.val + 1 < 4
      · have hcast : i.succ = (⟨i.val + 1, hi⟩ : Fin 4).castSucc := Fin.ext rfl
        rw [hcast, snocND_castSucc, ihy ⟨i.val + 1, hi⟩]
        congr 1; apply Fin.ext; simp; omega
      · have hlast : i.succ = Fin.last 4 := Fin.ext (by simp; omega)
        rw [hlast, snocND_last]
        have hi3 : i.val = 3 := by omega
        unfold heightBinAt
        have hge : ¬(t + 1 + i.val < 4) := by omega
        simp only [hge, ↓reduceDIte]
        congr 1; congr 1; apply Fin.ext; simp; omega

/-- Full 4-gap and 5-height window at step `t` matches `gapBinAt` and `heightBinAt`. -/
lemma fullGaps_at_step {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) (t : Fin (4 + m)) :
    let wt : Fin t.val → Label 4 6 := fun i => w ⟨i.val, by omega⟩
    let zt := runWindow z₀ wt
    (∀ i : Fin 4, fullGaps zt (w t) i = gapBinAt z₀ w ⟨t.val + i.val, by omega⟩) ∧
    (∀ i : Fin 5, fullHeights zt (w t) i = heightBinAt z₀ w ⟨t.val + i.val, by omega⟩) := by
  intro wt zt
  obtain ⟨hg, hy⟩ := runWindow_take_eq z₀ w t.val (le_of_lt t.isLt)
  constructor
  · intro i
    exact Fin.lastCases (motive := fun j => fullGaps zt (w t) j = gapBinAt z₀ w ⟨t.val + j.val, by omega⟩)
      (by
        rw [fullGaps, snocND_last]
        unfold gapBinAt
        have hge : ¬(t.val + (Fin.last 3).val < 3) := by simp
        simp only [hge, ↓reduceDIte]
        congr 1)
      (fun j => by
        rw [fullGaps, snocND_castSucc, hg j]
        rfl) i
  · intro i
    exact Fin.lastCases (motive := fun j => fullHeights zt (w t) j = heightBinAt z₀ w ⟨t.val + j.val, by omega⟩)
      (by
        rw [fullHeights, snocND_last]
        unfold heightBinAt
        have hge : ¬(t.val + (Fin.last 4).val < 4) := by simp
        simp only [hge, ↓reduceDIte]
        congr 1)
      (fun j => by
        rw [fullHeights, snocND_castSucc, hy j]
        rfl) i

/-- Conditional measure on `(E, Y)` given discrete bins `(z₀, w)`. -/
noncomputable def stripBinMeasure {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) :
    Measure ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) :=
  (Measure.pi fun j : Fin (7 + m) => expBinMeasure 4 (gapBinAt z₀ w j).val).prod
    (Measure.pi fun j : Fin (8 + m) => heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w j).val)

instance stripBinMeasure_isProb {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) :
    IsProbabilityMeasure (stripBinMeasure z₀ w) := by
  haveI : ∀ j : Fin (7 + m), IsProbabilityMeasure (expBinMeasure 4 (gapBinAt z₀ w j).val) :=
    fun j => isProbabilityMeasure_expBinMeasure (gapBinAt z₀ w j).isLt
  haveI : ∀ j : Fin (8 + m), IsProbabilityMeasure (heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w j).val) :=
    fun j => isProbabilityMeasure_heightBinMeasure (by norm_num) (by norm_num) _
  unfold stripBinMeasure
  infer_instance

/-- For any step `t : Fin (4 + m)` and any
active slot `v : Fin 4` (with `4 - v.val ≤ t.val + 1`), the conditional expected Euclidean
distance between `stripPt (t + 1 - (4 - v))` and `stripPt (t + 1)` given `(z₀, w)` is at most
`edgeCost4 v (fullGaps z_t (w t)) (fullHeights z_t (w t))`. -/
lemma strip_edge_integral_le {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6)
    (t : Fin (4 + m)) (v : Fin 4) (hact : 4 - v.val ≤ t.val + 1) :
    let wt : Fin t.val → Label 4 6 := fun i => w ⟨i.val, by omega⟩
    let zt := runWindow z₀ wt
    Integrable (fun p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) =>
      euclidDist (stripPt p.1 p.2 (t.val + 1 - (4 - v.val))) (stripPt p.1 p.2 (t.val + 1)))
      (stripBinMeasure z₀ w) ∧
    ∫ p, euclidDist (stripPt p.1 p.2 (t.val + 1 - (4 - v.val))) (stripPt p.1 p.2 (t.val + 1))
      ∂(stripBinMeasure z₀ w) ≤ edgeCost4 v (fullGaps zt (w t)) (fullHeights zt (w t)) := by
  intro wt zt
  haveI : ∀ j : Fin (7 + m), IsProbabilityMeasure (expBinMeasure 4 (gapBinAt z₀ w j).val) :=
    fun j => isProbabilityMeasure_expBinMeasure (gapBinAt z₀ w j).isLt
  haveI : ∀ j : Fin (8 + m), IsProbabilityMeasure (heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w j).val) :=
    fun j => isProbabilityMeasure_heightBinMeasure (by norm_num) (by norm_num) _
  haveI : ∀ i : Fin (4 - v.val),
      IsProbabilityMeasure (expBinMeasure 4 (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).val) :=
    fun i => isProbabilityMeasure_expBinMeasure (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).isLt
  haveI : IsProbabilityMeasure (heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) v.castSucc).val) :=
    isProbabilityMeasure_heightBinMeasure (by norm_num) (by norm_num) _
  haveI : IsProbabilityMeasure (heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) (Fin.last 4)).val) :=
    isProbabilityMeasure_heightBinMeasure (by norm_num) (by norm_num) _
  obtain ⟨hfg, hfh⟩ := fullGaps_at_step z₀ w t
  let projE : (Fin (7 + m) → ℝ) → (Fin (4 - v.val) → ℝ) :=
    fun E i => E ⟨t.val + v.val + i.val, by omega⟩
  let projY : (Fin (8 + m) → ℝ) → (ℝ × ℝ) :=
    fun Y => (Y ⟨t.val + v.val, by omega⟩, Y ⟨t.val + 4, by omega⟩)
  let proj : ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) → ((Fin (4 - v.val) → ℝ) × (ℝ × ℝ)) :=
    fun p => (projE p.1, projY p.2)
  have hmpE : MeasurePreserving projE
      (Measure.pi fun j : Fin (7 + m) => expBinMeasure 4 (gapBinAt z₀ w j).val)
      (Measure.pi fun i : Fin (4 - v.val) => expBinMeasure 4 (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).val) := by
    let emb : Fin (4 - v.val) ↪ Fin (7 + m) :=
      ⟨fun i => ⟨t.val + v.val + i.val, by omega⟩, fun i1 i2 h => by
        have hv := congrArg Fin.val h; simp at hv; exact Fin.ext (by omega)⟩
    have hmp := measurePreserving_pi_emb
      (fun j : Fin (7 + m) => expBinMeasure 4 (gapBinAt z₀ w j).val) emb
    have hmeas_eq : (Measure.pi fun i : Fin (4 - v.val) => expBinMeasure 4 (gapBinAt z₀ w (emb i)).val) =
        (Measure.pi fun i : Fin (4 - v.val) => expBinMeasure 4 (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).val) := by
      congr 1; funext i
      have h1 := hfg ⟨v.val + i.val, by omega⟩
      have hidx : (⟨t.val + (v.val + i.val), by omega⟩ : Fin (7 + m)) = emb i := Fin.ext (by simp [emb]; omega)
      rw [h1, hidx]
    rwa [hmeas_eq] at hmp
  have hmpY : MeasurePreserving projY
      (Measure.pi fun j : Fin (8 + m) => heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w j).val)
      ((heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) v.castSucc).val).prod
       (heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) (Fin.last 4)).val)) := by
    let emb : Fin 2 ↪ Fin (8 + m) :=
      ⟨fun i => if i = 0 then ⟨t.val + v.val, by omega⟩ else ⟨t.val + 4, by omega⟩, by
        intro i1 i2 h
        fin_cases i1 <;> fin_cases i2
        · rfl
        · have hv := congrArg Fin.val h; simp at hv; have := v.isLt; omega
        · have hv := congrArg Fin.val h; simp at hv; have := v.isLt; omega
        · rfl⟩
    have hmp1 := measurePreserving_pi_emb
      (fun j : Fin (8 + m) => heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w j).val) emb
    have hmp2 : MeasurePreserving (fun f : Fin 2 → ℝ => (f 0, f 1))
        (Measure.pi fun i : Fin 2 => heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w (emb i)).val)
        ((heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w (emb 0)).val).prod
         (heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w (emb 1)).val)) := by
      have hm2 : Measurable (fun f : Fin 2 → ℝ => (f 0, f 1)) :=
        (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
      refine ⟨hm2, ?_⟩
      symm
      refine Measure.prod_eq fun s t hs ht => ?_
      rw [Measure.map_apply hm2 (hs.prod ht)]
      have hpre : (fun f : Fin 2 → ℝ => (f 0, f 1)) ⁻¹' (s ×ˢ t) =
          Set.univ.pi (fun i : Fin 2 => if i = 0 then s else t) := by
        ext f; simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left]
        constructor
        · rintro ⟨h0, h1⟩ i; fin_cases i <;> simpa using ‹_›
        · intro h; exact ⟨by simpa using h 0, by simpa using h 1⟩
      rw [hpre, Measure.pi_pi, Fin.prod_univ_two]
      simp
    have hcomp := hmp2.comp hmp1
    have hmeas_eq : ((heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w (emb 0)).val).prod
          (heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w (emb 1)).val)) =
        ((heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) v.castSucc).val).prod
          (heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) (Fin.last 4)).val)) := by
      rw [hfh v.castSucc, hfh (Fin.last 4)]
      rfl
    rwa [hmeas_eq] at hcomp
  have hmp : MeasurePreserving proj (stripBinMeasure z₀ w)
      ((Measure.pi fun i : Fin (4 - v.val) => expBinMeasure 4 (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).val).prod
       ((heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) v.castSucc).val).prod
        (heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) (Fin.last 4)).val))) :=
    hmpE.prod hmpY
  -- Check pointwise equality of `euclidDist` with the integrand of `edgeCost4_sound`
  let F : ((Fin (4 - v.val) → ℝ) × (ℝ × ℝ)) → ℝ :=
    fun q => Real.sqrt (((∑ i : Fin (4 - v.val), q.1 i) / (11 / 5 : ℝ)) ^ 2 + (q.2.1 - q.2.2) ^ 2)
  have hpt : ∀ p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ),
      euclidDist (stripPt p.1 p.2 (t.val + 1 - (4 - v.val))) (stripPt p.1 p.2 (t.val + 1)) = F (proj p) := by
    intro ⟨E, Y⟩
    unfold euclidDist sqDist stripPt F proj projE projY
    have hidx1 : t.val + 1 - (4 - v.val) + 3 = t.val + v.val := by omega
    have hidx2 : t.val + 1 + 3 = t.val + 4 := by omega
    have hlt1 : t.val + 1 - (4 - v.val) + 3 < 8 + m := by omega
    have hlt2 : t.val + 1 + 3 < 8 + m := by omega
    simp only [hlt1, hlt2, ↓reduceDIte]
    have hy1 : Y ⟨t.val + 1 - (4 - v.val) + 3, hlt1⟩ = Y ⟨t.val + v.val, by omega⟩ :=
      congrArg Y (Fin.ext hidx1)
    have hy2 : Y ⟨t.val + 1 + 3, hlt2⟩ = Y ⟨t.val + 4, by omega⟩ :=
      congrArg Y (Fin.ext hidx2)
    rw [hy1, hy2]
    congr 1; congr 1
    have hxdiff : (∑ j : Fin (7 + m), if 3 ≤ j.val ∧ j.val < t.val + 1 + 3 then E j else 0) -
        (∑ j : Fin (7 + m), if 3 ≤ j.val ∧ j.val < t.val + 1 - (4 - v.val) + 3 then E j else 0) =
        ∑ i : Fin (4 - v.val), E ⟨t.val + v.val + i.val, by omega⟩ := by
      rw [← Finset.sum_sub_distrib]
      have hsub : ∀ j : Fin (7 + m),
          (if 3 ≤ j.val ∧ j.val < t.val + 1 + 3 then E j else 0) -
          (if 3 ≤ j.val ∧ j.val < t.val + 1 - (4 - v.val) + 3 then E j else 0) =
          if t.val + v.val ≤ j.val ∧ j.val < t.val + 4 then E j else 0 := by
        intro j; have := v.isLt; have h3 : 3 ≤ t.val + v.val := by omega
        rw [hidx1, hidx2]
        split_ifs <;> first | (exfalso; omega) | ring
      simp_rw [hsub]
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun j _ => ⟨j.val - (t.val + v.val), by
          have hj := (Finset.mem_filter.mp ‹_›).2; omega⟩) ?_ ?_ ?_ ?_
      · intro j _; exact Finset.mem_univ _
      · intro j1 hj1 j2 hj2 heq
        have h1 := (Finset.mem_filter.mp hj1).2
        have h2 := (Finset.mem_filter.mp hj2).2
        have hv := congrArg Fin.val heq; simp at hv
        exact Fin.ext (by omega)
      · intro i _
        have hi := i.isLt; have hv := v.isLt
        refine ⟨⟨t.val + v.val + i.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp; omega⟩, ?_⟩
        apply Fin.ext; simp
      · intro j hj
        have h1 := (Finset.mem_filter.mp hj).2
        congr 1; apply Fin.ext; simp; omega
    have hdiv : ((∑ j : Fin (7 + m), if 3 ≤ j.val ∧ j.val < t.val + 1 - (4 - v.val) + 3 then E j else 0) / (11 / 5 : ℝ) -
        (∑ j : Fin (7 + m), if 3 ≤ j.val ∧ j.val < t.val + 1 + 3 then E j else 0) / (11 / 5 : ℝ)) ^ 2 =
        ((∑ i : Fin (4 - v.val), E ⟨t.val + v.val + i.val, by omega⟩) / (11 / 5 : ℝ)) ^ 2 := by
      rw [← sub_div, ← neg_sub, neg_div, neg_sq, hxdiff]
    rw [hdiv]
  -- Integrability of `F` on target measure (since `F q ≤ √(Z q) ≤ Z q + 1`)
  have hF_int : Integrable F
      ((Measure.pi fun i : Fin (4 - v.val) => expBinMeasure 4 (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).val).prod
       ((heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) v.castSucc).val).prod
        (heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) (Fin.last 4)).val))) := by
    let μX := Measure.pi fun i : Fin (4 - v.val) =>
      expBinMeasure 4 (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).val
    let μY := (heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) v.castSucc).val).prod
      (heightBinMeasure 6 (11 / 5) (fullHeights zt (w t) (Fin.last 4)).val)
    have hZ1 : Integrable (fun q : (Fin (4 - v.val) → ℝ) × (ℝ × ℝ) =>
        ((∑ i : Fin (4 - v.val), q.1 i) / (11 / 5 : ℝ)) ^ 2) (μX.prod μY) := by
      have hsq := (integral_pi_sum_sq
        (fun i : Fin (4 - v.val) => expBinMeasure 4 (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).val)
        (fun i => integrable_id_expBinMeasure (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).isLt)
        (fun i => integrable_sq_expBinMeasure (fullGaps zt (w t) ⟨v.val + i.val, by omega⟩).isLt)).1
      have hdiv : Integrable (fun xs : Fin (4 - v.val) → ℝ =>
          ((∑ i : Fin (4 - v.val), xs i) / (11 / 5 : ℝ)) ^ 2) μX := by
        have : (fun xs : Fin (4 - v.val) → ℝ => ((∑ i : Fin (4 - v.val), xs i) / (11 / 5 : ℝ)) ^ 2) =
            fun xs => (∑ i : Fin (4 - v.val), xs i) ^ 2 / (11 / 5 : ℝ) ^ 2 := by funext xs; ring
        rw [this]; exact hsq.div_const _
      exact integrable_comp_mp measurePreserving_fst hdiv
    have hZ2 : Integrable (fun q : (Fin (4 - v.val) → ℝ) × (ℝ × ℝ) => (q.2.1 - q.2.2) ^ 2) (μX.prod μY) :=
      integrable_comp_mp measurePreserving_snd (integrable_heightBin_diff_sq (by norm_num) (by norm_num) (by norm_num) _ _)
    have hZ := hZ1.add hZ2
    have hFcont : Continuous F := by unfold F; fun_prop
    refine Integrable.mono' (hZ.add (integrable_const 1)) hFcont.aestronglyMeasurable ?_
    filter_upwards with q
    have hq0 : 0 ≤ ((∑ i : Fin (4 - v.val), q.1 i) / (11 / 5 : ℝ)) ^ 2 + (q.2.1 - q.2.2) ^ 2 := by positivity
    have hsr0 : 0 ≤ F q := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg hsr0]
    have hsq := sq_nonneg (F q - 1)
    rw [sub_sq] at hsq
    have hFsq : F q ^ 2 = ((∑ i : Fin (4 - v.val), q.1 i) / (11 / 5 : ℝ)) ^ 2 + (q.2.1 - q.2.2) ^ 2 :=
      Real.sq_sqrt hq0
    change F q ≤ (((∑ i : Fin (4 - v.val), q.1 i) / (11 / 5 : ℝ)) ^ 2 + (q.2.1 - q.2.2) ^ 2) + 1
    linarith
  simp_rw [hpt]
  refine ⟨integrable_comp_mp hmp hF_int, ?_⟩
  rw [integral_comp_measurePreserving hmp hF_int.aestronglyMeasurable]
  exact edgeCost4_sound v (fullGaps zt (w t)) (fullHeights zt (w t))

/-! ## Section 4: Single-Strip Expected Hamiltonian Path Bound -/

/-- Any vertex `v ∈ chosen` in a valid transition from a matched state satisfies `4 - v ≤ k + 1`. -/
lemma stepState_chosen_active {d k : ℕ} {st st' : Mate d} {F : LinearForest k}
    (hm : Matches st F) {chosen : List (Fin d)} (hs : stepState st chosen = some st') :
    ∀ v ∈ chosen, d - v.val ≤ k + 1 := by
  unfold stepState at hs
  cases hfold : chosen.foldlM connectToNew (addIsolated st) with
  | none => simp [hfold] at hs
  | some m1 =>
    have haux : ∀ (l : List (Fin d)) (m m' : Mate (d + 1)) (G : LinearForest (k + 1)),
        Matches m G → l.foldlM connectToNew m = some m' → ∀ v ∈ l, d - v.val ≤ k + 1 := by
      intro l
      induction l with
      | nil => intro _ _ _ _ _ v hv; simp at hv
      | cons a rest ih =>
        intro m m' G hMG hf v hv
        simp only [List.foldlM_cons] at hf
        cases h1 : connectToNew m a with
        | none => simp [h1] at hf
        | some m2 =>
          simp [h1] at hf
          have hact : m a.castSucc ≠ -2 := by
            unfold connectToNew at h1; intro h; simp [h] at h1
          have hnn := slotGlobal_nonneg_of_active hMG hact
          rcases List.mem_cons.mp hv with rfl | hr
          · unfold slotGlobal at hnn; simp at hnn; omega
          · obtain ⟨G2, hMG2, _⟩ := connectToNew_sound (fun _ _ : Unit => (0 : ℝ)) (fun _ _ => rfl)
              (fun _ => ()) hMG h1
            exact ih m2 m' G2 hMG2 hf v hr
    obtain ⟨F0, hMF0, _⟩ := addIsolated_sound (fun _ _ : Unit => (0 : ℝ)) (fun _ => ()) hm
    exact haux chosen (addIsolated st) m1 F0 hMF0 hfold

lemma walk_chosen_active {d N : ℕ} (hd : 0 < d)
    (states : Fin (N + 1) → Mate d) (choices : Fin N → List (Fin d))
    (hstart : states 0 = initState d)
    (hstep : ∀ t : Fin N, stepState (states t.castSucc) (choices t) = some (states t.succ)) :
    ∀ (t : Fin N) (v : Fin d), v ∈ choices t → d - v.val ≤ t.val + 1 := by
  have hind : ∀ (n : ℕ) (hn : n ≤ N),
      ∃ F : LinearForest n, Matches (states ⟨n, by omega⟩) F := by
    intro n hn
    induction n with
    | zero => exact ⟨initForest, by simpa [hstart] using init_matches d hd⟩
    | succ n ih =>
      obtain ⟨F, hMF⟩ := ih (by omega)
      obtain ⟨F', hMF', _⟩ := stepState_sound (fun _ _ : Unit => (0 : ℝ)) (fun _ _ => rfl)
        (fun _ => ()) hMF (hstep ⟨n, by omega⟩)
      exact ⟨F', hMF'⟩
  intro t v hv
  obtain ⟨F, hMF⟩ := hind t.val (le_of_lt t.isLt)
  exact stepState_chosen_active hMF (hstep t) v hv

/-- Disjointness of product bin rectangles indexed by `(z₀, w)`. -/
def stripBinRect {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) :
    Set ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) :=
  (Set.univ.pi fun j : Fin (7 + m) => expBinSet 4 (gapBinAt z₀ w j).val) ×ˢ
  (Set.univ.pi fun j : Fin (8 + m) => heightBinSet 6 (11 / 5) (heightBinAt z₀ w j).val)

lemma measurableSet_stripBinRect {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) :
    MeasurableSet (stripBinRect z₀ w) :=
  (MeasurableSet.univ_pi fun j => measurableSet_expBinSet 4 (gapBinAt z₀ w j).val).prod
    (MeasurableSet.univ_pi fun j => measurableSet_heightBinSet 6 (11 / 5) (heightBinAt z₀ w j).val)

lemma ae_mem_stripBinRect {m : ℕ} (z₀ : Window 3 4 6) (w : Fin (4 + m) → Label 4 6) :
    ∀ᵐ p ∂(stripBinMeasure z₀ w), p ∈ stripBinRect z₀ w := by
  have hE : ∀ᵐ E ∂(Measure.pi fun j : Fin (7 + m) => expBinMeasure 4 (gapBinAt z₀ w j).val),
      E ∈ Set.univ.pi fun j : Fin (7 + m) => expBinSet 4 (gapBinAt z₀ w j).val := by
    have hcoord : ∀ j : Fin (7 + m), ∀ᵐ E ∂(Measure.pi fun j => expBinMeasure 4 (gapBinAt z₀ w j).val),
        E j ∈ expBinSet 4 (gapBinAt z₀ w j).val := by
      intro j
      haveI : ∀ i : Fin (7 + m), IsProbabilityMeasure (expBinMeasure 4 (gapBinAt z₀ w i).val) :=
        fun i => isProbabilityMeasure_expBinMeasure (gapBinAt z₀ w i).isLt
      have hj : ∀ᵐ x ∂(expBinMeasure 4 (gapBinAt z₀ w j).val), x ∈ expBinSet 4 (gapBinAt z₀ w j).val := by
        rw [ae_iff]; unfold expBinMeasure
        change (volume.withDensity fun x => (expBinDensityNN 4 (gapBinAt z₀ w j).val x : ℝ≥0∞))
          (expBinSet 4 (gapBinAt z₀ w j).val)ᶜ = 0
        rw [withDensity_apply _ (measurableSet_expBinSet 4 _).compl]
        rw [lintegral_eq_zero_iff (Measurable.coe_nnreal_ennreal (measurable_expBinDensityNN 4 _))]
        filter_upwards [ae_restrict_mem (measurableSet_expBinSet 4 _).compl] with x hx
        simp [expBinDensityNN, Set.indicator_of_notMem hx]
      exact (measurePreserving_eval (fun i => expBinMeasure 4 (gapBinAt z₀ w i).val) j).quasiMeasurePreserving.ae hj
    rw [← ae_all_iff] at hcoord
    filter_upwards [hcoord] with E hE j _
    exact hE j
  have hY : ∀ᵐ Y ∂(Measure.pi fun j : Fin (8 + m) => heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w j).val),
      Y ∈ Set.univ.pi fun j : Fin (8 + m) => heightBinSet 6 (11 / 5) (heightBinAt z₀ w j).val := by
    have hcoord : ∀ j : Fin (8 + m),
        ∀ᵐ Y ∂(Measure.pi fun j => heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w j).val),
          Y j ∈ heightBinSet 6 (11 / 5) (heightBinAt z₀ w j).val := by
      intro j
      haveI : ∀ i : Fin (8 + m), IsProbabilityMeasure (heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w i).val) :=
        fun i => isProbabilityMeasure_heightBinMeasure (by norm_num) (by norm_num) _
      exact (measurePreserving_eval (fun i => heightBinMeasure 6 (11 / 5) (heightBinAt z₀ w i).val) j).quasiMeasurePreserving.ae
        (ae_mem_heightBinSet _)
    rw [← ae_all_iff] at hcoord
    filter_upwards [hcoord] with Y hY j _
    exact hY j
  exact (Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hE).and
    (Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd hY)

lemma stripBinRect_disjoint {m : ℕ} {a b : Window 3 4 6 × (Fin (4 + m) → Label 4 6)} (hne : a ≠ b) :
    Disjoint (stripBinRect a.1 a.2) (stripBinRect b.1 b.2) := by
  rw [Set.disjoint_left]
  intro ⟨E, Y⟩ hA hB
  have hne' : labelSeqEquiv m a ≠ labelSeqEquiv m b := fun h => hne ((labelSeqEquiv m).injective h)
  have hor : gapBinAt a.1 a.2 ≠ gapBinAt b.1 b.2 ∨ heightBinAt a.1 a.2 ≠ heightBinAt b.1 b.2 := by
    by_contra h
    push Not at h
    exact hne' (Prod.ext h.1 h.2)
  rcases hor with hg | hy
  · obtain ⟨j, hj⟩ : ∃ j, gapBinAt a.1 a.2 j ≠ gapBinAt b.1 b.2 j := Function.ne_iff.mp hg
    exact Set.disjoint_left.mp
      (expBinSet4_pairwiseDisjoint (Finset.mem_univ _) (Finset.mem_univ _) hj)
      (hA.1 j (mem_univ j)) (hB.1 j (mem_univ j))
  · obtain ⟨j, hj⟩ : ∃ j, heightBinAt a.1 a.2 j ≠ heightBinAt b.1 b.2 j := Function.ne_iff.mp hy
    exact Set.disjoint_left.mp
      (heightBinSet6_pairwiseDisjoint (Finset.mem_univ _) (Finset.mem_univ _) hj)
      (hA.2 j (mem_univ j)) (hB.2 j (mem_univ j))

/-- Full single-strip probability measure on `(E, Y)` (`7 + m` i.i.d. `Exp(1)` gaps and
`8 + m` i.i.d. `Unif(0, 11/5]` heights). -/
noncomputable def stripFullMeasure (m : ℕ) :
    Measure ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) :=
  (Measure.pi fun _ : Fin (7 + m) => exp1Measure).prod
    (Measure.pi fun _ : Fin (8 + m) => unifHMeasure)

instance stripFullMeasure_isProb (m : ℕ) : IsProbabilityMeasure (stripFullMeasure m) := by
  haveI : IsProbabilityMeasure exp1Measure := isProbabilityMeasure_exp1Measure
  haveI : IsProbabilityMeasure unifHMeasure := isProbabilityMeasure_unifHMeasure
  unfold stripFullMeasure; infer_instance

/-- Exact uniform decomposition of `stripFullMeasure m` into `stripBinMeasure z₀ w`. -/
lemma stripFullMeasure_eq_avg (m : ℕ) :
    stripFullMeasure m =
      (((Fintype.card (Window 3 4 6) * (4 * 6) ^ (4 + m) : ℕ) : ℝ≥0∞)⁻¹) •
        ∑ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6), stripBinMeasure p.1 p.2 := by
  haveI : ∀ g : Fin 4, IsProbabilityMeasure (expBinMeasure 4 g.val) :=
    fun g => isProbabilityMeasure_expBinMeasure g.isLt
  haveI : ∀ b : Fin 6, IsProbabilityMeasure (heightBinMeasure 6 (11 / 5) b.val) :=
    fun b => isProbabilityMeasure_heightBinMeasure (by norm_num) (by norm_num) _
  have hE : Measure.pi (fun _ : Fin (7 + m) => exp1Measure) =
      (((4 ^ (7 + m) : ℕ) : ℝ≥0∞)⁻¹) •
        ∑ gs : Fin (7 + m) → Fin 4, Measure.pi (fun j => expBinMeasure 4 (gs j).val) := by
    have h4 : (1 / 4 : ℝ≥0∞) = ((4 : ℕ) : ℝ≥0∞)⁻¹ := by norm_num
    rw [exp1Measure_eq_avg_bins, h4]
    exact pi_avg_eq_sum (by norm_num) (fun g : Fin 4 => expBinMeasure 4 g.val)
  have hY : Measure.pi (fun _ : Fin (8 + m) => unifHMeasure) =
      (((6 ^ (8 + m) : ℕ) : ℝ≥0∞)⁻¹) •
        ∑ ys : Fin (8 + m) → Fin 6, Measure.pi (fun j => heightBinMeasure 6 (11 / 5) (ys j).val) := by
    have h6 : (1 / 6 : ℝ≥0∞) = ((6 : ℕ) : ℝ≥0∞)⁻¹ := by norm_num
    rw [unifHMeasure_eq_avg_bins, h6]
    exact pi_avg_eq_sum (by norm_num) (fun b : Fin 6 => heightBinMeasure 6 (11 / 5) b.val)
  have hcard : Fintype.card (Window 3 4 6) * (4 * 6) ^ (4 + m) = 4 ^ (7 + m) * 6 ^ (8 + m) := by
    simp only [Window, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ]
    rw [mul_pow]
    ring
  rw [hcard]
  unfold stripFullMeasure
  rw [hE, hY]
  ext s hs
  rw [Measure.prod_apply hs]
  simp only [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_finsetSum_measure]
  have hinner : ∀ gs : Fin (7 + m) → Fin 4,
      ∫⁻ x, ((((6 ^ (8 + m) : ℕ) : ℝ≥0∞)⁻¹) *
        ∑ ys : Fin (8 + m) → Fin 6, (Measure.pi fun j => heightBinMeasure 6 (11 / 5) (ys j).val) (Prod.mk x ⁻¹' s))
        ∂(Measure.pi fun j => expBinMeasure 4 (gs j).val) =
      (((6 ^ (8 + m) : ℕ) : ℝ≥0∞)⁻¹) *
        ∑ ys : Fin (8 + m) → Fin 6,
          ((Measure.pi fun j => expBinMeasure 4 (gs j).val).prod
           (Measure.pi fun j => heightBinMeasure 6 (11 / 5) (ys j).val)) s := by
    intro gs
    rw [lintegral_const_mul' _ _ (by simp)]
    congr 1
    rw [lintegral_finsetSum _ (fun ys _ => measurable_measure_prodMk_left hs)]
    apply Finset.sum_congr rfl
    intro ys _
    rw [Measure.prod_apply hs]
  simp_rw [hinner, ← Finset.mul_sum, ← mul_assoc]
  have h4ne : ((4 ^ (7 + m) : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by positivity : (4 : ℕ) ^ (7 + m) ≠ 0)
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl h4ne) (Or.inl (ENNReal.natCast_ne_top _))]
  apply congrArg ((((4 ^ (7 + m) : ℕ) : ℝ≥0∞)⁻¹ * ((6 ^ (8 + m) : ℕ) : ℝ≥0∞)⁻¹) * ·)
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp (labelSeqEquiv m) (fun q =>
    ((Measure.pi fun j => expBinMeasure 4 (q.1 j).val).prod
     (Measure.pi fun j => heightBinMeasure 6 (11 / 5) (q.2 j).val)) s)).symm

private lemma walkTableCost_eq_sum {d₁ G B : ℕ}
    (edgeCost : Fin (d₁ + 1) → (Fin (d₁ + 1) → Fin G) → (Fin (d₁ + 2) → Fin B) → ℝ) :
    ∀ {k : ℕ} (z₀ : Window d₁ G B) (w : Fin k → Label G B) (ch : Fin k → List (Fin (d₁ + 1))),
      walkTableCost edgeCost z₀ w ch =
        ∑ t : Fin k, chosenTableCost edgeCost (ch t)
          (fullGaps (runWindow z₀ (fun i : Fin t.val => w ⟨i.val, by omega⟩)) (w t))
          (fullHeights (runWindow z₀ (fun i : Fin t.val => w ⟨i.val, by omega⟩)) (w t))
  | 0, _, _, _ => by simp [walkTableCost]
  | k + 1, z₀, w, ch => by
    unfold walkTableCost
    dsimp only
    rw [walkTableCost_eq_sum edgeCost z₀ (fun i => w i.castSucc) (fun i => ch i.castSucc),
        Fin.sum_univ_castSucc]
    rfl

/-- Single-strip expected path bound: given any concave DP fixed-point certificate `(V, uBound)`
for `automaton4`, there exists a constant `C_strip` (independent of `m`) and, for every `m : ℕ`,
a measurable function `len : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) → ℝ` such that:
1. For every `(E, Y)`, there is a Hamiltonian path `P : List ℕ` visiting `{0, ..., 4 + m}`
   from `0` to `4 + m` with `listPathLen (P.map (stripPt E Y)) ≤ len (E, Y)`.
2. `len` is integrable under `stripFullMeasure m` with
   `∫ p, len p ∂(stripFullMeasure m) ≤ (m : ℝ) * uBound + C_strip`. -/
theorem strip_expected_path_le
    (V : Fin 56 → Window 3 4 6 → ℝ) (uBound : ℝ)
    (hfp : ∀ u' z', dpOp automaton4 edgeCost4 V u' z' ≤ V u' z' + uBound) :
    ∃ C_strip : ℝ, ∀ m : ℕ,
      ∃ len : ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) → ℝ,
        (∀ p, ∃ (P : List ℕ) (hne : P ≠ []),
          P.Perm (List.range (4 + m + 1)) ∧
          P.head hne = 0 ∧
          P.getLast hne = 4 + m ∧
          listPathLen (P.map (stripPt p.1 p.2)) ≤ len p) ∧
        Integrable len (stripFullMeasure m) ∧
        ∫ p, len p ∂(stripFullMeasure m) ≤ (m : ℝ) * uBound + C_strip := by
  classical
  -- Step 1: Uniform constant `C₀` for the base case `m = 0` (independent of `m`).
  let C₀ : ℝ := Finset.univ.sup' Finset.univ_nonempty fun p : Fin 56 × Window 3 4 6 =>
    ((∑ q ∈ wordsEndingAt automaton4.reachSteps p.2, optDP automaton4 edgeCost4 0 q.1 q.2 p.1) /
      (((4 * 6) ^ automaton4.reachSteps : ℕ) : ℝ)) - V p.1 p.2
  have hbase : ∀ u z',
      (∑ q ∈ wordsEndingAt automaton4.reachSteps z', optDP automaton4 edgeCost4 0 q.1 q.2 u) /
        (((4 * 6) ^ automaton4.reachSteps : ℕ) : ℝ) ≤ V u z' + C₀ := by
    intro u z'
    have hle := Finset.le_sup' (f := fun p : Fin 56 × Window 3 4 6 =>
      ((∑ q ∈ wordsEndingAt automaton4.reachSteps p.2, optDP automaton4 edgeCost4 0 q.1 q.2 p.1) /
        (((4 * 6) ^ automaton4.reachSteps : ℕ) : ℝ)) - V p.1 p.2) (Finset.mem_univ (u, z'))
    linarith
  let C_strip : ℝ := (∑ z' : Window 3 4 6, V automaton4.initIdx z') /
    (Fintype.card (Window 3 4 6) : ℝ) + C₀
  refine ⟨C_strip, fun m => ?_⟩
  -- Step 2: For each discrete bin `(z₀, w)`, choose an optimal automaton walk achieving `optDP`
  have hwalk : ∀ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6),
      ∃ (states : Fin (4 + m + 1) → Fin 56) (choices : Fin (4 + m) → List (Fin 4)),
        states 0 = automaton4.initIdx ∧
        states (Fin.last (4 + m)) = automaton4.initIdx ∧
        (∀ t : Fin (4 + m), (states t.castSucc, choices t) ∈ automaton4.preds (states t.succ)) ∧
        (∑ t : Fin (4 + m),
          chosenTableCost edgeCost4 (choices t)
            (fullGaps (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t))
            (fullHeights (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t))) =
          optDP automaton4 edgeCost4 m p.1 p.2 automaton4.initIdx := fun p => by
    obtain ⟨st, ch, h0, hl, hst, hcost⟩ := optDP_achieved automaton4 edgeCost4 m p.1 p.2 automaton4.initIdx
    exact ⟨st, ch, h0, hl, hst, by rw [← walkTableCost_eq_sum]; exact hcost⟩
  let walkStates (p : Window 3 4 6 × (Fin (4 + m) → Label 4 6)) : Fin (4 + m + 1) → Fin 56 :=
    (hwalk p).choose
  let walkChoices (p : Window 3 4 6 × (Fin (4 + m) → Label 4 6)) : Fin (4 + m) → List (Fin 4) :=
    (hwalk p).choose_spec.choose
  have hwalk_spec (p : Window 3 4 6 × (Fin (4 + m) → Label 4 6)) :=
    (hwalk p).choose_spec.choose_spec
  let walkCost (p : Window 3 4 6 × (Fin (4 + m) → Label 4 6))
      (x : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) : ℝ :=
    ∑ t : Fin (4 + m), stepCost euclidDist (stripPt x.1 x.2) t.val (walkChoices p t)
  let p0 : Window 3 4 6 × (Fin (4 + m) → Label 4 6) :=
    (((fun _ => 0), (fun _ => 0)), fun _ => (0, 0))
  let unionBins : Set ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) :=
    ⋃ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6), stripBinRect p.1 p.2
  let len (x : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) : ℝ :=
    (∑ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6), (stripBinRect p.1 p.2).indicator (walkCost p) x) +
      unionBinsᶜ.indicator (walkCost p0) x
  have hwalk_path : ∀ p x,
      ∃ (P : List ℕ) (hne : P ≠ []),
        P.Perm (List.range (4 + m + 1)) ∧
        P.head hne = 0 ∧
        P.getLast hne = 4 + m ∧
        listPathLen (P.map (stripPt x.1 x.2)) = walkCost p x := by
    intro p x
    have hsp := hwalk_spec p
    have hsp0 : walkStates p 0 = automaton4.initIdx := hsp.1
    have hspN : walkStates p (Fin.last (4 + m)) = automaton4.initIdx := hsp.2.1
    have hstep_st : ∀ t : Fin (4 + m),
        stepState (automaton4.stateOf (walkStates p t.castSucc)) (walkChoices p t) =
          some (automaton4.stateOf (walkStates p t.succ)) := fun t =>
      automaton4.preds_valid _ _ (hsp.2.2.1 t)
    have hst0 : automaton4.stateOf (walkStates p 0) = initState 4 := by
      rw [hsp0, automaton4.init_eq]
    have hstN : automaton4.stateOf (walkStates p ⟨4 + m, Nat.lt_succ_self _⟩) = initState 4 := by
      have : (⟨4 + m, Nat.lt_succ_self _⟩ : Fin (4 + m + 1)) = Fin.last (4 + m) := rfl
      rw [this, hspN, automaton4.init_eq]
    obtain ⟨P, hne, hperm, hhead, hlast, hplen⟩ :=
      walk_to_hamiltonian_path (by norm_num) euclidDist euclidDist_symm (stripPt x.1 x.2)
        (fun i => automaton4.stateOf (walkStates p i)) (walkChoices p) hst0 hstN hstep_st
    exact ⟨P, hne, hperm, hhead, hlast, by rw [listPathLen_map_eq_pathLen, hplen]⟩
  have hclaim1 : ∀ x, ∃ (P : List ℕ) (hne : P ≠ []),
      P.Perm (List.range (4 + m + 1)) ∧ P.head hne = 0 ∧ P.getLast hne = 4 + m ∧
      listPathLen (P.map (stripPt x.1 x.2)) ≤ len x := by
    intro x
    by_cases hx : x ∈ unionBins
    · obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      have hlen_eq : len x = walkCost p x := by
        unfold len
        rw [Set.indicator_of_notMem (show x ∉ unionBinsᶜ from fun h => h hx), add_zero]
        rw [Finset.sum_eq_single p
          (fun q _ hne => Set.indicator_of_notMem
            (fun hq => Set.disjoint_left.mp (stripBinRect_disjoint hne) hq hp) _)
          (fun h => absurd (Finset.mem_univ p) h)]
        rw [Set.indicator_of_mem hp]
      obtain ⟨P, hne, hperm, hhead, hlast, hplen⟩ := hwalk_path p x
      exact ⟨P, hne, hperm, hhead, hlast, by rw [hplen, hlen_eq]⟩
    · have hlen_eq : len x = walkCost p0 x := by
        unfold len
        have hzero : ∀ q : Window 3 4 6 × (Fin (4 + m) → Label 4 6), x ∉ stripBinRect q.1 q.2 :=
          fun q hq => hx (mem_iUnion.mpr ⟨q, hq⟩)
        have hsum0 : (∑ q : Window 3 4 6 × (Fin (4 + m) → Label 4 6),
            (stripBinRect q.1 q.2).indicator (walkCost q) x) = 0 :=
          Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (hzero q) _
        rw [hsum0, zero_add, Set.indicator_of_mem (show x ∈ unionBinsᶜ from hx)]
      obtain ⟨P, hne, hperm, hhead, hlast, hplen⟩ := hwalk_path p0 x
      exact ⟨P, hne, hperm, hhead, hlast, by rw [hplen, hlen_eq]⟩
  have hbin_bound : ∀ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6),
      Integrable len (stripBinMeasure p.1 p.2) ∧
      ∫ x, len x ∂(stripBinMeasure p.1 p.2) ≤ optDP automaton4 edgeCost4 m p.1 p.2 automaton4.initIdx := by
    intro p
    have hsp := hwalk_spec p
    have hsp0 : walkStates p 0 = automaton4.initIdx := hsp.1
    have hact : ∀ (t : Fin (4 + m)) (v : Fin 4), v ∈ walkChoices p t → 4 - v.val ≤ t.val + 1 :=
      walk_chosen_active (by norm_num) (fun i => automaton4.stateOf (walkStates p i)) (walkChoices p)
        (by rw [hsp0, automaton4.init_eq])
        (fun t => automaton4.preds_valid _ _ (hsp.2.2.1 t))
    have hstep_int_le : ∀ t : Fin (4 + m),
        Integrable (fun x => stepCost euclidDist (stripPt x.1 x.2) t.val (walkChoices p t)) (stripBinMeasure p.1 p.2) ∧
        ∫ x, stepCost euclidDist (stripPt x.1 x.2) t.val (walkChoices p t) ∂(stripBinMeasure p.1 p.2) ≤
          chosenTableCost edgeCost4 (walkChoices p t)
            (fullGaps (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t))
            (fullHeights (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t)) := by
      intro t
      have hlist : ∀ (l : List (Fin 4)), (∀ v ∈ l, 4 - v.val ≤ t.val + 1) →
          Integrable (fun x => stepCost euclidDist (stripPt x.1 x.2) t.val l) (stripBinMeasure p.1 p.2) ∧
          ∫ x, stepCost euclidDist (stripPt x.1 x.2) t.val l ∂(stripBinMeasure p.1 p.2) ≤
            chosenTableCost edgeCost4 l
              (fullGaps (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t))
              (fullHeights (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t)) := by
        intro l
        induction l with
        | nil =>
          intro _
          simp [stepCost, chosenTableCost]
        | cons v rest ih =>
          intro hl
          obtain ⟨hint_v, hle_v⟩ := strip_edge_integral_le p.1 p.2 t v (hl v (List.mem_cons_self ..))
          obtain ⟨hint_r, hle_r⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
          have hstep_cons : (fun x : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) =>
                stepCost euclidDist (stripPt x.1 x.2) t.val (v :: rest)) =
              fun x => euclidDist (stripPt x.1 x.2 (t.val + 1 - (4 - v.val))) (stripPt x.1 x.2 (t.val + 1)) +
                stepCost euclidDist (stripPt x.1 x.2) t.val rest := by
            funext x; simp [stepCost]
          rw [hstep_cons]
          refine ⟨hint_v.add hint_r, ?_⟩
          rw [integral_add hint_v hint_r]
          change _ ≤ edgeCost4 v (fullGaps (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t))
              (fullHeights (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t)) +
            chosenTableCost edgeCost4 rest
              (fullGaps (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t))
              (fullHeights (runWindow p.1 (fun i : Fin t.val => p.2 ⟨i.val, by omega⟩)) (p.2 t))
          linarith
      exact hlist (walkChoices p t) (hact t)
    have hwc_int : Integrable (walkCost p) (stripBinMeasure p.1 p.2) :=
      integrable_finsetSum _ fun t _ => (hstep_int_le t).1
    have hwc_le : ∫ x, walkCost p x ∂(stripBinMeasure p.1 p.2) ≤
        optDP automaton4 edgeCost4 m p.1 p.2 automaton4.initIdx := by
      rw [← hsp.2.2.2]
      unfold walkCost
      rw [integral_finsetSum _ fun t _ => (hstep_int_le t).1]
      exact Finset.sum_le_sum fun t _ => (hstep_int_le t).2
    have hae : len =ᵐ[stripBinMeasure p.1 p.2] walkCost p := by
      filter_upwards [ae_mem_stripBinRect p.1 p.2] with x hx
      have hxu : x ∈ unionBins := mem_iUnion.mpr ⟨p, hx⟩
      unfold len
      rw [Set.indicator_of_notMem (show x ∉ unionBinsᶜ from fun h => h hxu), add_zero]
      rw [Finset.sum_eq_single p
        (fun q _ hne => Set.indicator_of_notMem
          (fun hq => Set.disjoint_left.mp (stripBinRect_disjoint hne) hq hx) _)
        (fun h => absurd (Finset.mem_univ p) h)]
      rw [Set.indicator_of_mem hx]
    exact ⟨hwc_int.congr hae.symm, by rw [integral_congr_ae hae]; exact hwc_le⟩
  let N_tot : ℕ := Fintype.card (Window 3 4 6) * (4 * 6) ^ (4 + m)
  have hN_pos : 0 < N_tot := by
    dsimp only [N_tot, Window]
    simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    positivity
  have hN_ne : (N_tot : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N_tot ≠ 0)
  have hN_top : ((N_tot : ℝ≥0∞)⁻¹) ≠ ⊤ := ENNReal.inv_ne_top.mpr hN_ne
  have hlen_sum_int : Integrable len (∑ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6), stripBinMeasure p.1 p.2) :=
    integrable_finsetSum_measure.mpr fun p _ => (hbin_bound p).1
  have hlen_full_int : Integrable len (stripFullMeasure m) := by
    rw [stripFullMeasure_eq_avg m]
    exact hlen_sum_int.smul_measure hN_top
  refine ⟨len, hclaim1, hlen_full_int, ?_⟩
  rw [stripFullMeasure_eq_avg m, integral_smul_measure, integral_finsetSum_measure (fun p _ => (hbin_bound p).1)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, inv_mul_eq_div]
  have hsum_le : (∑ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6), ∫ x, len x ∂(stripBinMeasure p.1 p.2)) / (N_tot : ℝ) ≤
      (∑ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6), optDP automaton4 edgeCost4 m p.1 p.2 automaton4.initIdx) / (N_tot : ℝ) :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun p _ => (hbin_bound p).2) (Nat.cast_nonneg _)
  refine hsum_le.trans ?_
  have hdp := concave_dp_total_bound (by norm_num : 0 < 3) (by norm_num : 0 < 4) (by norm_num : 0 < 6)
    automaton4 edgeCost4 V uBound C₀ hfp hbase m automaton4.initIdx
  have hdp' : (∑ p : Window 3 4 6 × (Fin (4 + m) → Label 4 6),
        optDP automaton4 edgeCost4 m p.1 p.2 automaton4.initIdx) / (N_tot : ℝ) ≤
      (∑ z' : Window 3 4 6, V automaton4.initIdx z') / (Fintype.card (Window 3 4 6) : ℝ) +
        (m : ℝ) * uBound + C₀ := hdp
  dsimp only [C_strip]
  linarith

end BHHBounds.Upper
