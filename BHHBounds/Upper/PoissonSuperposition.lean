import BHHBounds.Upper.PoissonRenewal

/-!
# Superposition of strips

The unit square is cut into `M` strips, so `unitSquarePi r` is a sum over assignments of the points
to strips. `multi_strip_hist_sum` matches the `M`-strip renewal integral with the Poisson-weighted
sum over assignments with a given histogram, and `bad_assignments_poisson_sum_le` bounds the
assignments that overfill a strip.
-/

namespace BHHBounds.Upper

open MeasureTheory Set Finset BigOperators
open scoped ENNReal NNReal

local instance : IsProbabilityMeasure exp1Measure := isProbabilityMeasure_exp1Measure
local instance : IsProbabilityMeasure unifHMeasure := isProbabilityMeasure_unifHMeasure

/-! ## Section 1: Strip Partition of `unitSquareMeasure` and `unitSquarePi` -/

lemma Ioc_zero_one_eq_union_strips {M : ℕ} (hM : 0 < M) :
    Ioc (0 : ℝ) 1 = ⋃ s : Fin M, Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  ext y
  simp only [Set.mem_Ioc, Set.mem_iUnion]
  constructor
  · rintro ⟨hy0, hy1⟩
    let k : ℕ := Nat.ceil ((M : ℝ) * y) - 1
    have hMy_pos : 0 < (M : ℝ) * y := mul_pos hMpos hy0
    have hceil_pos : 1 ≤ Nat.ceil ((M : ℝ) * y) := Nat.ceil_pos.mpr hMy_pos
    have hceil_le : Nat.ceil ((M : ℝ) * y) ≤ M := Nat.ceil_le.mpr (by nlinarith)
    have hk_lt : k < M := by omega
    refine ⟨⟨k, hk_lt⟩, ?_, ?_⟩
    · rw [div_lt_iff₀ hMpos]
      have hk1 : k < Nat.ceil ((M : ℝ) * y) := by omega
      have hlt : (k : ℝ) < (M : ℝ) * y := by
        by_contra hle
        push Not at hle
        have := Nat.ceil_le.mpr hle
        omega
      linarith
    · rw [le_div_iff₀ hMpos]
      have hk_eq : ((k : ℝ) + 1) = (Nat.ceil ((M : ℝ) * y) : ℝ) := by
        exact_mod_cast (by omega : k + 1 = Nat.ceil ((M : ℝ) * y))
      rw [hk_eq]
      have := Nat.le_ceil ((M : ℝ) * y)
      linarith
  · rintro ⟨s, hs1, hs2⟩
    have hs0 : (0 : ℝ) ≤ (s.val : ℝ) / (M : ℝ) := div_nonneg (Nat.cast_nonneg _) (le_of_lt hMpos)
    have hsM : ((s.val : ℝ) + 1) / (M : ℝ) ≤ 1 := by
      rw [div_le_one hMpos]
      exact_mod_cast s.isLt
    exact ⟨lt_of_le_of_lt hs0 hs1, le_trans hs2 hsM⟩

lemma stripIoc_pairwiseDisjoint {M : ℕ} (hM : 0 < M) :
    Pairwise (Function.onFun Disjoint fun s : Fin M =>
      Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  intro s1 s2 hne
  rw [Function.onFun, Set.disjoint_left]
  intro y hy1 hy2
  simp only [Set.mem_Ioc, div_lt_iff₀ hMpos, le_div_iff₀ hMpos] at hy1 hy2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have : (s1.val : ℝ) + 1 ≤ (s2.val : ℝ) := by exact_mod_cast hlt
    nlinarith
  · have : (s2.val : ℝ) + 1 ≤ (s1.val : ℝ) := by exact_mod_cast hlt
    nlinarith

lemma unitSquareMeasure_eq_sum_stripBox {M : ℕ} (hM : 0 < M) :
    unitSquareMeasure = ∑ s : Fin M, stripBoxMeasure M s := by
  unfold unitSquareMeasure stripBoxMeasure
  have hIcc : volume.restrict (Icc (0 : ℝ) 1) = volume.restrict (Ioc (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  rw [hIcc]
  have hsum_y : volume.restrict (Ioc (0 : ℝ) 1) =
      ∑ s : Fin M, volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))) := by
    ext A hA
    rw [Measure.finsetSum_apply]
    simp_rw [Measure.restrict_apply hA]
    rw [Ioc_zero_one_eq_union_strips hM, Set.inter_iUnion]
    have hdisj : Pairwise (Function.onFun Disjoint fun s : Fin M =>
        A ∩ Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))) := by
      intro s1 s2 hne
      exact (stripIoc_pairwiseDisjoint hM hne).mono Set.inter_subset_right Set.inter_subset_right
    rw [measure_iUnion hdisj (fun s => hA.inter measurableSet_Ioc), tsum_fintype]
  let μx : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  change μx.prod (volume.restrict (Ioc (0 : ℝ) 1)) =
    ∑ s : Fin M, μx.prod (volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))))
  rw [hsum_y]
  haveI : IsFiniteMeasure μx := by dsimp only [μx]; constructor; simp [Real.volume_Ioc]
  haveI : ∀ s : Fin M, IsFiniteMeasure (volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) :=
    fun s => by constructor; simp [Real.volume_Ioc]
  haveI : IsFiniteMeasure (∑ s : Fin M, volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))) := by
    rw [← hsum_y]; infer_instance
  haveI : IsFiniteMeasure (∑ s : Fin M, μx.prod
      (volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ))))) := by
    constructor
    rw [Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun s _ => measure_lt_top _ _
  refine Measure.prod_eq fun A B hA hB => ?_
  rw [Measure.finsetSum_apply, Measure.finsetSum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact Measure.prod_prod _ _

lemma unitSquarePi_eq_sum_assignments {M : ℕ} (hM : 0 < M) (r : ℕ) :
    unitSquarePi r = ∑ a : Fin r → Fin M, Measure.pi (fun i : Fin r => stripBoxMeasure M (a i)) := by
  unfold unitSquarePi
  haveI : ∀ a : Fin r → Fin M, IsFiniteMeasure (Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) :=
    fun _ => inferInstance
  haveI : IsFiniteMeasure (∑ a : Fin r → Fin M, Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) := by
    constructor
    rw [Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun a _ => measure_lt_top _ _
  refine Measure.pi_eq fun A hA => ?_
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.pi_pi, unitSquareMeasure_eq_sum_stripBox hM, Measure.finsetSum_apply]
  exact (Fintype.prod_sum (fun i s => stripBoxMeasure M s (A i))).symm

/-! ## Section 2: Histogram Combinatorics & Multinomial Identity -/

/-- Histogram of an assignment `a : Fin r → Fin M`. -/
def hist {r M : ℕ} (a : Fin r → Fin M) (s : Fin M) : ℕ :=
  (Finset.univ.filter fun i : Fin r => a i = s).card

lemma sum_hist {r M : ℕ} (a : Fin r → Fin M) : ∑ s : Fin M, hist a s = r := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin r)))
    (t := (Finset.univ : Finset (Fin M))) (f := a) (fun i _ => Finset.mem_univ (a i))
  simpa [hist] using h.symm

/-- Multinomial coefficient identity: the number of `a : Fin r → Fin M` with histogram `k`
(where `∑ s, k s = r`) satisfies `card * ∏ s, (k s)! = r!`. -/
lemma card_hist_mul_fact :
    ∀ (M r : ℕ) (k : Fin M → ℕ), (∑ s : Fin M, k s = r) →
      (Finset.univ.filter fun a : Fin r → Fin M => hist a = k).card *
        (∏ s : Fin M, (k s).factorial) = r.factorial
  | 0, r, k, hr => by
    have hr0 : r = 0 := by simpa using hr.symm
    subst hr0
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Nat.factorial_zero]
    have hcard : (Finset.univ.filter fun a : Fin 0 → Fin 0 => hist a = k).card = 1 := by
      have huniv : (Finset.univ.filter fun a : Fin 0 → Fin 0 => hist a = k) = Finset.univ := by
        ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        funext s; exact Fin.elim0 s
      rw [huniv, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; rfl
    exact hcard
  | M + 1, r, k, hr => by
    let q : ℕ := k (Fin.last M)
    let k' : Fin M → ℕ := fun s => k s.castSucc
    have hr_split : (∑ s : Fin M, k' s) + q = r := by
      simpa [k', q, Fin.sum_univ_castSucc] using hr
    have hq_le : q ≤ r := by omega
    let r' : ℕ := r - q
    have hr'_eq : ∑ s : Fin M, k' s = r' := by omega
    -- Partition `{a | hist a = k}` by `S := {i : Fin r | a i = Fin.last M} ∈ powersetCard q univ`
    let good : Finset (Fin r → Fin (M + 1)) := Finset.univ.filter fun a => hist a = k
    let fiber (S : Finset (Fin r)) : Finset (Fin r → Fin (M + 1)) :=
      good.filter fun a => (Finset.univ.filter fun i => a i = Fin.last M) = S
    have hpart : good.card = ∑ S ∈ Finset.powersetCard q (Finset.univ : Finset (Fin r)), (fiber S).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext a
        simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and,
          fiber, Finset.mem_filter]
        constructor
        · intro ha
          refine ⟨Finset.univ.filter fun i => a i = Fin.last M, ?_, ha, rfl⟩
          have hhk : hist a = k := (Finset.mem_filter.mp ha).2
          simpa [hist, q] using congrFun hhk (Fin.last M)
        · rintro ⟨_, _, ha, _⟩; exact ha
      · intro S1 _ S2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro a ha1 ha2
        exact hne ((Finset.mem_filter.mp ha1).2.symm.trans (Finset.mem_filter.mp ha2).2)
    -- Every `S ∈ powersetCard q univ` has the same fiber size `card(M, r', k')`.
    have hfiber_card : ∀ S ∈ Finset.powersetCard q (Finset.univ : Finset (Fin r)),
        (fiber S).card = (Finset.univ.filter fun b : Fin r' → Fin M => hist b = k').card := by
      intro S hS
      have hScard : S.card = q := (Finset.mem_powersetCard.mp hS).2
      have hcompl_card : Sᶜ.card = r' := by
        rw [Finset.card_compl, Fintype.card_fin, hScard]
      let eC : Fin r' ≃ {i : Fin r // i ∈ Sᶜ} :=
        (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcompl_card])).symm
      refine Finset.card_bij
        (fun a ha => fun j : Fin r' =>
          let i := (eC j).1
          let hne : a i ≠ Fin.last M := by
            have hfib := (Finset.mem_filter.mp ha).2
            intro heq
            have hiS : i ∈ S := by
              rw [← hfib]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
            exact (Finset.mem_compl.mp (eC j).2) hiS
          ⟨(a i).val, by have := (a i).isLt; have : (a i).val ≠ M := fun h => hne (Fin.ext h); omega⟩)
        ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hhk : hist a = k := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
        have hfib : (Finset.univ.filter fun i => a i = Fin.last M) = S := (Finset.mem_filter.mp ha).2
        funext s
        have hs_eq := congrFun hhk s.castSucc
        dsimp only [hist, k'] at hs_eq ⊢
        rw [← hs_eq]
        refine Finset.card_bij (fun j _ => (eC j).1) ?_ ?_ ?_
        · intro j hj
          have hj' := (Finset.mem_filter.mp hj).2
          have hval : (a (eC j).1).val = s.val := congrArg Fin.val hj'
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext hval⟩
        · intro j1 _ j2 _ heq
          exact eC.injective (Subtype.ext heq)
        · intro i hi
          have hai : a i = s.castSucc := (Finset.mem_filter.mp hi).2
          have hiC : i ∈ Sᶜ := by
            rw [Finset.mem_compl, ← hfib, Finset.mem_filter]
            rintro ⟨_, hlast⟩
            have : s.val = M := by simpa [hai] using congrArg Fin.val hlast
            omega
          refine ⟨eC.symm ⟨i, hiC⟩, ?_, by simp⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          apply Fin.ext; simp [hai]
      · intro a1 ha1 a2 ha2 heq
        have hfib1 : (Finset.univ.filter fun i => a1 i = Fin.last M) = S := (Finset.mem_filter.mp ha1).2
        have hfib2 : (Finset.univ.filter fun i => a2 i = Fin.last M) = S := (Finset.mem_filter.mp ha2).2
        funext i
        by_cases hiS : i ∈ S
        · have h1' : i ∈ Finset.univ.filter fun i => a1 i = Fin.last M := hfib1.symm ▸ hiS
          have h2' : i ∈ Finset.univ.filter fun i => a2 i = Fin.last M := hfib2.symm ▸ hiS
          have h1 : a1 i = Fin.last M := (Finset.mem_filter.mp h1').2
          have h2 : a2 i = Fin.last M := (Finset.mem_filter.mp h2').2
          rw [h1, h2]
        · have hiC : i ∈ Sᶜ := Finset.mem_compl.mpr hiS
          have hj := congrArg Fin.val (congrFun heq (eC.symm ⟨i, hiC⟩))
          simp only [Equiv.apply_symm_apply] at hj
          exact Fin.ext hj
      · intro b hb
        have hhb : hist b = k' := (Finset.mem_filter.mp hb).2
        let a : Fin r → Fin (M + 1) := fun i =>
          if h : i ∈ Sᶜ then (b (eC.symm ⟨i, h⟩)).castSucc else Fin.last M
        have hfib_a : (Finset.univ.filter fun i => a i = Fin.last M) = S := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
          by_cases hiS : i ∈ S
          · have hnot : i ∉ Sᶜ := by simp [hiS]
            simp [hnot, hiS]
          · have hiC : i ∈ Sᶜ := Finset.mem_compl.mpr hiS
            simp only [hiC, ↓reduceDIte, hiS, iff_false]
            intro heq
            have : (b (eC.symm ⟨i, hiC⟩)).val = M := congrArg Fin.val heq
            omega
        have hhist_a : hist a = k := by
          funext s
          refine Fin.lastCases ?_ (fun s' => ?_) s
          · dsimp only [hist]; rw [hfib_a, hScard]
          · have hbs' := congrFun hhb s'
            dsimp only [hist, k'] at hbs' ⊢
            rw [← hbs']
            refine Finset.card_bij
              (fun i hi =>
                have hiC : i ∈ Sᶜ := by
                  rw [Finset.mem_compl, ← hfib_a, Finset.mem_filter]
                  rintro ⟨_, hlast⟩
                  have h1 := (Finset.mem_filter.mp hi).2
                  have : s'.val = M := by simpa [h1] using congrArg Fin.val hlast
                  omega
                eC.symm ⟨i, hiC⟩)
              ?_ ?_ ?_
            · intro i hi
              have h1 := (Finset.mem_filter.mp hi).2
              have hiC : i ∈ Sᶜ := by
                rw [Finset.mem_compl, ← hfib_a, Finset.mem_filter]
                rintro ⟨_, hlast⟩
                have : s'.val = M := by simpa [h1] using congrArg Fin.val hlast
                omega
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              dsimp only [a] at h1
              rw [dif_pos hiC] at h1
              exact Fin.ext (by simpa using congrArg Fin.val h1)
            · intro i1 _ i2 _ heq
              have := congrArg (fun x => (eC x).1) heq
              simpa using this
            · intro j hj
              have hbj : b j = s' := (Finset.mem_filter.mp hj).2
              refine ⟨(eC j).1, ?_, by simp⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, a, (eC j).2, ↓reduceDIte,
                Subtype.coe_eta, Equiv.symm_apply_apply, hbj]
        refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhist_a⟩, hfib_a⟩, ?_⟩
        funext j
        apply Fin.ext
        have hnot : (eC j).1 ∉ S := Finset.mem_compl.mp (eC j).2
        simp [a, hnot]
    rw [hpart, Finset.sum_congr rfl hfiber_card, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fin.prod_univ_castSucc]
    have hih := card_hist_mul_fact M r' k' hr'_eq
    have hchoose := Nat.choose_mul_factorial_mul_factorial hq_le
    calc r.choose q * (Finset.univ.filter fun b : Fin r' → Fin M => hist b = k').card *
          ((∏ s : Fin M, (k' s).factorial) * q.factorial)
        = (r.choose q * q.factorial) *
            ((Finset.univ.filter fun b : Fin r' → Fin M => hist b = k').card *
              ∏ s : Fin M, (k' s).factorial) := by ring
      _ = r.choose q * q.factorial * r'.factorial := by rw [hih]
      _ = r.choose q * q.factorial * (r - q).factorial := rfl
      _ = r.factorial := by linarith

/-- Number of assignments `a : Fin r → Fin M` with `hist a s₀ = j`. -/
lemma card_hist_single {r M : ℕ} (s₀ : Fin M) (j : ℕ) (_ : j ≤ r) :
    (Finset.univ.filter fun a : Fin r → Fin M => hist a s₀ = j).card =
      r.choose j * (M - 1) ^ (r - j) := by
  let good := Finset.univ.filter fun a : Fin r → Fin M => hist a s₀ = j
  let fiber (S : Finset (Fin r)) :=
    good.filter fun a => (Finset.univ.filter fun i => a i = s₀) = S
  have hpart : good.card = ∑ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin r)), (fiber S).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext a
      simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and,
        fiber, Finset.mem_filter, good]
      constructor
      · intro ha; exact ⟨Finset.univ.filter fun i => a i = s₀, ha.2, ha, rfl⟩
      · rintro ⟨_, _, ha, _⟩; exact ha
    · intro S1 _ S2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha1 ha2
      exact hne ((Finset.mem_filter.mp ha1).2.symm.trans (Finset.mem_filter.mp ha2).2)
  have hfib : ∀ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin r)),
      (fiber S).card = (M - 1) ^ (r - j) := by
    intro S hS
    have hScard : S.card = j := (Finset.mem_powersetCard.mp hS).2
    have hCcard : Sᶜ.card = r - j := by rw [Finset.card_compl, Fintype.card_fin, hScard]
    have hMcard : Fintype.card {s : Fin M // s ≠ s₀} = M - 1 := by
      have : Fintype.card {s : Fin M // s ≠ s₀} = (Finset.univ.erase s₀).card := by
        rw [← Fintype.card_coe]; apply Fintype.card_congr
        exact ⟨fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩,
               fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩, fun _ => rfl, fun _ => rfl⟩
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hbij : (fiber S).card = Fintype.card ({i : Fin r // i ∈ Sᶜ} → {s : Fin M // s ≠ s₀}) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij
        (fun a ha => fun i : {i : Fin r // i ∈ Sᶜ} =>
          ⟨a i.1, fun heq => by
            have hfibS := (Finset.mem_filter.mp ha).2
            have hiS : i.1 ∈ S :=
              Eq.mp (congrArg (fun T : Finset (Fin r) => i.1 ∈ T) hfibS)
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
            exact (Finset.mem_compl.mp i.2) hiS⟩)
        (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro a1 ha1 a2 ha2 heq
        have h1 := (Finset.mem_filter.mp ha1).2
        have h2 := (Finset.mem_filter.mp ha2).2
        funext i
        by_cases hiS : i ∈ S
        · have h1' : i ∈ Finset.univ.filter fun i => a1 i = s₀ := h1.symm ▸ hiS
          have h2' : i ∈ Finset.univ.filter fun i => a2 i = s₀ := h2.symm ▸ hiS
          exact ((Finset.mem_filter.mp h1').2).trans ((Finset.mem_filter.mp h2').2).symm
        · exact congrArg Subtype.val (congrFun heq ⟨i, Finset.mem_compl.mpr hiS⟩)
      · intro b _
        let a : Fin r → Fin M := fun i => if h : i ∈ Sᶜ then (b ⟨i, h⟩).1 else s₀
        have hfa : (Finset.univ.filter fun i => a i = s₀) = S := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
          by_cases hiS : i ∈ S
          · have hnot : i ∉ Sᶜ := by simp [hiS]
            simp [hnot, hiS]
          · have hiC : i ∈ Sᶜ := Finset.mem_compl.mpr hiS
            simp [hiC, hiS, (b ⟨i, hiC⟩).2]
        refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            dsimp only [hist]; rw [hfa, hScard]⟩, hfa⟩, ?_⟩
        funext x
        apply Subtype.ext
        dsimp only [a]
        rw [dif_pos x.2]
    rw [hbij, Fintype.card_fun, hMcard, Fintype.card_coe, hCcard]
  rw [hpart, Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Union bound on the Poisson-weighted sum of bad assignments (`∃ s, hist a s ≥ N₀`) over `r ∈ Icc n R`. -/
lemma bad_assignments_poisson_sum_le {M : ℕ} (hM : 0 < M) {μ : ℝ} (hμ : 0 ≤ μ) (N₀ n R : ℕ) :
    ∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r *
        (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, N₀ ≤ hist a s).card : ℝ) / (M : ℝ) ^ r) ≤
      (M : ℝ) * ∑ j ∈ Finset.Icc N₀ R, poissonProb μ j := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  -- Step 1: Bound the bad count for each `r` by `∑ s : Fin M, ∑ j ∈ Icc N₀ r, r.choose j * (M - 1)^(r - j)`
  have hcard_le : ∀ r : ℕ,
      ((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, N₀ ≤ hist a s).card : ℝ) ≤
        (M : ℝ) * ∑ j ∈ Finset.Icc N₀ r, (r.choose j : ℝ) * ((M - 1 : ℕ) : ℝ) ^ (r - j) := by
    intro r
    have hsub : (Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, N₀ ≤ hist a s) ⊆
        Finset.univ.biUnion fun s : Fin M =>
          (Finset.Icc N₀ r).biUnion fun j =>
            Finset.univ.filter fun a : Fin r → Fin M => hist a s = j := by
      intro a ha
      obtain ⟨s, hs⟩ := (Finset.mem_filter.mp ha).2
      refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨hist a s, ?_, ?_⟩⟩
      · refine Finset.mem_Icc.mpr ⟨hs, ?_⟩
        calc hist a s ≤ ∑ s' : Fin M, hist a s' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
          _ = r := sum_hist a
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hnat : (Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, N₀ ≤ hist a s).card ≤
        M * ∑ j ∈ Finset.Icc N₀ r, r.choose j * (M - 1) ^ (r - j) := by
      calc (Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, N₀ ≤ hist a s).card
          ≤ ∑ s : Fin M, ∑ j ∈ Finset.Icc N₀ r, (Finset.univ.filter fun a : Fin r → Fin M => hist a s = j).card :=
            (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans
              (Finset.sum_le_sum fun s _ => Finset.card_biUnion_le))
        _ = ∑ s : Fin M, ∑ j ∈ Finset.Icc N₀ r, r.choose j * (M - 1) ^ (r - j) :=
            Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j hj =>
              card_hist_single s j (Finset.mem_Icc.mp hj).2
        _ = M * ∑ j ∈ Finset.Icc N₀ r, r.choose j * (M - 1) ^ (r - j) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact_mod_cast hnat
  -- Step 2: Substitute and swap the sums over `r` and `j`
  have hstep1 : ∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r *
        (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, N₀ ≤ hist a s).card : ℝ) / (M : ℝ) ^ r) ≤
      (M : ℝ) * ∑ r ∈ Finset.Icc n R, ∑ j ∈ Finset.Icc N₀ r,
        poissonProb ((M : ℝ) * μ) r * ((r.choose j : ℝ) * ((M - 1 : ℕ) : ℝ) ^ (r - j) / (M : ℝ) ^ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [Finset.mul_sum]
    have hnn : 0 ≤ poissonProb ((M : ℝ) * μ) r := poissonProb_nonneg (mul_nonneg (le_of_lt hMpos) hμ) r
    have hdiv := div_le_div_of_nonneg_right (hcard_le r) (pow_nonneg (le_of_lt hMpos) r)
    calc poissonProb ((M : ℝ) * μ) r *
          (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, N₀ ≤ hist a s).card : ℝ) / (M : ℝ) ^ r)
        ≤ poissonProb ((M : ℝ) * μ) r *
          (((M : ℝ) * ∑ j ∈ Finset.Icc N₀ r, (r.choose j : ℝ) * ((M - 1 : ℕ) : ℝ) ^ (r - j)) / (M : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left hdiv hnn
      _ = ∑ j ∈ Finset.Icc N₀ r, (M : ℝ) *
          (poissonProb ((M : ℝ) * μ) r * ((r.choose j : ℝ) * ((M - 1 : ℕ) : ℝ) ^ (r - j) / (M : ℝ) ^ r)) := by
          rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
  refine hstep1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hMpos)
  -- For `j ≤ r`, the summand equals `poissonProb μ j * poissonProb ((M - 1) * μ) (r - j)`.
  have halg : ∀ r j : ℕ, j ≤ r →
      poissonProb ((M : ℝ) * μ) r * ((r.choose j : ℝ) * ((M - 1 : ℕ) : ℝ) ^ (r - j) / (M : ℝ) ^ r) =
        poissonProb μ j * poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) := by
    intro r j hj
    unfold poissonProb
    have hMcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by exact_mod_cast (by omega : M - 1 + 1 = M)
    have hexp : Real.exp (-((M : ℝ) * μ)) = Real.exp (-μ) * Real.exp (-(((M - 1 : ℕ) : ℝ) * μ)) := by
      rw [← Real.exp_add]; congr 1; nlinarith
    have hchoose : (r.choose j : ℝ) * (j.factorial : ℝ) * ((r - j).factorial : ℝ) = (r.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
    have hpow_r : ((M : ℝ) * μ) ^ r = (M : ℝ) ^ r * μ ^ j * μ ^ (r - j) := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
    have hMne : (M : ℝ) ^ r ≠ 0 := pow_ne_zero r (ne_of_gt hMpos)
    have hrf : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    have hjf : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hqf : ((r - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (r - j))
    have hch_ne : (r.choose j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hj).ne'
    rw [hexp, hpow_r, mul_pow, ← hchoose]
    field_simp
  -- Widen `r ∈ Icc n R` to `r ∈ Icc 0 R` (nonnegative terms) and swap sums.
  have hwid : ∑ r ∈ Finset.Icc n R, ∑ j ∈ Finset.Icc N₀ r,
        poissonProb ((M : ℝ) * μ) r * ((r.choose j : ℝ) * ((M - 1 : ℕ) : ℝ) ^ (r - j) / (M : ℝ) ^ r) ≤
      ∑ r ∈ Finset.Icc 0 R, ∑ j ∈ Finset.Icc N₀ r,
        poissonProb μ j * poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) := by
    have hsub : Finset.Icc n R ⊆ Finset.Icc 0 R := fun r hr =>
      Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hr).2⟩
    calc ∑ r ∈ Finset.Icc n R, ∑ j ∈ Finset.Icc N₀ r,
          poissonProb ((M : ℝ) * μ) r * ((r.choose j : ℝ) * ((M - 1 : ℕ) : ℝ) ^ (r - j) / (M : ℝ) ^ r)
        = ∑ r ∈ Finset.Icc n R, ∑ j ∈ Finset.Icc N₀ r,
          poissonProb μ j * poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) :=
            Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j hj => halg r j (Finset.mem_Icc.mp hj).2
      _ ≤ ∑ r ∈ Finset.Icc 0 R, ∑ j ∈ Finset.Icc N₀ r,
          poissonProb μ j * poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ =>
              Finset.sum_nonneg fun j _ =>
                mul_nonneg (poissonProb_nonneg hμ j) (poissonProb_nonneg (by positivity) _)
  refine hwid.trans ?_
  have hswap : ∑ r ∈ Finset.Icc 0 R, ∑ j ∈ Finset.Icc N₀ r,
        poissonProb μ j * poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) =
      ∑ j ∈ Finset.Icc N₀ R, poissonProb μ j *
        ∑ r ∈ Finset.Icc j R, poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) := by
    have h1 : ∀ r ∈ Finset.Icc 0 R, ∑ j ∈ Finset.Icc N₀ r,
        poissonProb μ j * poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) =
        ∑ j ∈ Finset.Icc N₀ R, if j ≤ r then poissonProb μ j * poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) else 0 := by
      intro r hr
      have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext j; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext r; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  rw [hswap]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjR : j ≤ R := (Finset.mem_Icc.mp hj).2
  have hsub1 : ∑ r ∈ Finset.Icc j R, poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) ≤ 1 := by
    have hbij : ∑ r ∈ Finset.Icc j R, poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j) =
        ∑ q ∈ Finset.Icc 0 (R - j), poissonProb (((M - 1 : ℕ) : ℝ) * μ) q := by
      refine Finset.sum_bij (fun r _ => r - j) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
      · intro r1 hr1 r2 hr2 heq; simp only [Finset.mem_Icc] at hr1 hr2; omega
      · intro q hq; simp only [Finset.mem_Icc] at hq
        exact ⟨q + j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    rw [hbij]
    exact sum_poissonProb_le_one (by positivity) _
  calc poissonProb μ j * ∑ r ∈ Finset.Icc j R, poissonProb (((M - 1 : ℕ) : ℝ) * μ) (r - j)
      ≤ poissonProb μ j * 1 := mul_le_mul_of_nonneg_left hsub1 (poissonProb_nonneg hμ j)
    _ = poissonProb μ j := mul_one _

/-! ## Section 3: Multi-Strip Renewal Superposition & Histogram Identity -/

/-- General product-over-sum measure-preserving split for `Measure.pi`. -/
lemma measurePreserving_pi_sum {α : Type*} [MeasurableSpace α] {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂] (μ₁ : ι₁ → Measure α) (μ₂ : ι₂ → Measure α)
    [∀ i, IsFiniteMeasure (μ₁ i)] [∀ j, IsFiniteMeasure (μ₂ j)] :
    MeasurePreserving (fun p : (ι₁ → α) × (ι₂ → α) => Sum.elim p.1 p.2)
      ((Measure.pi μ₁).prod (Measure.pi μ₂))
      (Measure.pi (Sum.elim μ₁ μ₂)) := by
  have hmeas : Measurable (fun p : (ι₁ → α) × (ι₂ → α) => Sum.elim p.1 p.2) := by
    refine measurable_pi_lambda _ fun x => ?_
    cases x with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr j => exact (measurable_pi_apply j).comp measurable_snd
  haveI : ∀ x : ι₁ ⊕ ι₂, IsFiniteMeasure (Sum.elim μ₁ μ₂ x) := fun x => by
    cases x with
    | inl i => simpa using (inferInstance : IsFiniteMeasure (μ₁ i))
    | inr j => simpa using (inferInstance : IsFiniteMeasure (μ₂ j))
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun A hA => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hA)]
  have hpre : (fun p : (ι₁ → α) × (ι₂ → α) => Sum.elim p.1 p.2) ⁻¹' Set.pi Set.univ A =
      (Set.pi Set.univ fun i => A (Sum.inl i)) ×ˢ (Set.pi Set.univ fun j => A (Sum.inr j)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    exact ⟨fun h => ⟨fun i => h (Sum.inl i), fun j => h (Sum.inr j)⟩,
           fun ⟨h1, h2⟩ x => by cases x with | inl i => exact h1 i | inr j => exact h2 j⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fintype.prod_sum_type]
  rfl

/-- Multi-strip renewal identity proved by induction on the number of strips `n`. -/
lemma multi_strip_renewal_gen {M : ℕ} (hM : 0 < M) (m : ℕ) :
    ∀ (n : ℕ) (stripIdx : Fin n → Fin M) (k : Fin n → ℕ) (hk : ∀ s, k s < 4 + m)
      (r : ℕ) (e : (Σ s : Fin n, Fin (k s)) ≃ Fin r)
      (F : (Fin r → ℝ × ℝ) → ℝ≥0∞), Measurable F →
      (∀ σ : Equiv.Perm (Fin r), ∀ x, F (x ∘ σ) = F x) →
      ∫⁻ ω in Set.pi Set.univ (fun s : Fin n => stripArrivalEvent M m (k s) (hk s)),
        F (fun i => stripArrPts M m (k (e.symm i).1) (stripIdx (e.symm i).1) (ω (e.symm i).1) (e.symm i).2)
          ∂(Measure.pi fun _ : Fin n => stripFullMeasure m) =
      ENNReal.ofReal ((∏ s : Fin n, poissonProb ((M : ℝ) * (11 / 5 : ℝ) ^ 2) (k s)) * (M : ℝ) ^ r) *
        ∫⁻ x : (Σ s : Fin n, Fin (k s)) → ℝ × ℝ, F (x ∘ e.symm)
          ∂(Measure.pi fun p : Σ s : Fin n, Fin (k s) => stripBoxMeasure M (stripIdx p.1))
  | 0, stripIdx, k, hk, r, e, F, _, _ => by
    have hr0 : r = 0 := by
      have hcard := Fintype.card_congr e
      simpa using hcard.symm
    subst hr0
    simp only [Finset.univ_eq_empty, Finset.prod_empty, pow_zero, mul_one, ENNReal.ofReal_one, one_mul]
    have hset : Set.pi Set.univ (fun s : Fin 0 => stripArrivalEvent M m (k s) (hk s)) = Set.univ := by
      ext ω; simp
    rw [hset, Measure.restrict_univ]
    have h1 : ∀ ω : Fin 0 → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ),
        (fun i : Fin 0 => stripArrPts M m (k (e.symm i).1) (stripIdx (e.symm i).1) (ω (e.symm i).1) (e.symm i).2) =
          Fin.elim0 := fun _ => funext fun i => Fin.elim0 i
    have h2 : ∀ x : (Σ s : Fin 0, Fin (k s)) → ℝ × ℝ, (x ∘ e.symm) = Fin.elim0 :=
      fun _ => funext fun i => Fin.elim0 i
    simp_rw [h1, h2]
    rw [lintegral_const, lintegral_const]
    have hprob1 : (Measure.pi fun _ : Fin 0 => stripFullMeasure m) Set.univ = 1 := measure_univ
    have hprob2 : (Measure.pi fun p : Σ s : Fin 0, Fin (k s) => stripBoxMeasure M (stripIdx p.1)) Set.univ = 1 := by
      rw [← Set.pi_univ, Measure.pi_pi]
      simp
    rw [hprob1, hprob2]
  | n' + 1, stripIdx, k, hk, r, e, F, hF, hFsym => by
    set μ : ℝ := (M : ℝ) * (11 / 5 : ℝ) ^ 2
    have hμ : 0 < μ := by positivity
    let k0 : ℕ := k 0
    let k' : Fin n' → ℕ := fun s => k s.succ
    let stripIdx' : Fin n' → Fin M := fun s => stripIdx s.succ
    let r' : ℕ := ∑ s : Fin n', k' s
    have hr_eq : k0 + r' = r := by
      have hc := Fintype.card_congr e
      simp only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_succ] at hc
      exact hc
    let e' : (Σ s : Fin n', Fin (k' s)) ≃ Fin r' :=
      Fintype.equivFinOfCardEq (by simp [r'])
    -- Bijection `Fin k0 ⊕ (Σ s : Fin n', Fin (k' s)) ≃ Σ s : Fin (n' + 1), Fin (k s)`
    let sumEquiv : (Fin k0 ⊕ (Σ s : Fin n', Fin (k' s))) ≃ (Σ s : Fin (n' + 1), Fin (k s)) :=
      { toFun := Sum.elim (fun j => ⟨0, j⟩) (fun p => ⟨p.1.succ, p.2⟩)
        invFun := fun ⟨s, j⟩ =>
          Fin.cases (motive := fun s => Fin (k s) → Fin k0 ⊕ (Σ s : Fin n', Fin (k' s)))
            Sum.inl (fun s' j' => Sum.inr ⟨s', j'⟩) s j
        left_inv := fun x => by cases x <;> rfl
        right_inv := fun ⟨s, j⟩ => by revert j; refine Fin.cases (fun _ => rfl) (fun _ _ => rfl) s }
    -- Bijection `Fin k0 ⊕ Fin r' ≃ Fin r` via `sumEquiv` and `e`
    let splitR : (Fin k0 ⊕ Fin r') ≃ Fin r :=
      (Equiv.sumCongr (Equiv.refl (Fin k0)) e'.symm).trans (sumEquiv.trans e)
    -- Split `ω : Fin (n' + 1) → Ω_strip` into `(ω0, ω')` via `piFinSuccAbove 0`
    let sp := MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n' + 1) => (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) 0
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n' + 1) => stripFullMeasure m) 0
    let A0 := stripArrivalEvent M m (k 0) (hk 0)
    let A' := Set.pi Set.univ (fun s : Fin n' => stripArrivalEvent M m (k' s) (hk s.succ))
    have hA0_meas : MeasurableSet A0 := measurableSet_stripArrivalEvent M m (k 0) (hk 0)
    have hA'_meas : MeasurableSet A' := MeasurableSet.univ_pi fun s =>
      measurableSet_stripArrivalEvent M m (k' s) (hk s.succ)
    have hA_full_meas : MeasurableSet (Set.pi Set.univ fun s : Fin (n' + 1) => stripArrivalEvent M m (k s) (hk s)) :=
      MeasurableSet.univ_pi fun s => measurableSet_stripArrivalEvent M m (k s) (hk s)
    let evalω (ω : Fin (n' + 1) → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) : Fin r → ℝ × ℝ :=
      fun i => stripArrPts M m (k (e.symm i).1) (stripIdx (e.symm i).1) (ω (e.symm i).1) (e.symm i).2
    have heval_meas : Measurable evalω := by
      refine measurable_pi_lambda _ fun i => ?_
      exact ((measurable_pi_apply (e.symm i).2).comp (measurable_stripArrPts M m (k (e.symm i).1) (stripIdx (e.symm i).1))).comp
        (measurable_pi_apply (e.symm i).1)
    -- Rewrite LHS by indicator and `sp`
    rw [← lintegral_indicator hA_full_meas]
    change (∫⁻ ω, (Set.pi Set.univ fun s : Fin (n' + 1) => stripArrivalEvent M m (k s) (hk s)).indicator (F ∘ evalω) ω
        ∂(Measure.pi fun _ : Fin (n' + 1) => stripFullMeasure m)) = _
    rw [← hmp.symm.lintegral_comp ((hF.comp heval_meas).indicator hA_full_meas)]
    -- Rewrite the pulled-back integrand on `(ω0, ω')` using `splitR`
    let evalPair (x0 : Fin k0 → ℝ × ℝ) (x' : Fin r' → ℝ × ℝ) : Fin r → ℝ × ℝ :=
      (Sum.elim x0 x') ∘ splitR.symm
    let evalTail (ω' : Fin n' → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) : Fin r' → ℝ × ℝ :=
      fun i => stripArrPts M m (k' (e'.symm i).1) (stripIdx' (e'.symm i).1) (ω' (e'.symm i).1) (e'.symm i).2
    have hcongr_sp : ∀ p : ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) ×
        (Fin n' → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)),
        (Set.pi Set.univ fun s : Fin (n' + 1) => stripArrivalEvent M m (k s) (hk s)).indicator (F ∘ evalω) (sp.symm p) =
        (A0 ×ˢ A').indicator (fun p => F (evalPair (stripArrPts M m k0 (stripIdx 0) p.1) (evalTail p.2))) p := by
      intro ⟨ω0, ω'⟩
      have hmem : sp.symm (ω0, ω') ∈ Set.pi Set.univ (fun s : Fin (n' + 1) => stripArrivalEvent M m (k s) (hk s)) ↔
          (ω0, ω') ∈ A0 ×ˢ A' := by
        simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod, A0, A', k', Fin.forall_fin_succ]
        simp [sp]
      by_cases hp : (ω0, ω') ∈ A0 ×ˢ A'
      · rw [Set.indicator_of_mem (hmem.mpr hp), Set.indicator_of_mem hp]
        dsimp only [Function.comp]; congr 1; funext i
        dsimp only [evalω, evalPair, evalTail, Function.comp]
        have hsplit : splitR.symm i = (Equiv.sumCongr (Equiv.refl (Fin k0)) e') (sumEquiv.symm (e.symm i)) := by
          simp [splitR]
        rw [hsplit]
        cases hq : e.symm i with
        | mk s j =>
          revert j hq
          refine Fin.cases (fun j _ => ?_) (fun s' j _ => ?_) s
          · simp [sumEquiv, sp, k0]
          · simp only [sumEquiv, k', stripIdx', Equiv.coe_fn_symm_mk, Fin.cases_succ,
              Equiv.sumCongr_apply, Sum.map_inr, Sum.elim_inr]
            have h1 : sp.symm (ω0, ω') s'.succ = ω' s' := by simp [sp]
            rw [h1]
            have hp : e'.symm (e' ⟨s', j⟩) = ⟨s', j⟩ := e'.symm_apply_apply ⟨s', j⟩
            generalize e'.symm (e' ⟨s', j⟩) = p at hp ⊢
            subst hp; rfl
      · rw [Set.indicator_of_notMem (mt hmem.mp hp), Set.indicator_of_notMem hp]
    have hmeas_rhs_sp : Measurable ((A0 ×ˢ A').indicator
        (fun p : ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) × (Fin n' → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) =>
          F (evalPair (stripArrPts M m k0 (stripIdx 0) p.1) (evalTail p.2)))) := by
      refine Measurable.indicator ?_ (hA0_meas.prod hA'_meas)
      refine hF.comp (measurable_pi_lambda _ fun i => ?_)
      dsimp only [evalPair, Function.comp]
      cases hsi : splitR.symm i with
      | inl j =>
        simp only [Sum.elim_inl]
        exact ((measurable_pi_apply j).comp (measurable_stripArrPts M m k0 (stripIdx 0))).comp measurable_fst
      | inr j =>
        simp only [Sum.elim_inr, evalTail]
        exact ((measurable_pi_apply (e'.symm j).2).comp
          (measurable_stripArrPts M m (k' (e'.symm j).1) (stripIdx' (e'.symm j).1))).comp
          ((measurable_pi_apply (e'.symm j).1).comp measurable_snd)
    have hcongr_fn : (fun p => (Set.pi Set.univ fun s : Fin (n' + 1) => stripArrivalEvent M m (k s) (hk s)).indicator
        (F ∘ evalω) (sp.symm p)) =
        (A0 ×ˢ A').indicator (fun p => F (evalPair (stripArrPts M m k0 (stripIdx 0) p.1) (evalTail p.2))) :=
      funext hcongr_sp
    rw [hcongr_fn, MeasureTheory.lintegral_prod_symm _ hmeas_rhs_sp.aemeasurable]
    -- Inner integral over `ω0` using `single_strip_renewal_lintegral`.
    have hinner0 : ∀ ω' : Fin n' → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ),
        ∫⁻ ω0, (A0 ×ˢ A').indicator (fun p => F (evalPair (stripArrPts M m k0 (stripIdx 0) p.1) (evalTail p.2))) (ω0, ω')
          ∂(stripFullMeasure m) =
        ENNReal.ofReal (poissonProb μ k0 * (M : ℝ) ^ k0) *
          A'.indicator (fun ω' =>
            ∫⁻ x0 : Fin k0 → ℝ × ℝ, F (evalPair x0 (evalTail ω'))
              ∂(Measure.pi fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0))) ω' := by
      intro ω'
      by_cases hω' : ω' ∈ A'
      · rw [Set.indicator_of_mem hω']
        have hcongr0 : (fun ω0 => (A0 ×ˢ A').indicator
            (fun p => F (evalPair (stripArrPts M m k0 (stripIdx 0) p.1) (evalTail p.2))) (ω0, ω')) =
            A0.indicator (fun ω0 => F (evalPair (stripArrPts M m k0 (stripIdx 0) ω0) (evalTail ω'))) := by
          funext ω0
          by_cases h0 : ω0 ∈ A0
          · have hp : (ω0, ω') ∈ A0 ×ˢ A' := ⟨h0, hω'⟩
            rw [Set.indicator_of_mem hp, Set.indicator_of_mem h0]
          · rw [Set.indicator_of_notMem (fun h => h0 h.1), Set.indicator_of_notMem h0]
        rw [hcongr0, lintegral_indicator hA0_meas]
        have hF0_meas : Measurable (fun x0 : Fin k0 → ℝ × ℝ => F (evalPair x0 (evalTail ω'))) := by
          refine hF.comp (measurable_pi_lambda _ fun i => ?_)
          dsimp only [evalPair]
          cases hsi : splitR.symm i with
          | inl j => simp only [hsi, Function.comp, Sum.elim_inl]; exact measurable_pi_apply j
          | inr j => simp only [hsi, Function.comp, Sum.elim_inr]; exact measurable_const
        have hF0_sym : ∀ σ : Equiv.Perm (Fin k0), ∀ x0,
            F (evalPair (x0 ∘ σ) (evalTail ω')) = F (evalPair x0 (evalTail ω')) := by
          intro σ x0
          let σ_full : Equiv.Perm (Fin r) :=
            (splitR.symm.trans (Equiv.sumCongr σ (Equiv.refl (Fin r')))).trans splitR
          have heq : evalPair (x0 ∘ σ) (evalTail ω') = (evalPair x0 (evalTail ω')) ∘ σ_full := by
            funext i
            dsimp only [evalPair, σ_full, Function.comp, Equiv.trans_apply, Equiv.symm_apply_apply]
            cases hsi : splitR.symm i <;> simp
          rw [heq, hFsym σ_full]
        exact single_strip_renewal_lintegral hM m k0 (hk 0) (stripIdx 0) _ hF0_meas hF0_sym
      · rw [Set.indicator_of_notMem hω', mul_zero]
        have h0 : ∀ ω0, (ω0, ω') ∉ A0 ×ˢ A' := fun _ h => hω' h.2
        simp [Set.indicator_of_notMem (h0 _)]
    simp_rw [hinner0]
    have hmeas_x0ω' : Measurable (fun p : (Fin n' → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) × (Fin k0 → ℝ × ℝ) =>
        A'.indicator (fun ω' => F (evalPair p.2 (evalTail ω'))) p.1) := by
      have hm1 : Measurable (fun p : (Fin n' → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) × (Fin k0 → ℝ × ℝ) =>
          F (evalPair p.2 (evalTail p.1))) := by
        refine hF.comp (measurable_pi_lambda _ fun i => ?_)
        dsimp only [evalPair, Function.comp]
        cases hsi : splitR.symm i with
        | inl j =>
          simp only [Sum.elim_inl]
          exact (measurable_pi_apply j).comp measurable_snd
        | inr j =>
          simp only [Sum.elim_inr, evalTail]
          exact ((measurable_pi_apply (e'.symm j).2).comp
            (measurable_stripArrPts M m (k' (e'.symm j).1) (stripIdx' (e'.symm j).1))).comp
            ((measurable_pi_apply (e'.symm j).1).comp measurable_fst)
      have hm2 := hm1.indicator (hA'_meas.prod MeasurableSet.univ)
      convert hm2 using 1
      funext ⟨ω', x0⟩
      by_cases h : ω' ∈ A'
      · have hp : (ω', x0) ∈ A' ×ˢ (Set.univ : Set (Fin k0 → ℝ × ℝ)) := ⟨h, Set.mem_univ _⟩
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h hc.1)]
    have hmeas_outer : Measurable (A'.indicator fun ω' =>
        ∫⁻ x0 : Fin k0 → ℝ × ℝ, F (evalPair x0 (evalTail ω'))
          ∂(Measure.pi fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0))) := by
      refine Measurable.indicator ?_ hA'_meas
      have hm1 : Measurable (fun p : (Fin n' → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) × (Fin k0 → ℝ × ℝ) =>
          F (evalPair p.2 (evalTail p.1))) := by
        refine hF.comp (measurable_pi_lambda _ fun i => ?_)
        dsimp only [evalPair, Function.comp]
        cases hsi : splitR.symm i with
        | inl j =>
          simp only [Sum.elim_inl]
          exact (measurable_pi_apply j).comp measurable_snd
        | inr j =>
          simp only [Sum.elim_inr, evalTail]
          exact ((measurable_pi_apply (e'.symm j).2).comp
            (measurable_stripArrPts M m (k' (e'.symm j).1) (stripIdx' (e'.symm j).1))).comp
            ((measurable_pi_apply (e'.symm j).1).comp measurable_fst)
      exact Measurable.lintegral_prod_right' hm1
    rw [lintegral_const_mul _ hmeas_outer]
    -- Move `A'.indicator` inside `∫⁻ x0` and swap `ω'` and `x0`.
    have hmove : ∀ ω' : Fin n' → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ),
        A'.indicator (fun ω' => ∫⁻ x0 : Fin k0 → ℝ × ℝ, F (evalPair x0 (evalTail ω'))
          ∂(Measure.pi fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0))) ω' =
        ∫⁻ x0 : Fin k0 → ℝ × ℝ, A'.indicator (fun ω' => F (evalPair x0 (evalTail ω'))) ω'
          ∂(Measure.pi fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0)) := by
      intro ω'
      by_cases h : ω' ∈ A'
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    simp_rw [hmove]
    rw [MeasureTheory.lintegral_lintegral_swap hmeas_x0ω'.aemeasurable]
    -- For each fixed `x0`, apply the induction hypothesis on `n'` strips.
    have hih_x0 : ∀ x0 : Fin k0 → ℝ × ℝ,
        ∫⁻ ω', A'.indicator (fun ω' => F (evalPair x0 (evalTail ω'))) ω'
          ∂(Measure.pi fun _ : Fin n' => stripFullMeasure m) =
        ENNReal.ofReal ((∏ s : Fin n', poissonProb μ (k' s)) * (M : ℝ) ^ r') *
          ∫⁻ x' : (Σ s : Fin n', Fin (k' s)) → ℝ × ℝ, F (evalPair x0 (x' ∘ e'.symm))
            ∂(Measure.pi fun p : Σ s : Fin n', Fin (k' s) => stripBoxMeasure M (stripIdx' p.1)) := by
      intro x0
      rw [lintegral_indicator hA'_meas]
      have hFx0_meas : Measurable (fun y : Fin r' → ℝ × ℝ => F (evalPair x0 y)) := by
        refine hF.comp (measurable_pi_lambda _ fun i => ?_)
        dsimp only [evalPair]
        cases hsi : splitR.symm i with
        | inl j => simp only [hsi, Function.comp, Sum.elim_inl]; exact measurable_const
        | inr j => simp only [hsi, Function.comp, Sum.elim_inr]; exact measurable_pi_apply j
      have hFx0_sym : ∀ σ : Equiv.Perm (Fin r'), ∀ y, F (evalPair x0 (y ∘ σ)) = F (evalPair x0 y) := by
        intro σ y
        let σ_full : Equiv.Perm (Fin r) :=
          (splitR.symm.trans (Equiv.sumCongr (Equiv.refl (Fin k0)) σ)).trans splitR
        have heq : evalPair x0 (y ∘ σ) = (evalPair x0 y) ∘ σ_full := by
          funext i
          dsimp only [evalPair, σ_full, Function.comp, Equiv.trans_apply, Equiv.symm_apply_apply]
          cases hsi : splitR.symm i <;> simp
        rw [heq, hFsym σ_full]
      exact multi_strip_renewal_gen hM m n' stripIdx' k' (fun s => hk s.succ) r' e'
        (fun y => F (evalPair x0 y)) hFx0_meas hFx0_sym
    simp_rw [hih_x0]
    have hF_pair_meas : Measurable (fun p : (Fin k0 → ℝ × ℝ) × ((Σ s : Fin n', Fin (k' s)) → ℝ × ℝ) =>
        F (evalPair p.1 (p.2 ∘ e'.symm))) := by
      refine hF.comp (measurable_pi_lambda _ fun i => ?_)
      dsimp only [evalPair, Function.comp]
      cases hsi : splitR.symm i with
      | inl j =>
        simp only [Sum.elim_inl]
        exact (measurable_pi_apply j).comp measurable_fst
      | inr j =>
        simp only [Sum.elim_inr]
        exact (measurable_pi_apply (e'.symm j)).comp measurable_snd
    rw [lintegral_const_mul _ (Measurable.lintegral_prod_right' hF_pair_meas)]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (poissonProb_nonneg (le_of_lt hμ) k0) (pow_nonneg (Nat.cast_nonneg M) k0))]
    have hconst : (poissonProb μ k0 * (M : ℝ) ^ k0) *
        ((∏ s : Fin n', poissonProb μ (k' s)) * (M : ℝ) ^ r') =
        (∏ s : Fin (n' + 1), poissonProb μ (k s)) * (M : ℝ) ^ r := by
      rw [Fin.prod_univ_succ]
      have hpow : (M : ℝ) ^ k0 * (M : ℝ) ^ r' = (M : ℝ) ^ r := by rw [← pow_add, hr_eq]
      dsimp only [k0, k'] at hpow ⊢
      rw [← hpow]
      ring
    rw [hconst]
    congr 1
    -- Combine `(stripBoxMeasure M (stripIdx 0))^k0 × (Measure.pi stripBoxMeasure')` via `measurePreserving_pi_sum` and `sumEquiv`.
    rw [← MeasureTheory.lintegral_prod _ hF_pair_meas.aemeasurable]
    haveI : ∀ x : Fin k0 ⊕ (Σ s : Fin n', Fin (k' s)),
        IsFiniteMeasure (Sum.elim (fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0))
          (fun p : Σ s : Fin n', Fin (k' s) => stripBoxMeasure M (stripIdx' p.1)) x) := fun x => by
      cases x with
      | inl _ => simpa using (inferInstance : IsFiniteMeasure (stripBoxMeasure M (stripIdx 0)))
      | inr p => simpa using (inferInstance : IsFiniteMeasure (stripBoxMeasure M (stripIdx' p.1)))
    have hmp_sum := measurePreserving_pi_sum
      (fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0))
      (fun p : Σ s : Fin n', Fin (k' s) => stripBoxMeasure M (stripIdx' p.1))
    have hmp_eqv := measurePreserving_pi_equiv sumEquiv.symm
      (Sum.elim (fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0))
        (fun p : Σ s : Fin n', Fin (k' s) => stripBoxMeasure M (stripIdx' p.1)))
    have hmeas_sig : (Measure.pi fun q : Σ s : Fin (n' + 1), Fin (k s) =>
          Sum.elim (fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0))
            (fun p : Σ s : Fin n', Fin (k' s) => stripBoxMeasure M (stripIdx' p.1)) (sumEquiv.symm q)) =
        (Measure.pi fun q : Σ s : Fin (n' + 1), Fin (k s) => stripBoxMeasure M (stripIdx q.1)) := by
      congr 1; funext ⟨s, j⟩
      revert j; refine Fin.cases (fun _ => rfl) (fun _ _ => rfl) s
    have hmp_comb : MeasurePreserving
        (fun p : (Fin k0 → ℝ × ℝ) × ((Σ s : Fin n', Fin (k' s)) → ℝ × ℝ) =>
          fun q : Σ s : Fin (n' + 1), Fin (k s) => Sum.elim p.1 p.2 (sumEquiv.symm q))
        ((Measure.pi fun _ : Fin k0 => stripBoxMeasure M (stripIdx 0)).prod
          (Measure.pi fun p : Σ s : Fin n', Fin (k' s) => stripBoxMeasure M (stripIdx' p.1)))
        (Measure.pi fun q : Σ s : Fin (n' + 1), Fin (k s) => stripBoxMeasure M (stripIdx q.1)) := by
      rw [← hmeas_sig]
      exact hmp_eqv.comp hmp_sum
    have hF_sig_meas : Measurable (fun x : (Σ s : Fin (n' + 1), Fin (k s)) → ℝ × ℝ => F (x ∘ e.symm)) :=
      hF.comp (measurable_pi_lambda _ fun i => measurable_pi_apply (e.symm i))
    rw [← hmp_comb.lintegral_comp hF_sig_meas]
    apply lintegral_congr
    rintro ⟨x0, x'⟩
    congr 1; funext i
    dsimp only [evalPair, Function.comp]
    have hsplit : splitR.symm i = (Equiv.sumCongr (Equiv.refl (Fin k0)) e') (sumEquiv.symm (e.symm i)) := by
      simp [splitR]
    rw [hsplit]
    cases sumEquiv.symm (e.symm i) with
    | inl j => rfl
    | inr p => simp

/-- For any `M > 0`, `m`, `r`, and histogram
`k : Fin M → ℕ` with `∑ s, k s = r` and `∀ s, k s < 4 + m`, the Poisson-weighted sum of `∫⁻ F`
over all assignments `a : Fin r → Fin M` with `hist a = k` equals the `M`-strip renewal integral
over `multiArrivalEvent`. -/
theorem multi_strip_hist_sum {M : ℕ} (hM : 0 < M) (m r : ℕ)
    (k : Fin M → ℕ) (hk : ∀ s : Fin M, k s < 4 + m) (hr : ∑ s : Fin M, k s = r)
    (e : (Σ s : Fin M, Fin (k s)) ≃ Fin r)
    (F : (Fin r → ℝ × ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hFsym : ∀ σ : Equiv.Perm (Fin r), ∀ x, F (x ∘ σ) = F x) :
    ENNReal.ofReal (poissonProb ((M : ℝ) * ((M : ℝ) * (11 / 5 : ℝ) ^ 2)) r) *
      ∑ a ∈ Finset.univ.filter (fun a : Fin r → Fin M => hist a = k),
        ∫⁻ x : Fin r → ℝ × ℝ, F x ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) =
    ∫⁻ ω in Set.pi Set.univ (fun s : Fin M => stripArrivalEvent M m (k s) (hk s)),
      F (fun i => stripArrPts M m (k (e.symm i).1) (e.symm i).1 (ω (e.symm i).1) (e.symm i).2)
        ∂(Measure.pi fun _ : Fin M => stripFullMeasure m) := by
  set μ : ℝ := (M : ℝ) * (11 / 5 : ℝ) ^ 2
  have hμ : 0 < μ := by positivity
  -- Every `a` with `hist a = k` yields the same integral.
  have ha_eq : ∀ a ∈ Finset.univ.filter (fun a : Fin r → Fin M => hist a = k),
      ∫⁻ x : Fin r → ℝ × ℝ, F x ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) =
        ∫⁻ y : (Σ s : Fin M, Fin (k s)) → ℝ × ℝ, F (y ∘ e.symm)
          ∂(Measure.pi fun p : Σ s : Fin M, Fin (k s) => stripBoxMeasure M p.1) := by
    intro a ha
    have hha : hist a = k := (Finset.mem_filter.mp ha).2
    -- Construct a bijection `e_a : (Σ s : Fin M, Fin (k s)) ≃ Fin r` with `a (e_a ⟨s, j⟩) = s`
    have hfib : ∀ s : Fin M, Fintype.card {i : Fin r // a i = s} = k s := fun s => by
      have hs := congrFun hha s
      dsimp only [hist] at hs
      rw [← hs, Fintype.card_subtype]
    let e_fib (s : Fin M) : Fin (k s) ≃ {i : Fin r // a i = s} :=
      (Fintype.equivFinOfCardEq (hfib s)).symm
    let e_a : (Σ s : Fin M, Fin (k s)) ≃ Fin r :=
      (Equiv.sigmaCongrRight e_fib).trans (Equiv.sigmaFiberEquiv a)
    have hea_prop : ∀ p : Σ s : Fin M, Fin (k s), a (e_a p) = p.1 := fun ⟨s, j⟩ => (e_fib s j).2
    have hmp := measurePreserving_pi_equiv e_a (fun i : Fin r => stripBoxMeasure M (a i))
    have hmeas_eq : (Measure.pi fun p : Σ s : Fin M, Fin (k s) => stripBoxMeasure M (a (e_a p))) =
        (Measure.pi fun p : Σ s : Fin M, Fin (k s) => stripBoxMeasure M p.1) := by
      congr 1; funext p; rw [hea_prop p]
    rw [hmeas_eq] at hmp
    have hF_ea : Measurable (fun y : (Σ s : Fin M, Fin (k s)) → ℝ × ℝ => F (y ∘ e_a.symm)) :=
      hF.comp (measurable_pi_lambda _ fun i => measurable_pi_apply (e_a.symm i))
    have hstep : ∫⁻ x : Fin r → ℝ × ℝ, F x ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) =
        ∫⁻ y : (Σ s : Fin M, Fin (k s)) → ℝ × ℝ, F (y ∘ e_a.symm)
          ∂(Measure.pi fun p : Σ s : Fin M, Fin (k s) => stripBoxMeasure M p.1) := by
      rw [← hmp.lintegral_comp hF_ea]
      apply lintegral_congr; intro x
      congr 1; funext i; simp [Function.comp]
    rw [hstep]
    apply lintegral_congr; intro y
    let σ : Equiv.Perm (Fin r) := e.symm.trans e_a
    have hcomp : y ∘ e_a.symm = (y ∘ e.symm) ∘ σ.symm := by
      funext i; simp [σ, Function.comp]
    rw [hcomp, hFsym σ.symm]
  rw [Finset.sum_congr rfl ha_eq, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  have hgen := multi_strip_renewal_gen hM m M id k hk r e F hF hFsym
  dsimp only [id_eq] at hgen
  rw [hgen]
  congr 1
  -- Show `poissonProb (M * μ) r * card = (∏ s, poissonProb μ (k s)) * M^r`.
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (poissonProb_nonneg (by positivity) r)]
  congr 1
  have hmult : ((Finset.univ.filter fun a : Fin r → Fin M => hist a = k).card : ℝ) *
      ∏ s : Fin M, ((k s).factorial : ℝ) = (r.factorial : ℝ) := by
    exact_mod_cast card_hist_mul_fact M r k hr
  have hprod_fact_ne : (∏ s : Fin M, ((k s).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k s))
  have hrf_ne : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hcard_val : ((Finset.univ.filter fun a : Fin r → Fin M => hist a = k).card : ℝ) =
      (r.factorial : ℝ) / ∏ s : Fin M, ((k s).factorial : ℝ) := by
    rw [eq_div_iff hprod_fact_ne]; exact hmult
  rw [hcard_val]
  unfold poissonProb
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_nat_mul, Finset.prod_pow_eq_pow_sum, hr, mul_pow]
  dsimp only [μ]
  have hMexp : ((M : ℝ) * -((M : ℝ) * (11 / 5 : ℝ) ^ 2)) = -((M : ℝ) * ((M : ℝ) * (11 / 5 : ℝ) ^ 2)) := by ring
  rw [hMexp]
  field_simp

end BHHBounds.Upper
