import BHHBounds.Defs
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# From `IsBHHConstant` to expected tour length

If `β` is a BHH constant then `expectedTourLength n / √n → β`, by dominated convergence with the
deterministic bound `tourLength x ≤ 4 * √n + 4` on `[0, 1]²`.
-/

open MeasureTheory Set Filter ProbabilityTheory Finset
open scoped ENNReal

namespace BHHBounds

noncomputable section

/-! ## Measure-Theoretic Properties of `unitSquareMeasure` -/

lemma volume_Icc_zero_one : volume (Icc (0 : ℝ) 1) = 1 := by
  rw [Real.volume_Icc]; norm_num

instance instIsProbabilityMeasure_Icc_zero_one :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, volume_Icc_zero_one]

instance instIsProbabilityMeasure_unitSquareMeasure :
    IsProbabilityMeasure unitSquareMeasure := by
  unfold unitSquareMeasure
  infer_instance

instance instIsProbabilityMeasure_unitSquarePi (n : ℕ) :
    IsProbabilityMeasure (unitSquarePi n) := by
  unfold unitSquarePi
  infer_instance

lemma restrict_unitSquare_eq :
    (volume.restrict unitSquare : Measure Pt) = unitSquareMeasure := by
  unfold unitSquare unitSquareMeasure
  rw [Measure.volume_eq_prod]
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [Measure.restrict_apply (hs.prod ht), Set.prod_inter_prod, Measure.prod_prod,
    Measure.restrict_apply hs, Measure.restrict_apply ht]

lemma ae_mem_unitSquareMeasure : ∀ᵐ p ∂unitSquareMeasure, p ∈ unitSquare := by
  rw [← restrict_unitSquare_eq]
  exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)

lemma measurePreserving_infinitePi_take {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun ω : ℕ → α => fun i : Fin n => ω i.val)
      (Measure.infinitePi fun _ : ℕ => μ) (Measure.pi fun _ : Fin n => μ) := by
  have hmeas : Measurable (fun ω : ℕ → α => fun i : Fin n => ω i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun A hA => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hA)]
  let I : Finset ℕ := Finset.range n
  let s : ℕ → Set α := fun k => if h : k < n then A ⟨k, h⟩ else Set.univ
  have hpre : (fun ω : ℕ → α => fun i : Fin n => ω i.val) ⁻¹' Set.pi Set.univ A =
      Set.pi (I : Set ℕ) s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Finset.mem_coe,
      I, Finset.mem_range, s]
    constructor
    · intro h k hk
      rw [dif_pos hk]; exact h ⟨k, hk⟩
    · intro h i
      have hi := h i.val i.isLt
      rwa [dif_pos i.isLt] at hi
  rw [hpre, Measure.infinitePi_pi _
    (fun k _ => by dsimp only [s]; split_ifs; exact hA _; exact MeasurableSet.univ)]
  refine Finset.prod_bij (fun k hk => ⟨k, Finset.mem_range.mp hk⟩)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro k1 _ k2 _ heq; exact congrArg Fin.val heq
  · intro i _; exact ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩
  · intro k hk
    have hlt : k < n := Finset.mem_range.mp hk
    simp only [s, dif_pos hlt]

/-! ## Continuity and Deterministic `4√n + 4` Envelope for `tourLength` -/

lemma tourLength_nonneg {n : ℕ} (x : Fin n → Pt) : 0 ≤ tourLength x := by
  unfold tourLength
  exact Real.iInf_nonneg fun σ => Finset.sum_nonneg fun i _ => euclidDist_nonneg _ _

lemma tourLength_le_perm {n : ℕ} (x : Fin n → Pt) (σ : Equiv.Perm (Fin n)) :
    tourLength x ≤ ∑ i : Fin n, euclidDist (x (σ i)) (x (σ (finRotate n i))) := by
  unfold tourLength
  exact ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) σ

lemma exists_optimal_tour {n : ℕ} (x : Fin n → Pt) :
    ∃ σ : Equiv.Perm (Fin n),
      tourLength x = ∑ i : Fin n, euclidDist (x (σ i)) (x (σ (finRotate n i))) := by
  unfold tourLength
  have hne : (Finset.univ : Finset (Equiv.Perm (Fin n))).Nonempty := Finset.univ_nonempty
  obtain ⟨σ, _, hσ⟩ := Finset.exists_min_image Finset.univ
    (fun τ : Equiv.Perm (Fin n) => ∑ i : Fin n, euclidDist (x (τ i)) (x (τ (finRotate n i)))) hne
  refine ⟨σ, le_antisymm (ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) σ) ?_⟩
  exact le_ciInf fun τ => hσ τ (Finset.mem_univ τ)

lemma measurable_euclidDist : Measurable (fun p : Pt × Pt => euclidDist p.1 p.2) :=
  continuous_euclidDist.measurable

lemma continuous_tourLength (n : ℕ) : Continuous (fun x : Fin n → Pt => tourLength x) := by
  let f : Equiv.Perm (Fin n) → (Fin n → Pt) → ℝ :=
    fun σ x => ∑ i : Fin n, euclidDist (x (σ i)) (x (σ (finRotate n i)))
  have hf : ∀ σ, Continuous (f σ) := fun σ =>
    continuous_finsetSum _ fun i _ =>
      continuous_euclidDist.comp (Continuous.prodMk (continuous_apply (σ i))
        (continuous_apply (σ (finRotate n i))))
  have heq : (fun x : Fin n → Pt => tourLength x) =
      fun x => (Finset.univ : Finset (Equiv.Perm (Fin n))).inf' Finset.univ_nonempty (fun σ => f σ x) := by
    funext x
    unfold tourLength
    apply le_antisymm
    · rw [Finset.le_inf'_iff]
      intro σ _
      exact ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) σ
    · refine le_ciInf fun σ => Finset.inf'_le (fun τ => f τ x) (Finset.mem_univ σ)
  rw [heq]
  have hinf : ∀ (s : Finset (Equiv.Perm (Fin n))) (hs : s.Nonempty),
      Continuous (fun x => s.inf' hs (fun σ => f σ x)) := by
    intro s
    refine Finset.induction_on s (fun hs => absurd hs (by simp)) fun a t hat ih _ => ?_
    by_cases ht : t.Nonempty
    · have hfn : (fun x => (insert a t).inf' (Finset.insert_nonempty a t) (fun σ => f σ x)) =
          fun x => min (f a x) (t.inf' ht (fun σ => f σ x)) := by
        funext x; exact Finset.inf'_insert ht _
      rw [hfn]; exact (hf a).min (ih ht)
    · have hte : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst hte
      simpa using hf a
  exact hinf Finset.univ Finset.univ_nonempty

lemma measurable_tourLength (n : ℕ) : Measurable (fun x : Fin n → Pt => tourLength x) := by
  let f : Equiv.Perm (Fin n) → (Fin n → Pt) → ℝ :=
    fun σ x => ∑ i : Fin n, euclidDist (x (σ i)) (x (σ (finRotate n i)))
  have hf : ∀ σ, Measurable (f σ) := fun σ =>
    Finset.measurable_sum _ fun i _ =>
      measurable_euclidDist.comp (Measurable.prodMk (measurable_pi_apply (σ i))
        (measurable_pi_apply (σ (finRotate n i))))
  have heq : (fun x : Fin n → Pt => tourLength x) =
      fun x => (Finset.univ : Finset (Equiv.Perm (Fin n))).inf' Finset.univ_nonempty (fun σ => f σ x) := by
    funext x
    unfold tourLength
    apply le_antisymm
    · rw [Finset.le_inf'_iff]
      intro σ _
      exact ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) σ
    · refine le_ciInf fun σ => Finset.inf'_le (fun τ => f τ x) (Finset.mem_univ σ)
  rw [heq]
  have hinf : ∀ (s : Finset (Equiv.Perm (Fin n))) (hs : s.Nonempty),
      Measurable (fun x => s.inf' hs (fun σ => f σ x)) := by
    intro s
    refine Finset.induction_on s (fun hs => absurd hs (by simp)) fun a t hat ih _ => ?_
    by_cases ht : t.Nonempty
    · have hfn : (fun x => (insert a t).inf' (Finset.insert_nonempty a t) (fun σ => f σ x)) =
          fun x => min (f a x) (t.inf' ht (fun σ => f σ x)) := by
        funext x; exact Finset.inf'_insert ht _
      rw [hfn]; exact (hf a).min (ih ht)
    · have hte : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst hte
      simpa using hf a
  exact hinf Finset.univ Finset.univ_nonempty

lemma euclidDist_le_l1 (a b : Pt) : euclidDist a b ≤ |a.1 - b.1| + |a.2 - b.2| := by
  unfold euclidDist sqDist
  rw [Real.sqrt_le_left (by positivity)]
  rw [← sq_abs (a.1 - b.1), ← sq_abs (a.2 - b.2)]
  nlinarith [abs_nonneg (a.1 - b.1), abs_nonneg (a.2 - b.2)]

private lemma euclidDist_unitSquare_le_two {a b : Pt} (ha : a ∈ unitSquare) (hb : b ∈ unitSquare) :
    euclidDist a b ≤ 2 := by
  have hx : |a.1 - b.1| ≤ 1 :=
    abs_sub_le_iff.mpr ⟨by linarith [ha.1.2, hb.1.1], by linarith [hb.1.2, ha.1.1]⟩
  have hy : |a.2 - b.2| ≤ 1 :=
    abs_sub_le_iff.mpr ⟨by linarith [ha.2.2, hb.2.1], by linarith [hb.2.2, ha.2.1]⟩
  linarith [euclidDist_le_l1 a b]

private lemma fin_sum_telescope : ∀ (m : ℕ) (f : Fin (m + 1) → ℝ),
    ∑ i : Fin m, (f i.succ - f i.castSucc) = f (Fin.last m) - f 0
  | 0, _ => by simp
  | m' + 1, f => by
    rw [Fin.sum_univ_castSucc]
    have h4 : ∀ i : Fin m', i.castSucc.succ = i.succ.castSucc := fun i => Fin.ext (by simp)
    simp_rw [h4]
    rw [fin_sum_telescope m' (fun j => f j.castSucc)]
    have h2 : (Fin.last m').succ = Fin.last (m' + 1) := Fin.ext (by simp)
    have h3 : (0 : Fin (m' + 1)).castSucc = (0 : Fin (m' + 2)) := rfl
    rw [h2, h3]; ring

private lemma finRotate_castSucc_eq {m : ℕ} (i : Fin m) :
    finRotate (m + 1) i.castSucc = i.succ := by
  rw [finRotate_apply]
  exact Fin.ext (by simp)

/-- Any `n` points in `[0, 1]²` admit a closed tour of length at most `4 * √n + 4`. -/
theorem tourLength_unitSquare_le {n : ℕ} (x : Fin n → Pt) (hx : ∀ i, x i ∈ unitSquare) :
    tourLength x ≤ 4 * Real.sqrt (n : ℝ) + 4 := by
  cases n with
  | zero =>
    have h0 : tourLength x ≤ 0 := by simpa using tourLength_le_perm x 1
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add]
    linarith
  | succ m =>
    let n := m + 1
    let k : ℕ := Nat.sqrt n + 1
    have hk_pos : 0 < k := Nat.succ_pos _
    have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
    let strip : Fin n → ℕ := fun i => min (k - 1) ⌊(k : ℝ) * (x i).2⌋₊
    have hstrip_lt : ∀ i, strip i < k := fun i => by dsimp only [strip]; omega
    have hstrip_y : ∀ i, ((strip i : ℕ) : ℝ) / (k : ℝ) ≤ (x i).2 ∧
        (x i).2 ≤ (((strip i : ℕ) + 1 : ℕ) : ℝ) / (k : ℝ) := by
      intro i
      have hy0 : 0 ≤ (x i).2 := (hx i).2.1
      have hy1 : (x i).2 ≤ 1 := (hx i).2.2
      dsimp only [strip]
      by_cases hle : ⌊(k : ℝ) * (x i).2⌋₊ ≤ k - 1
      · rw [min_eq_right hle]
        constructor
        · rw [div_le_iff₀ hkR_pos]
          linarith [Nat.floor_le (mul_nonneg (le_of_lt hkR_pos) hy0)]
        · rw [le_div_iff₀ hkR_pos]
          have := Nat.lt_floor_add_one ((k : ℝ) * (x i).2)
          push_cast; linarith
      · rw [min_eq_left (by omega)]
        have hfl : k ≤ ⌊(k : ℝ) * (x i).2⌋₊ := by omega
        have hksub : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        constructor
        · rw [div_le_iff₀ hkR_pos, hksub]
          have := (Nat.le_floor_iff (mul_nonneg (le_of_lt hkR_pos) hy0)).mp hfl
          linarith
        · rw [le_div_iff₀ hkR_pos]
          have : ((k - 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast (by omega : k - 1 + 1 = k)
          rw [this]; nlinarith
    let key : Fin n → ℕ ×ₗ ℝ := fun i => toLex (strip i, (x i).1)
    let σ : Equiv.Perm (Fin n) := Tuple.sort key
    have hmono : Monotone (key ∘ σ) := Tuple.monotone_sort key
    refine (tourLength_le_perm x σ).trans ?_
    rw [Fin.sum_univ_castSucc]
    have hclose : euclidDist (x (σ (Fin.last m))) (x (σ (finRotate n (Fin.last m)))) ≤ 2 :=
      euclidDist_unitSquare_le_two (hx _) (hx _)
    have hstep_uni : ∀ i : Fin m,
        euclidDist (x (σ i.castSucc)) (x (σ (finRotate n i.castSucc))) ≤
          ((x (σ i.succ)).1 - (x (σ i.castSucc)).1) + 1 / (k : ℝ) +
            3 * ((strip (σ i.succ) : ℝ) - (strip (σ i.castSucc) : ℝ)) := by
      intro i
      rw [finRotate_castSucc_eq i]
      have hmi := hmono (show i.castSucc ≤ i.succ by simp [Fin.le_def])
      have hs_le : strip (σ i.castSucc) ≤ strip (σ i.succ) := by
        rcases (Prod.Lex.le_iff.mp hmi) with hlt | ⟨heq, _⟩
        · exact le_of_lt hlt
        · exact le_of_eq heq
      by_cases heq : strip (σ i.castSucc) = strip (σ i.succ)
      · have hx_le : (x (σ i.castSucc)).1 ≤ (x (σ i.succ)).1 := by
          rcases (Prod.Lex.le_iff.mp hmi) with hlt | ⟨_, hle⟩
          · exact absurd heq (ne_of_lt hlt)
          · exact hle
        have hxa : |(x (σ i.castSucc)).1 - (x (σ i.succ)).1| =
            (x (σ i.succ)).1 - (x (σ i.castSucc)).1 := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hx_le)]
        have hy1 := hstrip_y (σ i.castSucc)
        have hy2 := hstrip_y (σ i.succ)
        rw [heq] at hy1
        have hya : |(x (σ i.castSucc)).2 - (x (σ i.succ)).2| ≤ 1 / (k : ℝ) := by
          rw [abs_sub_le_iff]
          have hstep_div :
              (((strip (σ i.succ) + 1 : ℕ) : ℝ) / (k : ℝ)) -
                ((strip (σ i.succ) : ℕ) : ℝ) / (k : ℝ) = 1 / (k : ℝ) := by
            push_cast; ring
          constructor <;> linarith
        rw [heq]
        linarith [euclidDist_le_l1 (x (σ i.castSucc)) (x (σ i.succ))]
      · have hsdiff : (1 : ℝ) ≤ (strip (σ i.succ) : ℝ) - (strip (σ i.castSucc) : ℝ) := by
          have : ((strip (σ i.castSucc) + 1 : ℕ) : ℝ) ≤ (strip (σ i.succ) : ℝ) := by
            exact_mod_cast (by omega : strip (σ i.castSucc) + 1 ≤ strip (σ i.succ))
          push_cast at this; linarith
        have hx1 := (hx (σ i.succ)).1
        have hx0 := (hx (σ i.castSucc)).1
        have hk0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
        linarith [euclidDist_unitSquare_le_two (hx (σ i.castSucc)) (hx (σ i.succ)), hx1.1, hx0.2]
    have hsum_le := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hstep_uni i
    have hsum_eval : ∑ i : Fin m, (((x (σ i.succ)).1 - (x (σ i.castSucc)).1) + 1 / (k : ℝ) +
          3 * ((strip (σ i.succ) : ℝ) - (strip (σ i.castSucc) : ℝ))) =
        ((x (σ (Fin.last m))).1 - (x (σ 0)).1) + (m : ℝ) / (k : ℝ) +
          3 * ((strip (σ (Fin.last m)) : ℝ) - (strip (σ 0) : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        fin_sum_telescope m (fun i => (x (σ i)).1),
        fin_sum_telescope m (fun i => (strip (σ i) : ℝ)),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
    rw [hsum_eval] at hsum_le
    have hxdiff : (x (σ (Fin.last m))).1 - (x (σ 0)).1 ≤ 1 := by
      linarith [(hx (σ (Fin.last m))).1.2, (hx (σ 0)).1.1]
    have hsdiff : (strip (σ (Fin.last m)) : ℝ) - (strip (σ 0) : ℝ) ≤ (k : ℝ) - 1 := by
      have h1 : (strip (σ (Fin.last m)) : ℝ) ≤ (k : ℝ) - 1 := by
        have : ((strip (σ (Fin.last m)) + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast hstrip_lt (σ (Fin.last m))
        push_cast at this; linarith
      have h0 : (0 : ℝ) ≤ (strip (σ 0) : ℝ) := Nat.cast_nonneg _
      linarith
    have hk_le : (k : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := by
      have hsq : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _), sq]
        exact_mod_cast Nat.sqrt_le n
      dsimp only [k]; push_cast; linarith
    have hmk_le : (m : ℝ) / (k : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [div_le_iff₀ hkR_pos]
      have hlt : (n : ℝ) < (k : ℝ) ^ 2 := by
        have : n < k * k := by dsimp only [k]; exact Nat.lt_succ_sqrt n
        rw [sq]; exact_mod_cast this
      have hsn_le : Real.sqrt (n : ℝ) ≤ (k : ℝ) := by
        rw [Real.sqrt_le_left (le_of_lt hkR_pos)]
        exact le_of_lt hlt
      have hm_le : (m : ℝ) ≤ (n : ℝ) := by dsimp only [n]; push_cast; linarith
      have hsq_n : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg n)
      nlinarith [Real.sqrt_nonneg (n : ℝ)]
    linarith

/-! ## Convergence of Expected Tour Length -/

/-- For any BHH constant `β`, the normalized expected shortest tour length
`expectedTourLength n / √n` converges to `β`. -/
theorem expectedTourLength_div_sqrt_tendsto {β : ℝ} (hβ : IsBHHConstant β) :
    Tendsto (fun n : ℕ => expectedTourLength n / Real.sqrt (n : ℝ)) atTop (nhds β) := by
  let P : Measure (ℕ → Pt) := Measure.infinitePi fun _ : ℕ => unitSquareMeasure
  haveI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  let X : ℕ → (ℕ → Pt) → Pt := fun i ω => ω i
  have hX_meas : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hX_indep : iIndepFun X P := iIndepFun_infinitePi fun _ => measurable_id
  have hX_law : ∀ i, P.map (X i) = volume.restrict unitSquare := fun i => by
    rw [restrict_unitSquare_eq]
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => unitSquareMeasure) i).map_eq
  have hae_lim : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => tourLength (fun i : Fin n => X i ω) / Real.sqrt (n : ℝ))
        atTop (nhds β) :=
    hβ (ℕ → Pt) P X hX_meas hX_indep hX_law
  let F (n : ℕ) (ω : ℕ → Pt) : ℝ :=
    if n = 0 then 0 else tourLength (fun i : Fin n => ω i.val) / Real.sqrt (n : ℝ)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) P := fun n => by
    dsimp only [F]
    split_ifs
    · exact aestronglyMeasurable_const
    · have htake : Measurable (fun ω : ℕ → Pt => fun i : Fin n => ω i.val) :=
        (measurePreserving_infinitePi_take unitSquareMeasure n).measurable
      exact (((measurable_tourLength n).comp htake).div_const (Real.sqrt (n : ℝ))).aestronglyMeasurable
  have hae_sq : ∀ᵐ ω ∂P, ∀ k : ℕ, ω k ∈ unitSquare := by
    refine ae_all_iff.mpr fun k => ?_
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => unitSquareMeasure) k).quasiMeasurePreserving.ae
      ae_mem_unitSquareMeasure
  have hF_bound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ (8 : ℝ) := fun n => by
    filter_upwards [hae_sq] with ω hω
    dsimp only [F]
    split_ifs with hn0
    · norm_num
    · have hnn : 0 ≤ tourLength (fun i : Fin n => ω i.val) / Real.sqrt (n : ℝ) :=
        div_nonneg (tourLength_nonneg _) (Real.sqrt_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hsn1 : 1 ≤ Real.sqrt (n : ℝ) := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn1
      have hsn_pos : 0 < Real.sqrt (n : ℝ) := by linarith
      rw [div_le_iff₀ hsn_pos]
      have hle := tourLength_unitSquare_le (fun i : Fin n => ω i.val) (fun i => hω i.val)
      linarith
  have hF_lim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds β) := by
    filter_upwards [hae_lim] with ω hω
    refine Tendsto.congr' ?_ hω
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    simp only [F, hn0, ↓reduceIte, X]
  have hint_lim : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (nhds (∫ _, β ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (8 : ℝ))
      hF_meas (integrable_const 8) hF_bound hF_lim
  have hconst_int : ∫ _, β ∂P = β := by simp [Measure.real]
  rw [hconst_int] at hint_lim
  have hF_int_eq : ∀ n ≥ 1, ∫ ω, F n ω ∂P = expectedTourLength n / Real.sqrt (n : ℝ) := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hfun : F n = fun ω => tourLength (fun i : Fin n => ω i.val) / Real.sqrt (n : ℝ) := by
      funext ω; simp [F, hn0]
    rw [hfun, integral_div]
    congr 1
    have hmp := measurePreserving_infinitePi_take unitSquareMeasure n
    unfold expectedTourLength unitSquarePi
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (measurable_tourLength n).aestronglyMeasurable]
  refine Tendsto.congr' ?_ hint_lim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact hF_int_eq n hn

/-- Lower-bound criterion: if `L ≤ expectedTourLength n / √n + ε` eventually for every `ε > 0`,
then `L ≤ β` for every BHH constant `β`. -/
theorem le_of_eventually_expectedTourLength {β L : ℝ} (hβ : IsBHHConstant β)
    (hlim : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, L - ε ≤ expectedTourLength n / Real.sqrt (n : ℝ)) :
    L ≤ β := by
  have htend := expectedTourLength_div_sqrt_tendsto hβ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 : L - ε ≤ β := ge_of_tendsto htend (hlim ε hε)
  linarith

end

end BHHBounds
