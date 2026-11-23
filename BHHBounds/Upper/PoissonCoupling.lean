import BHHBounds.Upper.PoissonSuperposition

/-!
# From strips to the unit square

The strips are traversed in serpentine order and their paths joined into one tour, and a Poisson
number of points is compared with exactly `n` points. The result is
`expectedTourLength_div_sqrt_le_of_dp`: a DP certificate `(V, uBound)` for `automaton4` gives
`expectedTourLength n / √n ≤ uBound + ε` for all large `n`.
-/

namespace BHHBounds.Upper

open MeasureTheory Set Finset BigOperators
open scoped ENNReal NNReal

local instance : IsProbabilityMeasure exp1Measure := isProbabilityMeasure_exp1Measure
local instance : IsProbabilityMeasure unifHMeasure := isProbabilityMeasure_unifHMeasure

/-! ## Section 1: Right-Boundary Deviation of `Exp(1)` Partial Sums -/

/-- Scaled x-coordinate of the right endpoint `4 + m` of a strip (`(∑_{j=0}^{3+m} E_{j+3}) / μ`). -/
noncomputable def stripEndX (μ : ℝ) {m : ℕ} (E : Fin (7 + m) → ℝ) : ℝ :=
  (∑ j : Fin (4 + m), E ⟨j.val + 3, by omega⟩) / μ

lemma stripEndX_eq_stripUnitPt_fst {M : ℕ} (_hM : 0 < M) (s : Fin M) {m : ℕ}
    (E : Fin (7 + m) → ℝ) (Y : Fin (8 + m) → ℝ) :
    (stripUnitPt M s E Y (4 + m)).1 = stripEndX ((M : ℝ) * (11 / 5 : ℝ) ^ 2) E := by
  unfold stripUnitPt stripPt stripEndX
  have hsum : (∑ j : Fin (7 + m), if 3 ≤ j.val ∧ j.val < 4 + m + 3 then E j else 0) =
      ∑ j : Fin (4 + m), E ⟨j.val + 3, by omega⟩ := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun j hj => ⟨j.val - 3, by have := (Finset.mem_filter.mp hj).2; omega⟩)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro j1 hj1 j2 hj2 heq
      have h1 := (Finset.mem_filter.mp hj1).2
      have h2 := (Finset.mem_filter.mp hj2).2
      have hv := congrArg Fin.val heq; simp at hv
      exact Fin.ext (by omega)
    · intro i _
      refine ⟨⟨i.val + 3, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, ?_⟩
      apply Fin.ext; simp
    · intro j hj
      have h1 := (Finset.mem_filter.mp hj).2
      congr 1; apply Fin.ext; simp; omega
  rw [hsum, div_div]
  ring

/-- Expected absolute deviation of `stripEndX` from `1`:
`E[|stripEndX μ E - 1|] ≤ √(((4 + m)/μ - 1)^2 + (4 + m)/μ^2)`. -/
lemma stripEndX_abs_dev_le {μ : ℝ} (hμ : 0 < μ) (m : ℕ) :
    Integrable (fun p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) => |stripEndX μ p.1 - 1|)
      (stripFullMeasure m) ∧
    ∫ p, |stripEndX μ p.1 - 1| ∂(stripFullMeasure m) ≤
      Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) := by
  let emb : Fin (4 + m) ↪ Fin (7 + m) :=
    ⟨fun j => ⟨j.val + 3, by omega⟩, fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simp at this; omega)⟩
  let ν : Measure (Fin (4 + m) → ℝ) := Measure.pi fun _ : Fin (4 + m) => exp1Measure
  have hmpE : MeasurePreserving (fun E : Fin (7 + m) → ℝ => fun j : Fin (4 + m) => E (emb j))
      (Measure.pi fun _ : Fin (7 + m) => exp1Measure) ν :=
    measurePreserving_pi_emb_gen (fun _ => exp1Measure) emb
  have hmp : MeasurePreserving (fun p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) =>
      fun j : Fin (4 + m) => p.1 (emb j)) (stripFullMeasure m) ν :=
    hmpE.comp measurePreserving_fst
  let S (e : Fin (4 + m) → ℝ) : ℝ := ∑ j : Fin (4 + m), e j
  have hS_int : Integrable S ν :=
    integrable_finsetSum _ fun j _ =>
      integrable_comp_mp (measurePreserving_eval (fun _ : Fin (4 + m) => exp1Measure) j) integrable_id_exp1Measure
  have hS_val : ∫ e, S e ∂ν = ((4 + m : ℕ) : ℝ) := by
    unfold S
    rw [integral_finsetSum _ fun j _ =>
      integrable_comp_mp (measurePreserving_eval (fun _ : Fin (4 + m) => exp1Measure) j) integrable_id_exp1Measure]
    have h1 : ∀ j : Fin (4 + m), ∫ e, e j ∂ν = 1 := fun j => by
      have hm := measurePreserving_eval (fun _ : Fin (4 + m) => exp1Measure) j
      have hmap := integral_map (μ := ν) hm.measurable.aemeasurable (f := fun x : ℝ => x) continuous_id.aestronglyMeasurable
      rw [hm.map_eq, integral_id_exp1Measure] at hmap
      exact hmap.symm
    dsimp only [ν] at h1 ⊢
    simp [h1]
  have hSsq := integral_pi_sum_sq (fun _ : Fin (4 + m) => exp1Measure)
    (fun _ => integrable_id_exp1Measure) (fun _ => integrable_sq_exp1Measure)
  have hSsq_int : Integrable (fun e : Fin (4 + m) → ℝ => (S e) ^ 2) ν := hSsq.1
  have hSsq_val : ∫ e, (S e) ^ 2 ∂ν = ((4 + m : ℕ) : ℝ) ^ 2 + ((4 + m : ℕ) : ℝ) := by
    have h := hSsq.2
    simp only [integral_sq_exp1Measure, integral_id_exp1Measure, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    change ∫ e, (S e) ^ 2 ∂ν = _
    dsimp only [S, ν]
    rw [h]; ring
  let Z (e : Fin (4 + m) → ℝ) : ℝ := (S e / μ - 1) ^ 2
  have hZ_eq : Z = fun e => ((S e) ^ 2 / μ ^ 2 - (2 / μ) * S e) + 1 := by
    funext e; dsimp only [Z]; ring
  have hZ_part_int : Integrable (fun e : Fin (4 + m) → ℝ => (S e) ^ 2 / μ ^ 2 - (2 / μ) * S e) ν :=
    (hSsq_int.div_const (μ ^ 2)).sub (hS_int.const_mul (2 / μ))
  have hZ_int : Integrable Z ν := by
    rw [hZ_eq]
    exact hZ_part_int.add (integrable_const 1)
  have hZ_val : ∫ e, Z e ∂ν = (((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2 := by
    rw [hZ_eq]
    rw [integral_add hZ_part_int (integrable_const 1),
        integral_sub (hSsq_int.div_const (μ ^ 2)) (hS_int.const_mul (2 / μ)),
        integral_div, integral_const_mul, integral_const, hSsq_val, hS_val]
    have hprob : ν.real Set.univ = 1 := by simp [Measure.real]
    rw [hprob, smul_eq_mul, mul_one]
    field_simp; ring
  have habs_int : Integrable (fun e => |S e / μ - 1|) ν := by
    refine Integrable.mono' (hZ_int.add (integrable_const 1)) (by
      have hc : Continuous (fun e : Fin (4 + m) → ℝ => |S e / μ - 1|) := by
        unfold S; fun_prop
      exact hc.aestronglyMeasurable) (ae_of_all _ fun e => ?_)
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    change |S e / μ - 1| ≤ Z e + 1
    dsimp only [Z]
    have hsq : |S e / μ - 1| ^ 2 = (S e / μ - 1) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (S e / μ - 1)]
  have habs_le : ∫ e, |S e / μ - 1| ∂ν ≤
      Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) := by
    have hsq_eq : (fun e : Fin (4 + m) → ℝ => |S e / μ - 1|) = fun e => Real.sqrt (Z e) := by
      funext e; exact (Real.sqrt_sq_eq_abs _).symm
    rw [hsq_eq]
    have hMpos : 0 < (((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2 := by
      have h4m : (0 : ℝ) < ((4 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 4 + m)
      positivity
    exact integral_sqrt_le_sqrt_of_le (fun e => sq_nonneg _) hZ_int (hsq_eq ▸ habs_int) hMpos (le_of_eq hZ_val)
  have hcomp_eq : (fun p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) => |stripEndX μ p.1 - 1|) =
      (fun e : Fin (4 + m) → ℝ => |S e / μ - 1|) ∘ (fun p => fun j => p.1 (emb j)) := by
    funext ⟨E, Y⟩; rfl
  rw [hcomp_eq]
  refine ⟨integrable_comp_mp hmp habs_int, ?_⟩
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by
    have hc : Continuous (fun e : Fin (4 + m) → ℝ => |S e / μ - 1|) := by unfold S; fun_prop
    exact hc.aestronglyMeasurable)] at habs_le
  exact habs_le

/-! ## Section 2: Serpentine Tour Containment & Cycle Length Upper Bound -/

/-- Length of a flattened list of `M` equal-length blocks of length `B`. -/
lemma flatten_finRange_length {α : Type*} {M B : ℕ} (L : Fin M → List α)
    (hL : ∀ s, (L s).length = B) :
    ((List.finRange M).map L).flatten.length = M * B := by
  rw [List.length_flatten, List.map_map]
  have heq : (List.finRange M).map (List.length ∘ L) = List.replicate M B := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp [hL]
  rw [heq, List.sum_replicate, smul_eq_mul]

/-- Block indexing into a flattened list of `M` equal-length blocks of length `B`. -/
lemma flatten_finRange_getElem {α : Type*} :
    ∀ {M B : ℕ} (L : Fin M → List α) (hL : ∀ s, (L s).length = B)
      (s : Fin M) (u : ℕ) (hu : u < B),
      (((List.finRange M).map L).flatten)[s.val * B + u]'(by
          rw [flatten_finRange_length L hL]
          have hs : s.val + 1 ≤ M := s.isLt
          calc s.val * B + u < s.val * B + B := Nat.add_lt_add_left hu _
            _ = (s.val + 1) * B := by ring
            _ ≤ M * B := Nat.mul_le_mul_right B hs) = (L s)[u]'(by rw [hL s]; exact hu)
  | 0, _, _, _, s, _, _ => Fin.elim0 s
  | M' + 1, B, L, hL, s, u, hu => by
    have hsplit : ((List.finRange (M' + 1)).map L).flatten =
        ((List.finRange M').map fun j => L j.castSucc).flatten ++ L (Fin.last M') := by
      rw [List.finRange_succ_last, List.map_append, List.map_singleton, List.flatten_append,
        List.flatten_singleton, List.map_map]
      rfl
    have hpref_len : (((List.finRange M').map fun j => L j.castSucc).flatten).length = M' * B :=
      flatten_finRange_length (fun j => L j.castSucc) (fun j => hL j.castSucc)
    refine Fin.lastCases ?_ (fun s' => ?_) s
    · -- `s = Fin.last M'`
      have hge : (((List.finRange M').map fun j => L j.castSucc).flatten).length ≤ (Fin.last M').val * B + u := by
        rw [hpref_len]; simp
      simp_rw [hsplit]
      rw [List.getElem_append_right hge]
      congr 1
      rw [hpref_len]; simp
    · -- `s = s'.castSucc`
      have hlt : s'.castSucc.val * B + u < (((List.finRange M').map fun j => L j.castSucc).flatten).length := by
        rw [hpref_len]; simp only [Fin.val_castSucc]
        have hs : s'.val + 1 ≤ M' := s'.isLt
        calc s'.val * B + u < s'.val * B + B := Nat.add_lt_add_left hu _
          _ = (s'.val + 1) * B := by ring
          _ ≤ M' * B := Nat.mul_le_mul_right B hs
      simp_rw [hsplit]
      rw [List.getElem_append_left hlt]
      exact flatten_finRange_getElem (fun j => L j.castSucc) (fun j => hL j.castSucc) s' u hu

/-- If each strip `s : Fin (M' + 1)` has a Hamiltonian path `P s` visiting `0..4+m`,
then the serpentine concatenation of the rescaled paths upper-bounds `tourLength` of any
arrival configuration with `k s < 4 + m` points per strip. -/
lemma serpentine_tourLength_le {M' m r : ℕ}
    (k : Fin (M' + 1) → ℕ) (hk : ∀ s, k s < 4 + m)
    (e : (Σ s : Fin (M' + 1), Fin (k s)) ≃ Fin r)
    (ω : Fin (M' + 1) → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ))
    (P : Fin (M' + 1) → List ℕ)
    (hP : ∀ s, (P s).Perm (List.range (4 + m + 1))) :
    tourLength (fun i : Fin r =>
      stripArrPts (M' + 1) m (k (e.symm i).1) (e.symm i).1 (ω (e.symm i).1) (e.symm i).2) ≤
    cycleLen (serpentineConcat fun s : Fin (M' + 1) =>
      (P s).map (stripUnitPt (M' + 1) s (ω s).1 (ω s).2)) := by
  classical
  let B : ℕ := 4 + m + 1
  let Q (s : Fin (M' + 1)) : List (ℝ × ℝ) := (P s).map (stripUnitPt (M' + 1) s (ω s).1 (ω s).2)
  let seg (s : Fin (M' + 1)) : List (ℝ × ℝ) := if s.val % 2 = 0 then Q s else (Q s).reverse
  have hPlen : ∀ s, (P s).length = B := fun s => by
    rw [(hP s).length_eq, List.length_range]
  have hQlen : ∀ s, (Q s).length = B := fun s => by simp [Q, hPlen s]
  have hseg_len : ∀ s, (seg s).length = B := fun s => by
    dsimp only [seg]; split_ifs <;> simp [hQlen s]
  have hserp_eq : serpentineConcat Q = ((List.finRange (M' + 1)).map seg).flatten := rfl
  have hLlen : (serpentineConcat Q).length = (M' + 1) * B := by
    rw [hserp_eq]; exact flatten_finRange_length seg hseg_len
  -- For each `s` and `j : Fin (k s)`, `j.val + 1 ∈ P s` so `idxOf (j.val + 1) < B`
  have hmem : ∀ (s : Fin (M' + 1)) (j : Fin (k s)), j.val + 1 ∈ P s := fun s j => by
    rw [(hP s).mem_iff, List.mem_range]
    have := hk s; have := j.isLt; omega
  have hidx_lt : ∀ (s : Fin (M' + 1)) (j : Fin (k s)), (P s).idxOf (j.val + 1) < B := fun s j => by
    rw [← hPlen s]; exact List.idxOf_lt_length_iff.mpr (hmem s j)
  let uOf (s : Fin (M' + 1)) (j : Fin (k s)) : ℕ :=
    if s.val % 2 = 0 then (P s).idxOf (j.val + 1) else B - 1 - (P s).idxOf (j.val + 1)
  have hu_lt : ∀ (s : Fin (M' + 1)) (j : Fin (k s)), uOf s j < B := fun s j => by
    have hlt := hidx_lt s j
    dsimp only [uOf]; split_ifs <;> omega
  let f : Fin r → Fin (serpentineConcat Q).length := fun i =>
    let p := e.symm i
    ⟨p.1.val * B + uOf p.1 p.2, by
      rw [hLlen]
      have hs : p.1.val + 1 ≤ M' + 1 := p.1.isLt
      calc p.1.val * B + uOf p.1 p.2 < p.1.val * B + B := Nat.add_lt_add_left (hu_lt p.1 p.2) _
        _ = (p.1.val + 1) * B := by ring
        _ ≤ (M' + 1) * B := Nat.mul_le_mul_right B hs⟩
  have hf_inj : Function.Injective f := by
    intro i1 i2 h12
    have hv := congrArg Fin.val h12
    dsimp only [f] at hv
    have hBpos : 0 < B := by dsimp only [B]; omega
    have h1u := hu_lt (e.symm i1).1 (e.symm i1).2
    have h2u := hu_lt (e.symm i2).1 (e.symm i2).2
    have hs_eq : (e.symm i1).1 = (e.symm i2).1 := by
      apply Fin.ext
      have hdiv1 : ((e.symm i1).1.val * B + uOf (e.symm i1).1 (e.symm i1).2) / B = (e.symm i1).1.val := by
        rw [mul_comm _ B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt h1u, add_zero]
      have hdiv2 : ((e.symm i2).1.val * B + uOf (e.symm i2).1 (e.symm i2).2) / B = (e.symm i2).1.val := by
        rw [mul_comm _ B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt h2u, add_zero]
      rw [← hdiv1, hv, hdiv2]
    apply e.symm.injective
    generalize hp1 : e.symm i1 = p1 at hs_eq hv ⊢
    generalize hp2 : e.symm i2 = p2 at hs_eq hv ⊢
    cases p1 with
    | mk s1 j1 =>
      cases p2 with
      | mk s2 j2 =>
        dsimp only at hs_eq hv
        subst hs_eq
        have hu_eq : uOf s1 j1 = uOf s1 j2 := by omega
        congr 1
        have hidx_eq : (P s1).idxOf (j1.val + 1) = (P s1).idxOf (j2.val + 1) := by
          have h1 := hidx_lt s1 j1; have h2 := hidx_lt s1 j2
          dsimp only [uOf] at hu_eq
          split_ifs at hu_eq <;> omega
        have hg1 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hmem s1 j1))
        have hg2 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hmem s1 j2))
        have hval_eq : j1.val + 1 = j2.val + 1 := by
          rw [← hg1, ← hg2]
          congr 1
        exact Fin.ext (by omega)
  have hf_val : ∀ i : Fin r, (serpentineConcat Q)[f i] =
      stripArrPts (M' + 1) m (k (e.symm i).1) (e.symm i).1 (ω (e.symm i).1) (e.symm i).2 := by
    intro i
    let s := (e.symm i).1
    let j := (e.symm i).2
    have hget := flatten_finRange_getElem seg hseg_len s (uOf s j) (hu_lt s j)
    change (serpentineConcat Q)[s.val * B + uOf s j]'(f i).isLt = _
    simp_rw [hserp_eq]
    rw [hget]
    dsimp only [seg, uOf, Q]
    have hidx := hidx_lt s j
    have hPget : (P s)[(P s).idxOf (j.val + 1)]'(by rw [hPlen s]; exact hidx) = j.val + 1 :=
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hmem s j))
    split_ifs with hev
    · simp only [List.getElem_map, hPget]; rfl
    · rw [List.getElem_reverse]
      simp only [List.getElem_map]
      have hsub : ((P s).map (stripUnitPt (M' + 1) s (ω s).1 (ω s).2)).length - 1 -
          (B - 1 - (P s).idxOf (j.val + 1)) = (P s).idxOf (j.val + 1) := by
        rw [List.length_map, hPlen s]; omega
      simp_rw [hsub, hPget]; rfl
  exact tourLength_le_cycleLen_of_inj _ (serpentineConcat Q) f hf_inj hf_val

/-- Pointwise bound on `cycleLen (serpentineConcat Q)` in terms of strip path lengths
and right-boundary deviations `|stripEndX μ (ω s).1 - 1|`. -/
lemma serpentine_cycleLen_le_bound {M' m : ℕ}
    (ω : Fin (M' + 1) → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ))
    (hY : ∀ (s : Fin (M' + 1)) (j : Fin (8 + m)), 0 < (ω s).2 j ∧ (ω s).2 j ≤ 11 / 5)
    (P : Fin (M' + 1) → List ℕ) (hne : ∀ s, P s ≠ [])
    (hhead : ∀ s, (P s).head (hne s) = 0)
    (hlast : ∀ s, (P s).getLast (hne s) = 4 + m)
    (len : ((Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) → ℝ)
    (hlen : ∀ s, listPathLen ((P s).map (stripPt (ω s).1 (ω s).2)) ≤ len (ω s)) :
    let M := M' + 1
    let μ := (M : ℝ) * (11 / 5 : ℝ) ^ 2
    cycleLen (serpentineConcat fun s : Fin M => (P s).map (stripUnitPt M s (ω s).1 (ω s).2)) ≤
      (∑ s : Fin M, len (ω s)) / ((M : ℝ) * (11 / 5 : ℝ)) +
      3 * (∑ s : Fin M, |stripEndX μ (ω s).1 - 1|) + 4 := by
  intro M μ
  have hMpos : 0 < M := Nat.succ_pos M'
  have hMR_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  let Q (s : Fin M) : List (ℝ × ℝ) := (P s).map (stripUnitPt M s (ω s).1 (ω s).2)
  have hQne : ∀ s, Q s ≠ [] := fun s => by simp [Q, hne s]
  rw [cycleLen_serpentine Q hQne]
  -- 1. Strip path lengths rescale by `1 / (M * (11 / 5))`
  have hlist_scale : ∀ (s : Fin M) (l : List ℕ),
      listPathLen (l.map (stripUnitPt M s (ω s).1 (ω s).2)) =
        listPathLen (l.map (stripPt (ω s).1 (ω s).2)) / ((M : ℝ) * (11 / 5 : ℝ)) := by
    intro s l
    induction l with
    | nil => simp [listPathLen]
    | cons a rest ih =>
      cases rest with
      | nil => simp [listPathLen]
      | cons b rest' =>
        simp only [List.map_cons, listPathLen] at ih ⊢
        rw [ih, euclidDist_stripUnitPt hMpos s, add_div]
  have hpath_sum : ∑ s : Fin M, listPathLen (Q s) ≤
      (∑ s : Fin M, len (ω s)) / ((M : ℝ) * (11 / 5 : ℝ)) := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun s _ => ?_
    dsimp only [Q]
    rw [hlist_scale s (P s)]
    exact div_le_div_of_nonneg_right (hlen s) (by positivity)
  -- Coordinates of `head` and `getLast` of `Q s`
  have hQhead : ∀ s : Fin M, (Q s).head (hQne s) = stripUnitPt M s (ω s).1 (ω s).2 0 := fun s => by
    dsimp only [Q]; rw [List.head_map, hhead s]
  have hQlast : ∀ s : Fin M, (Q s).getLast (hQne s) = stripUnitPt M s (ω s).1 (ω s).2 (4 + m) := fun s => by
    dsimp only [Q]; rw [List.getLast_map, hlast s]
  have hhead_x : ∀ s : Fin M, (stripUnitPt M s (ω s).1 (ω s).2 0).1 = 0 := fun s => by
    unfold stripUnitPt stripPt
    have h0 : (∑ j : Fin (7 + m), if 3 ≤ j.val ∧ j.val < 0 + 3 then (ω s).1 j else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg (by omega)
    rw [h0]; simp
  have hlast_x : ∀ s : Fin M, (stripUnitPt M s (ω s).1 (ω s).2 (4 + m)).1 = stripEndX μ (ω s).1 := fun s =>
    stripEndX_eq_stripUnitPt_fst hMpos s (ω s).1 (ω s).2
  have hy_band : ∀ (s : Fin M) (k : ℕ), k + 3 < 8 + m →
      (s.val : ℝ) / (M : ℝ) ≤ (stripUnitPt M s (ω s).1 (ω s).2 k).2 ∧
      (stripUnitPt M s (ω s).1 (ω s).2 k).2 ≤ ((s.val : ℝ) + 1) / (M : ℝ) := by
    intro s k hk
    unfold stripUnitPt stripPt
    simp only [hk, ↓reduceDIte]
    have hb := hY s ⟨k + 3, hk⟩
    have h0 : 0 ≤ (ω s).2 ⟨k + 3, hk⟩ / (11 / 5 : ℝ) := div_nonneg (le_of_lt hb.1) (by norm_num)
    have h1 : (ω s).2 ⟨k + 3, hk⟩ / (11 / 5 : ℝ) ≤ 1 := (div_le_one (by norm_num)).mpr hb.2
    constructor <;> exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hMR_pos)
  -- 2. Adjacent strip jumps: bound each jump `s : Fin M'`
  have hjump_le : ∀ s : Fin M',
      (if s.val % 2 = 0 then
          euclidDist ((Q s.castSucc).getLast (hQne _)) ((Q s.succ).getLast (hQne _))
        else
          euclidDist ((Q s.castSucc).head (hQne _)) ((Q s.succ).head (hQne _))) ≤
      |stripEndX μ (ω s.castSucc).1 - 1| + |stripEndX μ (ω s.succ).1 - 1| + 2 / (M : ℝ) := by
    intro s
    have hys1 := hy_band s.castSucc (4 + m) (by omega)
    have hys2 := hy_band s.succ (4 + m) (by omega)
    have hyh1 := hy_band s.castSucc 0 (by omega)
    have hyh2 := hy_band s.succ 0 (by omega)
    have hsucc_val : (s.succ.val : ℝ) = (s.castSucc.val : ℝ) + 1 := by simp
    split_ifs
    · rw [hQlast, hQlast]
      have hl1 := euclidDist_le_l1 (stripUnitPt M s.castSucc (ω s.castSucc).1 (ω s.castSucc).2 (4 + m))
        (stripUnitPt M s.succ (ω s.succ).1 (ω s.succ).2 (4 + m))
      rw [hlast_x, hlast_x] at hl1
      have hdx : |stripEndX μ (ω s.castSucc).1 - stripEndX μ (ω s.succ).1| ≤
          |stripEndX μ (ω s.castSucc).1 - 1| + |stripEndX μ (ω s.succ).1 - 1| := by
        have : stripEndX μ (ω s.castSucc).1 - stripEndX μ (ω s.succ).1 =
            (stripEndX μ (ω s.castSucc).1 - 1) - (stripEndX μ (ω s.succ).1 - 1) := by ring
        rw [this]; exact abs_sub _ _
      have hdy : |(stripUnitPt M s.castSucc (ω s.castSucc).1 (ω s.castSucc).2 (4 + m)).2 -
          (stripUnitPt M s.succ (ω s.succ).1 (ω s.succ).2 (4 + m)).2| ≤ 2 / (M : ℝ) := by
        rw [hsucc_val] at hys2
        rw [abs_le]
        constructor
        · have : ((s.castSucc.val : ℝ) / (M : ℝ)) - (((s.castSucc.val : ℝ) + 1 + 1) / (M : ℝ)) = -(2 / (M : ℝ)) := by
            field_simp; ring
          linarith [hys1.1, hys2.2]
        · have : (((s.castSucc.val : ℝ) + 1) / (M : ℝ)) - (((s.castSucc.val : ℝ) + 1) / (M : ℝ)) = 0 := sub_self _
          have h2pos : 0 ≤ 2 / (M : ℝ) := by positivity
          linarith [hys1.2, hys2.1]
      linarith
    · rw [hQhead, hQhead]
      have hl1 := euclidDist_le_l1 (stripUnitPt M s.castSucc (ω s.castSucc).1 (ω s.castSucc).2 0)
        (stripUnitPt M s.succ (ω s.succ).1 (ω s.succ).2 0)
      rw [hhead_x, hhead_x, sub_self, abs_zero, zero_add] at hl1
      have hdy : |(stripUnitPt M s.castSucc (ω s.castSucc).1 (ω s.castSucc).2 0).2 -
          (stripUnitPt M s.succ (ω s.succ).1 (ω s.succ).2 0).2| ≤ 2 / (M : ℝ) := by
        rw [hsucc_val] at hyh2
        rw [abs_le]
        constructor
        · have : ((s.castSucc.val : ℝ) / (M : ℝ)) - (((s.castSucc.val : ℝ) + 1 + 1) / (M : ℝ)) = -(2 / (M : ℝ)) := by
            field_simp; ring
          linarith [hyh1.1, hyh2.2]
        · have : (((s.castSucc.val : ℝ) + 1) / (M : ℝ)) - (((s.castSucc.val : ℝ) + 1) / (M : ℝ)) = 0 := sub_self _
          have h2pos : 0 ≤ 2 / (M : ℝ) := by positivity
          linarith [hyh1.2, hyh2.1]
      linarith [abs_nonneg (stripEndX μ (ω s.castSucc).1 - 1), abs_nonneg (stripEndX μ (ω s.succ).1 - 1)]
  -- Sum adjacent jumps: `≤ 2 * ∑ s, |stripEndX - 1| + 2`
  have hsum_jumps : (∑ s : Fin M',
      if s.val % 2 = 0 then
        euclidDist ((Q s.castSucc).getLast (hQne _)) ((Q s.succ).getLast (hQne _))
      else
        euclidDist ((Q s.castSucc).head (hQne _)) ((Q s.succ).head (hQne _))) ≤
      2 * (∑ s : Fin M, |stripEndX μ (ω s).1 - 1|) + 2 := by
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M'))) fun s _ => hjump_le s
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    have hcs : ∑ s : Fin M', |stripEndX μ (ω s.castSucc).1 - 1| ≤ ∑ s : Fin M, |stripEndX μ (ω s).1 - 1| := by
      rw [Fin.sum_univ_castSucc]
      linarith [abs_nonneg (stripEndX μ (ω (Fin.last M')).1 - 1)]
    have hsc : ∑ s : Fin M', |stripEndX μ (ω s.succ).1 - 1| ≤ ∑ s : Fin M, |stripEndX μ (ω s).1 - 1| := by
      rw [Fin.sum_univ_succ]
      linarith [abs_nonneg (stripEndX μ (ω 0).1 - 1)]
    have h2m : (M' : ℝ) * (2 / (M : ℝ)) ≤ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hMR_pos]
      have hM_eq : (M : ℝ) = (M' : ℝ) + 1 := by exact_mod_cast rfl
      linarith
    linarith
  -- 3. Closing edge: `≤ |stripEndX (last) - 1| + 2`
  have hclose : euclidDist (if M' % 2 = 0 then (Q (Fin.last M')).getLast (hQne _) else (Q (Fin.last M')).head (hQne _))
      ((Q 0).head (hQne 0)) ≤ (∑ s : Fin M, |stripEndX μ (ω s).1 - 1|) + 2 := by
    have hlast_term : |stripEndX μ (ω (Fin.last M')).1 - 1| ≤ ∑ s : Fin M, |stripEndX μ (ω s).1 - 1| :=
      Finset.single_le_sum (f := fun s : Fin M => |stripEndX μ (ω s).1 - 1|)
        (fun s _ => abs_nonneg _) (Finset.mem_univ (Fin.last M'))
    have hy0 := hy_band 0 0 (by omega)
    have hyl := hy_band (Fin.last M') (4 + m) (by omega)
    have hyh := hy_band (Fin.last M') 0 (by omega)
    have hy0_01 : 0 ≤ (stripUnitPt M 0 (ω 0).1 (ω 0).2 0).2 ∧ (stripUnitPt M 0 (ω 0).1 (ω 0).2 0).2 ≤ 1 := by
      constructor
      · linarith [hy0.1, show ((0 : Fin M).val : ℝ) / (M : ℝ) = 0 by simp]
      · refine le_trans hy0.2 ?_
        rw [div_le_one hMR_pos]; exact_mod_cast (by omega : 0 + 1 ≤ M)
    have hyl_01 : 0 ≤ (stripUnitPt M (Fin.last M') (ω (Fin.last M')).1 (ω (Fin.last M')).2 (4 + m)).2 ∧
        (stripUnitPt M (Fin.last M') (ω (Fin.last M')).1 (ω (Fin.last M')).2 (4 + m)).2 ≤ 1 := by
      constructor
      · exact le_trans (div_nonneg (Nat.cast_nonneg _) (le_of_lt hMR_pos)) hyl.1
      · refine le_trans hyl.2 ?_
        rw [div_le_one hMR_pos]; exact_mod_cast (by simp [M] : (Fin.last M').val + 1 ≤ M)
    have hyh_01 : 0 ≤ (stripUnitPt M (Fin.last M') (ω (Fin.last M')).1 (ω (Fin.last M')).2 0).2 ∧
        (stripUnitPt M (Fin.last M') (ω (Fin.last M')).1 (ω (Fin.last M')).2 0).2 ≤ 1 := by
      constructor
      · exact le_trans (div_nonneg (Nat.cast_nonneg _) (le_of_lt hMR_pos)) hyh.1
      · refine le_trans hyh.2 ?_
        rw [div_le_one hMR_pos]; exact_mod_cast (by simp [M] : (Fin.last M').val + 1 ≤ M)
    rw [hQhead 0]
    split_ifs
    · rw [hQlast]
      have hl1 := euclidDist_le_l1 (stripUnitPt M (Fin.last M') (ω (Fin.last M')).1 (ω (Fin.last M')).2 (4 + m))
        (stripUnitPt M 0 (ω 0).1 (ω 0).2 0)
      rw [hlast_x, hhead_x, sub_zero] at hl1
      have hx : |stripEndX μ (ω (Fin.last M')).1| ≤ |stripEndX μ (ω (Fin.last M')).1 - 1| + 1 := by
        have := abs_add_le (stripEndX μ (ω (Fin.last M')).1 - 1) 1
        simpa using this
      have hy : |(stripUnitPt M (Fin.last M') (ω (Fin.last M')).1 (ω (Fin.last M')).2 (4 + m)).2 -
          (stripUnitPt M 0 (ω 0).1 (ω 0).2 0).2| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hyl_01.1, hy0_01.2], by linarith [hyl_01.2, hy0_01.1]⟩
      linarith
    · rw [hQhead]
      have hl1 := euclidDist_le_l1 (stripUnitPt M (Fin.last M') (ω (Fin.last M')).1 (ω (Fin.last M')).2 0)
        (stripUnitPt M 0 (ω 0).1 (ω 0).2 0)
      rw [hhead_x, hhead_x, sub_self, abs_zero, zero_add] at hl1
      have hy : |(stripUnitPt M (Fin.last M') (ω (Fin.last M')).1 (ω (Fin.last M')).2 0).2 -
          (stripUnitPt M 0 (ω 0).1 (ω 0).2 0).2| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hyh_01.1, hy0_01.2], by linarith [hyh_01.2, hy0_01.1]⟩
      linarith [Finset.sum_nonneg (s := Finset.univ) fun (s : Fin M) _ => abs_nonneg (stripEndX μ (ω s).1 - 1)]
  linarith

/-! ## Section 3: Finite-`(n, M, m, R)` Coupling Inequality -/

lemma ae_mem_stripBoxMeasure {M : ℕ} (hM : 0 < M) (s : Fin M) :
    ∀ᵐ p ∂(stripBoxMeasure M s), p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  unfold stripBoxMeasure
  have hx : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Icc (0 : ℝ) 1 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hy : ∀ᵐ y : ℝ ∂(volume.restrict (Ioc ((s.val : ℝ) / (M : ℝ)) (((s.val : ℝ) + 1) / (M : ℝ)))),
      y ∈ Icc (0 : ℝ) 1 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun y hy => by
      have hs0 : 0 ≤ (s.val : ℝ) / (M : ℝ) := div_nonneg (Nat.cast_nonneg _) (le_of_lt hMpos)
      have hs1 : ((s.val : ℝ) + 1) / (M : ℝ) ≤ 1 := by rw [div_le_one hMpos]; exact_mod_cast s.isLt
      exact ⟨le_of_lt (lt_of_le_of_lt hs0 hy.1), le_trans hy.2 hs1⟩
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).mpr
    (hx.mono fun x hx => hy.mono fun y hy => ⟨hx, hy⟩)

lemma ae_mem_stripFullMeasure_Y (m : ℕ) :
    ∀ᵐ p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) ∂(stripFullMeasure m),
      ∀ j : Fin (8 + m), 0 < p.2 j ∧ p.2 j ≤ 11 / 5 := by
  have h1 : ∀ j : Fin (8 + m), ∀ᵐ Y ∂(Measure.pi fun _ : Fin (8 + m) => unifHMeasure),
      0 < Y j ∧ Y j ≤ 11 / 5 := by
    intro j
    have hm := measurePreserving_eval (fun _ : Fin (8 + m) => unifHMeasure) j
    have hY1 : ∀ᵐ y : ℝ ∂unifHMeasure, 0 < y ∧ y ≤ 11 / 5 := by
      unfold unifHMeasure heightBinMeasure
      rw [ae_withDensity_iff (f := fun y : ℝ => (heightBinDensityNN 1 (11 / 5) 0 y : ℝ≥0∞))
        (measurable_coe_nnreal_ennreal.comp (measurable_heightBinDensityNN 1 (11 / 5) 0))]
      refine ae_of_all _ fun y hy => ?_
      by_contra hnot
      have hmem : y ∉ heightBinSet 1 (11 / 5) 0 := by
        simp only [heightBinSet, Set.mem_Ioc, Nat.cast_zero, zero_mul, zero_add,
          Nat.cast_one, one_mul, div_one]; exact hnot
      simp [heightBinDensityNN, Set.indicator_of_notMem hmem] at hy
    exact hm.quasiMeasurePreserving.ae hY1
  exact measurePreserving_snd.quasiMeasurePreserving.ae (ae_all_iff.mpr h1)

set_option maxHeartbeats 800000 in
/-- Given any concave DP fixed-point certificate
`(V, uBound)` on `automaton4`, there exists `C_strip` independent of `(n, M, m, R)` such that
for all `M ≥ 1`, `m`, and `n ≤ R` (with `μ = M * (11 / 5)^2`):
`(∑ r ∈ Icc n R, poissonProb (M * μ) r) * expectedTourLength n ≤ ...`. -/
theorem expectedTourLength_finite_bound
    (V : Fin 56 → Window 3 4 6 → ℝ) (uBound : ℝ)
    (hfp : ∀ u' z', dpOp automaton4 edgeCost4 V u' z' ≤ V u' z' + uBound) :
    ∃ C_strip : ℝ, ∀ (M' m n R : ℕ), n ≤ R →
      let M : ℕ := M' + 1
      let μ : ℝ := (M : ℝ) * (11 / 5 : ℝ) ^ 2
      (∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r) * expectedTourLength n ≤
        ((m : ℝ) * uBound + C_strip) / (11 / 5 : ℝ) +
        3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) +
        4 +
        (4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j := by
  classical
  obtain ⟨C_strip, hstrip⟩ := strip_expected_path_le V uBound hfp
  refine ⟨C_strip, fun M' m n R hnR => ?_⟩
  intro M μ
  have hMpos : 0 < M := Nat.succ_pos M'
  have hMR_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hμ_pos : 0 < μ := by positivity
  obtain ⟨len, hlen_path, hlen_int, hlen_bound⟩ := hstrip m
  let P_M : Measure (Fin M → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) :=
    Measure.pi fun _ : Fin M => stripFullMeasure m
  haveI : IsProbabilityMeasure P_M := by dsimp only [P_M]; infer_instance
  -- Define the integrable serpentine upper bound `serpBound : (Fin M → Ω_strip) → ℝ`
  let serpBound (ω : Fin M → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) : ℝ :=
    (∑ s : Fin M, len (ω s)) / ((M : ℝ) * (11 / 5 : ℝ)) +
    3 * (∑ s : Fin M, |stripEndX μ (ω s).1 - 1|) + 4
  have hserp_nonneg : ∀ ω, 0 ≤ serpBound ω := by
    intro ω
    have hlen_nn : ∀ s, 0 ≤ len (ω s) := fun s => by
      obtain ⟨P, _, _, _, _, hle⟩ := hlen_path (ω s)
      exact le_trans (listPathLen_nonneg _) hle
    dsimp only [serpBound]
    have h1 : 0 ≤ (∑ s : Fin M, len (ω s)) / ((M : ℝ) * (11 / 5 : ℝ)) :=
      div_nonneg (Finset.sum_nonneg fun s _ => hlen_nn s) (by positivity)
    have h2 : 0 ≤ 3 * (∑ s : Fin M, |stripEndX μ (ω s).1 - 1|) :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => abs_nonneg _)
    linarith
  have hdev := stripEndX_abs_dev_le hμ_pos m
  have hlen_comp_int : ∀ s : Fin M, Integrable (fun ω => len (ω s)) P_M := fun s =>
    integrable_comp_mp (measurePreserving_eval (fun _ : Fin M => stripFullMeasure m) s) hlen_int
  have hdev_comp_int : ∀ s : Fin M, Integrable (fun ω => |stripEndX μ (ω s).1 - 1|) P_M := fun s =>
    integrable_comp_mp (measurePreserving_eval (fun _ : Fin M => stripFullMeasure m) s) hdev.1
  have hserp_int : Integrable serpBound P_M :=
    (((integrable_finsetSum _ fun s _ => hlen_comp_int s).div_const _).add
      ((integrable_finsetSum _ fun s _ => hdev_comp_int s).const_mul 3)).add (integrable_const 4)
  have hserp_exp_le : ∫ ω, serpBound ω ∂P_M ≤
      ((m : ℝ) * uBound + C_strip) / (11 / 5 : ℝ) +
      3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) + 4 := by
    let f1 : (Fin M → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) → ℝ :=
      fun ω => (∑ s : Fin M, len (ω s)) / ((M : ℝ) * (11 / 5 : ℝ))
    let f2 : (Fin M → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) → ℝ :=
      fun ω => 3 * (∑ s : Fin M, |stripEndX μ (ω s).1 - 1|)
    have hf1 : Integrable f1 P_M := (integrable_finsetSum _ fun s _ => hlen_comp_int s).div_const _
    have hf2 : Integrable f2 P_M := (integrable_finsetSum _ fun s _ => hdev_comp_int s).const_mul 3
    have hsplit : ∫ ω, serpBound ω ∂P_M =
        (∑ s : Fin M, ∫ ω, len (ω s) ∂P_M) / ((M : ℝ) * (11 / 5 : ℝ)) +
        3 * (∑ s : Fin M, ∫ ω, |stripEndX μ (ω s).1 - 1| ∂P_M) + 4 := by
      have h1 : ∫ ω, serpBound ω ∂P_M = (∫ ω, (f1 ω + f2 ω) ∂P_M) + ∫ _, (4 : ℝ) ∂P_M :=
        integral_add (hf1.add hf2) (integrable_const 4)
      have h2 : ∫ ω, (f1 ω + f2 ω) ∂P_M = (∫ ω, f1 ω ∂P_M) + ∫ ω, f2 ω ∂P_M :=
        integral_add hf1 hf2
      have h3 : ∫ ω, f1 ω ∂P_M = (∑ s : Fin M, ∫ ω, len (ω s) ∂P_M) / ((M : ℝ) * (11 / 5 : ℝ)) := by
        dsimp only [f1]; rw [integral_div, integral_finsetSum _ (fun s _ => hlen_comp_int s)]
      have h4 : ∫ ω, f2 ω ∂P_M = 3 * ∑ s : Fin M, ∫ ω, |stripEndX μ (ω s).1 - 1| ∂P_M := by
        dsimp only [f2]; rw [integral_const_mul, integral_finsetSum _ (fun s _ => hdev_comp_int s)]
      have h5 : ∫ _, (4 : ℝ) ∂P_M = 4 := by
        rw [integral_const, show P_M.real Set.univ = 1 by simp [Measure.real], smul_eq_mul, one_mul]
      rw [h1, h2, h3, h4, h5]
    rw [hsplit]
    have hlen_s : ∀ s : Fin M, ∫ ω, len (ω s) ∂P_M ≤ (m : ℝ) * uBound + C_strip := fun s => by
      have hm := measurePreserving_eval (fun _ : Fin M => stripFullMeasure m) s
      have haesm : AEStronglyMeasurable len (Measure.map (Function.eval s) P_M) := by
        rw [hm.map_eq]; exact hlen_int.aestronglyMeasurable
      have hmap := integral_map (μ := P_M) hm.measurable.aemeasurable haesm
      rw [hm.map_eq] at hmap; rw [← hmap]; exact hlen_bound
    have hdev_s : ∀ s : Fin M, ∫ ω, |stripEndX μ (ω s).1 - 1| ∂P_M ≤
        Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) := fun s => by
      have hm := measurePreserving_eval (fun _ : Fin M => stripFullMeasure m) s
      have haesm : AEStronglyMeasurable (fun p : (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ) => |stripEndX μ p.1 - 1|)
          (Measure.map (Function.eval s) P_M) := by
        rw [hm.map_eq]; exact hdev.1.aestronglyMeasurable
      have hmap := integral_map (μ := P_M) hm.measurable.aemeasurable haesm
      rw [hm.map_eq] at hmap; rw [← hmap]; exact hdev.2
    have hsum1 : (∑ s : Fin M, ∫ ω, len (ω s) ∂P_M) / ((M : ℝ) * (11 / 5 : ℝ)) ≤
        ((m : ℝ) * uBound + C_strip) / (11 / 5 : ℝ) := by
      have h1 : ∑ s : Fin M, ∫ ω, len (ω s) ∂P_M ≤ (M : ℝ) * ((m : ℝ) * uBound + C_strip) := by
        calc ∑ s : Fin M, ∫ ω, len (ω s) ∂P_M
            ≤ ∑ _ : Fin M, ((m : ℝ) * uBound + C_strip) := Finset.sum_le_sum fun s _ => hlen_s s
          _ = (M : ℝ) * ((m : ℝ) * uBound + C_strip) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc (∑ s : Fin M, ∫ ω, len (ω s) ∂P_M) / ((M : ℝ) * (11 / 5 : ℝ))
          ≤ ((M : ℝ) * ((m : ℝ) * uBound + C_strip)) / ((M : ℝ) * (11 / 5 : ℝ)) :=
            div_le_div_of_nonneg_right h1 (by positivity)
        _ = ((m : ℝ) * uBound + C_strip) / (11 / 5 : ℝ) := mul_div_mul_left _ _ (ne_of_gt hMR_pos)
    have hsum2 : 3 * ∑ s : Fin M, ∫ ω, |stripEndX μ (ω s).1 - 1| ∂P_M ≤
        3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) := by
      have h2 : ∑ s : Fin M, ∫ ω, |stripEndX μ (ω s).1 - 1| ∂P_M ≤
          (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) := by
        calc ∑ s : Fin M, ∫ ω, |stripEndX μ (ω s).1 - 1| ∂P_M
            ≤ ∑ _ : Fin M, Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) :=
              Finset.sum_le_sum fun s _ => hdev_s s
          _ = (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linarith
    linarith
  -- Step 1: Work in `ℝ≥0∞` via `ENNReal.ofReal`.
  -- First show `ENNReal.ofReal ((∑ r ∈ Icc n R, poissonProb (M * μ) r) * expectedTourLength n)` is bounded by
  -- `∑ r ∈ Icc n R, ENNReal.ofReal (poissonProb (M * μ) r) * ∫⁻ x, ENNReal.ofReal (tourLength x) ∂(unitSquarePi r)`.
  have hlhs_enn : ENNReal.ofReal ((∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r) * expectedTourLength n) ≤
      ∑ r ∈ Finset.Icc n R, ENNReal.ofReal (poissonProb ((M : ℝ) * μ) r) *
        ∫⁻ x : Fin r → ℝ × ℝ, ENNReal.ofReal (tourLength x) ∂(unitSquarePi r) := by
    have hmono_sum : (∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r) * expectedTourLength n ≤
        ∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r * expectedTourLength r := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun r hr =>
        mul_le_mul_of_nonneg_left (expectedTourLength_mono (Finset.mem_Icc.mp hr).1)
          (poissonProb_nonneg (by positivity) r)
    refine (ENNReal.ofReal_le_ofReal hmono_sum).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun r => poissonProb ((M : ℝ) * μ) r * expectedTourLength r)
      (fun r _ => mul_nonneg (poissonProb_nonneg (by positivity) r)
        (integral_nonneg fun x => tourLength_nonneg x))]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [ENNReal.ofReal_mul (poissonProb_nonneg (by positivity) r)]
    dsimp only [expectedTourLength]
    rw [ofReal_integral_eq_lintegral_ofReal (tourLength_integrable r) (ae_of_all _ fun x => tourLength_nonneg x)]
  -- Step 2: For each `r ∈ Icc n R`, split `unitSquarePi r` into `Good(r)` (`∀ s, hist a s < 4 + m`) and `Bad(r)`.
  let goodK (r : ℕ) : Finset (Fin M → Fin (4 + m)) :=
    Finset.univ.filter fun kf : Fin M → Fin (4 + m) => ∑ s : Fin M, (kf s).val = r
  let evK (kf : Fin M → Fin (4 + m)) : Set (Fin M → (Fin (7 + m) → ℝ) × (Fin (8 + m) → ℝ)) :=
    Set.pi Set.univ fun s : Fin M => stripArrivalEvent M m (kf s).val (kf s).isLt
  have hae_Y_M : ∀ᵐ ω ∂P_M, ∀ (s : Fin M) (j : Fin (8 + m)), 0 < (ω s).2 j ∧ (ω s).2 j ≤ 11 / 5 := by
    refine ae_all_iff.mpr fun s => ?_
    exact (measurePreserving_eval (fun _ : Fin M => stripFullMeasure m) s).quasiMeasurePreserving.ae
      (ae_mem_stripFullMeasure_Y m)
  have hsplit_r : ∀ r ∈ Finset.Icc n R,
      ENNReal.ofReal (poissonProb ((M : ℝ) * μ) r) *
        ∫⁻ x : Fin r → ℝ × ℝ, ENNReal.ofReal (tourLength x) ∂(unitSquarePi r) ≤
      (∑ kf ∈ goodK r, ∫⁻ ω in evK kf, ENNReal.ofReal (serpBound ω) ∂P_M) +
      ENNReal.ofReal ((4 * Real.sqrt (R : ℝ) + 4) * poissonProb ((M : ℝ) * μ) r *
        (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, 4 + m ≤ hist a s).card : ℝ) / (M : ℝ) ^ r)) := by
    intro r hr
    rw [unitSquarePi_eq_sum_assignments hMpos r, lintegral_finsetSum_measure]
    let goodA := Finset.univ.filter fun a : Fin r → Fin M => ∀ s : Fin M, hist a s < 4 + m
    let badA := Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, 4 + m ≤ hist a s
    have hpartA : (Finset.univ : Finset (Fin r → Fin M)) = goodA ∪ badA := by
      ext a; simp only [goodA, badA, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, true_iff]
      by_cases h : ∀ s : Fin M, hist a s < 4 + m
      · exact Or.inl h
      · push Not at h; exact Or.inr h
    have hdisjA : Disjoint goodA badA := by
      rw [Finset.disjoint_left]
      intro a h1 h2
      obtain ⟨s, hs⟩ := (Finset.mem_filter.mp h2).2
      have := (Finset.mem_filter.mp h1).2 s; omega
    conv_lhs => rw [hpartA, Finset.sum_union hdisjA, mul_add]
    refine add_le_add ?_ ?_
    · -- Good part: group `goodA` by `kf : Fin M → Fin (4 + m)` with `∑ s, (kf s).val = r`
      have hgroup : ∑ a ∈ goodA, ∫⁻ x : Fin r → ℝ × ℝ, ENNReal.ofReal (tourLength x)
            ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) =
          ∑ kf ∈ goodK r, ∑ a ∈ Finset.univ.filter (fun a : Fin r → Fin M => hist a = fun s => (kf s).val),
            ∫⁻ x : Fin r → ℝ × ℝ, ENNReal.ofReal (tourLength x)
              ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) := by
        rw [← Finset.sum_biUnion]
        · congr 1; ext a
          simp only [goodA, goodK, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro ha
            refine ⟨fun s => ⟨hist a s, ha s⟩, sum_hist a, rfl⟩
          · rintro ⟨kf, _, hkf⟩ s
            rw [congrFun hkf s]; exact (kf s).isLt
        · intro kf1 _ kf2 _ hne
          rw [Function.onFun, Finset.disjoint_left]
          intro a h1 h2
          apply hne; funext s; apply Fin.ext
          exact congrFun ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2) s
      rw [hgroup, Finset.mul_sum]
      refine Finset.sum_le_sum fun kf hkf => ?_
      have hr_kf : ∑ s : Fin M, (kf s).val = r := (Finset.mem_filter.mp hkf).2
      let e : (Σ s : Fin M, Fin (kf s).val) ≃ Fin r :=
        Fintype.equivFinOfCardEq (by rw [Fintype.card_sigma]; simp only [Fintype.card_fin]; exact hr_kf)
      have hhist := multi_strip_hist_sum hMpos m r (fun s => (kf s).val) (fun s => (kf s).isLt) hr_kf e
        (fun x => ENNReal.ofReal (tourLength x))
        (ENNReal.measurable_ofReal.comp (continuous_tourLength r).measurable)
        (fun σ x => by rw [tourLength_perm])
      rw [hhist]
      -- Bound `tourLength (multiArrPts)` by `serpBound ω` a.e. on `evK kf`.
      refine setLIntegral_mono_ae' (MeasurableSet.univ_pi fun s =>
        measurableSet_stripArrivalEvent M m (kf s).val (kf s).isLt) ?_
      filter_upwards [hae_Y_M] with ω hYω _
      refine ENNReal.ofReal_le_ofReal ?_
      let P : Fin M → List ℕ := fun s => (hlen_path (ω s)).choose
      have hPspec : ∀ s, ∃ hne : P s ≠ [],
          (P s).Perm (List.range (4 + m + 1)) ∧
          (P s).head hne = 0 ∧
          (P s).getLast hne = 4 + m ∧
          listPathLen ((P s).map (stripPt (ω s).1 (ω s).2)) ≤ len (ω s) := fun s =>
        (hlen_path (ω s)).choose_spec
      have h1 := serpentine_tourLength_le (fun s => (kf s).val) (fun s => (kf s).isLt) e ω P
        (fun s => (hPspec s).choose_spec.1)
      have h2 := serpentine_cycleLen_le_bound ω hYω P
        (fun s => (hPspec s).choose)
        (fun s => (hPspec s).choose_spec.2.1)
        (fun s => (hPspec s).choose_spec.2.2.1)
        len (fun s => (hPspec s).choose_spec.2.2.2)
      exact h1.trans h2
    · -- Bad part: on each `a ∈ badA`, `tourLength x ≤ 4 * √r + 4 ≤ 4 * √R + 4` a.e., and total mass is `M^(-r)`.
      have hrR : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).2
      have hsqrt_le : 4 * Real.sqrt (r : ℝ) + 4 ≤ 4 * Real.sqrt (R : ℝ) + 4 := by
        have := Real.sqrt_le_sqrt hrR; linarith
      have ha_le : ∀ a : Fin r → Fin M,
          ∫⁻ x : Fin r → ℝ × ℝ, ENNReal.ofReal (tourLength x)
            ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) ≤
          ENNReal.ofReal (4 * Real.sqrt (R : ℝ) + 4) * ((M : ℝ≥0∞)⁻¹) ^ r := by
        intro a
        have hae_sq : ∀ᵐ x ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i)),
            ∀ i : Fin r, x i ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
          refine ae_all_iff.mpr fun i => ?_
          have hI : ∀ j : Fin r, IsFiniteMeasure (stripBoxMeasure M (a j)) := fun _ => inferInstance
          -- Evaluate coordinate `i` directly via `Measure.pi_pi` on `{x | x i ∉ [0,1]^2}`.
          have hnull : (Measure.pi fun j : Fin r => stripBoxMeasure M (a j))
              {x : Fin r → ℝ × ℝ | x i ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1} = 0 := by
            let t : Fin r → Set (ℝ × ℝ) := fun j =>
              if j = i then (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)ᶜ else Set.univ
            have heq : {x : Fin r → ℝ × ℝ | x i ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1} = Set.pi Set.univ t := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left, t]
              constructor
              · intro hx j; split_ifs with h
                · subst h; exact hx
                · trivial
              · intro hx; simpa using hx i
            rw [heq, Measure.pi_pi]
            refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
            simp only [t, ↓reduceIte]
            exact ae_iff.mp (ae_mem_stripBoxMeasure hMpos (a i))
          exact ae_iff.mpr hnull
        calc ∫⁻ x, ENNReal.ofReal (tourLength x) ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i))
            ≤ ∫⁻ _, ENNReal.ofReal (4 * Real.sqrt (R : ℝ) + 4)
                ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) :=
              lintegral_mono_ae (hae_sq.mono fun x hx =>
                ENNReal.ofReal_le_ofReal ((tourLength_unitSquare_le x hx).trans hsqrt_le))
          _ = ENNReal.ofReal (4 * Real.sqrt (R : ℝ) + 4) *
                (Measure.pi fun i : Fin r => stripBoxMeasure M (a i)) Set.univ := lintegral_const _
          _ = ENNReal.ofReal (4 * Real.sqrt (R : ℝ) + 4) * ((M : ℝ≥0∞)⁻¹) ^ r := by
              congr 1
              rw [← Set.pi_univ, Measure.pi_pi]
              simp [stripBoxMeasure_univ hMpos]
      calc ENNReal.ofReal (poissonProb ((M : ℝ) * μ) r) *
            ∑ a ∈ badA, ∫⁻ x, ENNReal.ofReal (tourLength x) ∂(Measure.pi fun i : Fin r => stripBoxMeasure M (a i))
          ≤ ENNReal.ofReal (poissonProb ((M : ℝ) * μ) r) *
            ∑ _ ∈ badA, (ENNReal.ofReal (4 * Real.sqrt (R : ℝ) + 4) * ((M : ℝ≥0∞)⁻¹) ^ r) := by
            gcongr; exact ha_le _
        _ = ENNReal.ofReal ((4 * Real.sqrt (R : ℝ) + 4) * poissonProb ((M : ℝ) * μ) r *
              ((badA.card : ℝ) / (M : ℝ) ^ r)) := by
            have h4R_nn : 0 ≤ 4 * Real.sqrt (R : ℝ) + 4 := by linarith [Real.sqrt_nonneg (R : ℝ)]
            have hinv_nn : 0 ≤ ((M : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt hMR_pos)
            have hcard_nn : 0 ≤ (badA.card : ℝ) := Nat.cast_nonneg _
            have hpp_nn : 0 ≤ poissonProb ((M : ℝ) * μ) r :=
              poissonProb_nonneg (mul_nonneg (le_of_lt hMR_pos) (le_of_lt hμ_pos)) r
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_inv_of_pos hMR_pos,
                ← ENNReal.ofReal_pow hinv_nn, ← ENNReal.ofReal_natCast badA.card,
                ← ENNReal.ofReal_mul h4R_nn, ← ENNReal.ofReal_mul hcard_nn,
                ← ENNReal.ofReal_mul hpp_nn]
            congr 1; rw [inv_pow, div_eq_mul_inv]; ring
  -- Step 3: Sum `hsplit_r` over `r ∈ Icc n R`.
  -- The `evK kf` across all `(r, kf)` with `kf ∈ goodK r` are pairwise disjoint (since `kf` uniquely determines `r`),
  -- so their sum is `≤ ∫⁻ ω, ENNReal.ofReal (serpBound ω) ∂P_M = ENNReal.ofReal (∫ ω, serpBound ω ∂P_M)`.
  have hgood_sum : ∑ r ∈ Finset.Icc n R, ∑ kf ∈ goodK r, ∫⁻ ω in evK kf, ENNReal.ofReal (serpBound ω) ∂P_M ≤
      ENNReal.ofReal (∫ ω, serpBound ω ∂P_M) := by
    let allGood : Finset (Fin M → Fin (4 + m)) := (Finset.Icc n R).biUnion goodK
    have hbiU : ∑ r ∈ Finset.Icc n R, ∑ kf ∈ goodK r, ∫⁻ ω in evK kf, ENNReal.ofReal (serpBound ω) ∂P_M =
        ∑ kf ∈ allGood, ∫⁻ ω in evK kf, ENNReal.ofReal (serpBound ω) ∂P_M := by
      symm
      refine Finset.sum_biUnion fun r1 _ r2 _ hne => ?_
      rw [Function.onFun, Finset.disjoint_left]
      intro kf h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hbiU]
    have hdisj_ev : (allGood : Set (Fin M → Fin (4 + m))).PairwiseDisjoint evK := by
      intro kf1 _ kf2 _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω h1 h2
      have hex : ∃ s : Fin M, kf1 s ≠ kf2 s := by
        by_contra hall; push Not at hall; exact hne (funext hall)
      obtain ⟨s, hs⟩ := hex
      exact Set.disjoint_left.mp (stripArrivalEvent_pairwiseDisjoint M m hs)
        (h1 s (Set.mem_univ s)) (h2 s (Set.mem_univ s))
    rw [← lintegral_biUnion_finset hdisj_ev (fun kf _ => MeasurableSet.univ_pi fun s =>
      measurableSet_stripArrivalEvent M m (kf s).val (kf s).isLt)]
    refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
    exact (ofReal_integral_eq_lintegral_ofReal hserp_int (ae_of_all _ hserp_nonneg)).symm
  have hbad_sum : ∑ r ∈ Finset.Icc n R,
        ENNReal.ofReal ((4 * Real.sqrt (R : ℝ) + 4) * poissonProb ((M : ℝ) * μ) r *
          (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, 4 + m ≤ hist a s).card : ℝ) / (M : ℝ) ^ r)) ≤
      ENNReal.ofReal ((4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => by
      have := poissonProb_nonneg (by positivity : 0 ≤ (M : ℝ) * μ) r; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hfact : ∑ r ∈ Finset.Icc n R, (4 * Real.sqrt (R : ℝ) + 4) * poissonProb ((M : ℝ) * μ) r *
          (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, 4 + m ≤ hist a s).card : ℝ) / (M : ℝ) ^ r) =
        (4 * Real.sqrt (R : ℝ) + 4) * ∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r *
          (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, 4 + m ≤ hist a s).card : ℝ) / (M : ℝ) ^ r) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
    rw [hfact, mul_assoc]
    exact mul_le_mul_of_nonneg_left (bad_assignments_poisson_sum_le hMpos (le_of_lt hμ_pos) (4 + m) n R) (by positivity)
  -- Combine in `ℝ≥0∞` and convert back to `ℝ`.
  have htot_enn : ENNReal.ofReal ((∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r) * expectedTourLength n) ≤
      ENNReal.ofReal (∫ ω, serpBound ω ∂P_M +
        (4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j) := by
    rw [ENNReal.ofReal_add (integral_nonneg hserp_nonneg)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => poissonProb_nonneg (le_of_lt hμ_pos) j))]
    calc ENNReal.ofReal ((∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r) * expectedTourLength n)
        ≤ ∑ r ∈ Finset.Icc n R, ENNReal.ofReal (poissonProb ((M : ℝ) * μ) r) *
            ∫⁻ x : Fin r → ℝ × ℝ, ENNReal.ofReal (tourLength x) ∂(unitSquarePi r) := hlhs_enn
      _ ≤ ∑ r ∈ Finset.Icc n R,
            ((∑ kf ∈ goodK r, ∫⁻ ω in evK kf, ENNReal.ofReal (serpBound ω) ∂P_M) +
              ENNReal.ofReal ((4 * Real.sqrt (R : ℝ) + 4) * poissonProb ((M : ℝ) * μ) r *
                (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, 4 + m ≤ hist a s).card : ℝ) / (M : ℝ) ^ r))) :=
          Finset.sum_le_sum hsplit_r
      _ = (∑ r ∈ Finset.Icc n R, ∑ kf ∈ goodK r, ∫⁻ ω in evK kf, ENNReal.ofReal (serpBound ω) ∂P_M) +
          ∑ r ∈ Finset.Icc n R, ENNReal.ofReal ((4 * Real.sqrt (R : ℝ) + 4) * poissonProb ((M : ℝ) * μ) r *
            (((Finset.univ.filter fun a : Fin r → Fin M => ∃ s : Fin M, 4 + m ≤ hist a s).card : ℝ) / (M : ℝ) ^ r)) :=
          Finset.sum_add_distrib
      _ ≤ ENNReal.ofReal (∫ ω, serpBound ω ∂P_M) +
          ENNReal.ofReal ((4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j) :=
          add_le_add hgood_sum hbad_sum
  have htot_real : (∑ r ∈ Finset.Icc n R, poissonProb ((M : ℝ) * μ) r) * expectedTourLength n ≤
      ∫ ω, serpBound ω ∂P_M +
        (4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j := by
    have hrhs_nn : 0 ≤ ∫ ω, serpBound ω ∂P_M +
        (4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j :=
      add_nonneg (integral_nonneg hserp_nonneg)
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => poissonProb_nonneg (le_of_lt hμ_pos) j))
    exact (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp htot_enn
  linarith [hserp_exp_le]

/-! ## Section 4: Asymptotic Upper Bound `expectedTourLength n / √n ≤ uBound + ε` -/

/-- Elementary polynomial lower bound on `exp x`: `x ^ k / k! ≤ exp x` for `x ≥ 0`. -/
lemma pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ k / (k.factorial : ℝ) ≤ Real.exp x := by
  calc x ^ k / (k.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (k + 1), x ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum (f := fun i : ℕ => x ^ i / (i.factorial : ℝ))
          (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self k))
    _ ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx (k + 1)

set_option maxHeartbeats 800000 in
/-- Asymptotic upper bound: for any concave DP fixed-point certificate `(V, uBound)`
on `automaton4`, `expectedTourLength n / √n ≤ uBound + ε` for all sufficiently large `n`. -/
theorem expectedTourLength_div_sqrt_le_of_dp
    (V : Fin 56 → Window 3 4 6 → ℝ) (uBound : ℝ)
    (hfp : ∀ u' z', dpOp automaton4 edgeCost4 V u' z' ≤ V u' z' + uBound) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, expectedTourLength n / Real.sqrt (n : ℝ) ≤ uBound + ε := by
  obtain ⟨C_strip, hfin⟩ := expectedTourLength_finite_bound V uBound hfp
  intro ε hε
  set Uabs : ℝ := |uBound| + 1
  set Cabs : ℝ := |C_strip| + 1
  -- Choose `r₀ : ℕ` large enough that all error terms are `< ε / 6` when `r = ⌊n^(1/8)⌋ ≥ r₀`
  let K : ℝ := 1000 * (Uabs + Cabs + 10 ^ 15)
  let r₀ : ℕ := max 100 (Nat.ceil (K / ε) + 1)
  refine ⟨r₀ ^ 8, fun n hn => ?_⟩
  have hr₀_ge : 100 ≤ r₀ := le_max_left _ _
  have hr₀_eps : K / ε ≤ (r₀ : ℝ) := by
    have : Nat.ceil (K / ε) ≤ r₀ := le_trans (Nat.le_succ _) (le_max_right _ _)
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  -- Define pure-`Nat.sqrt` dyadic-scale parameters `s ≈ n^(1/2)`, `q ≈ n^(1/4)`, `r ≈ n^(1/8)`
  let s : ℕ := Nat.sqrt n
  let q : ℕ := Nat.sqrt s
  let r : ℕ := Nat.sqrt q
  have hs_ge : r₀ ^ 4 ≤ s := by
    rw [Nat.le_sqrt]; calc r₀ ^ 4 * r₀ ^ 4 = r₀ ^ 8 := by ring
      _ ≤ n := hn
  have hq_ge : r₀ ^ 2 ≤ q := by
    rw [Nat.le_sqrt]; calc r₀ ^ 2 * r₀ ^ 2 = r₀ ^ 4 := by ring
      _ ≤ s := hs_ge
  have hr_ge : r₀ ≤ r := by
    rw [Nat.le_sqrt]; calc r₀ * r₀ = r₀ ^ 2 := by ring
      _ ≤ q := hq_ge
  have hr_100 : (100 : ℝ) ≤ (r : ℝ) := by exact_mod_cast le_trans hr₀_ge hr_ge
  have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hq_lo : (r : ℝ) ^ 2 ≤ (q : ℝ) := by exact_mod_cast (by rw [sq]; exact Nat.sqrt_le q)
  have hq_hi : (q : ℝ) ≤ ((r : ℝ) + 1) ^ 2 := by
    have hlt : q < (r + 1) * (r + 1) := Nat.lt_succ_sqrt q
    exact_mod_cast (by nlinarith only [hlt] : q ≤ (r + 1) ^ 2)
  have hs_lo : (q : ℝ) ^ 2 ≤ (s : ℝ) := by exact_mod_cast (by rw [sq]; exact Nat.sqrt_le s)
  have hs_hi : (s : ℝ) ≤ ((q : ℝ) + 1) ^ 2 := by
    have hlt : s < (q + 1) * (q + 1) := Nat.lt_succ_sqrt s
    exact_mod_cast (by nlinarith only [hlt] : s ≤ (q + 1) ^ 2)
  have hn_lo : (s : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast (by rw [sq]; exact Nat.sqrt_le n)
  have hn_hi : (n : ℝ) ≤ ((s : ℝ) + 1) ^ 2 := by
    have hlt : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
    exact_mod_cast (by nlinarith only [hlt] : n ≤ (s + 1) ^ 2)
  have hq_10000 : (10000 : ℝ) ≤ (q : ℝ) := by nlinarith only [hr_100, hq_lo]
  have hr100_le_q : 100 * (r : ℝ) ≤ (q : ℝ) := by nlinarith only [hr_100, hq_lo]
  have hr_le_q : (r : ℝ) ≤ (q : ℝ) := by linarith
  have hqr2 : (q : ℝ) * (r : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith only [hq_lo, hq_10000]
  have hs_ge_q2 : (10 ^ 8 : ℝ) ≤ (s : ℝ) := by nlinarith only [hq_10000, hs_lo]
  have hsn_lo : (s : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; exact hn_lo
  have hsn_hi : Real.sqrt (n : ℝ) ≤ (s : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; exact hn_hi
  have hsn_pos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hsn_ge_q2 : (q : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) := le_trans hs_lo hsn_lo
  have hsn_le_2q2 : Real.sqrt (n : ℝ) ≤ 2 * (q : ℝ) ^ 2 := by nlinarith only [hsn_hi, hs_hi, hq_10000]
  -- Choose strip count `M = M' + 1`, per-strip budget `m`, and cap `R`
  let c : ℝ := 11 / 5
  let M : ℕ := Nat.ceil (Real.sqrt (n : ℝ) / c) + q
  have hq_pos : 0 < q := by
    have : 100 ^ 2 ≤ q := le_trans (Nat.pow_le_pow_left hr₀_ge 2) hq_ge
    omega
  have hM_pos : 0 < M := by dsimp only [M]; omega
  let M' : ℕ := M - 1
  have hM_eq : M' + 1 = M := by omega
  let μ : ℝ := (M : ℝ) * c ^ 2
  let lam : ℝ := (M : ℝ) * μ
  let m : ℕ := Nat.floor μ + q * r
  let R : ℕ := Nat.ceil (2 * lam)
  have hMc_lo : Real.sqrt (n : ℝ) + c * (q : ℝ) ≤ (M : ℝ) * c := by
    have h1 : Real.sqrt (n : ℝ) / c ≤ (Nat.ceil (Real.sqrt (n : ℝ) / c) : ℝ) := Nat.le_ceil _
    have hMcast : (M : ℝ) = (Nat.ceil (Real.sqrt (n : ℝ) / c) : ℝ) + (q : ℝ) := by
      dsimp only [M]; push_cast; rfl
    rw [hMcast]; dsimp only [c] at h1 ⊢; linarith
  have hMc_hi : (M : ℝ) * c ≤ Real.sqrt (n : ℝ) + c * (q : ℝ) + c := by
    have h1 : (Nat.ceil (Real.sqrt (n : ℝ) / c) : ℝ) < Real.sqrt (n : ℝ) / c + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hMcast : (M : ℝ) = (Nat.ceil (Real.sqrt (n : ℝ) / c) : ℝ) + (q : ℝ) := by
      dsimp only [M]; push_cast; rfl
    rw [hMcast]; dsimp only [c] at h1 ⊢; linarith
  have hlam_eq : lam = ((M : ℝ) * c) ^ 2 := by dsimp only [lam, μ]; ring
  have hμ_lo : c * Real.sqrt (n : ℝ) ≤ μ := by
    dsimp only [μ, c] at hMc_lo ⊢; nlinarith only [hMc_lo, hq_10000]
  have hμ_hi : μ ≤ 2 * c * Real.sqrt (n : ℝ) := by
    dsimp only [μ, c] at hMc_hi ⊢; nlinarith only [hMc_hi, hsn_ge_q2, hq_10000]
  have hμ_pos : 0 < μ := by dsimp only [c] at hμ_lo; linarith
  have hlam_lo : (n : ℝ) + 2 * c * Real.sqrt (n : ℝ) * (q : ℝ) ≤ lam := by
    rw [hlam_eq]
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    dsimp only [c] at hMc_lo ⊢
    nlinarith only [hMc_lo, hsq, hsn_pos, hq_10000]
  have hlam_hi : lam ≤ 2 * (n : ℝ) := by
    rw [hlam_eq]
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    dsimp only [c] at hMc_hi ⊢
    have hMc_54 : (M : ℝ) * (11 / 5 : ℝ) ≤ (5 / 4 : ℝ) * Real.sqrt (n : ℝ) := by
      nlinarith only [hMc_hi, hsn_ge_q2, hq_10000]
    have hMc_nn : 0 ≤ (M : ℝ) * (11 / 5 : ℝ) := by positivity
    nlinarith only [hMc_54, hMc_nn, hsq]
  have hlam_nn : 0 ≤ lam := by rw [hlam_eq]; exact sq_nonneg _
  have hnR : n ≤ R := by
    have hlam_ge_n : (n : ℝ) ≤ lam := by
      dsimp only [c] at hlam_lo; nlinarith only [hlam_lo, hsn_pos, hq_10000]
    have h1 : (n : ℝ) ≤ (R : ℝ) := by
      have := Nat.le_ceil (2 * lam)
      dsimp only [R]; linarith
    exact_mod_cast h1
  have hmain := hfin M' m n R hnR
  simp only [hM_eq] at hmain
  -- Step 1: Chebyshev lower bound on `p_good := ∑ r ∈ Icc n R, poissonProb lam r ≥ 1 - 1 / q^2 ≥ 1/2`
  let p_good : ℝ := ∑ k ∈ Finset.Icc n R, poissonProb lam k
  let d : ℝ := c * Real.sqrt (n : ℝ) * (q : ℝ)
  have hd_pos : 0 < d := by dsimp only [d, c]; positivity
  have hcheb : 1 - p_good ≤ lam / d ^ 2 := by
    refine poisson_chebyshev hlam_nn hd_pos ?_ ?_
    · have : (n : ℝ) + 2 * d ≤ lam := by dsimp only [d]; linarith [hlam_lo]
      linarith
    · have hR_lo : 2 * lam ≤ (R : ℝ) := Nat.le_ceil _
      have hd_le_lam : d ≤ lam := by
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have : (n : ℝ) + 2 * d ≤ lam := by dsimp only [d]; linarith [hlam_lo]
        linarith
      linarith
  have hcheb_small : 1 - p_good ≤ 1 / (r : ℝ) := by
    have h1 : lam / d ^ 2 ≤ 1 / (r : ℝ) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hd_pos) hr_pos]
      have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
      have hd2 : d ^ 2 = c ^ 2 * (n : ℝ) * (q : ℝ) ^ 2 := by dsimp only [d]; rw [mul_pow, mul_pow, hsq]
      rw [hd2]
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hlam_r : lam * (r : ℝ) ≤ 2 * (n : ℝ) * (q : ℝ) := by
        have h1 : lam * (r : ℝ) ≤ (2 * (n : ℝ)) * (q : ℝ) :=
          mul_le_mul hlam_hi hr_le_q (le_of_lt hr_pos) (by linarith)
        linarith
      have hnq : (n : ℝ) * (q : ℝ) ≤ (n : ℝ) * (q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hq_10000]) hn_nn
      dsimp only [c]
      nlinarith only [hlam_r, hnq]
    exact hcheb.trans h1
  have hp_ge_half : (1 / 2 : ℝ) ≤ p_good := by
    have : 1 / (r : ℝ) ≤ 1 / 100 := by
      rw [div_le_div_iff₀ hr_pos (by norm_num)]; linarith
    linarith
  -- Step 2: Bound each of the 4 RHS terms divided by `√n`.
  -- Term A: `((m * uBound + C_strip) / c) / √n ≤ uBound + (3 * Uabs + Cabs) / r`
  have hm_lo : μ + (q : ℝ) * (r : ℝ) - 1 ≤ (m : ℝ) := by
    have hfl : μ - 1 < (Nat.floor μ : ℝ) := Nat.sub_one_lt_floor μ
    have hmcast : (m : ℝ) = (Nat.floor μ : ℝ) + (q : ℝ) * (r : ℝ) := by dsimp only [m]; push_cast; rfl
    linarith
  have hm_hi : (m : ℝ) ≤ μ + (q : ℝ) * (r : ℝ) := by
    have hfl : (Nat.floor μ : ℝ) ≤ μ := Nat.floor_le (le_of_lt hμ_pos)
    have hmcast : (m : ℝ) = (Nat.floor μ : ℝ) + (q : ℝ) * (r : ℝ) := by dsimp only [m]; push_cast; rfl
    linarith
  have hm_div_diff : |(m : ℝ) / (c * Real.sqrt (n : ℝ)) - 1| ≤ 3 / (r : ℝ) := by
    have hc_pos : 0 < c := by dsimp only [c]; norm_num
    have hden_pos : 0 < c * Real.sqrt (n : ℝ) := mul_pos hc_pos hsn_pos
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hden_pos, add_mul, one_mul, neg_mul]
      -- `m ≥ μ ≥ c * √n`, so `m / (c √n) ≥ 1`.
      have hm_ge : c * Real.sqrt (n : ℝ) ≤ (m : ℝ) := by nlinarith only [hm_lo, hμ_lo, hq_10000, hr_100]
      have h3r : 0 ≤ 3 / (r : ℝ) * (c * Real.sqrt (n : ℝ)) := by positivity
      calc -(3 / (r : ℝ) * (c * Real.sqrt (n : ℝ))) + c * Real.sqrt (n : ℝ)
          ≤ 0 + c * Real.sqrt (n : ℝ) := add_le_add (neg_nonpos.mpr h3r) le_rfl
        _ = c * Real.sqrt (n : ℝ) := zero_add _
        _ ≤ (m : ℝ) := hm_ge
    · rw [sub_le_iff_le_add, div_le_iff₀ hden_pos, add_mul, one_mul]
      -- `m ≤ μ + q*r ≤ c*(√n + c*q + c) + q*r = c*√n + c^2*q + c^2 + q*r`
      have hμ_ub : μ ≤ c * Real.sqrt (n : ℝ) + c ^ 2 * (q : ℝ) + c ^ 2 := by
        dsimp only [μ, c] at hMc_hi ⊢; nlinarith only [hMc_hi]
      -- Need `c^2*q + c^2 + q*r ≤ (3 / r) * c * √n`, i.e., `r * (c^2*q + c^2 + q*r) ≤ 3 * c * √n`
      have hmul : (r : ℝ) * (c ^ 2 * (q : ℝ) + c ^ 2 + (q : ℝ) * (r : ℝ)) ≤ 3 * (c * Real.sqrt (n : ℝ)) := by
        dsimp only [c]
        nlinarith only [hr100_le_q, hqr2, hsn_ge_q2, hr_100, hq_10000]
      have hdiv_r : c ^ 2 * (q : ℝ) + c ^ 2 + (q : ℝ) * (r : ℝ) ≤ (3 / (r : ℝ)) * (c * Real.sqrt (n : ℝ)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr_pos]; linarith
      calc (m : ℝ) ≤ μ + (q : ℝ) * (r : ℝ) := hm_hi
        _ ≤ (c * Real.sqrt (n : ℝ) + c ^ 2 * (q : ℝ) + c ^ 2) + (q : ℝ) * (r : ℝ) := add_le_add hμ_ub le_rfl
        _ = (c ^ 2 * (q : ℝ) + c ^ 2 + (q : ℝ) * (r : ℝ)) + c * Real.sqrt (n : ℝ) := by ring
        _ ≤ 3 / (r : ℝ) * (c * Real.sqrt (n : ℝ)) + c * Real.sqrt (n : ℝ) := add_le_add hdiv_r le_rfl
  have htermA : ((m : ℝ) * uBound + C_strip) / c / Real.sqrt (n : ℝ) ≤
      uBound + (3 * Uabs + Cabs) / (r : ℝ) := by
    have hsplit : ((m : ℝ) * uBound + C_strip) / c / Real.sqrt (n : ℝ) =
        uBound + ((m : ℝ) / (c * Real.sqrt (n : ℝ)) - 1) * uBound + C_strip / (c * Real.sqrt (n : ℝ)) := by
      have hc0 : c ≠ 0 := by dsimp only [c]; norm_num
      have hs0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsn_pos
      field_simp; ring
    rw [hsplit]
    have h1 : ((m : ℝ) / (c * Real.sqrt (n : ℝ)) - 1) * uBound ≤ 3 * Uabs / (r : ℝ) := by
      calc ((m : ℝ) / (c * Real.sqrt (n : ℝ)) - 1) * uBound
          ≤ |((m : ℝ) / (c * Real.sqrt (n : ℝ)) - 1) * uBound| := le_abs_self _
        _ = |(m : ℝ) / (c * Real.sqrt (n : ℝ)) - 1| * |uBound| := abs_mul _ _
        _ ≤ (3 / (r : ℝ)) * Uabs := mul_le_mul hm_div_diff (by dsimp only [Uabs]; linarith) (abs_nonneg _) (by positivity)
        _ = 3 * Uabs / (r : ℝ) := by ring
    have h2 : C_strip / (c * Real.sqrt (n : ℝ)) ≤ Cabs / (r : ℝ) := by
      have hc_sn : (r : ℝ) ≤ c * Real.sqrt (n : ℝ) := by
        dsimp only [c]; nlinarith only [hq_lo, hsn_ge_q2, hr_100, hq_10000]
      calc C_strip / (c * Real.sqrt (n : ℝ))
          ≤ Cabs / (c * Real.sqrt (n : ℝ)) := div_le_div_of_nonneg_right (by dsimp only [Cabs]; linarith [le_abs_self C_strip]) (by dsimp only [c]; positivity)
        _ ≤ Cabs / (r : ℝ) := div_le_div_of_nonneg_left (by dsimp only [Cabs]; positivity) hr_pos hc_sn
    linarith [show 3 * Uabs / (r : ℝ) + Cabs / (r : ℝ) = (3 * Uabs + Cabs) / (r : ℝ) by ring]
  -- Term B: Stitching error `(3 * M * √(((4 + m)/μ - 1)^2 + (4 + m)/μ^2) + 4) / √n ≤ 10 / r`
  have htermB : (3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) + 4) /
      Real.sqrt (n : ℝ) ≤ 10 / (r : ℝ) := by
    have hdev_sq : (((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2 ≤ (2 / (r : ℝ)) ^ 2 := by
      have hnum_le : ((4 + m : ℕ) : ℝ) - μ ≤ (q : ℝ) * (r : ℝ) + 4 := by
        have : ((4 + m : ℕ) : ℝ) = 4 + (m : ℝ) := by push_cast; rfl
        linarith
      have hnum_ge : 0 ≤ ((4 + m : ℕ) : ℝ) - μ := by
        have : ((4 + m : ℕ) : ℝ) = 4 + (m : ℝ) := by push_cast; rfl
        nlinarith only [hm_lo, hq_10000, hr_100, this]
      have hfrac1 : ((4 + m : ℕ) : ℝ) / μ - 1 ≤ 1 / (r : ℝ) := by
        have heq : ((4 + m : ℕ) : ℝ) / μ - 1 = (((4 + m : ℕ) : ℝ) - μ) / μ := by field_simp
        rw [heq, div_le_div_iff₀ hμ_pos hr_pos]
        dsimp only [c] at hμ_lo
        nlinarith only [hnum_le, hμ_lo, hqr2, hsn_ge_q2, hr_100, hq_10000]
      have hfrac1_nn : 0 ≤ ((4 + m : ℕ) : ℝ) / μ - 1 := by
        have heq : ((4 + m : ℕ) : ℝ) / μ - 1 = (((4 + m : ℕ) : ℝ) - μ) / μ := by field_simp
        rw [heq]; exact div_nonneg hnum_ge (le_of_lt hμ_pos)
      have hsq1 : (((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 ≤ (1 / (r : ℝ)) ^ 2 := by
        nlinarith only [hfrac1, hfrac1_nn]
      have hfrac2 : ((4 + m : ℕ) : ℝ) / μ ^ 2 ≤ (1 / (r : ℝ)) ^ 2 := by
        rw [div_le_iff₀ (sq_pos_of_pos hμ_pos)]
        have h4m : ((4 + m : ℕ) : ℝ) ≤ 2 * μ := by
          have : ((4 + m : ℕ) : ℝ) = 4 + (m : ℝ) := by push_cast; rfl
          dsimp only [c] at hμ_lo; nlinarith only [hm_hi, hμ_lo, hr_le_q, hsn_ge_q2, hr_100, hq_10000, this]
        have hμ_ge_2r2 : 2 * (r : ℝ) ^ 2 ≤ μ := by
          dsimp only [c] at hμ_lo; nlinarith only [hμ_lo, hq_lo, hsn_ge_q2, hr_100, hq_10000]
        have : (1 / (r : ℝ)) ^ 2 * μ ^ 2 = (μ / (r : ℝ)) ^ 2 := by ring
        rw [this]
        have hsq2 : 2 * μ ≤ (μ / (r : ℝ)) ^ 2 := by
          rw [div_pow, le_div_iff₀ (sq_pos_of_pos hr_pos)]
          nlinarith only [hμ_ge_2r2, hμ_pos]
        linarith
      linarith [hsq1, hfrac2, show (2 / (r : ℝ)) ^ 2 = 4 * (1 / (r : ℝ)) ^ 2 by ring, sq_nonneg (1 / (r : ℝ))]
    have hsqrt_le : Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) ≤ 2 / (r : ℝ) := by
      calc Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2)
          ≤ Real.sqrt ((2 / (r : ℝ)) ^ 2) := Real.sqrt_le_sqrt hdev_sq
        _ = 2 / (r : ℝ) := Real.sqrt_sq (by positivity)
    have hM_le : (M : ℝ) ≤ Real.sqrt (n : ℝ) := by
      dsimp only [c] at hMc_hi; nlinarith only [hMc_hi, hsn_ge_q2, hq_10000]
    have h4_le : 4 / Real.sqrt (n : ℝ) ≤ 4 / (r : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hr_pos (by nlinarith only [hq_lo, hsn_ge_q2, hr_100, hq_10000])
    calc (3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) + 4) / Real.sqrt (n : ℝ)
        ≤ (3 * Real.sqrt (n : ℝ) * (2 / (r : ℝ)) + 4) / Real.sqrt (n : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hsn_pos)
          have hmul1 : 3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) ≤
              3 * Real.sqrt (n : ℝ) * (2 / (r : ℝ)) :=
            mul_le_mul (by linarith) hsqrt_le (Real.sqrt_nonneg _) (by positivity)
          linarith
      _ = 6 / (r : ℝ) + 4 / Real.sqrt (n : ℝ) := by field_simp; ring
      _ ≤ 6 / (r : ℝ) + 4 / (r : ℝ) := by linarith
      _ = 10 / (r : ℝ) := by ring
  -- Term C: Bad-strip Chernoff tail `((4 * √R + 4) * M * ∑ j ∈ Icc (4 + m) R, poissonProb μ j) / √n ≤ 10^15 / r`
  have htermC : ((4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j) /
      Real.sqrt (n : ℝ) ≤ (10 ^ 15 : ℝ) / (r : ℝ) := by
    let δ : ℝ := (q : ℝ) * (r : ℝ) / μ
    have hδ0 : 0 < δ := by dsimp only [δ]; positivity
    have hδ1 : δ ≤ 1 := by
      dsimp only [δ]; rw [div_le_one hμ_pos]; dsimp only [c] at hμ_lo
      nlinarith only [hμ_lo, hr_le_q, hsn_ge_q2, hq_10000]
    have hN0 : (1 + δ) * μ ≤ ((4 + m : ℕ) : ℝ) := by
      have : (1 + δ) * μ = μ + (q : ℝ) * (r : ℝ) := by dsimp only [δ]; field_simp
      rw [this]
      have hcast : ((4 + m : ℕ) : ℝ) = 4 + (m : ℝ) := by push_cast; rfl
      linarith
    have hch := poisson_chernoff_upper hμ_pos hδ0 hδ1 (R := R) hN0
    -- Exponent `x := μ * δ^2 / 4 ≥ r^2 / 40`, and `exp(-x) = 1 / exp(x) ≤ 6! / x^6`.
    set x : ℝ := μ * δ ^ 2 / 4
    have hx_lo : (r : ℝ) ^ 2 / 40 ≤ x := by
      have hx_eq : x = ((q : ℝ) * (r : ℝ)) ^ 2 / (4 * μ) := by dsimp only [x, δ]; field_simp
      rw [hx_eq, div_le_div_iff₀ (by norm_num) (by positivity)]
      -- Need `r^2 * 4 * μ ≤ 40 * (q * r)^2`, i.e., `μ ≤ 10 * q^2`.
      have hμ_10q2 : μ ≤ 10 * (q : ℝ) ^ 2 := by
        dsimp only [c] at hμ_hi; nlinarith only [hμ_hi, hsn_le_2q2]
      nlinarith only [hμ_10q2, sq_nonneg (r : ℝ)]
    have hx_pos : 0 < x := by linarith [show (0 : ℝ) < (r : ℝ) ^ 2 / 40 by positivity]
    have hexp_bound : Real.exp (-x) ≤ (720 : ℝ) / x ^ 6 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (pow_pos hx_pos 6)]
      have h6 := pow_div_factorial_le_exp (le_of_lt hx_pos) 6
      have hfact6 : ((6 : ℕ).factorial : ℝ) = 720 := by
        exact_mod_cast (by decide : (6 : ℕ).factorial = 720)
      rw [hfact6, div_le_iff₀ (by norm_num)] at h6
      linarith
    have hexp_r : Real.exp (-x) ≤ (720 * 40 ^ 6 : ℝ) / (r : ℝ) ^ 12 := by
      refine hexp_bound.trans ?_
      have hx6 : ((r : ℝ) ^ 2 / 40) ^ 6 ≤ x ^ 6 := pow_le_pow_left₀ (by positivity) hx_lo 6
      have heq6 : ((r : ℝ) ^ 2 / 40) ^ 6 = (r : ℝ) ^ 12 / (40 ^ 6 : ℝ) := by ring
      rw [heq6] at hx6
      rw [div_le_div_iff₀ (pow_pos hx_pos 6) (by positivity)]
      rw [div_le_iff₀ (by norm_num)] at hx6
      nlinarith only [hx6]
    have hR_le : (R : ℝ) ≤ 5 * (n : ℝ) := by
      have h1 : (R : ℝ) < 2 * lam + 1 := Nat.ceil_lt_add_one (by linarith [hlam_nn])
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by nlinarith only [hs_ge_q2, hn_lo]
      linarith
    have hsqrtR : Real.sqrt (R : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3), ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hM_le_sn : (M : ℝ) ≤ Real.sqrt (n : ℝ) := by
      dsimp only [c] at hMc_hi; nlinarith only [hMc_hi, hsn_ge_q2, hq_10000]
    have hsn_le_r4 : Real.sqrt (n : ℝ) ≤ 4 * (r : ℝ) ^ 4 := by
      have hq_11r2 : (q : ℝ) ≤ (11 / 10 : ℝ) * (r : ℝ) ^ 2 := by nlinarith only [hq_hi, hr_100]
      have hq2_le : (q : ℝ) ^ 2 ≤ (121 / 100 : ℝ) * (r : ℝ) ^ 4 := by
        have := mul_le_mul hq_11r2 hq_11r2 (by linarith) (by positivity)
        linarith [show ((11 / 10 : ℝ) * (r : ℝ) ^ 2) * ((11 / 10 : ℝ) * (r : ℝ) ^ 2) =
          (121 / 100 : ℝ) * (r : ℝ) ^ 4 by ring, show (q : ℝ) * (q : ℝ) = (q : ℝ) ^ 2 by ring]
      nlinarith only [hsn_le_2q2, hq2_le]
    have hpref : (4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) / Real.sqrt (n : ℝ) ≤ 100 * (r : ℝ) ^ 4 := by
      have h1 : 4 * Real.sqrt (R : ℝ) + 4 ≤ 16 * Real.sqrt (n : ℝ) := by linarith
      calc (4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) / Real.sqrt (n : ℝ)
          ≤ (16 * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) / Real.sqrt (n : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul h1 hM_le_sn (by positivity) (by positivity)) (le_of_lt hsn_pos)
        _ = 16 * Real.sqrt (n : ℝ) := by field_simp
        _ ≤ 100 * (r : ℝ) ^ 4 := by linarith
    have hch' : ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j ≤ (720 * 40 ^ 6 : ℝ) / (r : ℝ) ^ 12 := by
      have hneg : -μ * δ ^ 2 / 4 = -x := by dsimp only [x]; ring
      rw [hneg] at hch
      exact hch.trans hexp_r
    calc ((4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j) / Real.sqrt (n : ℝ)
        = ((4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) / Real.sqrt (n : ℝ)) *
            ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j := by ring
      _ ≤ (100 * (r : ℝ) ^ 4) * ((720 * 40 ^ 6 : ℝ) / (r : ℝ) ^ 12) :=
          mul_le_mul hpref hch' (Finset.sum_nonneg fun j _ => poissonProb_nonneg (le_of_lt hμ_pos) j) (by positivity)
      _ ≤ (10 ^ 15 : ℝ) / (r : ℝ) := by
          rw [mul_div_assoc', div_le_div_iff₀ (pow_pos hr_pos 12) hr_pos]
          have hr5_le : (r : ℝ) ^ 5 ≤ (r : ℝ) ^ 12 := by
            have hr1 : 1 ≤ (r : ℝ) := by linarith
            calc (r : ℝ) ^ 5 = (r : ℝ) ^ 5 * 1 := (mul_one _).symm
              _ ≤ (r : ℝ) ^ 5 * (r : ℝ) ^ 7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hr1) (by positivity)
              _ = (r : ℝ) ^ 12 := by ring
          have hlhs_r5 : 100 * (r : ℝ) ^ 4 * (720 * 40 ^ 6 : ℝ) * (r : ℝ) = (100 * 720 * 40 ^ 6 : ℝ) * (r : ℝ) ^ 5 := by ring
          rw [hlhs_r5]
          nlinarith only [hr5_le, show (0 : ℝ) ≤ (r : ℝ) ^ 5 by positivity]
  -- Step 3: Divide `hmain` by `√n` and then by `p_good ≥ 1 - 1 / r ≥ 1 / 2`.
  have hdiv_sn : p_good * (expectedTourLength n / Real.sqrt (n : ℝ)) ≤
      uBound + (3 * Uabs + Cabs + 10 + 10 ^ 15) / (r : ℝ) := by
    have h1 : p_good * expectedTourLength n / Real.sqrt (n : ℝ) ≤
        (((m : ℝ) * uBound + C_strip) / c +
          3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) + 4 +
          (4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j) / Real.sqrt (n : ℝ) :=
      div_le_div_of_nonneg_right hmain (le_of_lt hsn_pos)
    have hlhs_eq : p_good * expectedTourLength n / Real.sqrt (n : ℝ) =
        p_good * (expectedTourLength n / Real.sqrt (n : ℝ)) := by ring
    rw [← hlhs_eq]
    have hadd_div : (((m : ℝ) * uBound + C_strip) / c +
          3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) + 4 +
          (4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j) / Real.sqrt (n : ℝ) =
        ((m : ℝ) * uBound + C_strip) / c / Real.sqrt (n : ℝ) +
        (3 * (M : ℝ) * Real.sqrt ((((4 + m : ℕ) : ℝ) / μ - 1) ^ 2 + ((4 + m : ℕ) : ℝ) / μ ^ 2) + 4) / Real.sqrt (n : ℝ) +
        ((4 * Real.sqrt (R : ℝ) + 4) * (M : ℝ) * ∑ j ∈ Finset.Icc (4 + m) R, poissonProb μ j) / Real.sqrt (n : ℝ) := by
      ring
    rw [hadd_div] at h1
    have hsum_err : (3 * Uabs + Cabs) / (r : ℝ) + 10 / (r : ℝ) + (10 ^ 15 : ℝ) / (r : ℝ) =
        (3 * Uabs + Cabs + 10 + 10 ^ 15) / (r : ℝ) := by ring
    linarith [htermA, htermB, htermC, hsum_err]
  -- Conclude `L_n / √n ≤ (uBound + E) / p_good ≤ uBound + 2 * E + 2 * Uabs / r ≤ uBound + ε`.
  set E : ℝ := (3 * Uabs + Cabs + 10 + 10 ^ 15) / (r : ℝ)
  have hE_nn : 0 ≤ E := by dsimp only [E, Uabs, Cabs]; positivity
  have hL_nn : 0 ≤ expectedTourLength n / Real.sqrt (n : ℝ) :=
    div_nonneg (integral_nonneg fun x => tourLength_nonneg x) (le_of_lt hsn_pos)
  have hUE_nn : 0 ≤ uBound + E := le_trans (mul_nonneg (by linarith) hL_nn) hdiv_sn
  have hfinal_p : expectedTourLength n / Real.sqrt (n : ℝ) ≤ uBound + E + 2 * (uBound + E) / (r : ℝ) := by
    have h1 : expectedTourLength n / Real.sqrt (n : ℝ) ≤ (uBound + E) / p_good :=
      (le_div_iff₀ (by linarith)).mpr (by linarith)
    refine h1.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have hpg : 1 - 1 / (r : ℝ) ≤ p_good := by linarith
    have hmul := mul_le_mul_of_nonneg_left hpg (show 0 ≤ uBound + E + 2 * (uBound + E) / (r : ℝ) by positivity)
    have h2 : uBound + E ≤ (uBound + E + 2 * (uBound + E) / (r : ℝ)) * (1 - 1 / (r : ℝ)) := by
      have hr2 : 2 / (r : ℝ) ≤ 1 := by rw [div_le_one hr_pos]; linarith
      have : (uBound + E + 2 * (uBound + E) / (r : ℝ)) * (1 - 1 / (r : ℝ)) - (uBound + E) =
          (uBound + E) / (r : ℝ) * (1 - 2 / (r : ℝ)) := by ring
      nlinarith only [this, hr2, div_nonneg hUE_nn (le_of_lt hr_pos)]
    linarith
  have hU_le : uBound ≤ Uabs := by dsimp only [Uabs]; linarith [le_abs_self uBound]
  have hE_le : E ≤ K / (4 * (r : ℝ)) := by
    dsimp only [E, K, Uabs, Cabs]
    rw [div_le_div_iff₀ hr_pos (by positivity)]
    nlinarith only [hr_pos, abs_nonneg uBound, abs_nonneg C_strip]
  have hE_le2 : 2 * (uBound + E) / (r : ℝ) ≤ K / (2 * (r : ℝ)) := by
    have h1 : 2 * (uBound + E) ≤ 2 * (Uabs + (3 * Uabs + Cabs + 10 + 10 ^ 15)) := by
      have hE_raw : E ≤ 3 * Uabs + Cabs + 10 + 10 ^ 15 := by
        dsimp only [E]; exact div_le_self (by dsimp only [Uabs, Cabs]; positivity) (by linarith)
      linarith
    have h2 : 2 * (Uabs + (3 * Uabs + Cabs + 10 + 10 ^ 15)) ≤ K / 2 := by
      dsimp only [K, Uabs, Cabs]; linarith [abs_nonneg uBound, abs_nonneg C_strip]
    calc 2 * (uBound + E) / (r : ℝ) ≤ (K / 2) / (r : ℝ) := div_le_div_of_nonneg_right (by linarith) (le_of_lt hr_pos)
      _ = K / (2 * (r : ℝ)) := by ring
  have hK_eps : K / (r : ℝ) ≤ ε := by
    rw [div_le_iff₀ hr_pos]
    have h1 : K ≤ ε * (r₀ : ℝ) := by rw [div_le_iff₀ hε] at hr₀_eps; linarith
    have hr_ge_R : (r₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
    nlinarith only [h1, hr_ge_R, hε]
  have hK_tot : E + 2 * (uBound + E) / (r : ℝ) ≤ ε := by
    have : K / (4 * (r : ℝ)) + K / (2 * (r : ℝ)) = 3 / 4 * (K / (r : ℝ)) := by ring
    linarith
  linarith

end BHHBounds.Upper

