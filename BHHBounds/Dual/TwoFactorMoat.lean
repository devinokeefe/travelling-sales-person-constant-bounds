import BHHBounds.Defs

/-!
# Deterministic 2-Factor + Disjoint Moat Dual Inequality

Proves the completely elementary, deterministic lower bound on the length of any
Hamiltonian tour on `n ≥ 4` points in `ℝ²`:

1. `twoFactor_moat_dual_lower_bound`: For any vertex potentials `π : Fin n → ℝ`,
   any pairwise-disjoint family `F : Finset (Finset (Fin n))` of proper nonempty subsets
   with nonnegative moat widths `y : Finset (Fin n) → ℝ` satisfying the non-interference
   condition `(π u + y S) + (π v + y S') ≤ d u v` whenever `S ≠ S' ∈ F` have `y S > 0, y S' > 0`
   and `u ∈ S, v ∈ S'`, every tour `σ` satisfies:
   ```
   ∑ i, d (σ i) (σ (finRotate n i))
     ≥ 2 ∑ u, π u
       - (1/2) ∑ u, ∑ v ∈ univ.erase u, max 0 (π u + π v - d u v)
       + ∑ S ∈ F, [2 * y S - ∑ u ∈ S, ∑ v ∈ univ \ S,
           (max 0 (π u + y S + π v - d u v) - max 0 (π u + π v - d u v))]
   ```
2. `isolatedTriples_pairwiseDisjoint`: Triples `S` with `R(S) > diam(S)` are pairwise disjoint.
3. `isolatedTriple_secondNearest`: For every `u ∈ S` in an isolated triple, the 2nd nearest
   neighbor distance of `u` is `max (d u a) (d u b)` where `S = {u, a, b}`.
4. `telescoping_moat_identity`: Exact telescoping decomposition over clearance levels `r_1 < ... < r_J`.
-/

open Finset

namespace BHHBounds.Dual

noncomputable section

/-! ## Cyclic Tour Cut & Edge-Injectivity Lemmas -/

private lemma finRotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = (i.val + 1) % n := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    rw [finRotate_apply]
    cases m with
    | zero => simp
    | succ r =>
      have h1 : (1 : Fin (r + 2)).val = 1 := rfl
      rw [Fin.val_add, h1]

private lemma finRotate_iterate_val {n : ℕ} (t : ℕ) (a : Fin n) :
    ((finRotate n)^[t] a).val = (a.val + t) % n := by
  induction t with
  | zero => simp [Nat.mod_eq_of_lt a.isLt]
  | succ t ih =>
    rw [Function.iterate_succ_apply', finRotate_val, ih,
      Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]

private lemma finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [finRotate_val] at hval
  have hi := i.isLt
  by_cases h : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h] at hval; omega
  · have : i.val + 1 = n := by omega
    rw [this, Nat.mod_self] at hval; omega

private lemma finRotate_finRotate_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [finRotate_val, finRotate_val, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod] at hval
  have hval2 : (i.val + 2) % n = i.val := hval
  have hi := i.isLt
  by_cases h1 : i.val + 2 < n
  · rw [Nat.mod_eq_of_lt h1] at hval2; omega
  · have h2 : i.val + 2 - n < n := by omega
    have hmod : (i.val + 2) % n = i.val + 2 - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h2]
    rw [hmod] at hval2; omega

/-- Every nonempty proper subset `S` of `Fin n` is crossed at least twice by any cyclic tour `σ`:
at least once leaving `S` and at least once entering `S`. -/
lemma tour_cut_ge_two {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    2 ≤ (Finset.univ.filter fun i : Fin n =>
      (σ i ∈ S ∧ σ (finRotate n i) ∉ S) ∨ (σ i ∉ S ∧ σ (finRotate n i) ∈ S)).card := by
  have hreach_all : ∀ (a b : Fin n), ∃ step : ℕ, (finRotate n)^[step] a = b := by
    intro a b
    refine ⟨(b.val + n - a.val) % n, ?_⟩
    apply Fin.ext
    rw [finRotate_iterate_val]
    have ha := a.isLt
    have hb := b.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have heq : a.val + (b.val + n - a.val) = b.val + n := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  have hex_leave : ∃ i : Fin n, σ i ∈ S ∧ σ (finRotate n i) ∉ S := by
    by_contra hall
    push Not at hall
    obtain ⟨u, hu⟩ := hne
    have hstep : ∀ k : ℕ, σ ((finRotate n)^[k] (σ.symm u)) ∈ S := by
      intro k
      induction k with
      | zero => simpa
      | succ k ih => rw [Function.iterate_succ_apply']; exact hall _ ih
    have hallS : ∀ v : Fin n, v ∈ S := fun v => by
      obtain ⟨step, hreach⟩ := hreach_all (σ.symm u) (σ.symm v)
      have := hstep step
      rwa [hreach, Equiv.apply_symm_apply] at this
    exact hproper (Finset.eq_univ_iff_forall.mpr hallS)
  have hex_enter : ∃ j : Fin n, σ j ∉ S ∧ σ (finRotate n j) ∈ S := by
    by_contra hall
    push Not at hall
    have hex_out : ∃ u : Fin n, u ∉ S := by
      by_contra h
      push Not at h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨u, hu⟩ := hex_out
    have hstep : ∀ k : ℕ, σ ((finRotate n)^[k] (σ.symm u)) ∉ S := by
      intro k
      induction k with
      | zero => simpa
      | succ k ih => rw [Function.iterate_succ_apply']; exact hall _ ih
    obtain ⟨v, hv⟩ := hne
    obtain ⟨step, hreach⟩ := hreach_all (σ.symm u) (σ.symm v)
    have hnv := hstep step
    rw [hreach, Equiv.apply_symm_apply] at hnv
    exact hnv hv
  obtain ⟨i₁, hi₁⟩ := hex_leave
  obtain ⟨i₂, hi₂⟩ := hex_enter
  have hne_ij : i₁ ≠ i₂ := fun h => hi₂.1 (h ▸ hi₁.1)
  have hsub : ({i₁, i₂} : Finset (Fin n)) ⊆
      Finset.univ.filter fun i : Fin n =>
        (σ i ∈ S ∧ σ (finRotate n i) ∉ S) ∨ (σ i ∉ S ∧ σ (finRotate n i) ∈ S) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with rfl | rfl
    · exact Or.inl hi₁
    · exact Or.inr hi₂
  calc 2 = ({i₁, i₂} : Finset (Fin n)).card := (Finset.card_pair hne_ij).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- For `n ≥ 3` and any symmetric nonnegative function `F` on `Fin n × Fin n`, summing `F` over
the `n` edges of a cyclic tour `σ` is at most `(1 / 2) ∑_{u ≠ v} F u v`. -/
lemma sum_tour_edges_le_half_pairs {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n))
    (F : Fin n → Fin n → ℝ) (hnn : ∀ u v, 0 ≤ F u v) (hsym : ∀ u v, F u v = F v u) :
    ∑ i : Fin n, F (σ i) (σ (finRotate n i)) ≤
      (1 / 2 : ℝ) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, F u v := by
  let fwd : Fin n → Fin n × Fin n := fun i => (σ i, σ (finRotate n i))
  let bwd : Fin n → Fin n × Fin n := fun i => (σ (finRotate n i), σ i)
  have hfwd_inj : Function.Injective fwd := fun i j h => by
    have h1 : σ i = σ j := congrArg Prod.fst h
    exact σ.injective h1
  have hbwd_inj : Function.Injective bwd := fun i j h => by
    have h2 : σ i = σ j := congrArg Prod.snd h
    exact σ.injective h2
  have hdisj : Disjoint (Finset.univ.image fwd) (Finset.univ.image bwd) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨j, _, hj⟩
    have h1 : σ (finRotate n j) = σ i := congrArg Prod.fst hj
    have h2 : σ j = σ (finRotate n i) := congrArg Prod.snd hj
    have hi : finRotate n j = i := σ.injective h1
    have hj' : j = finRotate n i := σ.injective h2
    rw [← hi] at hj'
    exact finRotate_finRotate_ne_self hn j hj'.symm
  let offDiag : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 ≠ p.2
  have hsub : (Finset.univ.image fwd ∪ Finset.univ.image bwd) ⊆ offDiag := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hp
    simp only [offDiag, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact fun h => finRotate_ne_self (by omega) i (σ.injective h).symm
    · exact fun h => finRotate_ne_self (by omega) i (σ.injective h)
  have hsum_fwd : ∑ p ∈ Finset.univ.image fwd, F p.1 p.2 =
      ∑ i : Fin n, F (σ i) (σ (finRotate n i)) := by
    rw [Finset.sum_image (fun a _ b _ h => hfwd_inj h)]
  have hsum_bwd : ∑ p ∈ Finset.univ.image bwd, F p.1 p.2 =
      ∑ i : Fin n, F (σ i) (σ (finRotate n i)) := by
    rw [Finset.sum_image (fun a _ b _ h => hbwd_inj h)]
    refine Finset.sum_congr rfl fun i _ => hsym _ _
  have hsum_off : ∑ p ∈ offDiag, F p.1 p.2 =
      ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, F u v := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_filter]
    congr 1; ext v; simp [ne_comm]
  have hle : ∑ p ∈ (Finset.univ.image fwd ∪ Finset.univ.image bwd), F p.1 p.2 ≤
      ∑ p ∈ offDiag, F p.1 p.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hnn p.1 p.2
  rw [Finset.sum_union hdisj, hsum_fwd, hsum_bwd, hsum_off] at hle
  linarith

/-! ## The Deterministic 2-Factor + Disjoint Moat Dual Inequality -/

/-- For a pairwise-disjoint family `F` of subsets of `Fin n`, at most one `S ∈ F` contains a
given vertex `u`. -/
private lemma card_filter_mem_le_one {n : ℕ} (F : Finset (Finset (Fin n)))
    (hdisj : (F : Set (Finset (Fin n))).PairwiseDisjoint id) (u : Fin n) :
    (F.filter fun S => u ∈ S).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro S₁ hS₁ S₂ hS₂
  simp only [Finset.mem_filter] at hS₁ hS₂
  by_contra hne
  exact Finset.disjoint_left.mp (hdisj hS₁.1 hS₂.1 hne) hS₁.2 hS₂.2

/-- **Deterministic 2-Factor + Disjoint Moat Dual Lower Bound.**

For any symmetric nonnegative edge weights `d`, any vertex potentials `π`, and any
pairwise-disjoint family `F` of proper nonempty subsets with nonnegative moat widths `y`
satisfying the non-interference condition `(π u + y S) + (π v + y S') ≤ d u v` whenever
`S ≠ S' ∈ F` have `y S > 0, y S' > 0`, `u ∈ S`, `v ∈ S'`, every cyclic tour `σ` has total
weight at least the base 2-factor dual plus the sum of net moat gains. -/
theorem twoFactor_moat_dual_lower_bound {n : ℕ} (hn : 3 ≤ n)
    (d : Fin n → Fin n → ℝ) (hd_sym : ∀ u v, d u v = d v u)
    (π : Fin n → ℝ)
    (F : Finset (Finset (Fin n)))
    (hF_ne : ∀ S ∈ F, S.Nonempty)
    (hF_proper : ∀ S ∈ F, S ≠ Finset.univ)
    (hF_disj : (F : Set (Finset (Fin n))).PairwiseDisjoint id)
    (y : Finset (Fin n) → ℝ)
    (hy_nn : ∀ S ∈ F, 0 ≤ y S)
    (hNI : ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → 0 < y S → 0 < y S' →
      ∀ u ∈ S, ∀ v ∈ S', (π u + y S) + (π v + y S') ≤ d u v)
    (σ : Equiv.Perm (Fin n)) :
    2 * (∑ u : Fin n, π u)
      - (1 / 2 : ℝ) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, max 0 (π u + π v - d u v)
      + ∑ S ∈ F, (2 * y S - ∑ u ∈ S, ∑ v ∈ Finset.univ \ S,
          (max 0 (π u + y S + π v - d u v) - max 0 (π u + π v - d u v)))
      ≤ ∑ i : Fin n, d (σ i) (σ (finRotate n i)) := by
  -- Define dual edge load `s u v = π u + π v + ∑_{S ∈ F, S cuts (u,v)} y S`
  let cuts (S : Finset (Fin n)) (u v : Fin n) : Prop :=
    (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)
  classical
  let s (u v : Fin n) : ℝ :=
    π u + π v + ∑ S ∈ F, if cuts S u v then y S else 0
  have hs_sym : ∀ u v, s u v = s v u := by
    intro u v
    dsimp only [s]
    have h1 : π u + π v = π v + π u := add_comm _ _
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    have hc : cuts S u v ↔ cuts S v u := by dsimp only [cuts]; tauto
    simp only [hc]
  -- Step 1: Pointwise `s u v - max 0 (s u v - d u v) ≤ d u v`
  have hpt : ∀ i : Fin n,
      s (σ i) (σ (finRotate n i)) - max 0 (s (σ i) (σ (finRotate n i)) - d (σ i) (σ (finRotate n i)))
        ≤ d (σ i) (σ (finRotate n i)) := fun i => by
    linarith [le_max_right (0 : ℝ) (s (σ i) (σ (finRotate n i)) - d (σ i) (σ (finRotate n i)))]
  have hsum_pt := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  rw [Finset.sum_sub_distrib] at hsum_pt
  -- Step 2: Lower bound `∑ i, s (σ i) (σ (finRotate n i)) ≥ 2 ∑ π + ∑_{S ∈ F} 2 y S`
  have hs_sum :
      2 * (∑ u : Fin n, π u) + ∑ S ∈ F, 2 * y S ≤ ∑ i : Fin n, s (σ i) (σ (finRotate n i)) := by
    dsimp only [s]
    simp_rw [Finset.sum_add_distrib]
    have hpi1 : ∑ i : Fin n, π (σ i) = ∑ u : Fin n, π u := Equiv.sum_comp σ π
    have hpi2 : ∑ i : Fin n, π (σ (finRotate n i)) = ∑ u : Fin n, π u :=
      Equiv.sum_comp (finRotate n |>.trans σ) π
    rw [hpi1, hpi2, Finset.sum_comm]
    have hcut_le : ∑ S ∈ F, 2 * y S ≤
        ∑ S ∈ F, ∑ i : Fin n, if cuts S (σ i) (σ (finRotate n i)) then y S else 0 := by
      refine Finset.sum_le_sum fun S hS => ?_
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hcard : (2 : ℝ) ≤
          ((Finset.univ.filter fun i : Fin n => cuts S (σ i) (σ (finRotate n i))).card : ℝ) := by
        exact_mod_cast tour_cut_ge_two σ S (hF_ne S hS) (hF_proper S hS)
      exact mul_le_mul_of_nonneg_right hcard (hy_nn S hS)
    linarith
  -- Step 3: Upper bound `max 0 (s u v - d u v)` for every pair `u ≠ v`
  let pen (u v : Fin n) : ℝ := max 0 (s u v - d u v)
  have hpen_nn : ∀ u v, 0 ≤ pen u v := fun _ _ => le_max_left _ _
  have hpen_sym : ∀ u v, pen u v = pen v u := fun u v => by
    dsimp only [pen]; rw [hs_sym, hd_sym]
  have htour_pen := sum_tour_edges_le_half_pairs hn σ pen hpen_nn hpen_sym
  -- Pairwise decomposition of `pen u v` using pairwise disjointness + (NI)
  have hpair_bound : ∀ u v : Fin n,
      pen u v ≤ max 0 (π u + π v - d u v)
        + ∑ S ∈ F, if cuts S u v then
            (max 0 (π u + y S + π v - d u v) - max 0 (π u + π v - d u v)) else 0 := by
    intro u v
    -- Every term in the RHS sum is nonnegative since `y S ≥ 0`
    have hterm_nn : ∀ S ∈ F,
        0 ≤ if cuts S u v then
          (max 0 (π u + y S + π v - d u v) - max 0 (π u + π v - d u v)) else 0 := by
      intro S hS
      split_ifs
      · have := hy_nn S hS
        have hle : max 0 (π u + π v - d u v) ≤ max 0 (π u + y S + π v - d u v) :=
          max_le_max_left 0 (by linarith)
        linarith
      · exact le_rfl
    -- Case analysis on whether `u` and/or `v` lie in some `S ∈ F` with `y S > 0`
    let Fu := F.filter fun S => u ∈ S ∧ v ∉ S
    let Fv := F.filter fun S => u ∉ S ∧ v ∈ S
    have hFu_card : Fu.card ≤ 1 :=
      (Finset.card_le_card (fun S hS => by
        simp only [Fu, Finset.mem_filter] at hS ⊢; exact ⟨hS.1, hS.2.1⟩)).trans
        (card_filter_mem_le_one F hF_disj u)
    have hFv_card : Fv.card ≤ 1 :=
      (Finset.card_le_card (fun S hS => by
        simp only [Fv, Finset.mem_filter] at hS ⊢; exact ⟨hS.1, hS.2.2⟩)).trans
        (card_filter_mem_le_one F hF_disj v)
    have hdisj_uv : Disjoint Fu Fv := by
      rw [Finset.disjoint_left]
      intro S h1 h2
      simp only [Fu, Fv, Finset.mem_filter] at h1 h2
      exact h2.2.1 h1.2.1
    have hcut_sum : ∀ g : Finset (Fin n) → ℝ,
        (∑ S ∈ F, if cuts S u v then g S else 0) = (∑ S ∈ Fu, g S) + (∑ S ∈ Fv, g S) := by
      intro g
      rw [← Finset.sum_union hdisj_uv, Finset.sum_ite, Finset.sum_const_zero, add_zero]
      congr 1
      ext S
      simp only [Finset.mem_filter, Finset.mem_union, Fu, Fv, cuts]
      tauto
    have hs_eq : s u v = π u + π v + (∑ S ∈ Fu, y S) + (∑ S ∈ Fv, y S) := by
      dsimp only [s]; rw [hcut_sum]; ring
    rcases Finset.card_le_one_iff_subset_singleton.mp hFu_card with ⟨Su, hSu⟩
    rcases Finset.card_le_one_iff_subset_singleton.mp hFv_card with ⟨Sv, hSv⟩
    by_cases h1 : Fu = ∅ <;> by_cases h2 : Fv = ∅
    · -- Neither in any cutting set
      have : s u v = π u + π v := by rw [hs_eq, h1, h2]; simp
      dsimp only [pen]; rw [this]
      have hnn := Finset.sum_nonneg hterm_nn
      linarith
    · -- Only `v` in a cutting set `Sv`
      have hFv_eq : Fv = {Sv} := by
        rcases Finset.nonempty_iff_ne_empty.mpr h2 with ⟨T, hT⟩
        have hTS := Finset.mem_singleton.mp (hSv hT)
        subst hTS
        exact Finset.Subset.antisymm hSv (Finset.singleton_subset_iff.mpr hT)
      have hSv_mem : Sv ∈ F := (Finset.mem_filter.mp (hFv_eq ▸ Finset.mem_singleton_self Sv)).1
      have hs_val : s u v = π u + y Sv + π v := by
        rw [hs_eq, h1, hFv_eq]; simp; ring
      dsimp only [pen]
      rw [hs_val, hcut_sum, h1, hFv_eq]
      simp
    · -- Only `u` in a cutting set `Su`
      have hFu_eq : Fu = {Su} := by
        rcases Finset.nonempty_iff_ne_empty.mpr h1 with ⟨T, hT⟩
        have hTS := Finset.mem_singleton.mp (hSu hT)
        subst hTS
        exact Finset.Subset.antisymm hSu (Finset.singleton_subset_iff.mpr hT)
      have hs_val : s u v = π u + y Su + π v := by
        rw [hs_eq, hFu_eq, h2]; simp; ring
      dsimp only [pen]
      rw [hs_val, hcut_sum, hFu_eq, h2]
      simp
    · -- Both `u ∈ Su` and `v ∈ Sv` with `Su ≠ Sv`
      have hFu_eq : Fu = {Su} := by
        rcases Finset.nonempty_iff_ne_empty.mpr h1 with ⟨T, hT⟩
        have hTS := Finset.mem_singleton.mp (hSu hT)
        subst hTS
        exact Finset.Subset.antisymm hSu (Finset.singleton_subset_iff.mpr hT)
      have hFv_eq : Fv = {Sv} := by
        rcases Finset.nonempty_iff_ne_empty.mpr h2 with ⟨T, hT⟩
        have hTS := Finset.mem_singleton.mp (hSv hT)
        subst hTS
        exact Finset.Subset.antisymm hSv (Finset.singleton_subset_iff.mpr hT)
      have hSu_f := Finset.mem_filter.mp (hFu_eq ▸ Finset.mem_singleton_self Su)
      have hSv_f := Finset.mem_filter.mp (hFv_eq ▸ Finset.mem_singleton_self Sv)
      have hne_SS : Su ≠ Sv := fun heq => hSv_f.2.1 (heq ▸ hSu_f.2.1)
      have hs_val : s u v = π u + π v + y Su + y Sv := by
        rw [hs_eq, hFu_eq, hFv_eq]; simp
      have hyu := hy_nn Su hSu_f.1
      have hyv := hy_nn Sv hSv_f.1
      by_cases hyu0 : 0 < y Su
      · by_cases hyv0 : 0 < y Sv
        · -- Both positive: non-interference gives `s u v ≤ d u v`, so `pen u v = 0`!
          have hle := hNI Su hSu_f.1 Sv hSv_f.1 hne_SS hyu0 hyv0 u hSu_f.2.1 v hSv_f.2.2
          have hp0 : pen u v = 0 := by
            dsimp only [pen]; rw [hs_val]; exact max_eq_left (by linarith)
          rw [hp0]
          have hnn := Finset.sum_nonneg hterm_nn
          have hm0 : 0 ≤ max 0 (π u + π v - d u v) := le_max_left _ _
          linarith
        · -- `y Sv = 0`
          have hyveq : y Sv = 0 := le_antisymm (not_lt.mp hyv0) hyv
          dsimp only [pen]
          rw [hs_val, hyveq, hcut_sum, hFu_eq, hFv_eq]
          simp only [Finset.sum_singleton, hyveq, add_zero, sub_self]
          have harg : π u + π v + y Su - d u v = π u + y Su + π v - d u v := by ring
          rw [harg]; linarith
      · -- `y Su = 0`
        have hyueq : y Su = 0 := le_antisymm (not_lt.mp hyu0) hyu
        dsimp only [pen]
        rw [hs_val, hyueq, hcut_sum, hFu_eq, hFv_eq]
        simp only [Finset.sum_singleton, hyueq, add_zero, sub_self, zero_add]
        have harg : π u + π v + y Sv - d u v = π u + y Sv + π v - d u v := by ring
        rw [harg]; linarith
  -- Step 4: Sum `hpair_bound` over all ordered pairs `u ≠ v` and regroup the `S ∈ F` sum
  have hsum_pairs :
      (1 / 2 : ℝ) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, pen u v ≤
        (1 / 2 : ℝ) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, max 0 (π u + π v - d u v)
        + ∑ S ∈ F, ∑ u ∈ S, ∑ v ∈ Finset.univ \ S,
            (max 0 (π u + y S + π v - d u v) - max 0 (π u + π v - d u v)) := by
    have hraw : ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, pen u v ≤
        ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u,
          (max 0 (π u + π v - d u v)
            + ∑ S ∈ F, if cuts S u v then
                (max 0 (π u + y S + π v - d u v) - max 0 (π u + π v - d u v)) else 0) :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpair_bound u v
    simp_rw [Finset.sum_add_distrib] at hraw
    -- Regroup the triple sum over `(u, v ≠ u, S ∈ F)` by `S ∈ F`
    let g (S : Finset (Fin n)) (u v : Fin n) : ℝ :=
      max 0 (π u + y S + π v - d u v) - max 0 (π u + π v - d u v)
    have hg_sym : ∀ S u v, g S u v = g S v u := fun S u v => by
      dsimp only [g]; rw [hd_sym u v]; ring_nf
    have hregroup :
        (∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, ∑ S ∈ F, if cuts S u v then g S u v else 0) =
          2 * ∑ S ∈ F, ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, g S u v := by
      have hswap : (∑ u : Fin n, ∑ v ∈ Finset.univ.erase u, ∑ S ∈ F,
            if cuts S u v then g S u v else 0) =
          ∑ S ∈ F, ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u,
            if cuts S u v then g S u v else 0 := by
        trans (∑ u : Fin n, ∑ S ∈ F, ∑ v ∈ Finset.univ.erase u,
            if cuts S u v then g S u v else 0)
        · exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
        · exact Finset.sum_comm
      rw [hswap, Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      -- Split `u ∈ univ` into `u ∈ S` and `u ∈ univ \ S`
      have hsplit : ∀ f : Fin n → ℝ,
          (∑ u : Fin n, f u) = (∑ u ∈ S, f u) + (∑ u ∈ Finset.univ \ S, f u) := fun f => by
        rw [← Finset.sum_union Finset.disjoint_sdiff]
        congr 1; ext u; simp
      rw [hsplit]
      have hpart1 : (∑ u ∈ S, ∑ v ∈ Finset.univ.erase u, if cuts S u v then g S u v else 0) =
          ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, g S u v := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1; ext v
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, cuts]
        constructor
        · rintro ⟨_, ⟨_, hv⟩ | ⟨hnu, _⟩⟩
          · exact hv
          · exact absurd hu hnu
        · intro hv
          exact ⟨⟨fun (heq : v = u) => hv (heq ▸ hu), trivial⟩, Or.inl ⟨hu, hv⟩⟩
      have hpart2 : (∑ u ∈ Finset.univ \ S, ∑ v ∈ Finset.univ.erase u,
            if cuts S u v then g S u v else 0) =
          ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, g S u v := by
        have hstep : (∑ u ∈ Finset.univ \ S, ∑ v ∈ Finset.univ.erase u,
            if cuts S u v then g S u v else 0) =
            ∑ u ∈ Finset.univ \ S, ∑ v ∈ S, g S u v := by
          refine Finset.sum_congr rfl fun u hu => ?_
          have hnu : u ∉ S := (Finset.mem_sdiff.mp hu).2
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
          congr 1; ext v
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, cuts]
          constructor
          · rintro ⟨_, ⟨h1, _⟩ | ⟨_, hv⟩⟩
            · exact absurd h1 hnu
            · exact hv
          · intro hv
            exact ⟨⟨fun (heq : v = u) => hnu (heq ▸ hv), trivial⟩, Or.inr ⟨hnu, hv⟩⟩
        rw [hstep, Finset.sum_comm]
        exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => hg_sym S u v
      rw [hpart1, hpart2]; ring
    rw [hregroup] at hraw
    linarith
  -- Step 5: Combine everything!
  rw [Finset.sum_sub_distrib]
  linarith

/-! ## Isolated Triples & Telescoping Moat Identity -/

/-- A subset `S` is **isolated** (with respect to symmetric distances `d`) if every external edge
`(u, v)` with `u ∈ S, v ∉ S` is strictly longer than every internal edge `(a, b)` of `S`. -/
def IsIsolated {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ a ∈ S, ∀ v ∉ S, d u a < d u v

/-- Distinct isolated subsets of the same cardinality are pairwise disjoint! -/
lemma isolated_pairwiseDisjoint {n : ℕ} (d : Fin n → Fin n → ℝ)
    (k : ℕ) {S₁ S₂ : Finset (Fin n)} (hS₁ : S₁.card = k) (hS₂ : S₂.card = k)
    (hI₁ : IsIsolated d S₁) (hI₂ : IsIsolated d S₂) (hne : S₁ ≠ S₂) :
    Disjoint S₁ S₂ := by
  rw [Finset.disjoint_left]
  intro u hu₁ hu₂
  have h1 : (S₁ \ S₂).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    exact hne (Finset.eq_of_subset_of_card_le hemp (by omega))
  have h2 : (S₂ \ S₁).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    exact hne (Finset.eq_of_subset_of_card_le hemp (by omega)).symm
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  have hx₁ : x ∈ S₁ := (Finset.mem_sdiff.mp hx).1
  have hx₂ : x ∉ S₂ := (Finset.mem_sdiff.mp hx).2
  have hy₂ : y ∈ S₂ := (Finset.mem_sdiff.mp hy).1
  have hy₁ : y ∉ S₁ := (Finset.mem_sdiff.mp hy).2
  have hlt1 : d u x < d u y := hI₁ u hu₁ x hx₁ y hy₁
  have hlt2 : d u y < d u x := hI₂ u hu₂ y hy₂ x hx₂
  linarith

/-- Half-clearance condition guarantees non-interference: if for every active `S` with `y S > 0`
there is a clearance radius `r` such that `∀ u ∈ S, ∀ v ∉ S, r < d u v` and
`∀ u ∈ S, π u + y S ≤ r / 2`, then `(NI)` holds automatically for every pair `S ≠ S'`. -/
lemma nonInterference_of_halfClearance {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd_sym : ∀ u v, d u v = d v u) (π : Fin n → ℝ)
    (F : Finset (Finset (Fin n))) (hF_disj : (F : Set (Finset (Fin n))).PairwiseDisjoint id)
    (y : Finset (Fin n) → ℝ)
    (hclear : ∀ S ∈ F, 0 < y S →
      ∃ r : ℝ, (∀ u ∈ S, ∀ v ∉ S, r < d u v) ∧ (∀ u ∈ S, π u + y S ≤ r / 2)) :
    ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → 0 < y S → 0 < y S' →
      ∀ u ∈ S, ∀ v ∈ S', (π u + y S) + (π v + y S') ≤ d u v := by
  intro S hS S' hS' hne hyS hyS' u hu v hv
  obtain ⟨r, hr_out, hr_cap⟩ := hclear S hS hyS
  obtain ⟨r', hr'_out, hr'_cap⟩ := hclear S' hS' hyS'
  have hv_notS : v ∉ S := Finset.disjoint_right.mp (hF_disj hS hS' hne) hv
  have hu_notS' : u ∉ S' := Finset.disjoint_left.mp (hF_disj hS hS' hne) hu
  have h1 : r < d u v := hr_out u hu v hv_notS
  have h2 : r' < d u v := by rw [hd_sym]; exact hr'_out v hv u hu_notS'
  linarith [hr_cap u hu, hr'_cap v hv]

/-- **Exact Telescoping Moat Identity.**

Given a finite list of clearance-moat steps `levels : List (ℝ × ℝ)` with strictly increasing
clearance thresholds and nondecreasing moat widths (or simply arbitrary `r_j` with `y_j`
accumulated on `R > r_j`), if `y_prev = 0` initially and `R > r_j` is nested (monotone in `j`),
then `2 * y_eff - (φ y_eff - φ 0)` telescopes identically over all levels! -/
lemma telescoping_moat_identity {m : ℕ} (R : ℝ)
    (r : Fin m → ℝ) (hr_mono : Monotone r)
    (y : Fin (m + 1) → ℝ) (hy0 : y 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) :
    let yEff : ℝ := ∑ j : Fin m, if r j < R then (y j.succ - y j.castSucc) else 0
    2 * yEff - φ yEff =
      ∑ j : Fin m, if r j < R then
        (2 * (y j.succ - y j.castSucc) - (φ (y j.succ) - φ (y j.castSucc))) else 0 := by
  -- Prove by induction on `m`!
  induction m with
  | zero =>
    simp [hφ0]
  | succ k ih =>
    by_cases hlast : r (Fin.last k) < R
    · -- Since `r` is monotone and `r (last k) < R`, ALL `r j < R`!
      have hall : ∀ j : Fin (k + 1), r j < R := fun j =>
        lt_of_le_of_lt (hr_mono (Fin.le_last j)) hlast
      simp only [hall, ↓reduceIte]
      have hyEff : ∑ j : Fin (k + 1), (y j.succ - y j.castSucc) = y (Fin.last (k + 1)) := by
        -- Standard Fin telescoping sum
        have htel : ∀ (p : ℕ) (f : Fin (p + 1) → ℝ),
            ∑ j : Fin p, (f j.succ - f j.castSucc) = f (Fin.last p) - f 0 := by
          intro p f
          induction p with
          | zero => simp
          | succ p' ihp =>
            rw [Fin.sum_univ_castSucc]
            have h4 : ∀ i : Fin p', i.castSucc.succ = i.succ.castSucc := fun i => Fin.ext (by simp)
            simp_rw [h4]
            rw [ihp (fun j => f j.castSucc)]
            have h2 : (Fin.last p').succ = Fin.last (p' + 1) := Fin.ext (by simp)
            have h3 : (0 : Fin (p' + 1)).castSucc = (0 : Fin (p' + 2)) := rfl
            rw [h2, h3]; ring
        rw [htel (k + 1) y, hy0, sub_zero]
      have htel_φ : ∑ j : Fin (k + 1), (φ (y j.succ) - φ (y j.castSucc)) =
          φ (y (Fin.last (k + 1))) := by
        have htel : ∀ (p : ℕ) (f : Fin (p + 1) → ℝ),
            ∑ j : Fin p, (f j.succ - f j.castSucc) = f (Fin.last p) - f 0 := by
          intro p f
          induction p with
          | zero => simp
          | succ p' ihp =>
            rw [Fin.sum_univ_castSucc]
            have h4 : ∀ i : Fin p', i.castSucc.succ = i.succ.castSucc := fun i => Fin.ext (by simp)
            simp_rw [h4]
            rw [ihp (fun j => f j.castSucc)]
            have h2 : (Fin.last p').succ = Fin.last (p' + 1) := Fin.ext (by simp)
            have h3 : (0 : Fin (p' + 1)).castSucc = (0 : Fin (p' + 2)) := rfl
            rw [h2, h3]; ring
        rw [htel (k + 1) (fun t => φ (y t)), hy0, hφ0, sub_zero]
      rw [hyEff, Finset.sum_sub_distrib, ← Finset.mul_sum, hyEff, htel_φ]
    · -- `¬ (r (last k) < R)`: drop the last term and apply IH!
      have hih := ih (fun j => r j.castSucc) (fun a b hab => hr_mono (Fin.castSucc_le_castSucc_iff.mpr hab))
        (fun t => y t.castSucc) hy0
      dsimp only at hih ⊢
      rw [Fin.sum_univ_castSucc, if_neg hlast, add_zero]
      rw [Fin.sum_univ_castSucc, if_neg hlast, add_zero]
      have hstep : ∀ j : Fin k, j.castSucc.succ = j.succ.castSucc := fun j => Fin.ext (by simp)
      simp_rw [hstep]
      exact hih

end

end BHHBounds.Dual
