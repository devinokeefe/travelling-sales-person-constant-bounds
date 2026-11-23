import BHHBounds.Upper.Automaton

/-!
# Soundness of `connectToNew`, `stepState`, and Automaton Walks

Proves that every valid walk in the bandwidth-`d` frontier automaton starting and
ending at `initState d` produces a single Hamiltonian path from `0` to `N` whose
edge length equals the sum of edge weights along the walk.
-/

namespace BHHBounds.Upper

lemma anchor_ne_free {w : ℕ} {m : Mate w} {ia i : Fin w} (ha : m ia = -1) (hf : 0 ≤ m i) :
    i ≠ ia := by
  intro h; subst h; omega

/-- Merge a free path `l` (with endpoints `ib, ic`, attaching at `ib`) onto the end `ia`
of `F.anchor`. Handles both singleton (`ib = ic`) and multi-vertex `l` uniformly. -/
lemma merge_anchor_free {α : Type*} {w k : ℕ} (dist : α → α → ℝ)
    (hsym : ∀ x y, dist x y = dist y x) (p : ℕ → α)
    {m : Mate w} {F : LinearForest k} (hm : Matches m F)
    {ia ib ic : Fin w} {l : List ℕ} (hl : l ∈ F.free) (hlne : l ≠ [])
    (ha : m ia = -1) (hib : m ib = (ic.val : ℤ)) (hic : m ic = (ib.val : ℤ))
    (hends : (slotGlobal w k ib = (l.head hlne : ℤ) ∧ slotGlobal w k ic = (l.getLast hlne : ℤ)) ∨
             (slotGlobal w k ic = (l.head hlne : ℤ) ∧ slotGlobal w k ib = (l.getLast hlne : ℤ))) :
    ∃ F' : LinearForest k,
      Matches (fun i => if i = ic then -1 else if i = ia ∨ i = ib then -2 else m i) F' ∧
      F'.totalLen dist p = F.totalLen dist p +
        dist (p (slotGlobal w k ia).toNat) (p (slotGlobal w k ib).toNat) := by
  have hia_sg : slotGlobal w k ia = (F.anchor.getLast F.anchor_ne : ℤ) := hm.anchor_unique ia ha
  have hib_nn : 0 ≤ slotGlobal w k ib := slotGlobal_nonneg_of_active hm (by omega)
  have hic_nn : 0 ≤ slotGlobal w k ic := slotGlobal_nonneg_of_active hm (by omega)
  set b := (slotGlobal w k ib).toNat
  set c := (slotGlobal w k ic).toNat
  have hb_eq : slotGlobal w k ib = (b : ℤ) := (Int.toNat_of_nonneg hib_nn).symm
  have hc_eq : slotGlobal w k ic = (c : ℤ) := (Int.toNat_of_nonneg hic_nn).symm
  have hends_nat : (l.head hlne = b ∧ l.getLast hlne = c) ∨ (l.head hlne = c ∧ l.getLast hlne = b) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Int.ofNat.inj (h1.symm.trans hb_eq), Int.ofNat.inj (h2.symm.trans hc_eq)⟩
    · exact Or.inr ⟨Int.ofNat.inj (h1.symm.trans hc_eq), Int.ofNat.inj (h2.symm.trans hb_eq)⟩
  let l' := orientStart l hlne b
  have hl'ne : l' ≠ [] := orientStart_ne l hlne b
  have hl'h : l'.head hl'ne = b := (orientStart_ends l hlne b c hends_nat).1
  have hl'l : l'.getLast hl'ne = c := (orientStart_ends l hlne b c hends_nat).2
  obtain ⟨rest, hperm_free⟩ := perm_extract hl
  let F' : LinearForest k := {
    anchor := F.anchor ++ l'
    free := rest
    anchor_ne := List.append_ne_nil_of_left_ne_nil F.anchor_ne l'
    anchor_head := by rw [List.head_append_of_ne_nil F.anchor_ne]; exact F.anchor_head
    free_ne := fun q hq => F.free_ne q (hperm_free.symm.subset (List.mem_cons_of_mem _ hq))
    cover := by
      have h1 : ((F.anchor ++ l') ++ rest.flatten).Perm (F.anchor ++ (l :: rest).flatten) := by
        simp only [List.append_assoc, List.flatten_cons]
        exact ((orientStart_perm l hlne b).append_right rest.flatten).append_left F.anchor
      exact (h1.trans ((perm_flatten hperm_free.symm).append_left F.anchor)).trans F.cover
  }
  have hrest_ne_l : ∀ q ∈ rest, q ≠ l := by
    intro q hq hql
    rw [hql] at hq
    have hnd := (perm_flatten hperm_free).nodup_iff.mp (List.nodup_append.mp F.nodup_all).2.1
    simp only [List.flatten_cons, List.nodup_append] at hnd
    have hmem : l.head hlne ∈ l := List.head_mem hlne
    exact hnd.2.2 _ hmem _ (List.mem_flatten.mpr ⟨l, hq, hmem⟩) rfl
  refine ⟨F', ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨ic, by simp, ?_⟩
      simp only [F', List.getLast_append_of_ne_nil _ hl'ne, hl'l, hc_eq]
    · intro i hi
      split_ifs at hi with h1 h2
      · subst h1; simp only [F', List.getLast_append_of_ne_nil _ hl'ne, hl'l, hc_eq]
      · omega
      · have hne_ia : i ≠ ia := fun h => h2 (Or.inl h)
        have hsg := hm.anchor_unique i hi
        exact absurd (slotGlobal_injective w k (hsg.trans hia_sg.symm)) hne_ia
    · intro q hq
      have hqF : q ∈ F.free := hperm_free.symm.subset (List.mem_cons_of_mem _ hq)
      have hqne : q ≠ l := hrest_ne_l q hq
      obtain ⟨hq_ne, i, j, hsi, hsj, hmi, hmj⟩ := hm.free_ends q hqF
      obtain ⟨h1, h2, h3, h4⟩ := F.other_free_disjoint hl hqF hqne.symm hends ⟨hsi, hsj⟩
      have hi_ia : i ≠ ia := anchor_ne_free ha (by omega)
      have hj_ia : j ≠ ia := anchor_ne_free ha (by omega)
      refine ⟨hq_ne, i, j, hsi, hsj, ?_, ?_⟩
      · simp [h2, hi_ia, h1, hmi]
      · simp [h4, hj_ia, h3, hmj]
    · intro i
      split_ifs with h1 h2
      · right; left; rfl
      · left; rfl
      · rcases hm.mate_valid i with h | h | ⟨j, hmi, hmj, q, hqF, hqne, hlr⟩
        · exact Or.inl h
        · have hsg := hm.anchor_unique i h
          exact absurd (slotGlobal_injective w k (hsg.trans hia_sg.symm)) (fun e => h2 (Or.inl e))
        · have hql : q ≠ l := by
            intro hql; subst hql
            rcases hlr with ⟨hi_h, _⟩ | ⟨_, hi_l⟩ <;> rcases hends with ⟨hb_h, hc_l⟩ | ⟨hc_h, hb_l⟩
            · exact h2 (Or.inr (slotGlobal_injective w k (hi_h.trans hb_h.symm)))
            · exact h1 (slotGlobal_injective w k (hi_h.trans hc_h.symm))
            · exact h1 (slotGlobal_injective w k (hi_l.trans hc_l.symm))
            · exact h2 (Or.inr (slotGlobal_injective w k (hi_l.trans hb_l.symm)))
          have hqrest : q ∈ rest := by
            have := hperm_free.subset hqF
            rcases List.mem_cons.mp this with rfl | hr
            · exact absurd rfl hql
            · exact hr
          have hj_ne_ia : j ≠ ia := anchor_ne_free ha (by omega)
          have hj_ne_ib : j ≠ ib := by
            intro e; subst e; rw [hib] at hmj
            exact h1 (Fin.ext (Int.ofNat.inj hmj.symm))
          have hj_ne_ic : j ≠ ic := by
            intro e; subst e; rw [hic] at hmj
            exact h2 (Or.inr (Fin.ext (Int.ofNat.inj hmj.symm)))
          right; right
          refine ⟨j, hmi, by simp [hj_ne_ic, hj_ne_ia, hj_ne_ib, hmj], q, hqrest, hqne, hlr⟩
  · unfold LinearForest.totalLen
    simp only [F']
    rw [pathLen_append dist p F.anchor l' F.anchor_ne hl'ne, hl'h, orientStart_len dist hsym p l hlne b]
    have hsum : (F.free.map fun q => pathLen dist q p).sum =
        pathLen dist l p + (rest.map fun q => pathLen dist q p).sum := by
      rw [perm_map_sum _ hperm_free]; simp
    have ha_nat : (slotGlobal w k ia).toNat = F.anchor.getLast F.anchor_ne := by
      rw [hia_sg]; simp
    rw [ha_nat, hsum]
    ring

/-- Merge two distinct free paths `l₁` (endpoints `i₁, j₁`, attaching at `i₁`) and `l₂`
(endpoints `i₂, j₂`, attaching at `i₂`). Handles all singleton/non-singleton combinations! -/
lemma merge_free_free {α : Type*} {w k : ℕ} (dist : α → α → ℝ)
    (hsym : ∀ x y, dist x y = dist y x) (p : ℕ → α)
    {m : Mate w} {F : LinearForest k} (hm : Matches m F)
    {i₁ j₁ i₂ j₂ : Fin w} {l₁ l₂ : List ℕ}
    (hl₁ : l₁ ∈ F.free) (hl₂ : l₂ ∈ F.free) (hne : l₁ ≠ l₂)
    (hl₁ne : l₁ ≠ []) (hl₂ne : l₂ ≠ [])
    (hm1 : m i₁ = (j₁.val : ℤ)) (hm1' : m j₁ = (i₁.val : ℤ))
    (hm2 : m i₂ = (j₂.val : ℤ)) (hm2' : m j₂ = (i₂.val : ℤ))
    (hends₁ : (slotGlobal w k i₁ = (l₁.head hl₁ne : ℤ) ∧ slotGlobal w k j₁ = (l₁.getLast hl₁ne : ℤ)) ∨
              (slotGlobal w k j₁ = (l₁.head hl₁ne : ℤ) ∧ slotGlobal w k i₁ = (l₁.getLast hl₁ne : ℤ)))
    (hends₂ : (slotGlobal w k i₂ = (l₂.head hl₂ne : ℤ) ∧ slotGlobal w k j₂ = (l₂.getLast hl₂ne : ℤ)) ∨
              (slotGlobal w k j₂ = (l₂.head hl₂ne : ℤ) ∧ slotGlobal w k i₂ = (l₂.getLast hl₂ne : ℤ))) :
    ∃ F' : LinearForest k,
      Matches (fun i =>
        if i = j₁ then (j₂.val : ℤ)
        else if i = j₂ then (j₁.val : ℤ)
        else if i = i₁ ∨ i = i₂ then -2
        else m i) F' ∧
      F'.totalLen dist p = F.totalLen dist p +
        dist (p (slotGlobal w k i₁).toNat) (p (slotGlobal w k i₂).toNat) := by
  have hi1_nn : 0 ≤ slotGlobal w k i₁ := slotGlobal_nonneg_of_active hm (by omega)
  have hj1_nn : 0 ≤ slotGlobal w k j₁ := slotGlobal_nonneg_of_active hm (by omega)
  have hi2_nn : 0 ≤ slotGlobal w k i₂ := slotGlobal_nonneg_of_active hm (by omega)
  have hj2_nn : 0 ≤ slotGlobal w k j₂ := slotGlobal_nonneg_of_active hm (by omega)
  set x₁ := (slotGlobal w k i₁).toNat
  set y₁ := (slotGlobal w k j₁).toNat
  set x₂ := (slotGlobal w k i₂).toNat
  set y₂ := (slotGlobal w k j₂).toNat
  have hx1 : slotGlobal w k i₁ = (x₁ : ℤ) := (Int.toNat_of_nonneg hi1_nn).symm
  have hy1 : slotGlobal w k j₁ = (y₁ : ℤ) := (Int.toNat_of_nonneg hj1_nn).symm
  have hx2 : slotGlobal w k i₂ = (x₂ : ℤ) := (Int.toNat_of_nonneg hi2_nn).symm
  have hy2 : slotGlobal w k j₂ = (y₂ : ℤ) := (Int.toNat_of_nonneg hj2_nn).symm
  have h1_nat : (l₁.head hl₁ne = y₁ ∧ l₁.getLast hl₁ne = x₁) ∨ (l₁.head hl₁ne = x₁ ∧ l₁.getLast hl₁ne = y₁) := by
    rcases hends₁ with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨Int.ofNat.inj (a.symm.trans hx1), Int.ofNat.inj (b.symm.trans hy1)⟩
    · exact Or.inl ⟨Int.ofNat.inj (a.symm.trans hy1), Int.ofNat.inj (b.symm.trans hx1)⟩
  have h2_nat : (l₂.head hl₂ne = x₂ ∧ l₂.getLast hl₂ne = y₂) ∨ (l₂.head hl₂ne = y₂ ∧ l₂.getLast hl₂ne = x₂) := by
    rcases hends₂ with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨Int.ofNat.inj (a.symm.trans hx2), Int.ofNat.inj (b.symm.trans hy2)⟩
    · exact Or.inr ⟨Int.ofNat.inj (a.symm.trans hy2), Int.ofNat.inj (b.symm.trans hx2)⟩
  let l₁' := orientEnd l₁ hl₁ne x₁
  let l₂' := orientStart l₂ hl₂ne x₂
  have hl₁'ne : l₁' ≠ [] := orientEnd_ne l₁ hl₁ne x₁
  have hl₂'ne : l₂' ≠ [] := orientStart_ne l₂ hl₂ne x₂
  have hl₁'h : l₁'.head hl₁'ne = y₁ := (orientEnd_ends l₁ hl₁ne x₁ y₁ h1_nat).1
  have hl₁'l : l₁'.getLast hl₁'ne = x₁ := (orientEnd_ends l₁ hl₁ne x₁ y₁ h1_nat).2
  have hl₂'h : l₂'.head hl₂'ne = x₂ := (orientStart_ends l₂ hl₂ne x₂ y₂ h2_nat).1
  have hl₂'l : l₂'.getLast hl₂'ne = y₂ := (orientStart_ends l₂ hl₂ne x₂ y₂ h2_nat).2
  let merged := l₁' ++ l₂'
  have hmerged_ne : merged ≠ [] := List.append_ne_nil_of_left_ne_nil hl₁'ne l₂'
  have hmerged_h : merged.head hmerged_ne = y₁ := by
    simp only [merged, List.head_append_of_ne_nil hl₁'ne, hl₁'h]
  have hmerged_l : merged.getLast hmerged_ne = y₂ := by
    simp only [merged, List.getLast_append_of_ne_nil _ hl₂'ne, hl₂'l]
  obtain ⟨rest, hperm_free⟩ := perm_extract_two hl₁ hl₂ hne
  have disj12 : i₂ ≠ i₁ ∧ i₂ ≠ j₁ ∧ j₂ ≠ i₁ ∧ j₂ ≠ j₁ := by
    rcases hends₂ with h2 | h2
    · exact F.other_free_disjoint hl₁ hl₂ hne hends₁ h2
    · obtain ⟨a, b, c, d⟩ := F.other_free_disjoint hl₁ hl₂ hne hends₁ h2
      exact ⟨c, d, a, b⟩
  have hj1_ne_j2 : j₁ ≠ j₂ := disj12.2.2.2.symm
  have hrest_ne : ∀ q ∈ rest, q ≠ l₁ ∧ q ≠ l₂ := by
    intro q hq
    have hnd := (perm_flatten hperm_free).nodup_iff.mp (List.nodup_append.mp F.nodup_all).2.1
    simp only [List.flatten_cons, List.nodup_append] at hnd
    constructor
    · intro e; rw [e] at hq
      have hmem1 := List.head_mem hl₁ne
      exact hnd.2.2 _ hmem1 _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨l₁, hq, hmem1⟩)) rfl
    · intro e; rw [e] at hq
      have hmem2 := List.head_mem hl₂ne
      exact hnd.2.1.2.2 _ hmem2 _ (List.mem_flatten.mpr ⟨l₂, hq, hmem2⟩) rfl
  let F' : LinearForest k := {
    anchor := F.anchor
    free := merged :: rest
    anchor_ne := F.anchor_ne
    anchor_head := F.anchor_head
    free_ne := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hr
      · exact hmerged_ne
      · exact F.free_ne q (hperm_free.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    cover := by
      have h1 : (merged :: rest).flatten.Perm (l₁ :: l₂ :: rest).flatten := by
        simp only [List.flatten_cons, merged, List.append_assoc]
        exact ((orientEnd_perm l₁ hl₁ne x₁).append ((orientStart_perm l₂ hl₂ne x₂).append_right rest.flatten))
      exact ((h1.trans (perm_flatten hperm_free.symm)).append_left F.anchor).trans F.cover
  }
  refine ⟨F', ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨ia, hma, hsg⟩ := hm.anchor_end
      have h1 : ia ≠ j₁ := (anchor_ne_free hma (by omega)).symm
      have h2 : ia ≠ j₂ := (anchor_ne_free hma (by omega)).symm
      have h3 : ia ≠ i₁ := (anchor_ne_free hma (by omega)).symm
      have h4 : ia ≠ i₂ := (anchor_ne_free hma (by omega)).symm
      exact ⟨ia, by simp [h1, h2, h3, h4, hma], hsg⟩
    · intro i hi
      by_cases h1 : i = j₁
      · simp [h1] at hi
      · by_cases h2 : i = j₂
        · simp [h2] at hi; omega
        · by_cases h3 : i = i₁ ∨ i = i₂
          · simp [h1, h2, h3] at hi
          · simp [h1, h2, h3] at hi; exact hm.anchor_unique i hi
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hr
      · refine ⟨hmerged_ne, j₁, j₂, ?_, ?_, by simp, by simp [hj1_ne_j2.symm]⟩
        · rw [hmerged_h, hy1]
        · rw [hmerged_l, hy2]
      · have hqF : q ∈ F.free := hperm_free.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
        obtain ⟨hq1, hq2⟩ := hrest_ne q hr
        obtain ⟨hqne, i, j, hsi, hsj, hmi, hmj⟩ := hm.free_ends q hqF
        obtain ⟨a1, b1, c1, d1⟩ := F.other_free_disjoint hl₁ hqF hq1.symm hends₁ ⟨hsi, hsj⟩
        obtain ⟨a2, b2, c2, d2⟩ := F.other_free_disjoint hl₂ hqF hq2.symm hends₂ ⟨hsi, hsj⟩
        refine ⟨hqne, i, j, hsi, hsj, by simp [b1, b2, a1, a2, hmi], by simp [d1, d2, c1, c2, hmj]⟩
    · intro i
      split_ifs with h1 h2 h3
      · subst h1; right; right
        refine ⟨j₂, rfl, by simp [hj1_ne_j2.symm], merged, List.mem_cons_self .., hmerged_ne, Or.inl ⟨?_, ?_⟩⟩
        · rw [hmerged_h, hy1]
        · rw [hmerged_l, hy2]
      · subst h2; right; right
        refine ⟨j₁, rfl, by simp, merged, List.mem_cons_self .., hmerged_ne, Or.inr ⟨?_, ?_⟩⟩
        · rw [hmerged_h, hy1]
        · rw [hmerged_l, hy2]
      · left; rfl
      · rcases hm.mate_valid i with h | h | ⟨j, hmi, hmj, q, hqF, hqne, hlr⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · have hq1 : q ≠ l₁ := by
            intro e; subst e
            rcases hlr with ⟨a, _⟩ | ⟨_, b⟩ <;> rcases hends₁ with ⟨c, d⟩ | ⟨c, d⟩
            · exact h3 (Or.inl (slotGlobal_injective w k (a.trans c.symm)))
            · exact h1 (slotGlobal_injective w k (a.trans c.symm))
            · exact h1 (slotGlobal_injective w k (b.trans d.symm))
            · exact h3 (Or.inl (slotGlobal_injective w k (b.trans d.symm)))
          have hq2 : q ≠ l₂ := by
            intro e; subst e
            rcases hlr with ⟨a, _⟩ | ⟨_, b⟩ <;> rcases hends₂ with ⟨c, d⟩ | ⟨c, d⟩
            · exact h3 (Or.inr (slotGlobal_injective w k (a.trans c.symm)))
            · exact h2 (slotGlobal_injective w k (a.trans c.symm))
            · exact h2 (slotGlobal_injective w k (b.trans d.symm))
            · exact h3 (Or.inr (slotGlobal_injective w k (b.trans d.symm)))
          have hqrest : q ∈ rest := by
            have := hperm_free.subset hqF
            rcases List.mem_cons.mp this with rfl | h'
            · exact absurd rfl hq1
            · rcases List.mem_cons.mp h' with rfl | hr
              · exact absurd rfl hq2
              · exact hr
          have hj_j1 : j ≠ j₁ := by
            intro e; subst e; rw [hm1'] at hmj
            exact h3 (Or.inl (Fin.ext (Int.ofNat.inj hmj.symm)))
          have hj_j2 : j ≠ j₂ := by
            intro e; subst e; rw [hm2'] at hmj
            exact h3 (Or.inr (Fin.ext (Int.ofNat.inj hmj.symm)))
          have hj_i1 : j ≠ i₁ := by
            intro e; subst e; rw [hm1] at hmj
            exact h1 (Fin.ext (Int.ofNat.inj hmj.symm))
          have hj_i2 : j ≠ i₂ := by
            intro e; subst e; rw [hm2] at hmj
            exact h2 (Fin.ext (Int.ofNat.inj hmj.symm))
          right; right
          exact ⟨j, hmi, by simp [hj_j1, hj_j2, hj_i1, hj_i2, hmj], q, List.mem_cons_of_mem _ hqrest, hqne, hlr⟩
  · unfold LinearForest.totalLen
    simp only [F', List.map_cons, List.sum_cons, merged]
    rw [pathLen_append dist p l₁' l₂' hl₁'ne hl₂'ne, hl₁'l, hl₂'h,
        orientEnd_len dist hsym p l₁ hl₁ne x₁, orientStart_len dist hsym p l₂ hl₂ne x₂]
    have hsum : (F.free.map fun q => pathLen dist q p).sum =
        pathLen dist l₁ p + pathLen dist l₂ p + (rest.map fun q => pathLen dist q p).sum := by
      rw [perm_map_sum _ hperm_free]; simp [add_assoc]
    rw [hsum]
    ring

/-- Helper: if slot `i` has `m i = j.val` and `i ≠ j` (or `l₁` is singleton at `i`), and `i₂` is a
different slot with `m i₂ ≠ i.val`, then their free paths `l₁` and `l₂` are distinct. -/
lemma free_ne_of_not_mate {w k : ℕ}
    {i₁ j₁ i₂ j₂ : Fin w} {l₁ l₂ : List ℕ}
    {hl₁ : l₁ ≠ []} {hl₂ : l₂ ≠ []}
    (hne_slot : i₁ ≠ i₂) (hnot_mate : j₁ ≠ i₂)
    (h1 : (slotGlobal w k i₁ = (l₁.head hl₁ : ℤ) ∧ slotGlobal w k j₁ = (l₁.getLast hl₁ : ℤ)) ∨
          (slotGlobal w k j₁ = (l₁.head hl₁ : ℤ) ∧ slotGlobal w k i₁ = (l₁.getLast hl₁ : ℤ)))
    (h2 : (slotGlobal w k i₂ = (l₂.head hl₂ : ℤ) ∧ slotGlobal w k j₂ = (l₂.getLast hl₂ : ℤ)) ∨
          (slotGlobal w k j₂ = (l₂.head hl₂ : ℤ) ∧ slotGlobal w k i₂ = (l₂.getLast hl₂ : ℤ))) :
    l₁ ≠ l₂ := by
  intro heq; subst heq
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases h2 with ⟨a2, _⟩ | ⟨_, b2⟩
  · exact hne_slot (slotGlobal_injective _ _ (a1.trans a2.symm))
  · exact hnot_mate (slotGlobal_injective _ _ (b1.trans b2.symm))
  · exact hnot_mate (slotGlobal_injective _ _ (a1.trans a2.symm))
  · exact hne_slot (slotGlobal_injective _ _ (b1.trans b2.symm))

/-- Connecting slot `v : Fin d` to `Fin.last d` preserves the linear forest invariant
and increases total length by the single Euclidean edge `(v, new)`. -/
lemma connectToNew_sound {α : Type*} {d k : ℕ} (dist : α → α → ℝ)
    (hsym : ∀ x y, dist x y = dist y x) (p : ℕ → α)
    {m m' : Mate (d + 1)} {F : LinearForest (k + 1)} (hm : Matches m F)
    {v : Fin d} (hc : connectToNew m v = some m') :
    ∃ F' : LinearForest (k + 1),
      Matches m' F' ∧
      F'.totalLen dist p = F.totalLen dist p +
        dist (p (slotGlobal (d + 1) (k + 1) v.castSucc).toNat) (p (k + 1)) := by
  have hlast_sg : (slotGlobal (d + 1) (k + 1) (Fin.last d)).toNat = k + 1 := by
    rw [slotGlobal_last]; simp
  have hv_ne_d : v.castSucc ≠ Fin.last d := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  unfold connectToNew at hc
  by_cases hbad : m v.castSucc = -2 ∨ m (Fin.last d) = -2 ∨ m v.castSucc = (d : ℤ)
  · simp [hbad] at hc
  rw [if_neg hbad] at hc
  by_cases hboth : m v.castSucc = (v.val : ℤ) ∧ m (Fin.last d) = (d : ℤ)
  · rw [if_pos hboth] at hc; injection hc with hm'; subst hm'
    obtain ⟨jv, lv, hlv, hlvne, hmv, hmjv, hendsv⟩ := hm.free_path_at (i := v.castSucc) (by omega)
    obtain ⟨jd, ld, hld, hldne, hmd, hmjd, hendsd⟩ := hm.free_path_at (i := Fin.last d) (by omega)
    have hjv_eq : jv = v.castSucc := Fin.ext (Int.ofNat.inj (hmv.symm.trans hboth.1))
    have hjd_eq : jd = Fin.last d := Fin.ext (Int.ofNat.inj (hmd.symm.trans hboth.2))
    subst hjv_eq; subst hjd_eq
    have hne := free_ne_of_not_mate hv_ne_d hv_ne_d hendsv hendsd
    obtain ⟨F', hMF', hlen⟩ := merge_free_free dist hsym p hm hlv hld hne hlvne hldne hmv hmjv hmd hmjd hendsv hendsd
    refine ⟨F', ?_, by rw [hlen, hlast_sg]⟩
    convert hMF' using 1
    funext i
    by_cases h1 : i = v.castSucc <;> by_cases h2 : i = Fin.last d <;> simp [h1, h2, Fin.val_last]
  rw [if_neg hboth] at hc
  by_cases hv_iso : m v.castSucc = (v.val : ℤ)
  · rw [if_pos hv_iso] at hc; injection hc with hm'; subst hm'
    obtain ⟨jv, lv, hlv, hlvne, hmv, hmjv, hendsv⟩ := hm.free_path_at (i := v.castSucc) (by omega)
    have hjv_eq : jv = v.castSucc := Fin.ext (Int.ofNat.inj (hmv.symm.trans hv_iso))
    subst hjv_eq
    rcases hm.mate_valid (Fin.last d) with h | h | ⟨jd, hmd, hmjd, ld, hld, hldne, hendsd⟩
    · exact absurd (Or.inr (Or.inl h)) hbad
    · obtain ⟨F', hMF', hlen⟩ := merge_anchor_free dist hsym p hm hlv hlvne h hmv hmjv hendsv
      refine ⟨F', ?_, by rw [hlen, hlast_sg, hsym]⟩
      convert hMF' using 1
      funext i
      by_cases h1 : i = v.castSucc
      · subst h1; simp [h]
      · by_cases h2 : i = Fin.last d
        · subst h2; simp [h1]
        · have h3 : (i.val : ℤ) ≠ m (Fin.last d) := by rw [h]; omega
          simp [h1, h2, h3]
    · have hjd_ne_d : jd ≠ Fin.last d := by
        intro e; subst e; exact hboth ⟨hv_iso, by simpa [Fin.val_last] using hmd⟩
      have hne := free_ne_of_not_mate hv_ne_d hv_ne_d hendsv hendsd
      obtain ⟨F', hMF', hlen⟩ := merge_free_free dist hsym p hm hlv hld hne hlvne hldne hmv hmjv hmd hmjd hendsv hendsd
      refine ⟨F', ?_, by rw [hlen, hlast_sg]⟩
      convert hMF' using 1
      funext i
      by_cases h1 : i = v.castSucc
      · subst h1; simp [hmd]
      · by_cases h2 : i = Fin.last d
        · subst h2; simp [h1, hjd_ne_d.symm]
        · by_cases h3 : i = jd
          · subst h3; simp [h1, h2, hmd]
          · have h4 : (i.val : ℤ) ≠ m (Fin.last d) := by
              rw [hmd]; intro e; exact h3 (Fin.ext (Int.ofNat.inj e))
            simp [h1, h2, h3, h4]
  rw [if_neg hv_iso] at hc
  by_cases hd_iso : m (Fin.last d) = (d : ℤ)
  · rw [if_pos hd_iso] at hc; injection hc with hm'; subst hm'
    obtain ⟨jd, ld, hld, hldne, hmd, hmjd, hendsd⟩ := hm.free_path_at (i := Fin.last d) (by omega)
    have hjd_eq : jd = Fin.last d := Fin.ext (Int.ofNat.inj (hmd.symm.trans hd_iso))
    subst hjd_eq
    rcases hm.mate_valid v.castSucc with h | h | ⟨jv, hmv, hmjv, lv, hlv, hlvne, hendsv⟩
    · exact absurd (Or.inl h) hbad
    · obtain ⟨F', hMF', hlen⟩ := merge_anchor_free dist hsym p hm hld hldne h hmd hmjd hendsd
      refine ⟨F', ?_, by rw [hlen, hlast_sg]⟩
      convert hMF' using 1
      funext i
      by_cases h1 : i = Fin.last d
      · subst h1; simp [h]
      · by_cases h2 : i = v.castSucc
        · subst h2; simp [h1]
        · have h3 : (i.val : ℤ) ≠ m v.castSucc := by rw [h]; omega
          simp [h1, h2, h3]
    · have hjv_ne_v : jv ≠ v.castSucc := by
        intro e; subst e; exact hv_iso (by simpa using hmv)
      have hjv_ne_d : jv ≠ Fin.last d := by
        intro e; subst e; exact hbad (Or.inr (Or.inr (by simpa [Fin.val_last] using hmv)))
      have hne := free_ne_of_not_mate hv_ne_d hjv_ne_d hendsv hendsd
      obtain ⟨F', hMF', hlen⟩ := merge_free_free dist hsym p hm hlv hld hne hlvne hldne hmv hmjv hmd hmjd hendsv hendsd
      refine ⟨F', ?_, by rw [hlen, hlast_sg]⟩
      convert hMF' using 1
      funext i
      by_cases h1 : i = Fin.last d
      · subst h1; simp [hmv, hjv_ne_d.symm]
      · by_cases h2 : i = v.castSucc
        · subst h2; simp [h1, hjv_ne_v.symm]
        · by_cases h3 : i = jv
          · subst h3; simp [h1, h2, hmv, Fin.val_last]
          · have h4 : (i.val : ℤ) ≠ m v.castSucc := by
              rw [hmv]; intro e; exact h3 (Fin.ext (Int.ofNat.inj e))
            simp [h1, h2, h3, h4]
  rw [if_neg hd_iso] at hc
  by_cases h2a : m v.castSucc = -1 ∧ m (Fin.last d) = -1
  · simp [h2a] at hc
  rw [if_neg h2a] at hc; injection hc with hm'; subst hm'
  rcases hm.mate_valid v.castSucc with hv2 | hv1 | ⟨jv, hmv, hmjv, lv, hlv, hlvne, hendsv⟩
  · exact absurd (Or.inl hv2) hbad
  · rcases hm.mate_valid (Fin.last d) with hd2 | hd1 | ⟨jd, hmd, hmjd, ld, hld, hldne, hendsd⟩
    · exact absurd (Or.inr (Or.inl hd2)) hbad
    · exact absurd ⟨hv1, hd1⟩ h2a
    · have hjd_ne_d : jd ≠ Fin.last d := by
        intro e; subst e; exact hd_iso (by simpa [Fin.val_last] using hmd)
      have hjd_ne_v : jd ≠ v.castSucc := anchor_ne_free hv1 (by omega)
      obtain ⟨F', hMF', hlen⟩ := merge_anchor_free dist hsym p hm hld hldne hv1 hmd hmjd hendsd
      refine ⟨F', ?_, by rw [hlen, hlast_sg]⟩
      convert hMF' using 1
      funext i
      by_cases h1 : i = v.castSucc
      · subst h1; simp [hjd_ne_v.symm]
      · by_cases h2 : i = Fin.last d
        · subst h2; simp [hjd_ne_d.symm]
        · by_cases h3 : i = jd
          · subst h3; simp [h1, h2, hv1, hmd]
          · have h4 : (i.val : ℤ) ≠ m v.castSucc := by rw [hv1]; omega
            have h5 : (i.val : ℤ) ≠ m (Fin.last d) := by
              rw [hmd]; intro e; exact h3 (Fin.ext (Int.ofNat.inj e))
            simp [h1, h2, h3, h4, h5]
  · have hjv_ne_v : jv ≠ v.castSucc := by
      intro e; subst e; exact hv_iso (by simpa using hmv)
    have hjv_ne_d : jv ≠ Fin.last d := by
      intro e; subst e; exact hbad (Or.inr (Or.inr (by simpa [Fin.val_last] using hmv)))
    rcases hm.mate_valid (Fin.last d) with hd2 | hd1 | ⟨jd, hmd, hmjd, ld, hld, hldne, hendsd⟩
    · exact absurd (Or.inr (Or.inl hd2)) hbad
    · obtain ⟨F', hMF', hlen⟩ := merge_anchor_free dist hsym p hm hlv hlvne hd1 hmv hmjv hendsv
      refine ⟨F', ?_, by rw [hlen, hlast_sg, hsym]⟩
      convert hMF' using 1
      funext i
      by_cases h1 : i = v.castSucc
      · subst h1; simp [hjv_ne_v.symm]
      · by_cases h2 : i = Fin.last d
        · subst h2; simp [hjv_ne_d.symm]
        · by_cases h3 : i = jv
          · subst h3; simp [h1, h2, hd1, hmv]
          · have h4 : (i.val : ℤ) ≠ m v.castSucc := by
              rw [hmv]; intro e; exact h3 (Fin.ext (Int.ofNat.inj e))
            have h5 : (i.val : ℤ) ≠ m (Fin.last d) := by rw [hd1]; omega
            simp [h1, h2, h3, h4, h5]
    · have hjd_ne_d : jd ≠ Fin.last d := by
        intro e; subst e; exact hd_iso (by simpa [Fin.val_last] using hmd)
      have hne := free_ne_of_not_mate hv_ne_d hjv_ne_d hendsv hendsd
      have hjv_ne_jd : jv ≠ jd := by
        intro e; subst e
        exact hne (by
          rcases hendsv with ⟨_, bv⟩ | ⟨av, _⟩ <;> rcases hendsd with ⟨_, bd⟩ | ⟨ad, _⟩
          · have hxy := Int.ofNat.inj (bv.symm.trans bd)
            exact F.free_eq_of_mem_inter hlv hld (List.getLast_mem hlvne) (by rw [hxy]; exact List.getLast_mem hldne)
          · have hxy := Int.ofNat.inj (bv.symm.trans ad)
            exact F.free_eq_of_mem_inter hlv hld (List.getLast_mem hlvne) (by rw [hxy]; exact List.head_mem hldne)
          · have hxy := Int.ofNat.inj (av.symm.trans bd)
            exact F.free_eq_of_mem_inter hlv hld (List.head_mem hlvne) (by rw [hxy]; exact List.getLast_mem hldne)
          · have hxy := Int.ofNat.inj (av.symm.trans ad)
            exact F.free_eq_of_mem_inter hlv hld (List.head_mem hlvne) (by rw [hxy]; exact List.head_mem hldne))
      have hjd_ne_v : jd ≠ v.castSucc := by
        intro e; subst e; rw [hmv] at hmjd
        exact hjv_ne_d (Fin.ext (Int.ofNat.inj hmjd))
      obtain ⟨F', hMF', hlen⟩ := merge_free_free dist hsym p hm hlv hld hne hlvne hldne hmv hmjv hmd hmjd hendsv hendsd
      refine ⟨F', ?_, by rw [hlen, hlast_sg]⟩
      convert hMF' using 1
      funext i
      by_cases h1 : i = v.castSucc
      · subst h1; simp [hjv_ne_v.symm, hjd_ne_v.symm]
      · by_cases h2 : i = Fin.last d
        · subst h2; simp [hjv_ne_d.symm, hjd_ne_d.symm]
        · by_cases h3 : i = jv
          · subst h3; simp [h1, h2, hmv, hmd]
          · by_cases h4 : i = jd
            · subst h4; simp [h1, h2, h3, hmv, hmd]
            · have h5 : (i.val : ℤ) ≠ m v.castSucc := by
                rw [hmv]; intro e; exact h3 (Fin.ext (Int.ofNat.inj e))
              have h6 : (i.val : ℤ) ≠ m (Fin.last d) := by
                rw [hmd]; intro e; exact h4 (Fin.ext (Int.ofNat.inj e))
              simp [h1, h2, h3, h4, h5, h6]

/-- Sum of edge distances for connecting new vertex `k + 1` to the chosen frontier slots. -/
def stepCost {α : Type*} {d : ℕ} (dist : α → α → ℝ) (p : ℕ → α) (k : ℕ)
    (chosen : List (Fin d)) : ℝ :=
  (chosen.map fun v => dist (p (k + 1 - (d - v.val))) (p (k + 1))).sum

lemma slotGlobal_toNat_eq (d k : ℕ) (v : Fin d) (hnn : 0 ≤ slotGlobal (d + 1) (k + 1) v.castSucc) :
    (slotGlobal (d + 1) (k + 1) v.castSucc).toNat = k + 1 - (d - v.val) := by
  unfold slotGlobal at hnn ⊢
  simp at hnn ⊢
  omega

/-- Soundness of folding `connectToNew` over a list `chosen` of connections. -/
lemma foldlM_connectToNew_sound {α : Type*} {d k : ℕ} (dist : α → α → ℝ)
    (hsym : ∀ x y, dist x y = dist y x) (p : ℕ → α) :
    ∀ (chosen : List (Fin d)) (m m' : Mate (d + 1)) (F : LinearForest (k + 1)),
      Matches m F →
      chosen.foldlM connectToNew m = some m' →
      ∃ F' : LinearForest (k + 1),
        Matches m' F' ∧ F'.totalLen dist p = F.totalLen dist p + stepCost dist p k chosen
  | [], m, m', F, hm, hfold => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
    subst hfold
    exact ⟨F, hm, by simp [stepCost]⟩
  | v :: rest, m, m', F, hm, hfold => by
    simp only [List.foldlM_cons] at hfold
    cases h1 : connectToNew m v with
    | none => simp [h1] at hfold
    | some m1 =>
      simp [h1] at hfold
      have hact : m v.castSucc ≠ -2 := by
        unfold connectToNew at h1
        intro h; simp [h] at h1
      have hnn := slotGlobal_nonneg_of_active hm hact
      obtain ⟨F1, hMF1, hlen1⟩ := connectToNew_sound dist hsym p hm h1
      obtain ⟨F2, hMF2, hlen2⟩ := foldlM_connectToNew_sound dist hsym p rest m1 m' F1 hMF1 hfold
      refine ⟨F2, hMF2, ?_⟩
      rw [hlen2, hlen1, slotGlobal_toNat_eq d k v hnn]
      simp only [stepCost, List.map_cons, List.sum_cons]
      ring

/-- One full automaton transition `stepState st chosen = some st'` advances a linear forest
from `k` to `k + 1` and adds `stepCost dist p k chosen` to its total length. -/
theorem stepState_sound {α : Type*} {d k : ℕ} (dist : α → α → ℝ)
    (hsym : ∀ x y, dist x y = dist y x) (p : ℕ → α)
    {st st' : Mate d} {F : LinearForest k} (hm : Matches st F)
    {chosen : List (Fin d)} (hs : stepState st chosen = some st') :
    ∃ F' : LinearForest (k + 1),
      Matches st' F' ∧ F'.totalLen dist p = F.totalLen dist p + stepCost dist p k chosen := by
  unfold stepState at hs
  cases hfold : chosen.foldlM connectToNew (addIsolated st) with
  | none => simp [hfold] at hs
  | some m1 =>
    simp [hfold] at hs
    obtain ⟨F0, hMF0, hlen0⟩ := addIsolated_sound dist p hm
    obtain ⟨F1, hMF1, hlen1⟩ := foldlM_connectToNew_sound dist hsym p chosen (addIsolated st) m1 F0 hMF0 hfold
    exact ⟨F1, shiftWindow_sound hMF1 hs, by rw [hlen1, hlen0]⟩

/-- **Main Automaton Theorem:** Any valid walk of length `N` in the bandwidth-`d` frontier
automaton starting and ending at `initState d` produces a single Hamiltonian path from `0`
to `N` visiting every vertex in `{0, ..., N}` exactly once, whose Euclidean path length
equals the sum of step costs along the walk. -/
theorem walk_to_hamiltonian_path {α : Type*} {d N : ℕ} (hd : 0 < d)
    (dist : α → α → ℝ) (hsym : ∀ x y, dist x y = dist y x) (p : ℕ → α)
    (states : Fin (N + 1) → Mate d) (choices : Fin N → List (Fin d))
    (hstart : states 0 = initState d)
    (hend : states ⟨N, Nat.lt_succ_self N⟩ = initState d)
    (hstep : ∀ t : Fin N, stepState (states t.castSucc) (choices t) = some (states t.succ)) :
    ∃ path : List ℕ, ∃ hne : path ≠ [],
      path.Perm (List.range (N + 1)) ∧
      path.head hne = 0 ∧
      path.getLast hne = N ∧
      pathLen dist path p = ∑ t : Fin N, stepCost dist p t.val (choices t) := by
  have hind : ∀ (n : ℕ) (hn : n ≤ N),
      ∃ F : LinearForest n,
        Matches (states ⟨n, by omega⟩) F ∧
        F.totalLen dist p = ∑ t : Fin n, stepCost dist p t.val (choices ⟨t.val, by omega⟩) := by
    intro n hn
    induction n with
    | zero =>
      refine ⟨initForest, ?_, by simp [initForest, LinearForest.totalLen, pathLen]⟩
      simpa [hstart] using init_matches d hd
    | succ n ih =>
      obtain ⟨F, hMF, hlen⟩ := ih (by omega)
      have hs := hstep ⟨n, by omega⟩
      obtain ⟨F', hMF', hlen'⟩ := stepState_sound dist hsym p hMF hs
      refine ⟨F', hMF', ?_⟩
      rw [hlen', hlen, Fin.sum_univ_castSucc]
      rfl
  obtain ⟨F, hMF, hlen⟩ := hind N (le_refl N)
  rw [hend] at hMF
  obtain ⟨hfree, hperm, hhead, hlast⟩ := final_matches_hamiltonian F hMF
  refine ⟨F.anchor, F.anchor_ne, hperm, hhead, hlast, ?_⟩
  have htot : F.totalLen dist p = pathLen dist F.anchor p := by
    simp [LinearForest.totalLen, hfree]
  rw [← htot, hlen]

end BHHBounds.Upper
