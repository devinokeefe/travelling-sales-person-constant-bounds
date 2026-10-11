/-
The recurrences of the plan: for every computed slot, the least of the sums over its terms is the
least cost of a path of the slot (`good_step`).
-/
import TSPBound.Correct.Paths

namespace Correct
open Spec Impl

/-- Lists without repetitions that have the same elements are rearrangements of each other. -/
theorem perm_of_nodup {l₁ l₂ : List Nat} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro a
  have h1 := List.nodup_iff_count.mp d₁ a
  have h2 := List.nodup_iff_count.mp d₂ a
  have h3 : 0 < List.count a l₁ ↔ a ∈ l₁ := List.count_pos_iff
  have h4 : 0 < List.count a l₂ ↔ a ∈ l₂ := List.count_pos_iff
  by_cases ha : a ∈ l₁
  · have := h3.mpr ha
    have := h4.mpr ((h a).mp ha)
    omega
  · have hb : a ∉ l₂ := fun hb => ha ((h a).mpr hb)
    have : ¬ 0 < List.count a l₁ := fun x => ha (h3.mp x)
    have : ¬ 0 < List.count a l₂ := fun x => hb (h4.mp x)
    omega

theorem filter_mem_subsets (l : List Nat) (q : Nat → Bool) : l.filter q ∈ subsets l := by
  induction l with
  | nil => simp [subsets]
  | cons x l ih =>
    simp only [subsets, List.mem_append, List.mem_map, List.filter_cons]
    by_cases hx : q x = true
    · simp only [hx, if_true]; exact Or.inr ⟨_, ih, rfl⟩
    · simp only [hx]; exact Or.inl ih

theorem getLast?_snoc (l : List Nat) (y : Nat) : (l ++ [y]).getLast? = some y :=
  List.getLast?_eq_some_iff.mpr ⟨l, rfl⟩

theorem getLast?_of_append_cons {l₁ l₂ : List Nat} {x w : Nat}
    (h : (l₁ ++ x :: l₂).getLast? = some w) (hne : w ≠ x) : l₂.getLast? = some w := by
  rw [List.getLast?_append, List.getLast?_cons] at h
  cases hl : l₂.getLast? with
  | none => simp [hl] at h; exact absurd h.symm hne
  | some z => simp [hl] at h; rw [h]

/-! ## The slots `A S u` -/

theorem good_A (k : Nat) (ein st en : Nat → Nat → Nat) (S : List Nat) (u : Nat) (v : Slot → Nat)
    (hne : terms k (.A S u) ≠ [])
    (hv : ∀ ab ∈ terms k (.A S u), Good k ein st en ab.1 (v ab.1) ∧ Good k ein st en ab.2 (v ab.2)) :
    Good k ein st en (.A S u) (minOf ((terms k (.A S u)).map (fun ab => v ab.1 + v ab.2))) := by
  apply good_of v hne hv
  · intro ab hab πa πb ha hb
    simp only [terms] at hab
    split at hab
    · rename_i hS
      simp only [List.mem_singleton] at hab
      subst hab
      simp only [Paths] at ha hb
      subst ha hb hS
      exact ⟨[u, k - 1], ⟨[], by simp, rfl⟩, by simp [Cost]⟩
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      simp only [Paths] at ha hb
      obtain ⟨σ', hσ', rfl⟩ := hb
      subst ha
      refine ⟨u :: ((y :: σ') ++ [k - 1]), ⟨y :: σ', ?_, rfl⟩, ?_⟩
      · exact (hσ'.cons y).trans (List.perm_cons_erase hy).symm
      · simp [Cost, pathLen]
  · intro π hπ
    simp only [Paths] at hπ
    obtain ⟨σ, hσ, rfl⟩ := hπ
    simp only [terms] at hne ⊢
    split
    · rename_i hS
      subst hS
      have : σ = [] := by simpa using hσ
      subst this
      exact ⟨_, List.mem_singleton.mpr rfl, [u, k - 1], [], rfl, rfl, by simp [Cost]⟩
    · rename_i hS
      simp only [hS, if_false] at hne
      have hne2 : S.erase u ≠ [] := by simpa using hne
      cases σ with
      | nil => exact absurd (List.nil_perm.mp hσ) hne2
      | cons y σ' =>
        have hy : y ∈ S.erase u := hσ.subset List.mem_cons_self
        have hσ' : σ'.Perm ((S.erase u).erase y) := by
          have := hσ.erase y
          simpa using this
        exact ⟨(.ein u y, .A (S.erase u) y), List.mem_map.mpr ⟨y, hy, rfl⟩, [u, y],
          y :: (σ' ++ [k - 1]), rfl, ⟨σ', hσ', rfl⟩, by simp [Cost, pathLen]⟩

/-! ## The slots `H u v` -/

/-- A path through all interior points from `u` to the last one is `u`, then the others, then the last. -/
theorem decomp_end {k u : Nat} (hk : 2 ≤ k) (hu : u ∈ others k) {π : List Nat}
    (hperm : π.Perm (interior k)) (hhead : π.head? = some u) (hlast : π.getLast? = some (k - 1)) :
    ∃ σ, σ.Perm ((others k).erase u) ∧ π = u :: (σ ++ [k - 1]) := by
  have huj : u ≠ k - 1 := fun h => last_not_mem_others k (h ▸ hu)
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  cases ys with
  | nil => simp at hhead; exact absurd hhead.symm huj
  | cons y σ =>
    simp at hhead
    subst hhead
    refine ⟨σ, ?_, rfl⟩
    rw [interior_eq k hk] at hperm
    have h1 : (y :: σ).Perm (others k) := (List.perm_append_right_iff [k - 1]).mp hperm
    have h2 := h1.erase y
    simpa using h2

theorem path_of_end {k u : Nat} (hk : 2 ≤ k) (hu : u ∈ others k) {σ : List Nat}
    (hσ : σ.Perm ((others k).erase u)) :
    (u :: (σ ++ [k - 1])).Perm (interior k) := by
  rw [interior_eq k hk]
  have h1 : (u :: σ).Perm (others k) := (hσ.cons u).trans (List.perm_cons_erase hu).symm
  exact h1.append_right [k - 1]

theorem good_H (k : Nat) (hk : 2 ≤ k) (ein st en : Nat → Nat → Nat) (hsym : ∀ x y, ein x y = ein y x)
    (u w : Nat) (v : Slot → Nat) (hvalid : (Slot.H u w).valid k = true)
    (hne : terms k (.H u w) ≠ [])
    (hv : ∀ ab ∈ terms k (.H u w), Good k ein st en ab.1 (v ab.1) ∧ Good k ein st en ab.2 (v ab.2)) :
    Good k ein st en (.H u w) (minOf ((terms k (.H u w)).map (fun ab => v ab.1 + v ab.2))) := by
  simp only [Slot.valid, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at hvalid
  obtain ⟨⟨hu, hw⟩, huw⟩ := hvalid
  apply good_of v hne hv
  · -- soundness
    intro ab hab πa πb ha hb
    simp only [terms] at hab
    split at hab
    · -- w = k - 1
      rename_i hwj
      simp only [List.mem_singleton] at hab
      subst hab
      have huo : u ∈ others k := mem_others_of hk hu (fun h => huw (h.trans hwj.symm))
      simp only [Paths] at ha hb
      obtain ⟨σ, hσ, rfl⟩ := ha
      subst hb
      refine ⟨u :: (σ ++ [k - 1]), ⟨path_of_end hk huo hσ, by simp, hwj ▸ getLast?_snoc (u :: σ) (k - 1)⟩, by simp [Cost]⟩
    · split at hab
      · -- u = k - 1
        rename_i hwj huj
        simp only [List.mem_singleton] at hab
        subst hab
        have hwo : w ∈ others k := mem_others_of hk hw hwj
        simp only [Paths] at ha hb
        obtain ⟨σ, hσ, rfl⟩ := ha
        subst hb
        refine ⟨(w :: (σ ++ [k - 1])).reverse,
          ⟨(List.reverse_perm _).trans (path_of_end hk hwo hσ), ?_, ?_⟩, ?_⟩
        · rw [List.head?_reverse, huj]; exact getLast?_snoc (w :: σ) (k - 1)
        · rw [List.getLast?_reverse]; simp
        · simp only [Cost, Nat.add_zero]
          rw [pathLen_reverse ein hsym]
          exact Nat.le_refl _
      · split at hab
        · -- u < w, both different from k - 1
          rename_i hwj huj hlt
          obtain ⟨R, _, rfl⟩ := List.mem_map.mp hab
          have huo : u ∈ others k := mem_others_of hk hu huj
          have hwo : w ∈ others k := mem_others_of hk hw hwj
          simp only [Paths] at ha hb
          obtain ⟨σ1, hσ1, rfl⟩ := ha
          obtain ⟨σ2, hσ2, rfl⟩ := hb
          -- the two sets are complementary in `others k`
          have hu1 : u ∈ (others k).filter (fun x => (R.contains x || x == u) && x != w) := by
            simp [List.mem_filter, huo, huw]
          have hw2 : w ∈ (others k).filter (fun x => !((R.contains x || x == u) && x != w)) := by
            simp [List.mem_filter, hwo]
          have p1 : (u :: σ1).Perm ((others k).filter (fun x => (R.contains x || x == u) && x != w)) :=
            (hσ1.cons u).trans (List.perm_cons_erase hu1).symm
          have p2 : (w :: σ2).Perm ((others k).filter (fun x => !((R.contains x || x == u) && x != w))) :=
            (hσ2.cons w).trans (List.perm_cons_erase hw2).symm
          have p3 := List.filter_append_perm (fun x => (R.contains x || x == u) && x != w) (others k)
          refine ⟨(u :: σ1) ++ (k - 1) :: (w :: σ2).reverse, ⟨?_, by simp,
            List.getLast?_eq_some_iff.mpr ⟨(u :: σ1) ++ (k - 1) :: σ2.reverse, by simp⟩⟩, ?_⟩
          · rw [interior_eq k hk]
            have h4 : ((u :: σ1) ++ (k - 1) :: (w :: σ2).reverse).Perm
                ((k - 1) :: ((u :: σ1) ++ (w :: σ2).reverse)) := List.perm_middle
            have h5 : ((u :: σ1) ++ (w :: σ2).reverse).Perm (others k) :=
              (List.Perm.append p1 ((List.reverse_perm _).trans p2)).trans p3
            exact h4.trans ((h5.cons (k - 1)).trans (List.perm_append_singleton (k - 1) (others k)).symm)
          · have h6 := pathLen_append ein (u :: σ1) (k - 1) (w :: σ2).reverse
            have h7 : (k - 1) :: (w :: σ2).reverse = (w :: (σ2 ++ [k - 1])).reverse := by simp
            have h8 := pathLen_reverse ein hsym (w :: (σ2 ++ [k - 1]))
            simp only [Cost]
            rw [h6, h7, h8]
            simp
        · -- w < u
          simp only [List.mem_singleton] at hab
          subst hab
          simp only [Paths] at ha hb
          obtain ⟨hp, hh, hl⟩ := ha
          subst hb
          refine ⟨πa.reverse, ⟨(List.reverse_perm _).trans hp, ?_, ?_⟩, ?_⟩
          · rw [List.head?_reverse]; exact hl
          · rw [List.getLast?_reverse]; exact hh
          · simp only [Cost, Nat.add_zero]
            rw [pathLen_reverse ein hsym]
            exact Nat.le_refl _
  · -- completeness
    intro π hπ
    simp only [Paths] at hπ
    obtain ⟨hperm, hhead, hlast⟩ := hπ
    simp only [terms]
    split
    · rename_i hwj
      have huo : u ∈ others k := mem_others_of hk hu (fun h => huw (h.trans hwj.symm))
      obtain ⟨σ, hσ, rfl⟩ := decomp_end hk huo hperm hhead (hwj ▸ hlast)
      exact ⟨_, List.mem_singleton.mpr rfl, _, [], ⟨σ, hσ, rfl⟩, rfl, by simp [Cost]⟩
    · split
      · rename_i hwj huj
        have hwo : w ∈ others k := mem_others_of hk hw hwj
        have hrev : ∃ σ, σ.Perm ((others k).erase w) ∧ π.reverse = w :: (σ ++ [k - 1]) :=
          decomp_end hk hwo ((List.reverse_perm _).trans hperm)
            (by rw [List.head?_reverse]; exact hlast) (by rw [List.getLast?_reverse, hhead, huj])
        obtain ⟨σ, hσ, hrev⟩ := hrev
        refine ⟨_, List.mem_singleton.mpr rfl, π.reverse, [], ⟨σ, hσ, hrev⟩, rfl, ?_⟩
        simp only [Cost, Nat.add_zero]
        rw [pathLen_reverse ein hsym]
        exact Nat.le_refl _
      · split
        · rename_i hwj huj hlt
          have huo : u ∈ others k := mem_others_of hk hu huj
          have hwo : w ∈ others k := mem_others_of hk hw hwj
          have hnd : π.Nodup := (hperm.nodup_iff).mpr (nodup_interior k)
          have hjmem : k - 1 ∈ π := hperm.symm.subset (by rw [interior_eq k hk]; simp)
          obtain ⟨π1, π2, rfl⟩ := List.append_of_mem hjmem
          -- the first part starts with `u`
          cases π1 with
          | nil => simp at hhead; exact absurd hhead.symm huj
          | cons u' σ1 =>
            simp at hhead
            subst hhead
            -- the second part ends with `w`
            have hl2 : π2.getLast? = some w := getLast?_of_append_cons hlast hwj
            obtain ⟨τ, rfl⟩ := List.getLast?_eq_some_iff.mp hl2
            -- membership in the path
            have hmem : ∀ x, x ∈ (u' :: σ1) ++ (k - 1) :: (τ ++ [w]) ↔ (x ∈ others k ∨ x = k - 1) := by
              intro x
              rw [hperm.mem_iff, interior_eq k hk]; simp
            have hnd' := hnd
            simp only [List.cons_append, List.nodup_cons, List.nodup_append, List.mem_append,
              List.mem_cons, List.nodup_nil, List.not_mem_nil] at hnd'
            let R := ((others k).filter (fun x => x != u' && x != w)).filter (fun x => σ1.contains x)
            have hR : R ∈ subsets ((others k).filter (fun x => x != u' && x != w)) :=
              filter_mem_subsets _ _
            have hRmem : ∀ x, x ∈ R ↔ x ∈ σ1 := by
              intro x
              simp only [R, List.mem_filter, List.contains_iff_mem, Bool.and_eq_true, bne_iff_ne, ne_eq]
              constructor
              · intro h; exact h.2
              · intro h
                have h1 := (hmem x).mp (by simp [h])
                have := last_not_mem_others k
                grind
            have hndo := nodup_others k
            have q1 : σ1.Perm (((others k).filter (fun x => (R.contains x || x == u') && x != w)).erase u') := by
              apply perm_of_nodup
              · grind
              · exact (hndo.filter _).erase _
              · intro x
                rw [List.Nodup.mem_erase_iff (hndo.filter _)]
                simp only [List.mem_filter, List.contains_iff_mem, Bool.and_eq_true, Bool.or_eq_true,
                  beq_iff_eq, bne_iff_ne, ne_eq, hRmem]
                have h1 := hmem x
                have := last_not_mem_others k
                grind
            have q2 : τ.reverse.Perm (((others k).filter (fun x => !((R.contains x || x == u') && x != w))).erase w) := by
              apply perm_of_nodup
              · rw [(List.reverse_perm τ).nodup_iff]; grind
              · exact (hndo.filter _).erase _
              · intro x
                rw [List.Nodup.mem_erase_iff (hndo.filter _)]
                simp only [List.mem_filter, ne_eq, Bool.not_eq_true', List.mem_reverse]
                have h1 := hmem x
                have := last_not_mem_others k
                grind
            refine ⟨_, List.mem_map.mpr ⟨R, hR, rfl⟩, u' :: (σ1 ++ [k - 1]), w :: (τ.reverse ++ [k - 1]),
              ⟨σ1, q1, rfl⟩, ⟨τ.reverse, q2, rfl⟩, ?_⟩
            have h6 := pathLen_append ein (u' :: σ1) (k - 1) (τ ++ [w])
            have h7 : w :: (τ.reverse ++ [k - 1]) = ((k - 1) :: (τ ++ [w])).reverse := by simp
            have h8 := pathLen_reverse ein hsym ((k - 1) :: (τ ++ [w]))
            simp only [Cost]
            rw [h6, h7, h8]
            simp
        · refine ⟨_, List.mem_singleton.mpr rfl, π.reverse, [],
            ⟨(List.reverse_perm _).trans hperm, ?_, ?_⟩, rfl, ?_⟩
          · rw [List.head?_reverse]; exact hlast
          · rw [List.getLast?_reverse]; exact hhead
          · simp only [Cost, Nat.add_zero]
            rw [pathLen_reverse ein hsym]
            exact Nat.le_refl _

/-! ## The slots `L a w` and `C a b` -/

theorem good_L (k : Nat) (ein st en : Nat → Nat → Nat) (a w : Nat) (v : Slot → Nat)
    (hvalid : (Slot.L a w).valid k = true)
    (hne : terms k (.L a w) ≠ [])
    (hv : ∀ ab ∈ terms k (.L a w), Good k ein st en ab.1 (v ab.1) ∧ Good k ein st en ab.2 (v ab.2)) :
    Good k ein st en (.L a w) (minOf ((terms k (.L a w)).map (fun ab => v ab.1 + v ab.2))) := by
  simp only [Slot.valid, List.contains_iff_mem] at hvalid
  apply good_of v hne hv
  · intro ab hab πa πb ha hb
    simp only [terms] at hab
    split at hab
    · rename_i hk2
      simp only [List.mem_singleton] at hab
      subst hab
      simp only [Paths] at ha hb
      subst ha hb
      have hint : interior k = [1] := by subst hk2; rfl
      have hw1 : w = 1 := by rw [hint] at hvalid; simpa using hvalid
      exact ⟨[w], ⟨by rw [hint, hw1], by simp⟩, by simp [Cost, pathLen]⟩
    · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hab
      simp only [Paths] at ha hb
      subst ha
      obtain ⟨hp, hh, hl⟩ := hb
      exact ⟨πb, ⟨hp, hl⟩, by simp [Cost, hh]⟩
  · intro π hπ
    simp only [Paths] at hπ
    obtain ⟨hperm, hlast⟩ := hπ
    simp only [terms]
    split
    · rename_i hk2
      have hint : interior k = [1] := by subst hk2; rfl
      rw [hint] at hperm
      have hπ1 : π = [1] := List.perm_singleton.mp hperm
      subst hπ1
      have hw1 : 1 = w := by simpa using hlast
      subst hw1
      exact ⟨_, List.mem_singleton.mpr rfl, [1], [], rfl, rfl, by simp [Cost, pathLen]⟩
    · have hlen : π.length = k - 1 := by rw [hperm.length_eq]; simp [interior]
      have hnd : π.Nodup := hperm.nodup_iff.mpr (nodup_interior k)
      cases π with
      | nil => simp at hlast
      | cons u π' =>
        cases π' with
        | nil =>
          rename_i hk2
          have : interior k = [u] := (List.perm_singleton.mp hperm.symm)
          simp [interior] at this hlen
          exact absurd (by omega) hk2
        | cons z π'' =>
          have hl2 : (z :: π'').getLast? = some w := by simpa using hlast
          have hwmem : w ∈ z :: π'' := List.mem_of_getLast? hl2
          have huw : u ≠ w := by
            intro h; subst h; exact (List.nodup_cons.mp hnd).1 hwmem
          have hu : u ∈ interior k := hperm.subset List.mem_cons_self
          exact ⟨(.st a u, .H u w), List.mem_map.mpr ⟨u, by simp [List.mem_filter, hu, huw], rfl⟩,
            [u], u :: z :: π'', rfl, ⟨hperm, by simp, hlast⟩, by simp [Cost]⟩

theorem good_C (k : Nat) (hk : 2 ≤ k) (ein st en : Nat → Nat → Nat) (a b : Nat) (v : Slot → Nat)
    (hne : terms k (.C a b) ≠ [])
    (hv : ∀ ab ∈ terms k (.C a b), Good k ein st en ab.1 (v ab.1) ∧ Good k ein st en ab.2 (v ab.2)) :
    Good k ein st en (.C a b) (minOf ((terms k (.C a b)).map (fun ab => v ab.1 + v ab.2))) := by
  apply good_of v hne hv
  · intro ab hab πa πb ha hb
    simp only [terms] at hab
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hab
    simp only [Paths] at ha hb
    obtain ⟨hp, hl⟩ := ha
    subst hb
    exact ⟨πa, hp, by simp [Cost, hl]⟩
  · intro π hπ
    simp only [Paths] at hπ
    have hne' : π ≠ [] := by
      intro h; subst h
      have := hπ.length_eq
      simp [interior] at this; omega
    obtain ⟨w, hw⟩ : ∃ w, π.getLast? = some w := by
      cases h : π.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne'
      | some w => exact ⟨w, rfl⟩
    have hwmem : w ∈ interior k := hπ.subset (List.mem_of_getLast? hw)
    exact ⟨(.L a w, .en b w), List.mem_map.mpr ⟨w, hwmem, rfl⟩, π, [w], ⟨hπ, hw⟩, rfl,
      by simp [Cost, hw]⟩

/-! ## All computed slots -/

/-- If the numbers `v` of the terms of a valid slot are good, the least of the sums is good. -/
theorem good_step (k : Nat) (hk : 2 ≤ k) (ein st en : Nat → Nat → Nat)
    (hsym : ∀ x y, ein x y = ein y x) (s : Slot) (v : Slot → Nat)
    (hvalid : s.valid k = true) (hne : terms k s ≠ [])
    (hv : ∀ ab ∈ terms k s, Good k ein st en ab.1 (v ab.1) ∧ Good k ein st en ab.2 (v ab.2)) :
    Good k ein st en s (minOf ((terms k s).map (fun ab => v ab.1 + v ab.2))) := by
  cases s with
  | zero => simp [Slot.valid] at hvalid
  | ein u w => simp [Slot.valid] at hvalid
  | st a u => simp [Slot.valid] at hvalid
  | en b w => simp [Slot.valid] at hvalid
  | A S u => exact good_A k ein st en S u v hne hv
  | H u w => exact good_H k hk ein st en hsym u w v hvalid hne hv
  | L a w => exact good_L k ein st en a w v hvalid hne hv
  | C a b => exact good_C k hk ein st en a b v hne hv

end Correct
