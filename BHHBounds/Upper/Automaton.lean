import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Bandwidth-d Linear-Forest Frontier Automaton for Strip Hamiltonian Paths

Given points `p : ℕ → α` and any symmetric distance `dist : α → α → ℝ`, a walk in
the bandwidth-`d` linear-forest automaton starting and ending at `initState d`
produces a single Hamiltonian path from vertex `0` to vertex `N` visiting every
vertex in `{0, ..., N}` exactly once, whose total edge length equals the sum of
edge weights along the walk.
-/

namespace BHHBounds.Upper

/-- Distance of a path (sum of consecutive edge weights). -/
def pathLen {α : Type*} (dist : α → α → ℝ) : List ℕ → (ℕ → α) → ℝ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, p => dist (p a) (p b) + pathLen dist (b :: rest) p

lemma pathLen_append_singleton {α : Type*} (dist : α → α → ℝ) (p : ℕ → α) :
    ∀ (l : List ℕ) (h : l ≠ []) (x : ℕ),
      pathLen dist (l ++ [x]) p = pathLen dist l p + dist (p (l.getLast h)) (p x)
  | [], h, _ => absurd rfl h
  | [a], _, x => by simp [pathLen]
  | a :: b :: rest, _, x => by
    have hne : b :: rest ≠ [] := List.cons_ne_nil _ _
    have ih := pathLen_append_singleton dist p (b :: rest) hne x
    simp only [List.cons_append, pathLen, List.getLast_cons hne] at ih ⊢
    linarith

lemma pathLen_append {α : Type*} (dist : α → α → ℝ) (p : ℕ → α) :
    ∀ (l₁ l₂ : List ℕ) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []),
      pathLen dist (l₁ ++ l₂) p =
        pathLen dist l₁ p + dist (p (l₁.getLast h₁)) (p (l₂.head h₂)) + pathLen dist l₂ p
  | l₁, [], _, h₂ => absurd rfl h₂
  | l₁, [b], h₁, _ => by
    simp [pathLen_append_singleton dist p l₁ h₁ b, pathLen]
  | l₁, b :: c :: rest, h₁, _ => by
    have hne : c :: rest ≠ [] := List.cons_ne_nil _ _
    have h1b : l₁ ++ [b] ≠ [] := by simp
    have hcat : l₁ ++ b :: c :: rest = (l₁ ++ [b]) ++ (c :: rest) := by simp
    rw [hcat, pathLen_append dist p (l₁ ++ [b]) (c :: rest) h1b hne]
    rw [pathLen_append_singleton dist p l₁ h₁ b]
    have hlast : (l₁ ++ [b]).getLast h1b = b := List.getLast_append_singleton _
    rw [hlast]
    simp only [List.head_cons, pathLen]
    ring

lemma pathLen_reverse {α : Type*} (dist : α → α → ℝ)
    (hsym : ∀ x y, dist x y = dist y x) (p : ℕ → α) :
    ∀ l : List ℕ, pathLen dist l.reverse p = pathLen dist l p
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
    have hne : (b :: rest).reverse ≠ [] := by simp
    have hrev : (a :: b :: rest).reverse = (b :: rest).reverse ++ [a] := by simp
    rw [hrev, pathLen_append_singleton dist p (b :: rest).reverse hne a]
    rw [pathLen_reverse dist hsym p (b :: rest)]
    have hlast : (b :: rest).reverse.getLast hne = b := by simp
    rw [hlast, hsym (p b) (p a)]
    simp only [pathLen]
    ring

/-- A frontier mate vector of width `w`. Values:
  * `-2`: closed / inactive (degree 2, or virtual vertex < 0)
  * `-1`: open endpoint of the anchored path starting at vertex `0`
  * `i` (`0 ≤ i < w`): open endpoint whose path's other endpoint is slot `i`
    (so `m i = i` means an isolated singleton path at slot `i`). -/
abbrev Mate (w : ℕ) := Fin w → ℤ

/-- Initial (and final) state for bandwidth `d`: only slot `d - 1` (vertex `0` at start,
or vertex `N` at end) is open and anchored (`-1`); all earlier slots are `-2`. -/
def initState (d : ℕ) : Mate d :=
  fun i => if i.val + 1 = d then -1 else -2

/-- Extend a `d`-slot mate vector with a newly arriving isolated vertex at slot `d`. -/
def addIsolated {d : ℕ} (m : Mate d) : Mate (d + 1) :=
  fun i => if h : i.val < d then m ⟨i.val, h⟩ else (d : ℤ)

/-- Connect open slot `v : Fin d` to the newly arrived vertex at slot `d`. -/
def connectToNew {d : ℕ} (m : Mate (d + 1)) (v : Fin d) : Option (Mate (d + 1)) :=
  let mv := m v.castSucc
  let md := m (Fin.last d)
  if mv = -2 ∨ md = -2 ∨ mv = (d : ℤ) then
    none
  else if mv = (v.val : ℤ) ∧ md = (d : ℤ) then
    some fun i =>
      if i = v.castSucc then (d : ℤ)
      else if i = Fin.last d then (v.val : ℤ)
      else m i
  else if mv = (v.val : ℤ) then
    some fun i =>
      if i = v.castSucc then md
      else if i = Fin.last d then -2
      else if (i.val : ℤ) = md then (v.val : ℤ)
      else m i
  else if md = (d : ℤ) then
    some fun i =>
      if i = Fin.last d then mv
      else if i = v.castSucc then -2
      else if (i.val : ℤ) = mv then (d : ℤ)
      else m i
  else if mv = -1 ∧ md = -1 then
    none
  else
    some fun i =>
      if i = v.castSucc ∨ i = Fin.last d then -2
      else if (i.val : ℤ) = mv then md
      else if (i.val : ℤ) = md then mv
      else m i

/-- Shift the frontier window right by 1, requiring slot `0` to be closed (`-2`). -/
def shiftWindow {d : ℕ} (m : Mate (d + 1)) : Option (Mate d) :=
  if m ⟨0, Nat.succ_pos d⟩ = -2 then
    some fun i =>
      let val := m i.succ
      if val ≥ 0 then val - 1 else val
  else
    none

/-- One step of the bandwidth-`d` frontier automaton when connecting the new vertex
to the list `chosen` of previous frontier vertices. -/
def stepState {d : ℕ} (st : Mate d) (chosen : List (Fin d)) : Option (Mate d) := do
  let m ← chosen.foldlM connectToNew (addIsolated st)
  shiftWindow m

/-- A linear forest of paths covering `{0, ..., k}`, where `anchor` starts at `0`
and `free` is a list of additional vertex-disjoint non-empty paths. -/
structure LinearForest (k : ℕ) where
  anchor : List ℕ
  free : List (List ℕ)
  anchor_ne : anchor ≠ []
  anchor_head : anchor.head anchor_ne = 0
  free_ne : ∀ p ∈ free, p ≠ []
  cover : (anchor ++ free.flatten).Perm (List.range (k + 1))

/-- Global vertex index corresponding to slot `i : Fin w` when the rightmost slot
`w - 1` corresponds to global vertex `k` (represented in `ℤ`, possibly `< 0` for
virtual pre-start slots). -/
def slotGlobal (w k : ℕ) (i : Fin w) : ℤ :=
  (k : ℤ) + 1 - (w : ℤ) + (i.val : ℤ)

/-- Total Euclidean length of all paths in a linear forest. -/
def LinearForest.totalLen {α : Type*} {k : ℕ} (dist : α → α → ℝ) (p : ℕ → α)
    (F : LinearForest k) : ℝ :=
  pathLen dist F.anchor p + (F.free.map fun l => pathLen dist l p).sum

/-- A mate vector `m : Mate w` accurately summarizes the endpoints of linear forest `F`
at right-edge `k`. -/
structure Matches {w k : ℕ} (m : Mate w) (F : LinearForest k) : Prop where
  anchor_end : ∃ i : Fin w, m i = -1 ∧ slotGlobal w k i = (F.anchor.getLast F.anchor_ne : ℤ)
  anchor_unique : ∀ i : Fin w, m i = -1 → slotGlobal w k i = (F.anchor.getLast F.anchor_ne : ℤ)
  free_ends : ∀ l ∈ F.free, ∃ (hl : l ≠ []) (i j : Fin w),
    slotGlobal w k i = (l.head hl : ℤ) ∧
    slotGlobal w k j = (l.getLast hl : ℤ) ∧
    m i = (j.val : ℤ) ∧ m j = (i.val : ℤ)
  mate_valid : ∀ i : Fin w,
    m i = -2 ∨ m i = -1 ∨
    ∃ j : Fin w, m i = (j.val : ℤ) ∧ m j = (i.val : ℤ) ∧
      ∃ l ∈ F.free, ∃ hl : l ≠ [],
        (slotGlobal w k i = (l.head hl : ℤ) ∧ slotGlobal w k j = (l.getLast hl : ℤ)) ∨
        (slotGlobal w k j = (l.head hl : ℤ) ∧ slotGlobal w k i = (l.getLast hl : ℤ))

lemma slotGlobal_injective (w k : ℕ) : Function.Injective (slotGlobal w k) := by
  intro i j h
  unfold slotGlobal at h
  exact Fin.ext (by omega)

lemma slotGlobal_castSucc (d k : ℕ) (i : Fin d) :
    slotGlobal (d + 1) (k + 1) i.castSucc = slotGlobal d k i := by
  unfold slotGlobal; simp

lemma slotGlobal_last (d k : ℕ) :
    slotGlobal (d + 1) (k + 1) (Fin.last d) = ((k + 1 : ℕ) : ℤ) := by
  unfold slotGlobal; simp

lemma slotGlobal_succ (d k : ℕ) (i : Fin d) :
    slotGlobal (d + 1) k i.succ = slotGlobal d k i := by
  unfold slotGlobal; simp; omega

lemma LinearForest.nodup_all {k : ℕ} (F : LinearForest k) :
    (F.anchor ++ F.free.flatten).Nodup :=
  F.cover.nodup_iff.mpr List.nodup_range

lemma LinearForest.mem_le {k : ℕ} (F : LinearForest k) {x : ℕ}
    (hx : x ∈ F.anchor ++ F.free.flatten) : x ≤ k := by
  have h := F.cover.subset hx
  rw [List.mem_range] at h
  omega

/-- Initial linear forest at `k = 0`: just the singleton anchored path `[0]`. -/
def initForest : LinearForest 0 where
  anchor := [0]
  free := []
  anchor_ne := by simp
  anchor_head := rfl
  free_ne := by simp
  cover := by simp

lemma init_matches (d : ℕ) (hd : 0 < d) : Matches (initState d) initForest where
  anchor_end := by
    refine ⟨⟨d - 1, by omega⟩, ?_, ?_⟩
    · simp [initState]; omega
    · unfold slotGlobal initForest; simp; omega
  anchor_unique := by
    intro i hi
    unfold initState at hi
    split_ifs at hi with h
    · unfold slotGlobal initForest; simp; omega
    · omega
  free_ends := by simp [initForest]
  mate_valid := by
    intro i
    unfold initState
    split_ifs with h
    · right; left; rfl
    · left; rfl

/-- When a linear forest at step `N` matches `initState d`, there are no free paths,
so `F.anchor` is a single Hamiltonian path from `0` to `N`. -/
theorem final_matches_hamiltonian {d N : ℕ} (F : LinearForest N)
    (hm : Matches (initState d) F) :
    F.free = [] ∧ F.anchor.Perm (List.range (N + 1)) ∧
    F.anchor.head F.anchor_ne = 0 ∧ F.anchor.getLast F.anchor_ne = N := by
  have hfree : F.free = [] := by
    by_contra hne
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil F.free hne
    obtain ⟨_, i, j, _, _, hmi, _⟩ := hm.free_ends l hl
    unfold initState at hmi
    split_ifs at hmi
  have hperm : F.anchor.Perm (List.range (N + 1)) := by
    simpa [hfree] using F.cover
  have hlast : F.anchor.getLast F.anchor_ne = N := by
    obtain ⟨i, hmi, hsg⟩ := hm.anchor_end
    unfold initState at hmi
    split_ifs at hmi with hi
    · unfold slotGlobal at hsg; omega
    · omega
  exact ⟨hfree, hperm, F.anchor_head, hlast⟩

/-- Adding an isolated vertex `k + 1` to `F` matches `addIsolated m` with zero added length. -/
lemma addIsolated_sound {α : Type*} {d k : ℕ} (dist : α → α → ℝ) (p : ℕ → α)
    {m : Mate d} {F : LinearForest k} (hm : Matches m F) :
    ∃ F' : LinearForest (k + 1),
      Matches (addIsolated m) F' ∧ F'.totalLen dist p = F.totalLen dist p := by
  let F' : LinearForest (k + 1) := {
    anchor := F.anchor
    free := [k + 1] :: F.free
    anchor_ne := F.anchor_ne
    anchor_head := F.anchor_head
    free_ne := by
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · exact F.free_ne l hl
    cover := by
      have h1 : (F.anchor ++ ([k + 1] :: F.free).flatten).Perm ((F.anchor ++ F.free.flatten) ++ [k + 1]) := by
        simp only [List.flatten_cons]
        exact (List.perm_append_comm_assoc _ _ _).trans List.perm_append_comm
      have h2 : ((F.anchor ++ F.free.flatten) ++ [k + 1]).Perm (List.range (k + 1) ++ [k + 1]) :=
        F.cover.append_right [k + 1]
      rw [← List.range_succ] at h2
      exact h1.trans h2
  }
  refine ⟨F', ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨i, hmi, hsg⟩ := hm.anchor_end
      refine ⟨i.castSucc, ?_, ?_⟩
      · simp [addIsolated, i.isLt, hmi]
      · rw [slotGlobal_castSucc]; exact hsg
    · intro i hi
      unfold addIsolated at hi
      split_ifs at hi with hlt
      · have := hm.anchor_unique ⟨i.val, hlt⟩ hi
        have hcast : i = (⟨i.val, hlt⟩ : Fin d).castSucc := Fin.ext rfl
        rw [hcast, slotGlobal_castSucc]; exact this
    · intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · refine ⟨by simp, Fin.last d, Fin.last d, ?_, ?_, ?_, ?_⟩
        · simp [slotGlobal_last]
        · simp [slotGlobal_last]
        · simp [addIsolated]
        · simp [addIsolated]
      · obtain ⟨hlne, i, j, hi, hj, hmi, hmj⟩ := hm.free_ends l hl
        refine ⟨hlne, i.castSucc, j.castSucc, ?_, ?_, ?_, ?_⟩
        · rw [slotGlobal_castSucc]; exact hi
        · rw [slotGlobal_castSucc]; exact hj
        · simp [addIsolated, i.isLt, hmi]
        · simp [addIsolated, j.isLt, hmj]
    · intro i
      unfold addIsolated
      split_ifs with hlt
      · have hmv := hm.mate_valid ⟨i.val, hlt⟩
        rcases hmv with h | h | ⟨j, hmi, hmj, l, hl, hlne, hlr⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · right; right
          refine ⟨j.castSucc, hmi, by simp [j.isLt, hmj], l, List.mem_cons_of_mem _ hl, hlne, ?_⟩
          have hcast : i = (⟨i.val, hlt⟩ : Fin d).castSucc := Fin.ext rfl
          rw [hcast, slotGlobal_castSucc, slotGlobal_castSucc]
          exact hlr
      · right; right
        have hi : i = Fin.last d := Fin.ext (by simp [Fin.last]; omega)
        subst hi
        refine ⟨Fin.last d, by simp, by simp, [k + 1], List.mem_cons_self .., by simp, Or.inl ?_⟩
        simp [slotGlobal_last]
  · simp [F', LinearForest.totalLen, pathLen]

/-- Shifting the window right preserves the matching linear forest when slot `0` is closed. -/
lemma shiftWindow_sound {d k : ℕ} {m : Mate (d + 1)} {m' : Mate d}
    {F : LinearForest k} (hm : Matches m F) (hs : shiftWindow m = some m') :
    Matches m' F := by
  unfold shiftWindow at hs
  split_ifs at hs with h0
  · injection hs with hm'
    subst hm'
    have hne0 : ∀ i : Fin (d + 1), m i ≠ -2 → i.val ≠ 0 := by
      intro i hi hiz
      have : i = ⟨0, Nat.succ_pos d⟩ := Fin.ext hiz
      rw [this] at hi; exact hi h0
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨i, hmi, hsg⟩ := hm.anchor_end
      have hpos : i.val ≠ 0 := hne0 i (by omega)
      refine ⟨⟨i.val - 1, by omega⟩, ?_, ?_⟩
      · have heq : (⟨i.val - 1, by omega⟩ : Fin d).succ = i := Fin.ext (by simp; omega)
        simp [heq, hmi]
      · have heq : (⟨i.val - 1, by omega⟩ : Fin d).succ = i := Fin.ext (by simp; omega)
        rw [← slotGlobal_succ, heq]; exact hsg
    · intro i hi
      dsimp only at hi
      split_ifs at hi with hge
      · have hzero : m i.succ = 0 := by omega
        rcases hm.mate_valid i.succ with h | h | ⟨j, hmi, hmj, _⟩
        · omega
        · omega
        · have hj0 : j = ⟨0, Nat.succ_pos d⟩ := Fin.ext (by
            have : (j.val : ℤ) = 0 := by omega
            exact Int.ofNat.inj this)
          rw [hj0, h0] at hmj
          omega
      · rw [← slotGlobal_succ]
        exact hm.anchor_unique i.succ hi
    · intro l hl
      obtain ⟨hlne, i, j, hsi, hsj, hmi, hmj⟩ := hm.free_ends l hl
      have hipos : i.val ≠ 0 := hne0 i (by omega)
      have hjpos : j.val ≠ 0 := hne0 j (by omega)
      let i' : Fin d := ⟨i.val - 1, by omega⟩
      let j' : Fin d := ⟨j.val - 1, by omega⟩
      have hi' : i'.succ = i := Fin.ext (by simp [i']; omega)
      have hj' : j'.succ = j := Fin.ext (by simp [j']; omega)
      refine ⟨hlne, i', j', ?_, ?_, ?_, ?_⟩
      · rw [← slotGlobal_succ, hi']; exact hsi
      · rw [← slotGlobal_succ, hj']; exact hsj
      · simp only [hi', hmi, Nat.cast_nonneg, ge_iff_le, ↓reduceIte, j']; omega
      · simp only [hj', hmj, Nat.cast_nonneg, ge_iff_le, ↓reduceIte, i']; omega
    · intro i
      have hmv := hm.mate_valid i.succ
      rcases hmv with h | h | ⟨j, hmi, hmj, l, hl, hlne, hlr⟩
      · left; simp [h]
      · right; left; simp [h]
      · right; right
        have hjpos : j.val ≠ 0 := hne0 j (by omega)
        let j' : Fin d := ⟨j.val - 1, by omega⟩
        have hj' : j'.succ = j := Fin.ext (by simp [j']; omega)
        refine ⟨j', ?_, ?_, l, hl, hlne, ?_⟩
        · simp only [hmi, Nat.cast_nonneg, ge_iff_le, ↓reduceIte, j']; omega
        · simp only [hj', hmj, Nat.cast_nonneg, ge_iff_le, ↓reduceIte, Fin.val_succ]; omega
        · rw [← slotGlobal_succ d k i, ← slotGlobal_succ d k j', hj']; exact hlr

/-- Helper: splitting a free path out of `F.free` via a permutation `F.free.Perm (l :: rest)`. -/
lemma perm_extract {α : Type*} {l : α} {L : List α} (hl : l ∈ L) :
    ∃ rest : List α, L.Perm (l :: rest) := by
  induction L with
  | nil => simp at hl
  | cons a t ih =>
    rcases List.mem_cons.mp hl with rfl | ht
    · exact ⟨t, List.Perm.refl _⟩
    · obtain ⟨rest, hperm⟩ := ih ht
      exact ⟨a :: rest, (hperm.cons a).trans (List.Perm.swap l a rest)⟩

/-- Helper: two distinct elements of `L` can both be extracted simultaneously. -/
lemma perm_extract_two {α : Type*} {l₁ l₂ : α} {L : List α}
    (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L) (hne : l₁ ≠ l₂) :
    ∃ rest : List α, L.Perm (l₁ :: l₂ :: rest) := by
  obtain ⟨r₁, hp₁⟩ := perm_extract h₁
  have h₂' : l₂ ∈ l₁ :: r₁ := hp₁.subset h₂
  rcases List.mem_cons.mp h₂' with rfl | h₂r
  · exact absurd rfl hne
  · obtain ⟨r₂, hp₂⟩ := perm_extract h₂r
    exact ⟨r₂, hp₁.trans (hp₂.cons l₁)⟩

lemma perm_flatten {α : Type*} {L₁ L₂ : List (List α)} (h : L₁.Perm L₂) :
    L₁.flatten.Perm L₂.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons x _ ih => exact ih.append_left x
  | swap x y l =>
    simp only [List.flatten_cons]
    exact (List.perm_append_comm_assoc y x l.flatten)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma perm_map_sum {α : Type*} (f : α → ℝ) {L₁ L₂ : List α} (h : L₁.Perm L₂) :
    (L₁.map f).sum = (L₂.map f).sum :=
  (h.map f).sum_eq

lemma LinearForest.free_singleton_of_head_eq_last {k : ℕ} (F : LinearForest k)
    {l : List ℕ} (hl : l ∈ F.free) (hlne : l ≠ []) (heq : l.head hlne = l.getLast hlne) :
    l = [l.head hlne] := by
  have hnodup : l.Nodup := by
    have hall := F.nodup_all
    rw [List.nodup_append] at hall
    obtain ⟨rest, hp⟩ := perm_extract hl
    have hfl := (perm_flatten hp).nodup_iff.mp hall.2.1
    simp only [List.flatten_cons, List.nodup_append] at hfl
    exact hfl.1
  match l, hlne, heq, hnodup with
  | [a], _, _, _ => rfl
  | a :: b :: rest, _, heq, hnd =>
    have hlast_mem : (a :: b :: rest).getLast (List.cons_ne_nil _ _) ∈ b :: rest := by
      rw [List.getLast_cons (List.cons_ne_nil b rest)]
      exact List.getLast_mem (List.cons_ne_nil b rest)
    rw [List.nodup_cons] at hnd
    simp only [List.head_cons] at heq
    rw [← heq] at hlast_mem
    exact absurd hlast_mem hnd.1

lemma LinearForest.free_eq_of_mem_inter {k : ℕ} (F : LinearForest k)
    {l₁ l₂ : List ℕ} (h₁ : l₁ ∈ F.free) (h₂ : l₂ ∈ F.free) {x : ℕ}
    (hx₁ : x ∈ l₁) (hx₂ : x ∈ l₂) : l₁ = l₂ := by
  by_contra hne
  obtain ⟨rest, hp⟩ := perm_extract_two h₁ h₂ hne
  have hall := F.nodup_all
  rw [List.nodup_append] at hall
  have hfl := (perm_flatten hp).nodup_iff.mp hall.2.1
  simp only [List.flatten_cons, List.nodup_append] at hfl
  exact hfl.2.2 x hx₁ x (List.mem_append_left _ hx₂) rfl

lemma LinearForest.disjoint_anchor_free {k : ℕ} (F : LinearForest k)
    {l : List ℕ} (hl : l ∈ F.free) {x : ℕ} (hx₁ : x ∈ F.anchor) (hx₂ : x ∈ l) : False := by
  have hall := F.nodup_all
  rw [List.nodup_append] at hall
  exact hall.2.2 x hx₁ x (List.mem_flatten.mpr ⟨l, hl, hx₂⟩) rfl

/-- Orient a non-empty list so that its head is `x` and its last is `y`. -/
def orientStart (l : List ℕ) (hl : l ≠ []) (x : ℕ) : List ℕ :=
  if l.head hl = x then l else l.reverse

lemma orientStart_ne (l : List ℕ) (hl : l ≠ []) (x : ℕ) : orientStart l hl x ≠ [] := by
  unfold orientStart; split_ifs <;> simp [hl]

lemma orientStart_perm (l : List ℕ) (hl : l ≠ []) (x : ℕ) : (orientStart l hl x).Perm l := by
  unfold orientStart; split_ifs
  · exact List.Perm.refl _
  · exact List.reverse_perm l

lemma orientStart_len {α : Type*} (dist : α → α → ℝ) (hsym : ∀ a b, dist a b = dist b a)
    (p : ℕ → α) (l : List ℕ) (hl : l ≠ []) (x : ℕ) :
    pathLen dist (orientStart l hl x) p = pathLen dist l p := by
  unfold orientStart; split_ifs
  · rfl
  · exact pathLen_reverse dist hsym p l

lemma orientStart_ends (l : List ℕ) (hl : l ≠ []) (x y : ℕ)
    (h : (l.head hl = x ∧ l.getLast hl = y) ∨ (l.head hl = y ∧ l.getLast hl = x)) :
    (orientStart l hl x).head (orientStart_ne l hl x) = x ∧
    (orientStart l hl x).getLast (orientStart_ne l hl x) = y := by
  by_cases hx : l.head hl = x
  · have heq : orientStart l hl x = l := if_pos hx
    simp only [heq]
    rcases h with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hx, h2⟩
    · exact ⟨hx, by rw [h2, ← h1, hx]⟩
  · have heq : orientStart l hl x = l.reverse := if_neg hx
    simp only [heq]
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd h1 hx
    · exact ⟨by rw [List.head_reverse]; exact h2, by rw [List.getLast_reverse]; exact h1⟩

/-- Orient a non-empty list so that its last is `x` and its head is `y`. -/
def orientEnd (l : List ℕ) (hl : l ≠ []) (x : ℕ) : List ℕ :=
  if l.getLast hl = x then l else l.reverse

lemma orientEnd_ne (l : List ℕ) (hl : l ≠ []) (x : ℕ) : orientEnd l hl x ≠ [] := by
  unfold orientEnd; split_ifs <;> simp [hl]

lemma orientEnd_perm (l : List ℕ) (hl : l ≠ []) (x : ℕ) : (orientEnd l hl x).Perm l := by
  unfold orientEnd; split_ifs
  · exact List.Perm.refl _
  · exact List.reverse_perm l

lemma orientEnd_len {α : Type*} (dist : α → α → ℝ) (hsym : ∀ a b, dist a b = dist b a)
    (p : ℕ → α) (l : List ℕ) (hl : l ≠ []) (x : ℕ) :
    pathLen dist (orientEnd l hl x) p = pathLen dist l p := by
  unfold orientEnd; split_ifs
  · rfl
  · exact pathLen_reverse dist hsym p l

lemma orientEnd_ends (l : List ℕ) (hl : l ≠ []) (x y : ℕ)
    (h : (l.head hl = y ∧ l.getLast hl = x) ∨ (l.head hl = x ∧ l.getLast hl = y)) :
    (orientEnd l hl x).head (orientEnd_ne l hl x) = y ∧
    (orientEnd l hl x).getLast (orientEnd_ne l hl x) = x := by
  by_cases hx : l.getLast hl = x
  · have heq : orientEnd l hl x = l := if_pos hx
    simp only [heq]
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact ⟨h1, hx⟩
    · exact ⟨by rw [h1, ← h2, hx], hx⟩
  · have heq : orientEnd l hl x = l.reverse := if_neg hx
    simp only [heq]
    rcases h with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 hx
    · exact ⟨by rw [List.head_reverse]; exact h2, by rw [List.getLast_reverse]; exact h1⟩

lemma slotGlobal_nonneg_of_active {w k : ℕ} {m : Mate w} {F : LinearForest k}
    (hm : Matches m F) {i : Fin w} (hact : m i ≠ -2) :
    0 ≤ slotGlobal w k i := by
  rcases hm.mate_valid i with h | h | ⟨_, _, _, _, _, _, hlr⟩
  · exact absurd h hact
  · rw [hm.anchor_unique i h]; exact Int.natCast_nonneg _
  · rcases hlr with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [h1]; exact Int.natCast_nonneg _
    · rw [h2]; exact Int.natCast_nonneg _

lemma Matches.free_path_at {w k : ℕ} {m : Mate w} {F : LinearForest k}
    (hm : Matches m F) {i : Fin w} (hge : 0 ≤ m i) :
    ∃ (j : Fin w) (l : List ℕ) (_ : l ∈ F.free) (hlne : l ≠ []),
      m i = (j.val : ℤ) ∧ m j = (i.val : ℤ) ∧
      ((slotGlobal w k i = (l.head hlne : ℤ) ∧ slotGlobal w k j = (l.getLast hlne : ℤ)) ∨
       (slotGlobal w k j = (l.head hlne : ℤ) ∧ slotGlobal w k i = (l.getLast hlne : ℤ))) := by
  rcases hm.mate_valid i with h | h | ⟨j, hmi, hmj, l, hl, hlne, hlr⟩
  · omega
  · omega
  · exact ⟨j, l, hl, hlne, hmi, hmj, hlr⟩

lemma LinearForest.other_free_disjoint {w k : ℕ} (F : LinearForest k)
    {l₁ l₂ : List ℕ} (h₁ : l₁ ∈ F.free) (h₂ : l₂ ∈ F.free) (hne : l₁ ≠ l₂)
    {i₁ j₁ i₂ j₂ : Fin w} {hl₁ : l₁ ≠ []} {hl₂ : l₂ ≠ []}
    (h1 : (slotGlobal w k i₁ = (l₁.head hl₁ : ℤ) ∧ slotGlobal w k j₁ = (l₁.getLast hl₁ : ℤ)) ∨
          (slotGlobal w k j₁ = (l₁.head hl₁ : ℤ) ∧ slotGlobal w k i₁ = (l₁.getLast hl₁ : ℤ)))
    (h2 : slotGlobal w k i₂ = (l₂.head hl₂ : ℤ) ∧ slotGlobal w k j₂ = (l₂.getLast hl₂ : ℤ)) :
    i₂ ≠ i₁ ∧ i₂ ≠ j₁ ∧ j₂ ≠ i₁ ∧ j₂ ≠ j₁ := by
  have noeq : ∀ a b : Fin w,
      (∃ x ∈ l₁, slotGlobal w k a = (x : ℤ)) →
      (∃ y ∈ l₂, slotGlobal w k b = (y : ℤ)) → b ≠ a := by
    intro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩ hba
    subst hba
    have hxy : x = y := Int.ofNat.inj (ha.symm.trans hb)
    subst hxy
    exact hne (F.free_eq_of_mem_inter h₁ h₂ hx hy)
  have hi1 : ∃ x ∈ l₁, slotGlobal w k i₁ = (x : ℤ) := by
    rcases h1 with ⟨a, _⟩ | ⟨_, b⟩
    · exact ⟨_, List.head_mem hl₁, a⟩
    · exact ⟨_, List.getLast_mem hl₁, b⟩
  have hj1 : ∃ x ∈ l₁, slotGlobal w k j₁ = (x : ℤ) := by
    rcases h1 with ⟨_, b⟩ | ⟨a, _⟩
    · exact ⟨_, List.getLast_mem hl₁, b⟩
    · exact ⟨_, List.head_mem hl₁, a⟩
  have hi2 : ∃ y ∈ l₂, slotGlobal w k i₂ = (y : ℤ) := ⟨_, List.head_mem hl₂, h2.1⟩
  have hj2 : ∃ y ∈ l₂, slotGlobal w k j₂ = (y : ℤ) := ⟨_, List.getLast_mem hl₂, h2.2⟩
  exact ⟨noeq i₁ i₂ hi1 hi2, noeq j₁ i₂ hj1 hi2, noeq i₁ j₂ hi1 hj2, noeq j₁ j₂ hj1 hj2⟩

end BHHBounds.Upper
