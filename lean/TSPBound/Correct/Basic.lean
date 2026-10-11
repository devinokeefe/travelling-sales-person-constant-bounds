/-
General lemmas: sums, minima, orders, tuples, tables.
-/
import TSPBound.Impl.CellSum

namespace Correct
open Spec Impl

/-! ## Sums -/

theorem sum_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    Spec.sum n f = Spec.sum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Spec.sum]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sum_succ' (n : Nat) (f : Nat → Nat) :
    Spec.sum (n + 1) f = f 0 + Spec.sum n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [Spec.sum]
  | succ n ih =>
    rw [Spec.sum, ih]
    simp only [Spec.sum]
    omega

theorem sum_zero (n : Nat) : Spec.sum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Spec.sum, ih]

theorem sum_add (n : Nat) (f g : Nat → Nat) :
    Spec.sum n (fun i => f i + g i) = Spec.sum n f + Spec.sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Spec.sum, ih]; omega

theorem sum_mul_const (n : Nat) (f : Nat → Nat) (c : Nat) :
    Spec.sum n (fun i => f i * c) = Spec.sum n f * c := by
  induction n with
  | zero => simp [Spec.sum]
  | succ n ih => simp only [Spec.sum, ih, Nat.add_mul]

theorem sum_comm (n k : Nat) (f : Nat → Nat → Nat) :
    Spec.sum n (fun i => Spec.sum k (fun j => f i j)) = Spec.sum k (fun j => Spec.sum n (fun i => f i j)) := by
  induction n with
  | zero => simp [Spec.sum, sum_zero]
  | succ n ih => simp only [Spec.sum, ih, sum_add]

theorem sum_eq_list (n : Nat) (f : Nat → Nat) : Spec.sum n f = ((List.range n).map f).sum := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Spec.sum, ih, List.range_succ]

theorem sumLoop_eq (f : Nat → Nat) (n lo acc : Nat) :
    sumLoop f n lo acc = acc + Spec.sum n (fun i => f (lo + i)) := by
  induction n generalizing lo acc with
  | zero => simp [sumLoop, Spec.sum]
  | succ n ih =>
    rw [sumLoop, ih, sum_succ']
    have : (fun i => f (lo + 1 + i)) = (fun i => f (lo + (i + 1))) := by
      funext i; congr 1; omega
    rw [this]; simp; omega

/-- A sum in which one index at most contributes. -/
theorem sum_single (n : Nat) (j : Nat) (f : Nat → Nat) :
    Spec.sum n (fun i => if i = j then f i else 0) = if j < n then f j else 0 := by
  induction n with
  | zero => simp [Spec.sum]
  | succ n ih =>
    simp only [Spec.sum, ih]
    by_cases h1 : j < n
    · have : n ≠ j := by omega
      simp [h1, this, Nat.lt_succ_of_lt h1]
    · by_cases h2 : n = j
      · subst h2; simp
      · have : ¬ j < n + 1 := by omega
        simp [h1, h2, this]

/-- A sum over an interval, written as a sum with a condition. -/
theorem sum_interval (n lo cnt : Nat) (h : lo + cnt ≤ n) (f : Nat → Nat) :
    Spec.sum n (fun i => if lo ≤ i ∧ i < lo + cnt then f i else 0) = Spec.sum cnt (fun i => f (lo + i)) := by
  induction n generalizing cnt with
  | zero =>
    have : cnt = 0 := by omega
    subst this; rfl
  | succ n ih =>
    simp only [Spec.sum]
    by_cases hlast : lo + cnt = n + 1
    · cases cnt with
      | zero =>
        have h0 : ∀ i, (if lo ≤ i ∧ i < lo + 0 then f i else 0) = 0 := by
          intro i
          have : ¬ (lo ≤ i ∧ i < lo + 0) := by omega
          simp only [this, if_false]
        simp only [h0, sum_zero, Spec.sum]
      | succ c =>
        have hn : lo + c = n := by omega
        have h0 : Spec.sum n (fun i => if lo ≤ i ∧ i < lo + (c + 1) then f i else 0)
            = Spec.sum n (fun i => if lo ≤ i ∧ i < lo + c then f i else 0) := by
          apply sum_congr; intro i hi
          have : (i < lo + (c + 1)) ↔ (i < lo + c) := by omega
          simp [this]
        rw [h0, ih c (by omega)]
        have h1 : lo ≤ n ∧ n < lo + (c + 1) := by omega
        simp only [h1, and_self, if_true, Spec.sum, hn]
    · have h1 : ¬ (lo ≤ n ∧ n < lo + cnt) := by omega
      simp only [h1, if_false, Nat.add_zero]
      exact ih cnt (by omega)

/-! ## Minima -/

theorem minOf_cons (x : Nat) (l : List Nat) (h : l ≠ []) : minOf (x :: l) = min x (minOf l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons y l => rfl

theorem minOf_spec : ∀ (l : List Nat), l ≠ [] → minOf l ∈ l ∧ ∀ x ∈ l, minOf l ≤ x
  | [], h => absurd rfl h
  | [x], _ => by simp [minOf]
  | x :: y :: l, _ => by
    have ih := minOf_spec (y :: l) (by simp)
    rw [minOf_cons x (y :: l) (by simp)]
    constructor
    · rcases Nat.le_total x (minOf (y :: l)) with h | h
      · rw [Nat.min_eq_left h]; simp
      · rw [Nat.min_eq_right h]; exact List.mem_cons_of_mem _ ih.1
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (ih.2 z hz)

theorem minOf_eq {l : List Nat} {x : Nat} (hx : x ∈ l) (hle : ∀ y ∈ l, x ≤ y) : minOf l = x := by
  have := minOf_spec l (List.ne_nil_of_mem hx)
  exact Nat.le_antisymm (this.2 x hx) (hle _ this.1)

/-! ## Orders -/

theorem perm_of_mem_inserts {x : Nat} {l π : List Nat} (h : π ∈ inserts x l) : π.Perm (x :: l) := by
  induction l generalizing π with
  | nil => simp [inserts] at h; subst h; exact List.Perm.refl _
  | cons y l ih =>
    simp only [inserts, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨σ, hσ, rfl⟩
    · exact List.Perm.refl _
    · exact ((ih hσ).cons y).trans (List.Perm.swap x y l)

theorem mem_inserts_append (x : Nat) (l₁ l₂ : List Nat) : l₁ ++ x :: l₂ ∈ inserts x (l₁ ++ l₂) := by
  induction l₁ with
  | nil => cases l₂ <;> simp [inserts]
  | cons y l₁ ih =>
    simp only [List.cons_append, inserts, List.mem_cons, List.mem_map]
    exact Or.inr ⟨_, ih, rfl⟩

/-- `orders l` consists of the rearrangements of `l`. -/
theorem mem_orders {l π : List Nat} : π ∈ orders l ↔ π.Perm l := by
  induction l generalizing π with
  | nil => simp [orders]
  | cons x l ih =>
    simp only [orders, List.mem_flatMap]
    constructor
    · rintro ⟨σ, hσ, hπ⟩
      exact (perm_of_mem_inserts hπ).trans ((ih.mp hσ).cons x)
    · intro h
      have hx : x ∈ π := h.symm.subset (List.mem_cons_self)
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
      refine ⟨l₁ ++ l₂, ih.mpr ?_, mem_inserts_append x l₁ l₂⟩
      exact (List.perm_middle.symm.trans h).cons_inv

/-! ## Tuples -/

/-- `tuples len n` consists of the lists of length `len` with entries below `n`. -/
theorem mem_tuples {len n : Nat} {a : List Nat} :
    a ∈ tuples len n ↔ a.length = len ∧ ∀ x ∈ a, x < n := by
  induction len generalizing a with
  | zero =>
    simp only [tuples, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, _⟩; exact List.eq_nil_of_length_eq_zero h
  | succ len ih =>
    simp only [tuples, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨x, hx, t, ht, rfl⟩
      have := ih.mp ht
      refine ⟨by simp [this.1], ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact this.2 y hy
    · rintro ⟨hlen, hall⟩
      cases a with
      | nil => simp at hlen
      | cons x t =>
        refine ⟨x, hall x (List.mem_cons_self), t, ih.mpr ⟨by simpa using hlen, ?_⟩, rfl⟩
        intro y hy
        exact hall y (List.mem_cons_of_mem _ hy)

/-! ## Tables -/

theorem size_tab {α : Type} (n : Nat) (f : Nat → α) : (tab n f).size = n := by
  simp [tab]

theorem getElem_tab {α : Type} (n : Nat) (f : Nat → α) (i : Nat) (h : i < (tab n f).size) :
    (tab n f)[i] = f i := by
  simp [tab]

/-- Every entry of `t` is the value of `f` at its index. -/
def IsTab (t : Array Nat) (f : Nat → Nat) : Prop := ∀ i (h : i < t.size), t[i] = f i

theorem isTab_tab (n : Nat) (f : Nat → Nat) : IsTab (tab n f) f :=
  fun i h => getElem_tab n f i h

theorem isTab_empty (f : Nat → Nat) : IsTab #[] f := by
  intro i h; simp at h

theorem look_eq {t : Array Nat} {f : Nat → Nat} (h : IsTab t f) (i : Nat) : look t f i = f i := by
  unfold look
  split
  · exact h i _
  · rfl

theorem look_fun {t : Array Nat} {f : Nat → Nat} (h : IsTab t f) : look t f = f :=
  funext (look_eq h)

/-- A table of tables of `f`. -/
def IsTab2 (t : Array (Array Nat)) (f : Nat → Nat → Nat) : Prop :=
  ∀ i (h : i < t.size), IsTab t[i] (f i)

theorem look2_eq {t : Array (Array Nat)} {f : Nat → Nat → Nat} (h : IsTab2 t f) (i j : Nat) :
    look2 t f i j = f i j := by
  unfold look2
  split
  · exact look_eq (h i _) j
  · rfl

theorem isTab2_tab (n : Nat) (len : Nat → Nat) (f : Nat → Nat → Nat) :
    IsTab2 (tab n (fun i => tab (len i) (f i))) f := by
  intro i h
  rw [getElem_tab]
  exact isTab_tab _ _

end Correct
