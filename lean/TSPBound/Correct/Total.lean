/-
The total: the recursion of Section 8, the list of cell sums by index, and the same on several threads.
Everything here is under the hypothesis `RowsOK p rows` on the table; `Correct/Table.lean` removes it.
-/
import TSPBound.Correct.CellSum

namespace Correct
open Spec Impl

theorem isTab_massArr (p : Params) : IsTab (massArr p) (P p) := isTab_tab _ _

theorem Arec_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows) (g : List Nat) :
    Arec p rows (mkPlan p.k p.n) (massArr p) g = A p g := by
  generalize hd : p.k - g.length = d
  induction d generalizing g with
  | zero =>
    have hk : p.k ≤ g.length := by omega
    rw [Arec, A, if_pos hk, if_pos hk]
    exact cellSum_eq p rows h g
  | succ d ih =>
    have hk : ¬ p.k ≤ g.length := by omega
    rw [Arec, A, if_neg hk, if_neg hk]
    congr 1
    apply sum_congr
    intro c _
    rw [look_eq (isTab_massArr p), ih (g ++ [c]) (by simp; omega)]

theorem Aof_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows) (g : List Nat) :
    Aof p rows g = A p g := Arec_eq p rows h g

/-! ## Gap tuples and their indices -/

/-- The index `g_1 + g_2·m + … + g_j·m^{j-1}` of a gap tuple. -/
def idx (mm : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => x + mm * idx mm l

theorem idx_append (mm : Nat) (g : List Nat) (c : Nat) :
    idx mm (g ++ [c]) = idx mm g + c * mm ^ g.length := by
  induction g with
  | nil => simp [idx]
  | cons x l ih =>
    simp only [List.cons_append, idx, ih, List.length_cons, Nat.pow_succ, Nat.mul_add]
    rw [Nat.add_assoc, Nat.mul_left_comm, Nat.mul_comm mm (mm ^ l.length)]

theorem idx_lt (mm : Nat) (g : List Nat) (h : ∀ x ∈ g, x < mm) : idx mm g < mm ^ g.length := by
  induction g with
  | nil => simp [idx]
  | cons x l ih =>
    have hx := h x (by simp)
    have hl := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [idx, List.length_cons, Nat.pow_succ]
    have h1 : mm * (idx mm l + 1) ≤ mm * mm ^ l.length := Nat.mul_le_mul_left mm hl
    rw [Nat.mul_add, Nat.mul_one] at h1
    rw [Nat.mul_comm (mm ^ l.length) mm]
    omega

theorem idx_digit (mm : Nat) (g : List Nat) (h : ∀ x ∈ g, x < mm) (i : Nat) (hi : i < g.length) :
    idx mm g / mm ^ i % mm = g[i] := by
  induction g generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    have hx := h x (by simp)
    have hpos : 0 < mm := by omega
    cases i with
    | zero =>
      simp only [idx, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hx
    | succ i =>
      simp only [idx, List.getElem_cons_succ]
      rw [Nat.pow_succ, Nat.mul_comm (mm ^ i) mm, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hx, Nat.zero_add]
      exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) i (by simpa using hi)

theorem gapOfIndex_idx (p : Params) (g : List Nat) (hlen : g.length = p.k) (h : ∀ x ∈ g, x < m p) :
    gapOfIndex p (idx (m p) g) = g := by
  apply List.ext_getElem
  · simp [gapOfIndex, hlen]
  · intro i h1 h2
    simp only [gapOfIndex, List.getElem_map, List.getElem_range]
    exact idx_digit (m p) g h i h2

/-! ## The total from the list of cell sums -/

theorem totalRec_eq (p : Params) (rest : Nat) (g : List Nat) (hlen : g.length + rest = p.k)
    (h : ∀ x ∈ g, x < m p) :
    totalRec p (massArr p) (cellSums p).toArray rest g.length (idx (m p) g) = A p g := by
  induction rest generalizing g with
  | zero =>
    have hk : p.k ≤ g.length := by omega
    rw [A, if_pos hk]
    simp only [totalRec]
    have hlt : idx (m p) g < (m p) ^ p.k := by
      have := idx_lt (m p) g h
      rwa [show g.length = p.k by omega] at this
    have hget : (cellSums p).toArray.getD (idx (m p) g) 0 = S p (gapOfIndex p (idx (m p) g)) := by
      simp [cellSums, hlt]
    rw [hget, gapOfIndex_idx p g (by omega) h]
  | succ rest ih =>
    have hk : ¬ p.k ≤ g.length := by omega
    rw [A, if_neg hk]
    simp only [totalRec]
    congr 1
    apply sum_congr
    intro c hc
    rw [look_eq (isTab_massArr p)]
    have hmem : ∀ x ∈ g ++ [c], x < m p := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h x hx
      · exact hc
    have := ih (g ++ [c]) (by simp; omega) hmem
    rw [idx_append, List.length_append, List.length_singleton] at this
    rw [this]

/-- The total of the recipe from the list of the cell sums of the recipe. -/
theorem totalOfSums_eq (p : Params) : totalOfSums p (cellSums p).toArray = Spec.total p :=
  totalRec_eq p p.k [] (by simp) (by simp)

theorem sumsRange_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (lo cnt : Nat) :
    sumsRange p rows lo cnt = (List.range' lo cnt).map (fun index => S p (gapOfIndex p index)) := by
  unfold sumsRange
  apply List.map_congr_left
  intro i _
  exact cellSum_eq p rows h _

theorem sumsRange_all (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows) :
    sumsRange p rows 0 ((m p) ^ p.k) = cellSums p := by
  rw [sumsRange_eq p rows h, cellSums, List.range_eq_range']

/-! ## Several threads -/

theorem sumsRange_append (p : Params) (rows : List (List Nat × Array Nat)) (lo a b : Nat) :
    sumsRange p rows lo a ++ sumsRange p rows (lo + a) b = sumsRange p rows lo (a + b) := by
  unfold sumsRange
  rw [← List.map_append, List.range'_append_1]

theorem task_get_spawn {α : Type} (f : Unit → α) (prio : Task.Priority) :
    (Task.spawn f prio).get = f () := rfl

theorem sumsWave_eq (p : Params) (rows : List (List Nat × Array Nat)) (threads chunk lo cnt : Nat)
    (acc : List Nat) :
    sumsWave p rows threads chunk lo cnt acc = acc ++ sumsRange p rows lo (min cnt (threads * chunk)) := by
  unfold sumsWave
  induction threads with
  | zero => simp [sumsRange]
  | succ T ih =>
    simp only [] at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [List.append_assoc, task_get_spawn, sumsRange_append]
    congr 2
    rw [Nat.succ_mul]; omega

theorem sumsWaves_eq (p : Params) (rows : List (List Nat × Array Nat)) (threads chunk fuel lo cnt : Nat)
    (acc : List Nat) :
    sumsWaves p rows threads chunk fuel lo cnt acc = acc ++ sumsRange p rows lo cnt := by
  induction fuel generalizing lo cnt acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [sumsWaves]
    split
    · rename_i h0; subst h0; simp [sumsRange]
    · rw [ih, sumsWave_eq, List.append_assoc, sumsRange_append]
      congr 2
      omega

theorem total_eq_of (p : Params) (h : RowsOK p (tableRows p 1)) : Impl.total p = Spec.total p :=
  Aof_eq p _ h []

theorem totalPar_eq_of (p : Params) (threads : Nat) (h : RowsOK p (tableRows p 1)) :
    totalPar p threads = Spec.total p := by
  unfold totalPar
  simp only []
  rw [sumsWaves_eq, List.nil_append, sumsRange_all p _ h]
  exact totalOfSums_eq p

end Correct
