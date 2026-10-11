/-
The cell sums: `Impl.cellSum` equals `Spec.S` (`cellSum_eq`).

Two things are shown: the plan, run on the edges of a block, gives the cost of `Spec.cost` for every
pair of heights of the end points; and summing over the heights of the interior points first and over
those of the end points inside is the sum over all height tuples.
-/
import TSPBound.Correct.Run

namespace Correct
open Spec Impl

/-! ## Sums over tuples -/

theorem sum_flatMap_range {α : Type} (cnt : Nat) (L : Nat → List α) (f : α → Nat) :
    (((List.range cnt).flatMap L).map f).sum = ∑ a < cnt, ((L a).map f).sum := by
  induction cnt with
  | zero => rfl
  | succ c ih => simp [List.range_succ, Spec.sum, ih]

/-- Splitting off the first entry of a tuple. -/
theorem sum_tuples_head (len n : Nat) (F : List Nat → Nat) :
    ((tuples (len + 1) n).map F).sum = ∑ a < n, ((tuples len n).map (fun t => F (a :: t))).sum := by
  simp only [tuples]
  rw [sum_flatMap_range]
  apply sum_congr
  intro a _
  rw [List.map_map]
  rfl

theorem sum_list_comm (n : Nat) (l : List (List Nat)) (G : Nat → List Nat → Nat) :
    ∑ a < n, (l.map (G a)).sum = (l.map (fun c => ∑ a < n, G a c)).sum := by
  induction l with
  | nil => simp [sum_zero]
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sum_add, ih]

/-- Splitting off the last entry of a tuple. -/
theorem sum_tuples_last (len n : Nat) (F : List Nat → Nat) :
    ((tuples (len + 1) n).map F).sum = ((tuples len n).map (fun c => ∑ b < n, F (c ++ [b]))).sum := by
  induction len generalizing F with
  | zero =>
    rw [sum_tuples_head]
    simp [tuples]
  | succ len ih =>
    rw [sum_tuples_head, sum_tuples_head]
    apply sum_congr
    intro a _
    rw [ih]
    rfl

/-- The sum over all tuples, with the two end entries summed inside. -/
theorem sum_tuples_ends (len n : Nat) (F : List Nat → Nat) :
    ((tuples (len + 2) n).map F).sum
      = ((tuples len n).map (fun c => ∑ a < n, ∑ b < n, F (a :: (c ++ [b])))).sum := by
  rw [sum_tuples_head]
  have h : ∀ a, ((tuples (len + 1) n).map (fun t => F (a :: t))).sum
      = ((tuples len n).map (fun c => ∑ b < n, F (a :: (c ++ [b])))).sum := by
    intro a; rw [sum_tuples_last]
  rw [sum_congr (fun a _ => h a)]
  exact sum_list_comm n (tuples len n) (fun a c => ∑ b < n, F (a :: (c ++ [b])))

theorem sumTuples_eq (n len : Nat) (f : List Nat → Nat) :
    sumTuples n len f = ((tuples len n).map f).sum := by
  induction len generalizing f with
  | zero => simp [sumTuples, tuples]
  | succ len ih =>
    rw [sumTuples, sumLoop_eq, sum_tuples_head, Nat.zero_add]
    apply sum_congr
    intro a _
    rw [Nat.zero_add, ih]

/-! ## The edges of a block -/

/-- Every stored row belongs to its key. -/
def RowsOK (p : Params) (rows : List (List Nat × Array Nat)) : Prop :=
  ∀ e ∈ rows, IsTab e.2 (Tab p e.1)

theorem isTab_rowOf (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (κ : List Nat) : IsTab (rowOf p rows κ) (Tab p κ) := by
  unfold rowOf
  cases hf : findRow rows κ with
  | none => exact isTab_tab _ _
  | some r =>
    simp only [findRow, Option.map_eq_some_iff] at hf
    obtain ⟨e, he, rfl⟩ := hf
    have hmem := List.mem_of_find?_eq_some he
    have hp := List.find?_some he
    have hκ : e.1 = κ := by simpa using hp
    rw [← hκ]; exact h e hmem

theorem getD_tab {α : Type} (n : Nat) (f : Nat → α) (i : Nat) (d : α) (h : i < n) :
    (tab n f).getD i d = f i := by
  simp [tab, h]

theorem get4_eq (t : Array (Array (Array (Array Nat)))) (i j x y : Nat) :
    get4 t i j x y = ((((t.getD i #[]).getD j #[]).getD x #[]).getD y 0) := by
  unfold get4
  by_cases h1 : i < t.size
  · by_cases h2 : j < t[i].size
    · by_cases h3 : x < t[i][j].size <;> simp [h1, h2, h3]
    · simp [h1, h2]
  · simp [h1]

theorem get4_edgeTab (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (g : List Nat) (i j x y : Nat) (hi : i ≤ p.k) (hj : j ≤ p.k) (hij : i ≠ j)
    (hx : x < p.n) (hy : y < p.n) :
    get4 (edgeTab p rows g) i j x y = Ef p g i j x y := by
  rw [get4_eq]
  unfold edgeTab
  rw [getD_tab _ _ _ _ (by omega), getD_tab _ _ _ _ (by omega), if_neg hij,
    getD_tab _ _ _ _ hx, getD_tab _ _ _ _ hy, look_eq (isTab_rowOf p rows h _)]
  rfl

theorem Ef_symm (p : Params) (g : List Nat) (i j x y : Nat) : Ef p g i j x y = Ef p g j i y x := by
  unfold Ef absDiff
  rw [Nat.min_comm, Nat.max_comm, Nat.add_comm]

/-- The height of the interior point `u` in the list `c` of the heights of the points `1, …, k - 1`. -/
def hgt (c : List Nat) (u : Nat) : Nat := c.getD (u - 1) 0

/-- The edges of a block with interior heights `c`. -/
def einOf (p : Params) (g c : List Nat) (u v : Nat) : Nat := Ef p g u v (hgt c u) (hgt c v)
def stOf (p : Params) (g c : List Nat) (a u : Nat) : Nat := Ef p g 0 u a (hgt c u)
def enOf (p : Params) (g c : List Nat) (b v : Nat) : Nat := Ef p g v p.k (hgt c v) b

theorem hgt_lt {k n : Nat} {c : List Nat} (hc : c ∈ tuples (k - 1) n) {u : Nat} (h1 : 1 ≤ u) (h2 : u < k) :
    hgt c u < n := by
  obtain ⟨hlen, hall⟩ := mem_tuples.mp hc
  have hlt : u - 1 < c.length := by omega
  unfold hgt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact hall _ (List.getElem_mem hlt)

theorem inputVal_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (g c : List Nat) (hc : c ∈ tuples (p.k - 1) p.n) (s : Slot) (hs : s.inRange p.k p.n = true) :
    inputVal (edgeTab p rows g) c.toArray p.k s
      = inputValA (einOf p g c) (stOf p g c) (enOf p g c) s := by
  have hget : ∀ i, c.toArray.getD i 0 = c.getD i 0 := by
    intro i; simp [List.getD_eq_getElem?_getD]
  cases s with
  | zero => rfl
  | ein u v =>
    simp only [Slot.inRange, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hs
    obtain ⟨⟨⟨⟨hu1, hu2⟩, hv1⟩, hv2⟩, huv⟩ := hs
    simp only [inputVal, inputValA, einOf, hget]
    exact get4_edgeTab p rows h g u v _ _ (by omega) (by omega) huv (hgt_lt hc hu1 hu2) (hgt_lt hc hv1 hv2)
  | st a u =>
    simp only [Slot.inRange, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨ha, hu1⟩, hu2⟩ := hs
    simp only [inputVal, inputValA, stOf, hget]
    exact get4_edgeTab p rows h g 0 u _ _ (by omega) (by omega) (by omega) ha (hgt_lt hc hu1 hu2)
  | en b v =>
    simp only [Slot.inRange, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨hb, hv1⟩, hv2⟩ := hs
    simp only [inputVal, inputValA, enOf, hget]
    exact get4_edgeTab p rows h g v p.k _ _ (by omega) (by omega) (by omega) (hgt_lt hc hv1 hv2) hb
  | A S u => simp [Slot.inRange] at hs
  | H u v => simp [Slot.inRange] at hs
  | L a v => simp [Slot.inRange] at hs
  | C a b => simp [Slot.inRange] at hs

theorem pushInputs_eq (eT : Array (Array (Array (Array Nat)))) (ca : Array Nat) (k : Nat)
    (ins : List Slot) (acc : Array Nat) :
    pushInputs eT ca k ins acc = acc ++ (ins.map (inputVal eT ca k)).toArray := by
  induction ins generalizing acc with
  | nil => simp [pushInputs]
  | cons s rest ih => simp [pushInputs, ih]

/-! ## The cost of a block -/

theorem pathLen_congr {E E' : Nat → Nat → Nat} :
    ∀ (l : List Nat), (∀ x ∈ l, ∀ y ∈ l, E x y = E' x y) → pathLen E l = pathLen E' l
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: l, h => by
    simp only [pathLen]
    rw [h x (by simp) y (by simp), pathLen_congr (y :: l) (fun a ha b hb =>
      h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))]

/-- The length of the path `0, π, k` in terms of its first and last edges. -/
theorem pathLen_ends (E : Nat → Nat → Nat) (π : List Nat) (hne : π ≠ []) (k : Nat) :
    pathLen E (0 :: π ++ [k]) = E 0 (π.headD 0) + pathLen E π + E (π.getLastD 0) k := by
  obtain ⟨w, hw⟩ : ∃ w, π.getLast? = some w := by
    cases h : π.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some w => exact ⟨w, rfl⟩
  obtain ⟨τ, rfl⟩ := List.getLast?_eq_some_iff.mp hw
  have h1 : 0 :: (τ ++ [w]) ++ [k] = (0 :: τ) ++ w :: [k] := by simp
  rw [h1, pathLen_append]
  have h2 : pathLen E ((0 :: τ) ++ [w]) = E 0 ((τ ++ [w]).headD 0) + pathLen E (τ ++ [w]) := by
    cases τ with
    | nil => simp [pathLen]
    | cons u τ => simp [pathLen]
  rw [h2]
  simp [pathLen]

theorem getD_full_zero (a b : Nat) (c : List Nat) : (a :: (c ++ [b])).getD 0 0 = a := rfl

theorem getD_full_mid (a b : Nat) (c : List Nat) (u : Nat) (h1 : 1 ≤ u) (h2 : u - 1 < c.length) :
    (a :: (c ++ [b])).getD u 0 = hgt c u := by
  obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
  simp only [List.getD_cons_succ, hgt, Nat.add_sub_cancel]
  simp only [Nat.add_sub_cancel] at h2
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h2]

theorem getD_full_last (a b : Nat) (c : List Nat) : (a :: (c ++ [b])).getD (c.length + 1) 0 = b := by
  simp [List.getD_eq_getElem?_getD]

/-- The cost found by the plan is the cost of the recipe. -/
theorem costC_eq_cost (p : Params) (g c : List Nat) (hk : 2 ≤ p.k) (hc : c ∈ tuples (p.k - 1) p.n)
    (a b : Nat) :
    costC p.k (einOf p g c) (stOf p g c) (enOf p g c) a b = cost p g (a :: (c ++ [b])) := by
  obtain ⟨hlen, _⟩ := mem_tuples.mp hc
  unfold costC cost interior
  congr 1
  apply List.map_congr_left
  intro π hπ
  have hperm : π.Perm (List.range' 1 (p.k - 1)) := mem_orders.mp hπ
  have hmem : ∀ x ∈ π, 1 ≤ x ∧ x < p.k := by
    intro x hx
    have := hperm.subset hx
    simp [List.mem_range'_1] at this
    omega
  have hne : π ≠ [] := by
    intro h; subst h
    have := hperm.length_eq
    simp at this; omega
  rw [pathLen_ends _ π hne]
  have hhead : π.headD 0 ∈ π := by
    cases π with
    | nil => exact absurd rfl hne
    | cons u π => simp
  have hlast : π.getLastD 0 ∈ π := by
    cases h : π.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some w =>
      simp only [List.getLastD_eq_getLast?, h, Option.getD_some]
      exact List.mem_of_getLast? h
  -- the three kinds of edges
  have e1 : E p g (a :: (c ++ [b])) 0 (π.headD 0) = stOf p g c a (π.headD 0) := by
    have := hmem _ hhead
    unfold E stOf
    rw [getD_full_zero, getD_full_mid a b c _ this.1 (by omega)]
    rfl
  have e2 : E p g (a :: (c ++ [b])) (π.getLastD 0) p.k = enOf p g c b (π.getLastD 0) := by
    have := hmem _ hlast
    have hk' : p.k = c.length + 1 := by omega
    unfold E enOf
    rw [getD_full_mid a b c _ this.1 (by omega)]
    conv => lhs; rw [hk']
    rw [getD_full_last]
    rw [← hk']
    rfl
  have e3 : pathLen (E p g (a :: (c ++ [b]))) π = pathLen (einOf p g c) π := by
    apply pathLen_congr
    intro x hx y hy
    have hx' := hmem x hx
    have hy' := hmem y hy
    unfold E einOf
    rw [getD_full_mid a b c _ hx'.1 (by omega), getD_full_mid a b c _ hy'.1 (by omega)]
    rfl
  rw [e1, e2, e3]

/-! ## The cell sum -/

theorem configSum_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (hok : (mkPlan p.k p.n).ok = true) (g c : List Nat) (hc : c ∈ tuples (p.k - 1) p.n) :
    configSum (mkPlan p.k p.n) (edgeTab p rows g) p.k c
      = ∑ a < p.n, ∑ b < p.n, cost p g (a :: (c ++ [b])) := by
  have hk : 2 ≤ p.k := by
    simp only [mkPlan, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1
  have hin : ∀ s ∈ inputSlots p.k p.n, s.inRange p.k p.n = true := by
    simp only [mkPlan, Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.1.1.2
  have hinputs : (mkPlan p.k p.n).inputs = inputSlots p.k p.n := rfl
  have hval0 : pushInputs (edgeTab p rows g) c.toArray p.k (mkPlan p.k p.n).inputs
        (Array.mkEmpty (mkPlan p.k p.n).size)
      = ((inputSlots p.k p.n).map (inputValA (einOf p g c) (stOf p g c) (enOf p g c))).toArray := by
    rw [pushInputs_eq, hinputs]
    simp only [Array.mkEmpty_eq, Array.empty_append]
    congr 1
    apply List.map_congr_left
    intro s hs
    exact inputVal_eq p rows h g c hc s (hin s hs)
  unfold configSum
  rw [hval0]
  rw [configSum_abs p.k p.n hok (einOf p g c) (stOf p g c) (enOf p g c)
    (fun x y => Ef_symm p g x y _ _) _ rfl]
  apply sum_congr; intro a _
  apply sum_congr; intro b _
  exact costC_eq_cost p g c hk hc a b

/-- The cell sum of the implementation is `S_g`. -/
theorem cellSum_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (g : List Nat) : cellSum p rows (mkPlan p.k p.n) g = S p g := by
  unfold cellSum
  split
  · rename_i hok
    have hk : 2 ≤ p.k := by
      simp only [mkPlan, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.1.1.1
    have hk' : p.k + 1 = (p.k - 1) + 2 := by omega
    unfold S
    rw [hk', sum_tuples_ends, sumTuples_eq]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact configSum_eq p rows h hok g c hc
  · rfl

end Correct
