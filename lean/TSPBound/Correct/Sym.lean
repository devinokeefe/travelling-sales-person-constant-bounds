/-
The symmetry of the heights (`cellSumFlip_eq`), and the total in pieces (`AofPar_eq`, `totalFrom_eq`).
-/
import TSPBound.Impl.Sym
import TSPBound.Correct.Table

namespace Correct
open Spec Impl

/-! ## Sums read backwards -/

theorem sum_flip (n : Nat) (f : Nat → Nat) : (∑ a < n, f (n - 1 - a)) = ∑ a < n, f a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ']
    have h : ∀ i, i < n → f (n + 1 - 1 - (i + 1)) = f (n - 1 - i) := by
      intro i hi; congr 1; omega
    rw [sum_congr h, ih]
    simp only [Spec.sum, Nat.add_sub_cancel, Nat.sub_zero]
    omega

theorem sum_append (a b : Nat) (f : Nat → Nat) :
    (∑ i < a + b, f i) = (∑ i < a, f i) + ∑ i < b, f (a + i) := by
  induction b with
  | zero => simp [Spec.sum]
  | succ b ih =>
    rw [← Nat.add_assoc]
    simp only [Spec.sum]
    rw [ih]; omega

theorem sum_sym (h r : Nat) (f : Nat → Nat) (hsym : ∀ x, x < h → f (h + r + (h - 1 - x)) = f x) :
    (∑ i < h + r + h, f i) = 2 * (∑ i < h, f i) + ∑ i < r, f (h + i) := by
  rw [sum_append (h + r) h, sum_append h r, ← sum_flip h (fun i => f (h + r + i)), sum_congr hsym]
  show Spec.sum h f + _ + Spec.sum h f = 2 * Spec.sum h f + _
  omega

theorem sumHalf_eq (n : Nat) (f : Nat → Nat) (hsym : ∀ x, x < n → f (n - 1 - x) = f x) :
    sumHalf n f = ∑ x < n, f x := by
  have hn : n / 2 + n % 2 + n / 2 = n := by omega
  have key := sum_sym (n / 2) (n % 2) f (by
    intro x hx
    have h1 := hsym x (by omega)
    rw [← h1]; congr 1; omega)
  rw [hn] at key
  unfold sumHalf
  rw [sumLoop_eq, key]
  simp only [Nat.zero_add]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · rw [h0]; simp [Spec.sum]
  · rw [h1]; simp [Spec.sum]

/-- The sum over all tuples is unchanged if every entry `x` is replaced by `n - 1 - x`. -/
theorem sum_tuples_flip (len n : Nat) (G : List Nat → Nat) :
    ((tuples len n).map (fun t => G (t.map (fun x => n - 1 - x)))).sum = ((tuples len n).map G).sum := by
  induction len generalizing G with
  | zero => simp [tuples]
  | succ len ih =>
    rw [sum_tuples_head, sum_tuples_head]
    have h : ∀ a, a < n →
        ((tuples len n).map (fun t => G ((a :: t).map (fun x => n - 1 - x)))).sum
          = ((tuples len n).map (fun t => G ((n - 1 - a) :: t))).sum := by
      intro a _
      exact ih (fun t => G ((n - 1 - a) :: t))
    rw [sum_congr h]
    exact sum_flip n (fun a => ((tuples len n).map (fun t => G (a :: t))).sum)

/-! ## The cost under the flip of the heights -/

theorem absDiff_flip (n u v : Nat) (hu : u < n) (hv : v < n) :
    absDiff (n - 1 - u) (n - 1 - v) = absDiff u v := by
  unfold absDiff; omega

theorem getD_lt {n : Nat} {t : List Nat} (ht : ∀ x ∈ t, x < n) {i : Nat} (hi : i < t.length) :
    t.getD i 0 < n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact ht _ (List.getElem_mem hi)

theorem getD_map_flip (n : Nat) (t : List Nat) (i : Nat) (hi : i < t.length) :
    (t.map (fun x => n - 1 - x)).getD i 0 = n - 1 - t.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem E_flip (p : Params) (g t : List Nat) (ht : ∀ x ∈ t, x < p.n) (i j : Nat)
    (hi : i < t.length) (hj : j < t.length) :
    E p g (t.map (fun x => p.n - 1 - x)) i j = E p g t i j := by
  unfold E
  rw [getD_map_flip _ _ _ hi, getD_map_flip _ _ _ hj, absDiff_flip _ _ _ (getD_lt ht hi) (getD_lt ht hj)]

/-- The cost of a height tuple is the cost of the flipped tuple. -/
theorem cost_flip (p : Params) (g t : List Nat) (hlen : t.length = p.k + 1) (ht : ∀ x ∈ t, x < p.n) :
    cost p g (t.map (fun x => p.n - 1 - x)) = cost p g t := by
  unfold cost
  refine congrArg minOf ?_
  apply List.map_congr_left
  intro π hπ
  have hperm : π.Perm (List.range' 1 (p.k - 1)) := mem_orders.mp hπ
  have hb : ∀ z ∈ 0 :: π ++ [p.k], z < t.length := by
    intro z hz
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · omega
    · have := hperm.subset hz
      simp [List.mem_range'_1] at this
      omega
    · omega
  apply pathLen_congr
  intro x hx y hy
  exact E_flip p g t ht x y (hb x hx) (hb y hy)

/-- The sum over the heights of the two end points, for given heights of the interior points. -/
def endSum (p : Params) (g c : List Nat) : Nat :=
  ∑ a < p.n, ∑ b < p.n, cost p g (a :: (c ++ [b]))

theorem endSum_flip (p : Params) (g c : List Nat) (hk : 2 ≤ p.k) (hlen : c.length = p.k - 1)
    (hc : ∀ x ∈ c, x < p.n) :
    endSum p g (c.map (fun x => p.n - 1 - x)) = endSum p g c := by
  unfold endSum
  have h1 : ∀ a, a < p.n → (∑ b < p.n, cost p g (a :: (c ++ [b])))
      = ∑ b < p.n, cost p g ((p.n - 1 - a) :: (c.map (fun x => p.n - 1 - x) ++ [b])) := by
    intro a ha
    rw [← sum_flip p.n (fun b => cost p g ((p.n - 1 - a) :: (c.map (fun x => p.n - 1 - x) ++ [b])))]
    apply sum_congr
    intro b hb
    rw [← cost_flip p g (a :: (c ++ [b])) (by simp; omega) (by
      intro x hx
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact ha
      · exact hc x hx
      · exact hb)]
    simp only [List.map_cons, List.map_append, List.map_nil]
  rw [sum_congr h1]
  exact (sum_flip p.n
    (fun a => ∑ b < p.n, cost p g (a :: (c.map (fun x => p.n - 1 - x) ++ [b])))).symm

/-! ## The cell sum -/

theorem cellSumFlip_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (g : List Nat) : cellSumFlip p rows (mkPlan p.k p.n) g = S p g := by
  unfold cellSumFlip
  split
  · rename_i hok
    have hk : 2 ≤ p.k := by
      simp only [mkPlan, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.1.1.1
    have hcons : ∀ x, x < p.n → ∀ c ∈ tuples (p.k - 2) p.n,
        (x :: c).length = p.k - 1 ∧ ∀ y ∈ x :: c, y < p.n := by
      intro x hx c hc
      obtain ⟨hl, ha⟩ := mem_tuples.mp hc
      refine ⟨by simp [hl]; omega, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ha y hy
    have inner : ∀ x, x < p.n →
        sumTuples p.n (p.k - 2)
            (fun c => configSum (mkPlan p.k p.n) (edgeTab p rows g) p.k (x :: c))
          = ((tuples (p.k - 2) p.n).map (fun c => endSum p g (x :: c))).sum := by
      intro x hx
      rw [sumTuples_eq]
      refine congrArg List.sum ?_
      apply List.map_congr_left
      intro c hc
      exact configSum_eq p rows h hok g (x :: c) (mem_tuples.mpr (hcons x hx c hc))
    have hsym : ∀ x, x < p.n →
        ((tuples (p.k - 2) p.n).map (fun c => endSum p g ((p.n - 1 - x) :: c))).sum
          = ((tuples (p.k - 2) p.n).map (fun c => endSum p g (x :: c))).sum := by
      intro x hx
      rw [← sum_tuples_flip (p.k - 2) p.n (fun c => endSum p g ((p.n - 1 - x) :: c))]
      refine congrArg List.sum ?_
      apply List.map_congr_left
      intro c hc
      have h2 := endSum_flip p g (x :: c) hk (hcons x hx c hc).1 (hcons x hx c hc).2
      rw [← h2]; rfl
    simp only []
    rw [sumHalf_eq _ _ (by
      intro x hx
      rw [inner _ (by omega), inner x hx, hsym x hx])]
    rw [sum_congr inner]
    have hk1 : p.k - 1 = (p.k - 2) + 1 := by omega
    have hk' : p.k + 1 = (p.k - 1) + 2 := by omega
    unfold S
    rw [hk', sum_tuples_ends, hk1, sum_tuples_head]
    rfl
  · rfl

theorem sumsStep_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (base step lo cnt : Nat) :
    sumsStep p rows base step lo cnt
      = (List.range' lo cnt).map (fun t => S p (gapOfIndex p (base + step * t))) := by
  unfold sumsStep
  apply List.map_congr_left
  intro t _
  exact cellSumFlip_eq p rows h _

theorem sumsStep_append (p : Params) (rows : List (List Nat × Array Nat)) (base step lo a b : Nat) :
    sumsStep p rows base step lo a ++ sumsStep p rows base step (lo + a) b
      = sumsStep p rows base step lo (a + b) := by
  unfold sumsStep
  rw [← List.map_append, List.range'_append_1]

/-! ## Several threads -/

theorem parWave_eq (r : Nat → Nat → List Nat) (hr : ∀ lo a b, r lo a ++ r (lo + a) b = r lo (a + b))
    (hr0 : ∀ lo, r lo 0 = []) (threads chunk lo cnt : Nat) (acc : List Nat) :
    parWave r threads chunk lo cnt acc = acc ++ r lo (min cnt (threads * chunk)) := by
  unfold parWave
  induction threads with
  | zero => simp [hr0]
  | succ T ih =>
    simp only [] at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [List.append_assoc, task_get_spawn, hr]
    congr 2
    rw [Nat.succ_mul]; omega

theorem parWaves_eq (r : Nat → Nat → List Nat) (hr : ∀ lo a b, r lo a ++ r (lo + a) b = r lo (a + b))
    (hr0 : ∀ lo, r lo 0 = []) (threads chunk fuel lo cnt : Nat) (acc : List Nat) :
    parWaves r threads chunk fuel lo cnt acc = acc ++ r lo cnt := by
  induction fuel generalizing lo cnt acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [parWaves]
    split
    · rename_i h0; subst h0; simp [hr0]
    · rw [ih, parWave_eq r hr hr0, List.append_assoc, hr]
      congr 2
      omega

/-! ## `A_j(g)` for the beginning of a gap tuple -/

theorem indexOf_eq (mm : Nat) (g : List Nat) : indexOf mm g = idx mm g := by
  induction g with
  | nil => rfl
  | cons x l ih => simp [indexOf, idx, ih]

theorem idx_append_list (mm : Nat) (g u : List Nat) :
    idx mm (g ++ u) = idx mm g + mm ^ g.length * idx mm u := by
  induction g with
  | nil => simp [idx]
  | cons x l ih =>
    simp only [List.cons_append, idx, ih, List.length_cons, Nat.pow_succ, Nat.mul_add]
    rw [Nat.add_assoc, ← Nat.mul_assoc, Nat.mul_comm mm (mm ^ l.length)]

theorem totalRec_under (p : Params) (g : List Nat) (hg : ∀ x ∈ g, x < m p) (r : Nat)
    (hr : g.length + r = p.k) (rest : Nat) (u : List Nat) (hu : u.length + rest = r)
    (hmem : ∀ x ∈ u, x < m p) :
    totalRec p (massArr p)
      ((List.range' 0 ((m p) ^ r)).map
        (fun t => S p (gapOfIndex p (idx (m p) g + (m p) ^ g.length * t)))).toArray
      rest u.length (idx (m p) u) = A p (g ++ u) := by
  induction rest generalizing u with
  | zero =>
    have hk : p.k ≤ (g ++ u).length := by simp; omega
    rw [A, if_pos hk]
    simp only [totalRec]
    have hlt : idx (m p) u < (m p) ^ r := by
      have := idx_lt (m p) u hmem
      rwa [show u.length = r by omega] at this
    have hget : (((List.range' 0 ((m p) ^ r)).map
          (fun t => S p (gapOfIndex p (idx (m p) g + (m p) ^ g.length * t)))).toArray).getD
            (idx (m p) u) 0
        = S p (gapOfIndex p (idx (m p) g + (m p) ^ g.length * idx (m p) u)) := by
      simp [hlt]
    have hall : ∀ x ∈ g ++ u, x < m p := by
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hg x hx
      · exact hmem x hx
    rw [hget, ← idx_append_list, gapOfIndex_idx p (g ++ u) (by simp; omega) hall]
  | succ rest ih =>
    have hk : ¬ p.k ≤ (g ++ u).length := by simp; omega
    rw [A, if_neg hk]
    simp only [totalRec]
    congr 1
    apply sum_congr
    intro c hc
    rw [look_eq (isTab_massArr p)]
    have hmem' : ∀ x ∈ u ++ [c], x < m p := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hmem x hx
      · exact hc
    have h2 := ih (u ++ [c]) (by simp; omega) hmem'
    rw [idx_append, List.length_append, List.length_singleton, ← List.append_assoc] at h2
    rw [h2]

/-- `AofPar` computes `A_j(g)`. -/
theorem AofPar_eq (p : Params) (threads : Nat) (g : List Nat) : AofPar p threads g = A p g := by
  unfold AofPar
  split
  · rename_i hcond
    obtain ⟨hlen, hall⟩ := hcond
    have hg : ∀ x ∈ g, x < m p := by simpa using hall
    simp only []
    rw [parWaves_eq (sumsStep p (tableRows p 1) (indexOf (m p) g) ((m p) ^ g.length))
        (fun lo a b => sumsStep_append p _ _ _ lo a b) (fun lo => by simp [sumsStep]),
      List.nil_append, sumsStep_eq p _ (rowsOK_tableRows p 1), indexOf_eq]
    have h2 := totalRec_under p g hg (p.k - g.length) (by omega) (p.k - g.length) [] (by simp)
      (by simp)
    rw [List.append_nil] at h2
    exact h2
  · rfl

/-! ## The total from the values of `A_j` -/

theorem valOf_eq (vals : List (List Nat × Nat)) (l : List (List Nat)) (F : List Nat → Nat)
    (h : vals = l.map (fun g => (g, F g))) (g : List Nat) (hg : g ∈ l) : valOf vals g = F g := by
  unfold valOf
  cases hfind : vals.find? (fun e => e.1 == g) with
  | none =>
    have h1 := List.find?_eq_none.mp hfind (g, F g) (by rw [h]; exact List.mem_map.mpr ⟨g, hg, rfl⟩)
    simp at h1
  | some e =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    rw [h] at hmem
    obtain ⟨g', _, rfl⟩ := List.mem_map.mp hmem
    have h1 : g' = g := by simpa using hp
    subst h1; rfl

theorem Afrom_eq (p : Params) (j : Nat) (f : List Nat → Nat) (hj : j ≤ p.k)
    (hf : ∀ g ∈ tuples j (m p), f g = A p g) (g : List Nat) (hlen : g.length ≤ j)
    (hmem : ∀ x ∈ g, x < m p) : Afrom p (massArr p) j f g = A p g := by
  generalize hd : j - g.length = d
  induction d generalizing g with
  | zero =>
    have h1 : j ≤ g.length := by omega
    rw [Afrom, if_pos h1]
    exact hf g (mem_tuples.mpr ⟨by omega, hmem⟩)
  | succ d ih =>
    have h1 : ¬ j ≤ g.length := by omega
    have h2 : ¬ p.k ≤ g.length := by omega
    rw [Afrom, if_neg h1, A, if_neg h2]
    congr 1
    apply sum_congr
    intro c hc
    have hmem' : ∀ x ∈ g ++ [c], x < m p := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hmem x hx
      · exact hc
    rw [look_eq (isTab_massArr p), ih (g ++ [c]) (by simp; omega) hmem' (by simp; omega)]

/-- The total from the values `A_j(g)` of all beginnings `g` of length `j`. -/
theorem totalFrom_eq (p : Params) (j : Nat) (vals : List (List Nat × Nat)) (hj : j ≤ p.k)
    (h : vals = (tuples j (m p)).map (fun g => (g, A p g))) : totalFrom p j vals = Spec.total p :=
  Afrom_eq p j (valOf vals) hj (fun g hg => valOf_eq vals _ (A p) h g hg) [] (Nat.zero_le _)
    (by simp)

end Correct
