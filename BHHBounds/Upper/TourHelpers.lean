import BHHBounds.Upper.AutomatonSound
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Geometric & Combinatorial Tour Helpers for the End-to-End BHH Upper Bound

Zero `import Mathlib` — compiles fast. Proves:
1. Euclidean distance `ptDist` triangle inequality, symmetry, scaling, L1 bound.
2. `listPathLen` and `cycleLen`, cyclic rotation invariance, reversal invariance,
   and **sublist shortcutting** (`cycleLen_sublist_le`).
3. `finTourLen` (matching `BHHBounds.tourLength`), bounded by `cycleLen L` whenever every
   point `x i` appears at a distinct position in `L`.
4. Deterministic strip bound `finTourLen x ≤ 4 * √n + 4` for `x i ∈ [0,1]²` (used for
   Dominated Convergence in `ToBHH.lean`).
5. Serpentine stitching of `M` strip Hamiltonian paths into a single closed cycle.
-/

namespace BHHBounds.Upper

open Set Finset

/-- Euclidean distance on `ℝ × ℝ` (matches `BHHBounds.euclidDist`). -/
noncomputable def ptDist (a b : ℝ × ℝ) : ℝ :=
  Real.sqrt ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2)

lemma ptDist_nonneg (a b : ℝ × ℝ) : 0 ≤ ptDist a b := Real.sqrt_nonneg _

lemma ptDist_self (a : ℝ × ℝ) : ptDist a a = 0 := by simp [ptDist]

lemma ptDist_symm (a b : ℝ × ℝ) : ptDist a b = ptDist b a := by
  unfold ptDist; congr 1; ring

lemma ptDist_le_l1 (a b : ℝ × ℝ) : ptDist a b ≤ |a.1 - b.1| + |a.2 - b.2| := by
  unfold ptDist
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : (a.1 - b.1) ^ 2 = |a.1 - b.1| ^ 2 := (sq_abs _).symm
  have h2 : (a.2 - b.2) ^ 2 = |a.2 - b.2| ^ 2 := (sq_abs _).symm
  rw [h1, h2]
  nlinarith [abs_nonneg (a.1 - b.1), abs_nonneg (a.2 - b.2)]

lemma ptDist_triangle (a b c : ℝ × ℝ) : ptDist a c ≤ ptDist a b + ptDist b c := by
  unfold ptDist
  set x1 := a.1 - b.1; set y1 := a.2 - b.2
  set x2 := b.1 - c.1; set y2 := b.2 - c.2
  have hsum : (a.1 - c.1) ^ 2 + (a.2 - c.2) ^ 2 = (x1 + x2) ^ 2 + (y1 + y2) ^ 2 := by
    dsimp only [x1, y1, x2, y2]; ring
  rw [hsum, Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hsq1 : Real.sqrt (x1 ^ 2 + y1 ^ 2) ^ 2 = x1 ^ 2 + y1 ^ 2 := Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt (x2 ^ 2 + y2 ^ 2) ^ 2 = x2 ^ 2 + y2 ^ 2 := Real.sq_sqrt (by positivity)
  have hcs : x1 * x2 + y1 * y2 ≤ Real.sqrt (x1 ^ 2 + y1 ^ 2) * Real.sqrt (x2 ^ 2 + y2 ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    have hnn : (x1 * x2 + y1 * y2) ^ 2 ≤ (x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2) := by
      nlinarith [sq_nonneg (x1 * y2 - y1 * x2)]
    exact Real.le_sqrt_of_sq_le hnn
  nlinarith [add_sq (Real.sqrt (x1 ^ 2 + y1 ^ 2)) (Real.sqrt (x2 ^ 2 + y2 ^ 2))]

lemma ptDist_scale {s : ℝ} (hs : 0 ≤ s) (a b : ℝ × ℝ) :
    ptDist (s * a.1, s * a.2) (s * b.1, s * b.2) = s * ptDist a b := by
  unfold ptDist
  have h : (s * a.1 - s * b.1) ^ 2 + (s * a.2 - s * b.2) ^ 2 =
      s ^ 2 * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

lemma ptDist_translate (t a b : ℝ × ℝ) :
    ptDist (a.1 + t.1, a.2 + t.2) (b.1 + t.1, b.2 + t.2) = ptDist a b := by
  unfold ptDist; congr 1; ring

/-! ## Open Path Length and Closed Cycle Length on `List (ℝ × ℝ)` -/

noncomputable def listPathLen : List (ℝ × ℝ) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => ptDist a b + listPathLen (b :: rest)

lemma listPathLen_nonneg : ∀ l : List (ℝ × ℝ), 0 ≤ listPathLen l
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: rest => add_nonneg (ptDist_nonneg a b) (listPathLen_nonneg (b :: rest))

lemma listPathLen_map_eq_pathLen (l : List ℕ) (p : ℕ → ℝ × ℝ) :
    listPathLen (l.map p) = pathLen ptDist l p := by
  match l with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    have ih := listPathLen_map_eq_pathLen (b :: rest) p
    simp only [List.map_cons, listPathLen, pathLen] at ih ⊢
    rw [ih]

lemma listPathLen_append_singleton :
    ∀ (l : List (ℝ × ℝ)) (h : l ≠ []) (x : ℝ × ℝ),
      listPathLen (l ++ [x]) = listPathLen l + ptDist (l.getLast h) x
  | [], h, _ => absurd rfl h
  | [a], _, x => by simp [listPathLen]
  | a :: b :: rest, _, x => by
    have hne : b :: rest ≠ [] := List.cons_ne_nil _ _
    have ih := listPathLen_append_singleton (b :: rest) hne x
    simp only [List.cons_append, listPathLen, List.getLast_cons hne] at ih ⊢
    linarith

lemma listPathLen_append :
    ∀ (l₁ l₂ : List (ℝ × ℝ)) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []),
      listPathLen (l₁ ++ l₂) = listPathLen l₁ + ptDist (l₁.getLast h₁) (l₂.head h₂) + listPathLen l₂
  | [], _, h₁, _ => absurd rfl h₁
  | _, [], _, h₂ => absurd rfl h₂
  | [a], b :: rest, _, _ => by simp [listPathLen]
  | a :: c :: r₁, b :: r₂, _, _ => by
    have hne : c :: r₁ ≠ [] := List.cons_ne_nil _ _
    have ih := listPathLen_append (c :: r₁) (b :: r₂) hne (List.cons_ne_nil _ _)
    simp only [List.cons_append, listPathLen, List.getLast_cons hne, List.head_cons] at ih ⊢
    linarith

lemma listPathLen_reverse : ∀ l : List (ℝ × ℝ), listPathLen l.reverse = listPathLen l
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have hne : b :: rest ≠ [] := List.cons_ne_nil _ _
    have hrev_ne : (b :: rest).reverse ≠ [] := by simp
    rw [List.reverse_cons, listPathLen_append_singleton _ hrev_ne a]
    have hlast : (b :: rest).reverse.getLast hrev_ne = b := by simp
    rw [hlast, listPathLen_reverse (b :: rest), listPathLen, ptDist_symm]
    ring

/-- Length of the closed cycle visiting `l` in order and returning from last to first. -/
noncomputable def cycleLen : List (ℝ × ℝ) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => listPathLen (a :: b :: rest) + ptDist ((a :: b :: rest).getLast (List.cons_ne_nil _ _)) a

lemma cycleLen_nonneg : ∀ l : List (ℝ × ℝ), 0 ≤ cycleLen l
  | [] => le_rfl
  | [_] => le_rfl
  | _ :: _ :: _ => add_nonneg (listPathLen_nonneg _) (ptDist_nonneg _ _)

lemma cycleLen_eq_pathLen_add_close (l : List (ℝ × ℝ)) (h : l ≠ []) :
    cycleLen l = listPathLen l + ptDist (l.getLast h) (l.head h) := by
  match l with
  | [] => exact absurd rfl h
  | [a] => simp [cycleLen, listPathLen, ptDist_self]
  | a :: b :: rest => rfl

lemma cycleLen_rotate (a : ℝ × ℝ) (l : List (ℝ × ℝ)) :
    cycleLen (l ++ [a]) = cycleLen (a :: l) := by
  cases l with
  | nil => simp [cycleLen]
  | cons b rest =>
    have hne1 : (b :: rest) ++ [a] ≠ [] := by simp
    have hne2 : b :: rest ≠ [] := List.cons_ne_nil _ _
    rw [cycleLen_eq_pathLen_add_close _ hne1, cycleLen_eq_pathLen_add_close _ (List.cons_ne_nil _ _)]
    rw [listPathLen_append_singleton (b :: rest) hne2 a]
    simp only [List.getLast_append_singleton, List.head_append_of_ne_nil hne2, List.head_cons,
      List.getLast_cons hne2, listPathLen]
    rw [ptDist_symm a b]
    ring

lemma cycleLen_append_comm (l₁ l₂ : List (ℝ × ℝ)) :
    cycleLen (l₁ ++ l₂) = cycleLen (l₂ ++ l₁) := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a rest ih =>
    have h1 : (a :: rest) ++ l₂ = a :: (rest ++ l₂) := rfl
    rw [h1, ← cycleLen_rotate a (rest ++ l₂)]
    have h2 : (rest ++ l₂) ++ [a] = rest ++ (l₂ ++ [a]) := List.append_assoc _ _ _
    rw [h2, ih (l₂ ++ [a]), List.append_assoc]
    rfl

lemma cycleLen_cons_le (a : ℝ × ℝ) (l : List (ℝ × ℝ)) :
    cycleLen l ≤ cycleLen (a :: l) := by
  match l with
  | [] => simp [cycleLen]
  | [b] => exact cycleLen_nonneg [a, b]
  | b :: c :: rest =>
    have hne : b :: c :: rest ≠ [] := List.cons_ne_nil _ _
    rw [cycleLen_eq_pathLen_add_close _ hne, cycleLen_eq_pathLen_add_close _ (List.cons_ne_nil _ _)]
    simp only [listPathLen, List.getLast_cons hne, List.head_cons]
    linarith [ptDist_triangle ((b :: c :: rest).getLast hne) a b]

lemma cycleLen_middle_drop (l₁ l₂ : List (ℝ × ℝ)) (b : ℝ × ℝ) :
    cycleLen (l₁ ++ l₂) ≤ cycleLen (l₁ ++ b :: l₂) := by
  rw [cycleLen_append_comm l₁ l₂, cycleLen_append_comm l₁ (b :: l₂)]
  exact cycleLen_cons_le b (l₂ ++ l₁)

private lemma cycleLen_append_sublist_le {l₁ l₂ : List (ℝ × ℝ)} (h : l₁.Sublist l₂) :
    ∀ l₀ : List (ℝ × ℝ), cycleLen (l₀ ++ l₁) ≤ cycleLen (l₀ ++ l₂) := by
  induction h with
  | slnil => intro _; exact le_rfl
  | cons a _ ih =>
    intro l₀
    exact (ih l₀).trans (cycleLen_middle_drop l₀ _ a)
  | @cons_cons l₁' l₂' a _ ih =>
    intro l₀
    have h1 : l₀ ++ a :: l₁' = (l₀ ++ [a]) ++ l₁' := by simp
    have h2 : l₀ ++ a :: l₂' = (l₀ ++ [a]) ++ l₂' := by simp
    rw [h1, h2]
    exact ih (l₀ ++ [a])

/-- **Sublist Shortcutting:** Removing any points from a tour never increases its cycle length. -/
theorem cycleLen_sublist_le {l₁ l₂ : List (ℝ × ℝ)} (h : l₁.Sublist l₂) :
    cycleLen l₁ ≤ cycleLen l₂ := by
  simpa using cycleLen_append_sublist_le h []

/-! ## Connection to `finTourLen` (matching `BHHBounds.tourLength`) -/

noncomputable def finTourLen {n : ℕ} (x : Fin n → ℝ × ℝ) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i)))

private lemma finRange_head (n : ℕ) : (List.finRange (n + 1)).head (by simp) = 0 := by
  simp [List.finRange_succ]

private lemma finRange_getLast (n : ℕ) : (List.finRange (n + 1)).getLast (by simp) = Fin.last n := by
  simp [List.finRange_succ_last]

private lemma finRotate_castSucc_eq {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ := by
  rw [finRotate_apply]
  exact Fin.ext (by simp)

lemma listPathLen_finRange (n : ℕ) (x : Fin (n + 1) → ℝ × ℝ) :
    listPathLen ((List.finRange (n + 1)).map x) =
      ∑ i : Fin n, ptDist (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => simp [List.finRange_succ, listPathLen]
  | succ n ih =>
    rw [List.finRange_succ_last, List.map_append, List.map_singleton]
    have hmap : ((List.finRange (n + 1)).map Fin.castSucc).map x =
        (List.finRange (n + 1)).map (fun i => x i.castSucc) := by
      rw [List.map_map]; rfl
    rw [hmap]
    have hne : (List.finRange (n + 1)).map (fun i => x i.castSucc) ≠ [] := by simp
    rw [listPathLen_append_singleton _ hne, ih (fun i => x i.castSucc)]
    have hlast : ((List.finRange (n + 1)).map (fun i => x i.castSucc)).getLast hne =
        x (Fin.last n).castSucc := by
      rw [List.getLast_map (by simp), finRange_getLast]
    rw [Fin.sum_univ_castSucc]
    congr 1
    rw [hlast]
    rfl

lemma cycleLen_finRange (n : ℕ) (x : Fin n → ℝ × ℝ) :
    cycleLen ((List.finRange n).map x) = ∑ i : Fin n, ptDist (x i) (x (finRotate n i)) := by
  cases n with
  | zero => simp [cycleLen]
  | succ n =>
    have hne : (List.finRange (n + 1)).map x ≠ [] := by simp
    rw [cycleLen_eq_pathLen_add_close _ hne, listPathLen_finRange]
    have hlast : ((List.finRange (n + 1)).map x).getLast hne = x (Fin.last n) := by
      rw [List.getLast_map (by simp), finRange_getLast]
    have hhead : ((List.finRange (n + 1)).map x).head hne = x 0 := by
      rw [List.head_map, finRange_head]
    rw [hlast, hhead, Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [finRotate_castSucc_eq]
    · rw [finRotate_last]

lemma finTourLen_le_perm {n : ℕ} (x : Fin n → ℝ × ℝ) (σ : Equiv.Perm (Fin n)) :
    finTourLen x ≤ ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i))) := by
  unfold finTourLen
  exact ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) σ

lemma finTourLen_nonneg {n : ℕ} (x : Fin n → ℝ × ℝ) : 0 ≤ finTourLen x := by
  unfold finTourLen
  exact Real.iInf_nonneg fun σ => Finset.sum_nonneg fun i _ => ptDist_nonneg _ _

lemma finTourLen_perm_eq {n : ℕ} (x : Fin n → ℝ × ℝ) (τ : Equiv.Perm (Fin n)) :
    finTourLen (x ∘ τ) = finTourLen x := by
  unfold finTourLen
  exact Equiv.iInf_congr (Equiv.mulLeft τ) fun σ => by simp [Function.comp]

/-- Given an injective map `f : Fin n → Fin L.length` with `L[f i] = x i`, there is a
permutation `σ` such that `(finRange n).map (x ∘ σ)` is a sublist of `L`, hence
`finTourLen x ≤ cycleLen L`. -/
lemma finTourLen_le_cycleLen_of_inj {n : ℕ} (x : Fin n → ℝ × ℝ) (L : List (ℝ × ℝ))
    (f : Fin n → Fin L.length) (hf : Function.Injective f) (hval : ∀ i, L[f i] = x i) :
    finTourLen x ≤ cycleLen L := by
  -- Sort `f` into strictly increasing order using `Tuple.sort f`
  let σ : Equiv.Perm (Fin n) := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hstrict : StrictMono (f ∘ σ) := hmono.strictMono_of_injective (hf.comp σ.injective)
  -- Helper: any strictly increasing index map `g : Fin m → Fin L.length` yields a sublist
  have hsub : ∀ {m : ℕ} (g : Fin m → Fin L.length), StrictMono g →
      ((List.finRange m).map (fun i => L[g i])).Sublist L := by
    intro m g hg
    -- Prove by induction on `L` using `List.sublist_iff_exists_fin_orderEmbedding_get_eq`
    let emb : Fin m ↪o Fin L.length := OrderEmbedding.ofStrictMono g hg
    have hiff := List.sublist_iff_exists_fin_orderEmbedding_get_eq
      (l := (List.finRange m).map (fun i => L[g i])) (l' := L)
    refine hiff.mpr ⟨(Fin.castOrderIso (by simp)).toOrderEmbedding.trans emb, ?_⟩
    intro i
    simp [emb]; rfl
  have hsubL : ((List.finRange n).map (x ∘ σ)).Sublist L := by
    have heq : (List.finRange n).map (x ∘ σ) = (List.finRange n).map (fun i => L[(f ∘ σ) i]) := by
      congr 1; funext i; exact (hval (σ i)).symm
    rw [heq]
    exact hsub (f ∘ σ) hstrict
  calc finTourLen x ≤ ∑ i : Fin n, ptDist (x (σ i)) (x (σ (finRotate n i))) := finTourLen_le_perm x σ
    _ = cycleLen ((List.finRange n).map (x ∘ σ)) := (cycleLen_finRange n (x ∘ σ)).symm
    _ ≤ cycleLen L := cycleLen_sublist_le hsubL

/-! ## Deterministic `4√n + 4` Strip Bound on `[0,1]²` (DCT Envelope) -/

private lemma ptDist_unitSquare_le_two {a b : ℝ × ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ptDist a b ≤ 2 := by
  have hx : |a.1 - b.1| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith [ha.1.2, hb.1.1], by linarith [hb.1.2, ha.1.1]⟩
  have hy : |a.2 - b.2| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith [ha.2.2, hb.2.1], by linarith [hb.2.2, ha.2.1]⟩
  linarith [ptDist_le_l1 a b]

private lemma fin_sum_telescope : ∀ (m : ℕ) (f : Fin (m + 1) → ℝ),
    ∑ i : Fin m, (f i.succ - f i.castSucc) = f (Fin.last m) - f 0
  | 0, f => by simp
  | m' + 1, f => by
    rw [Fin.sum_univ_castSucc]
    have h4 : ∀ i : Fin m', i.castSucc.succ = i.succ.castSucc := fun i => Fin.ext (by simp)
    simp_rw [h4]
    rw [fin_sum_telescope m' (fun j => f j.castSucc)]
    have h2 : (Fin.last m').succ = Fin.last (m' + 1) := Fin.ext (by simp)
    have h3 : (0 : Fin (m' + 1)).castSucc = (0 : Fin (m' + 2)) := rfl
    rw [h2, h3]; ring

/-- **Deterministic Strip Tour Bound:** Any `n` points in `[0,1]²` admit a closed tour of length
at most `4 * √n + 4`. -/
theorem finTourLen_unitSquare_le {n : ℕ} (x : Fin n → ℝ × ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    finTourLen x ≤ 4 * Real.sqrt (n : ℝ) + 4 := by
  cases n with
  | zero =>
    have h0 : finTourLen x ≤ 0 := by
      simpa using finTourLen_le_perm x 1
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
          have := Nat.floor_le (mul_nonneg (le_of_lt hkR_pos) hy0)
          linarith
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
    have hle_perm := finTourLen_le_perm x σ
    refine hle_perm.trans ?_
    rw [Fin.sum_univ_castSucc]
    have hclose : ptDist (x (σ (Fin.last m))) (x (σ (finRotate n (Fin.last m)))) ≤ 2 :=
      ptDist_unitSquare_le_two (hx _) (hx _)
    have hstep : ∀ i : Fin m,
        ptDist (x (σ i.castSucc)) (x (σ (finRotate n i.castSucc))) ≤
          (if strip (σ i.castSucc) = strip (σ i.succ) then
            ((x (σ i.succ)).1 - (x (σ i.castSucc)).1) + 1 / (k : ℝ)
          else
            2 * (((strip (σ i.succ) : ℝ) - (strip (σ i.castSucc) : ℝ)))) := by
      intro i
      rw [finRotate_castSucc_eq i]
      have hmi := hmono (show i.castSucc ≤ i.succ by simp [Fin.le_def])
      have hs_le : strip (σ i.castSucc) ≤ strip (σ i.succ) := by
        rcases (Prod.Lex.le_iff.mp hmi) with hlt | ⟨heq, _⟩
        · exact le_of_lt hlt
        · exact le_of_eq heq
      split_ifs with heq
      · have hx_le : (x (σ i.castSucc)).1 ≤ (x (σ i.succ)).1 := by
          rcases (Prod.Lex.le_iff.mp hmi) with hlt | ⟨_, hle⟩
          · exact absurd heq (ne_of_lt hlt)
          · exact hle
        have hxa : |(x (σ i.castSucc)).1 - (x (σ i.succ)).1| = (x (σ i.succ)).1 - (x (σ i.castSucc)).1 := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hx_le)]
        have hy1 := hstrip_y (σ i.castSucc)
        have hy2 := hstrip_y (σ i.succ)
        rw [heq] at hy1
        have hya : |(x (σ i.castSucc)).2 - (x (σ i.succ)).2| ≤ 1 / (k : ℝ) := by
          rw [abs_sub_le_iff]
          have hstep_div : (((strip (σ i.succ) + 1 : ℕ) : ℝ) / (k : ℝ)) - ((strip (σ i.succ) : ℕ) : ℝ) / (k : ℝ) =
              1 / (k : ℝ) := by push_cast; ring
          constructor <;> linarith
        linarith [ptDist_le_l1 (x (σ i.castSucc)) (x (σ i.succ))]
      · have hslt : strip (σ i.castSucc) + 1 ≤ strip (σ i.succ) := by omega
        have hsdiff : (1 : ℝ) ≤ (strip (σ i.succ) : ℝ) - (strip (σ i.castSucc) : ℝ) := by
          have : ((strip (σ i.castSucc) + 1 : ℕ) : ℝ) ≤ (strip (σ i.succ) : ℝ) := by exact_mod_cast hslt
          push_cast at this; linarith
        linarith [ptDist_unitSquare_le_two (hx (σ i.castSucc)) (hx (σ i.succ))]
    have hstep_uni : ∀ i : Fin m,
        ptDist (x (σ i.castSucc)) (x (σ (finRotate n i.castSucc))) ≤
          ((x (σ i.succ)).1 - (x (σ i.castSucc)).1) + 1 / (k : ℝ) +
            3 * ((strip (σ i.succ) : ℝ) - (strip (σ i.castSucc) : ℝ)) := by
      intro i
      have hs := hstep i
      split_ifs at hs with heq
      · rw [heq]; linarith
      · have hmi := hmono (show i.castSucc ≤ i.succ by simp [Fin.le_def])
        have hs_le : strip (σ i.castSucc) ≤ strip (σ i.succ) := by
          rcases (Prod.Lex.le_iff.mp hmi) with hlt | ⟨h, _⟩
          · exact le_of_lt hlt
          · exact le_of_eq h
        have hsdiff : (1 : ℝ) ≤ (strip (σ i.succ) : ℝ) - (strip (σ i.castSucc) : ℝ) := by
          have : ((strip (σ i.castSucc) + 1 : ℕ) : ℝ) ≤ (strip (σ i.succ) : ℝ) := by
            exact_mod_cast (by omega : strip (σ i.castSucc) + 1 ≤ strip (σ i.succ))
          push_cast at this; linarith
        have hx1 := (hx (σ i.succ)).1
        have hx0 := (hx (σ i.castSucc)).1
        have hk0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
        linarith [hx1.1, hx0.2]
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
        have := hstrip_lt (σ (Fin.last m))
        have : ((strip (σ (Fin.last m)) + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
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
        have : (n : ℝ) < (k : ℝ) * (k : ℝ) := by exact_mod_cast this
        linarith [sq (k : ℝ)]
      have hsq : Real.sqrt (n : ℝ) < (k : ℝ) := by
        rw [Real.sqrt_lt' hkR_pos]; exact hlt
      have hm_le : (m : ℝ) ≤ (n : ℝ) := by dsimp only [n]; push_cast; linarith
      have hn_eq : (n : ℝ) = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
      nlinarith [Real.sqrt_nonneg (n : ℝ)]
    linarith

/-! ## Serpentine Stitching of `M` Strip Paths -/

/-- Concatenate `M` paths in serpentine order: forward on even strips, reversed on odd strips. -/
def serpentineConcat {M : ℕ} (P : Fin M → List (ℝ × ℝ)) : List (ℝ × ℝ) :=
  ((List.finRange M).map fun s => if s.val % 2 = 0 then P s else (P s).reverse).flatten

lemma serpentine_listPathLen_le :
    ∀ {M : ℕ} (P : Fin (M + 1) → List (ℝ × ℝ)) (hne : ∀ s, P s ≠ []),
      serpentineConcat P ≠ [] ∧
      (serpentineConcat P).head (by
        have h0 : P 0 ≠ [] := hne 0
        unfold serpentineConcat
        rw [List.finRange_succ]; simp [h0]) = (P 0).head (hne 0) ∧
      (serpentineConcat P).getLast (by
        have h0 : P 0 ≠ [] := hne 0
        unfold serpentineConcat
        rw [List.finRange_succ]; simp [h0]) =
          (if M % 2 = 0 then (P (Fin.last M)).getLast (hne _) else (P (Fin.last M)).head (hne _)) ∧
      listPathLen (serpentineConcat P) =
        (∑ s : Fin (M + 1), listPathLen (P s)) +
        ∑ s : Fin M,
          if s.val % 2 = 0 then
            ptDist ((P s.castSucc).getLast (hne _)) ((P s.succ).getLast (hne _))
          else
            ptDist ((P s.castSucc).head (hne _)) ((P s.succ).head (hne _)) := by
  intro M
  induction M with
  | zero =>
    intro P hne
    have hserp : serpentineConcat P = P 0 := by simp [serpentineConcat, List.finRange_succ]
    refine ⟨by rw [hserp]; exact hne 0, ?_, ?_, ?_⟩
    · simp [hserp]
    · simp [hserp]
    · simp [hserp]
  | succ M ih =>
    intro P hne
    let P' : Fin (M + 1) → List (ℝ × ℝ) := fun s => P s.castSucc
    have hne' : ∀ s, P' s ≠ [] := fun s => hne s.castSucc
    obtain ⟨hserp_ne, hhead', hlast', hlen'⟩ := ih P' hne'
    let lastSeg : List (ℝ × ℝ) :=
      if (M + 1) % 2 = 0 then P (Fin.last (M + 1)) else (P (Fin.last (M + 1))).reverse
    have hlastSeg_ne : lastSeg ≠ [] := by
      dsimp only [lastSeg]; split_ifs <;> simp [hne]
    have hserp_eq : serpentineConcat P = serpentineConcat P' ++ lastSeg := by
      unfold serpentineConcat
      rw [List.finRange_succ_last, List.map_append, List.map_singleton, List.flatten_append,
        List.flatten_singleton, List.map_map]
      rfl
    have hfull_ne : serpentineConcat P ≠ [] := by rw [hserp_eq]; simp [hserp_ne]
    refine ⟨hfull_ne, ?_, ?_, ?_⟩
    · simp_rw [hserp_eq]
      rw [List.head_append_of_ne_nil hserp_ne, hhead']
      rfl
    · simp_rw [hserp_eq]
      rw [List.getLast_append_of_ne_nil _ hlastSeg_ne]
      dsimp only [lastSeg]
      split_ifs with hev
      · rfl
      · exact List.getLast_reverse (by simp [hne])
    · rw [hserp_eq, listPathLen_append _ _ hserp_ne hlastSeg_ne, hlen', hlast']
      have hlastLen : listPathLen lastSeg = listPathLen (P (Fin.last (M + 1))) := by
        dsimp only [lastSeg]; split_ifs
        · rfl
        · exact listPathLen_reverse _
      rw [hlastLen, Fin.sum_univ_castSucc (f := fun s : Fin (M + 2) => listPathLen (P s)),
          Fin.sum_univ_castSucc (f := fun s : Fin (M + 1) =>
            if s.val % 2 = 0 then
              ptDist ((P s.castSucc).getLast (hne _)) ((P s.succ).getLast (hne _))
            else
              ptDist ((P s.castSucc).head (hne _)) ((P s.succ).head (hne _)))]
      have hjump : ptDist (if M % 2 = 0 then (P' (Fin.last M)).getLast (hne' _)
              else (P' (Fin.last M)).head (hne' _)) (lastSeg.head hlastSeg_ne) =
          if (Fin.last M).val % 2 = 0 then
            ptDist ((P (Fin.last M).castSucc).getLast (hne _)) ((P (Fin.last M).succ).getLast (hne _))
          else
            ptDist ((P (Fin.last M).castSucc).head (hne _)) ((P (Fin.last M).succ).head (hne _)) := by
        have hval : (Fin.last M).val = M := rfl
        have hsucc : (Fin.last M).succ = Fin.last (M + 1) := Fin.ext (by simp)
        rw [hval, hsucc]
        dsimp only [lastSeg, P']
        by_cases hev : M % 2 = 0
        · have hodd : ¬((M + 1) % 2 = 0) := by omega
          simp only [hev, hodd, ↓reduceIte, List.head_reverse]
        · have hev1 : (M + 1) % 2 = 0 := by omega
          simp only [hev, hev1, ↓reduceIte]
      rw [hjump]
      have hsum_eq : ∑ x : Fin M,
            (if x.val % 2 = 0 then ptDist ((P' x.castSucc).getLast (hne' _)) ((P' x.succ).getLast (hne' _))
            else ptDist ((P' x.castSucc).head (hne' _)) ((P' x.succ).head (hne' _))) =
          ∑ x : Fin M,
            (if x.castSucc.val % 2 = 0 then ptDist ((P x.castSucc.castSucc).getLast (hne _)) ((P x.castSucc.succ).getLast (hne _))
            else ptDist ((P x.castSucc.castSucc).head (hne _)) ((P x.castSucc.succ).head (hne _))) := by
        apply Finset.sum_congr rfl
        intro x _
        have hcs : x.succ.castSucc = x.castSucc.succ := Fin.ext (by simp)
        dsimp only [P']
        simp only [Fin.val_castSucc, hcs]
        rfl
      rw [hsum_eq]
      dsimp only [P']
      ring

theorem cycleLen_serpentine {M : ℕ} (P : Fin (M + 1) → List (ℝ × ℝ)) (hne : ∀ s, P s ≠ []) :
    cycleLen (serpentineConcat P) =
      (∑ s : Fin (M + 1), listPathLen (P s)) +
      (∑ s : Fin M,
        if s.val % 2 = 0 then
          ptDist ((P s.castSucc).getLast (hne _)) ((P s.succ).getLast (hne _))
        else
          ptDist ((P s.castSucc).head (hne _)) ((P s.succ).head (hne _))) +
      ptDist (if M % 2 = 0 then (P (Fin.last M)).getLast (hne _) else (P (Fin.last M)).head (hne _))
        ((P 0).head (hne 0)) := by
  obtain ⟨hserp_ne, hhead, hlast, hlen⟩ := serpentine_listPathLen_le P hne
  rw [cycleLen_eq_pathLen_add_close _ hserp_ne, hlen, hhead, hlast]

end BHHBounds.Upper
