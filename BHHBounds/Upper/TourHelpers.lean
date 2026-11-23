import BHHBounds.Upper.AutomatonSound
import BHHBounds.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Paths, cycles and tours

Scaling and translation of `euclidDist`, the length of a path and of a cycle through a list of
points, removal of points from a cycle (`cycleLen_sublist_le`), the comparison of `tourLength`
with a cycle through the same points, and the serpentine concatenation of strip paths.
-/

namespace BHHBounds.Upper

open Set Finset

lemma euclidDist_scale {s : ℝ} (hs : 0 ≤ s) (a b : ℝ × ℝ) :
    euclidDist (s * a.1, s * a.2) (s * b.1, s * b.2) = s * euclidDist a b := by
  unfold euclidDist sqDist
  have h : (s * a.1 - s * b.1) ^ 2 + (s * a.2 - s * b.2) ^ 2 =
      s ^ 2 * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

lemma euclidDist_translate (t a b : ℝ × ℝ) :
    euclidDist (a.1 + t.1, a.2 + t.2) (b.1 + t.1, b.2 + t.2) = euclidDist a b := by
  unfold euclidDist sqDist; congr 1; ring

/-! ## Open Path Length and Closed Cycle Length on `List (ℝ × ℝ)` -/

noncomputable def listPathLen : List (ℝ × ℝ) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => euclidDist a b + listPathLen (b :: rest)

lemma listPathLen_nonneg : ∀ l : List (ℝ × ℝ), 0 ≤ listPathLen l
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: rest => add_nonneg (euclidDist_nonneg a b) (listPathLen_nonneg (b :: rest))

lemma listPathLen_map_eq_pathLen (l : List ℕ) (p : ℕ → ℝ × ℝ) :
    listPathLen (l.map p) = pathLen euclidDist l p := by
  match l with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    have ih := listPathLen_map_eq_pathLen (b :: rest) p
    simp only [List.map_cons, listPathLen, pathLen] at ih ⊢
    rw [ih]

lemma listPathLen_append_singleton :
    ∀ (l : List (ℝ × ℝ)) (h : l ≠ []) (x : ℝ × ℝ),
      listPathLen (l ++ [x]) = listPathLen l + euclidDist (l.getLast h) x
  | [], h, _ => absurd rfl h
  | [a], _, x => by simp [listPathLen]
  | a :: b :: rest, _, x => by
    have hne : b :: rest ≠ [] := List.cons_ne_nil _ _
    have ih := listPathLen_append_singleton (b :: rest) hne x
    simp only [List.cons_append, listPathLen, List.getLast_cons hne] at ih ⊢
    linarith

lemma listPathLen_append :
    ∀ (l₁ l₂ : List (ℝ × ℝ)) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []),
      listPathLen (l₁ ++ l₂) = listPathLen l₁ + euclidDist (l₁.getLast h₁) (l₂.head h₂) + listPathLen l₂
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
    rw [hlast, listPathLen_reverse (b :: rest), listPathLen, euclidDist_symm]
    ring

/-- Length of the closed cycle visiting `l` in order and returning from last to first. -/
noncomputable def cycleLen : List (ℝ × ℝ) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => listPathLen (a :: b :: rest) + euclidDist ((a :: b :: rest).getLast (List.cons_ne_nil _ _)) a

lemma cycleLen_nonneg : ∀ l : List (ℝ × ℝ), 0 ≤ cycleLen l
  | [] => le_rfl
  | [_] => le_rfl
  | _ :: _ :: _ => add_nonneg (listPathLen_nonneg _) (euclidDist_nonneg _ _)

lemma cycleLen_eq_pathLen_add_close (l : List (ℝ × ℝ)) (h : l ≠ []) :
    cycleLen l = listPathLen l + euclidDist (l.getLast h) (l.head h) := by
  match l with
  | [] => exact absurd rfl h
  | [a] => simp [cycleLen, listPathLen, euclidDist_self]
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
    rw [euclidDist_symm a b]
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
    linarith [euclidDist_triangle ((b :: c :: rest).getLast hne) a b]

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

/-- Removing any points from a tour never increases its cycle length. -/
theorem cycleLen_sublist_le {l₁ l₂ : List (ℝ × ℝ)} (h : l₁.Sublist l₂) :
    cycleLen l₁ ≤ cycleLen l₂ := by
  simpa using cycleLen_append_sublist_le h []

/-! ## Tours and cycles -/

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
      ∑ i : Fin n, euclidDist (x i.castSucc) (x i.succ) := by
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
    cycleLen ((List.finRange n).map x) = ∑ i : Fin n, euclidDist (x i) (x (finRotate n i)) := by
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

lemma tourLength_perm {n : ℕ} (x : Fin n → ℝ × ℝ) (τ : Equiv.Perm (Fin n)) :
    tourLength (x ∘ τ) = tourLength x := by
  unfold tourLength
  exact Equiv.iInf_congr (Equiv.mulLeft τ) fun σ => by simp [Function.comp]

/-- Given an injective map `f : Fin n → Fin L.length` with `L[f i] = x i`, there is a
permutation `σ` such that `(finRange n).map (x ∘ σ)` is a sublist of `L`, hence
`tourLength x ≤ cycleLen L`. -/
lemma tourLength_le_cycleLen_of_inj {n : ℕ} (x : Fin n → ℝ × ℝ) (L : List (ℝ × ℝ))
    (f : Fin n → Fin L.length) (hf : Function.Injective f) (hval : ∀ i, L[f i] = x i) :
    tourLength x ≤ cycleLen L := by
  -- Sort `f` into strictly increasing order using `Tuple.sort f`
  let σ : Equiv.Perm (Fin n) := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hstrict : StrictMono (f ∘ σ) := hmono.strictMono_of_injective (hf.comp σ.injective)
  -- Any strictly increasing index map `g : Fin m → Fin L.length` yields a sublist
  have hsub : ∀ {m : ℕ} (g : Fin m → Fin L.length), StrictMono g →
      ((List.finRange m).map (fun i => L[g i])).Sublist L := by
    intro m g hg
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
  calc tourLength x ≤ ∑ i : Fin n, euclidDist (x (σ i)) (x (σ (finRotate n i))) := tourLength_le_perm x σ
    _ = cycleLen ((List.finRange n).map (x ∘ σ)) := (cycleLen_finRange n (x ∘ σ)).symm
    _ ≤ cycleLen L := cycleLen_sublist_le hsubL

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
            euclidDist ((P s.castSucc).getLast (hne _)) ((P s.succ).getLast (hne _))
          else
            euclidDist ((P s.castSucc).head (hne _)) ((P s.succ).head (hne _)) := by
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
              euclidDist ((P s.castSucc).getLast (hne _)) ((P s.succ).getLast (hne _))
            else
              euclidDist ((P s.castSucc).head (hne _)) ((P s.succ).head (hne _)))]
      have hjump : euclidDist (if M % 2 = 0 then (P' (Fin.last M)).getLast (hne' _)
              else (P' (Fin.last M)).head (hne' _)) (lastSeg.head hlastSeg_ne) =
          if (Fin.last M).val % 2 = 0 then
            euclidDist ((P (Fin.last M).castSucc).getLast (hne _)) ((P (Fin.last M).succ).getLast (hne _))
          else
            euclidDist ((P (Fin.last M).castSucc).head (hne _)) ((P (Fin.last M).succ).head (hne _)) := by
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
            (if x.val % 2 = 0 then euclidDist ((P' x.castSucc).getLast (hne' _)) ((P' x.succ).getLast (hne' _))
            else euclidDist ((P' x.castSucc).head (hne' _)) ((P' x.succ).head (hne' _))) =
          ∑ x : Fin M,
            (if x.castSucc.val % 2 = 0 then euclidDist ((P x.castSucc.castSucc).getLast (hne _)) ((P x.castSucc.succ).getLast (hne _))
            else euclidDist ((P x.castSucc.castSucc).head (hne _)) ((P x.castSucc.succ).head (hne _))) := by
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
          euclidDist ((P s.castSucc).getLast (hne _)) ((P s.succ).getLast (hne _))
        else
          euclidDist ((P s.castSucc).head (hne _)) ((P s.succ).head (hne _))) +
      euclidDist (if M % 2 = 0 then (P (Fin.last M)).getLast (hne _) else (P (Fin.last M)).head (hne _))
        ((P 0).head (hne 0)) := by
  obtain ⟨hserp_ne, hhead, hlast, hlen⟩ := serpentine_listPathLen_le P hne
  rw [cycleLen_eq_pathLen_add_close _ hserp_ne, hlen, hhead, hlast]

end BHHBounds.Upper
