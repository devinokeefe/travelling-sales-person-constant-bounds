import BHHBounds.Upper.AutomatonSound
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Concave Dynamic-Programming Fixed-Point Bound for Bandwidth-(d₁ + 1) Strip Paths

Proves that any finite potential table `V : Fin U → Window d₁ G B → ℝ` satisfying
the pointwise concave Bellman inequality `T V ≤ V + uBound` gives an exact linear
upper bound `m * uBound + C` on the expected optimal bandwidth-(d₁ + 1) Hamiltonian
path cost over i.i.d. uniform discrete gap and height labels.
-/

namespace BHHBounds.Upper

open Finset

/-- One arriving point's discrete label: `(gap_bin, height_bin)`. -/
abbrev Label (G B : ℕ) := Fin G × Fin B

/-- Sliding window memory of the last `d₁` gaps and `d₁ + 1` heights (bandwidth `d = d₁ + 1`). -/
abbrev Window (d₁ G B : ℕ) := (Fin d₁ → Fin G) × (Fin (d₁ + 1) → Fin B)

/-- Non-dependent `Fin.snoc` wrapper with clean `@[simp]` lemmas. -/
def snocND {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) : Fin (n + 1) → α :=
  Fin.snoc (α := fun _ => α) f x

@[simp] lemma snocND_castSucc {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) (i : Fin n) :
    snocND f x i.castSucc = f i :=
  Fin.snoc_castSucc (α := fun _ => α) x f i

@[simp] lemma snocND_last {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) :
    snocND f x (Fin.last n) = x :=
  Fin.snoc_last (α := fun _ => α) x f

/-- Append a new gap/height arrival on the right of `z`. -/
def fullGaps {d₁ G B : ℕ} (z : Window d₁ G B) (x : Label G B) : Fin (d₁ + 1) → Fin G :=
  snocND z.1 x.1

def fullHeights {d₁ G B : ℕ} (z : Window d₁ G B) (x : Label G B) : Fin (d₁ + 2) → Fin B :=
  snocND z.2 x.2

/-- Shift window `z` right by one step upon observing new arrival `x`. -/
def advanceWindow {d₁ G B : ℕ} (z : Window d₁ G B) (x : Label G B) : Window d₁ G B :=
  (fun i => fullGaps z x i.succ, fun i => fullHeights z x i.succ)

/-- The oldest `(gap, height)` pair dropped when advancing window `z` (requires `0 < d₁`). -/
def oldestLabel {d₁ G B : ℕ} (hd : 0 < d₁) (z : Window d₁ G B) : Label G B :=
  (z.1 ⟨0, hd⟩, z.2 ⟨0, Nat.succ_pos d₁⟩)

/-- The newest `(gap, height)` pair at the right edge of window `z'`. -/
def newestLabel {d₁ G B : ℕ} (hd : 0 < d₁) (z' : Window d₁ G B) : Label G B :=
  (z'.1 ⟨d₁ - 1, Nat.sub_lt hd Nat.one_pos⟩, z'.2 (Fin.last d₁))

/-- Reconstruct the previous window `z` from the forgotten oldest pair `old` and new window `z'`. -/
def prevWindow {d₁ G B : ℕ} (old : Label G B) (z' : Window d₁ G B) : Window d₁ G B :=
  (fun i => if h : i.val = 0 then old.1 else z'.1 ⟨i.val - 1, by omega⟩,
   fun i => if h : i.val = 0 then old.2 else z'.2 ⟨i.val - 1, by omega⟩)

/-- Reconstruct full gaps `(g_old, z'.1)` from `old` and `z'`. -/
def fullGapsOf {d₁ G B : ℕ} (old : Label G B) (z' : Window d₁ G B) : Fin (d₁ + 1) → Fin G :=
  Fin.cons old.1 z'.1

/-- Reconstruct full heights `(y_old, z'.2)` from `old` and `z'`. -/
def fullHeightsOf {d₁ G B : ℕ} (old : Label G B) (z' : Window d₁ G B) : Fin (d₁ + 2) → Fin B :=
  Fin.cons old.2 z'.2

lemma prevWindow_advance {d₁ G B : ℕ} (hd : 0 < d₁) (z : Window d₁ G B) (x : Label G B) :
    prevWindow (oldestLabel hd z) (advanceWindow z x) = z := by
  apply Prod.ext <;> funext i
  · dsimp only [prevWindow, oldestLabel, advanceWindow, fullGaps]
    split_ifs with h
    · exact congrArg z.1 (Fin.ext h.symm)
    · have hcast : (⟨i.val - 1, by omega⟩ : Fin d₁).succ = (⟨i.val, i.isLt⟩ : Fin d₁).castSucc :=
        Fin.ext (by simp; omega)
      rw [hcast, snocND_castSucc]
  · dsimp only [prevWindow, oldestLabel, advanceWindow, fullHeights]
    split_ifs with h
    · exact congrArg z.2 (Fin.ext h.symm)
    · have hcast : (⟨i.val - 1, by omega⟩ : Fin (d₁ + 1)).succ =
          (⟨i.val, i.isLt⟩ : Fin (d₁ + 1)).castSucc :=
        Fin.ext (by simp; omega)
      rw [hcast, snocND_castSucc]

lemma newestLabel_advance {d₁ G B : ℕ} (hd : 0 < d₁) (z : Window d₁ G B) (x : Label G B) :
    newestLabel hd (advanceWindow z x) = x := by
  apply Prod.ext
  · dsimp only [newestLabel, advanceWindow, fullGaps]
    have hlast : (⟨d₁ - 1, Nat.sub_lt hd Nat.one_pos⟩ : Fin d₁).succ = Fin.last d₁ :=
      Fin.ext (by simp; omega)
    rw [hlast, snocND_last]
  · dsimp only [newestLabel, advanceWindow, fullHeights]
    have hlast : (Fin.last d₁).succ = Fin.last (d₁ + 1) := Fin.ext (by simp)
    rw [hlast, snocND_last]

lemma advance_prevWindow {d₁ G B : ℕ} (hd : 0 < d₁) (old : Label G B) (z' : Window d₁ G B) :
    advanceWindow (prevWindow old z') (newestLabel hd z') = z' := by
  apply Prod.ext <;> funext i
  · dsimp only [advanceWindow, fullGaps]
    by_cases hlt : i.val + 1 < d₁
    · have hcast : i.succ = (⟨i.val + 1, hlt⟩ : Fin d₁).castSucc := Fin.ext rfl
      rw [hcast, snocND_castSucc]
      dsimp only [prevWindow]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel]
    · have hlast : i.succ = Fin.last d₁ := Fin.ext (by simp; omega)
      rw [hlast, snocND_last]
      dsimp only [newestLabel]
      exact congrArg z'.1 (Fin.ext (by simp; omega))
  · dsimp only [advanceWindow, fullHeights]
    by_cases hlt : i.val + 1 < d₁ + 1
    · have hcast : i.succ = (⟨i.val + 1, hlt⟩ : Fin (d₁ + 1)).castSucc := Fin.ext rfl
      rw [hcast, snocND_castSucc]
      dsimp only [prevWindow]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel]
    · have hlast : i.succ = Fin.last (d₁ + 1) := Fin.ext (by simp; omega)
      rw [hlast, snocND_last]
      dsimp only [newestLabel]
      exact congrArg z'.2 (Fin.ext (by simp [Fin.last]; omega))

lemma oldest_prevWindow {d₁ G B : ℕ} (hd : 0 < d₁) (old : Label G B) (z' : Window d₁ G B) :
    oldestLabel hd (prevWindow old z') = old := by
  apply Prod.ext <;> simp [oldestLabel, prevWindow]

lemma fullGaps_eq_fullGapsOf {d₁ G B : ℕ} (hd : 0 < d₁) (old : Label G B) (z' : Window d₁ G B) :
    fullGaps (prevWindow old z') (newestLabel hd z') = fullGapsOf old z' := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · have h0 : (0 : Fin (d₁ + 1)) = (⟨0, hd⟩ : Fin d₁).castSucc := Fin.ext rfl
    rw [h0, fullGaps, snocND_castSucc]
    simp [prevWindow, fullGapsOf]
  · have hstep : fullGaps (prevWindow old z') (newestLabel hd z') j.succ =
        (advanceWindow (prevWindow old z') (newestLabel hd z')).1 j := rfl
    rw [hstep, advance_prevWindow hd old z', fullGapsOf, Fin.cons_succ]

lemma fullHeights_eq_fullHeightsOf {d₁ G B : ℕ} (hd : 0 < d₁) (old : Label G B) (z' : Window d₁ G B) :
    fullHeights (prevWindow old z') (newestLabel hd z') = fullHeightsOf old z' := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · have h0 : (0 : Fin (d₁ + 2)) = (⟨0, Nat.succ_pos d₁⟩ : Fin (d₁ + 1)).castSucc := Fin.ext rfl
    rw [h0, fullHeights, snocND_castSucc]
    simp [prevWindow, fullHeightsOf]
  · have hstep : fullHeights (prevWindow old z') (newestLabel hd z') j.succ =
        (advanceWindow (prevWindow old z') (newestLabel hd z')).2 j := rfl
    rw [hstep, advance_prevWindow hd old z', fullHeightsOf, Fin.cons_succ]

/-- Window obtained after advancing `z₀` through a sequence `w : Fin k → Label G B`. -/
def runWindow {d₁ G B : ℕ} : ∀ {k : ℕ}, Window d₁ G B → (Fin k → Label G B) → Window d₁ G B
  | 0, z₀, _ => z₀
  | _ + 1, z₀, w => advanceWindow (runWindow z₀ (fun i => w i.castSucc)) (w (Fin.last _))

/-- Concrete finite automaton graph for bandwidth `d = d₁ + 1` with `U` reachable states. -/
structure AutomatonGraph (d₁ U : ℕ) where
  stateOf : Fin U → Mate (d₁ + 1)
  initIdx : Fin U
  init_eq : stateOf initIdx = initState (d₁ + 1)
  preds : Fin U → List (Fin U × List (Fin (d₁ + 1)))
  preds_ne : ∀ u', preds u' ≠ []
  preds_valid : ∀ u', ∀ p ∈ preds u', stepState (stateOf p.1) p.2 = some (stateOf u')
  reachSteps : ℕ
  reachWalk : ∀ u : Fin U,
    ∃ (states : Fin (reachSteps + 1) → Fin U) (choices : Fin reachSteps → List (Fin (d₁ + 1))),
      states 0 = initIdx ∧
      states (Fin.last reachSteps) = u ∧
      ∀ t : Fin reachSteps, (states t.castSucc, choices t) ∈ preds (states t.succ)

/-- Minimum of a real function over a non-empty list. -/
def listMin {α : Type*} (f : α → ℝ) : (l : List α) → l ≠ [] → ℝ
  | [a], _ => f a
  | a :: b :: rest, _ => min (f a) (listMin f (b :: rest) (List.cons_ne_nil _ _))

lemma listMin_le {α : Type*} (f : α → ℝ) :
    ∀ (l : List α) (hl : l ≠ []) {a : α}, a ∈ l → listMin f l hl ≤ f a
  | [x], _, a, ha => by simp at ha; subst ha; exact le_rfl
  | x :: y :: rest, _, a, ha => by
    simp only [listMin]
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (listMin_le f (y :: rest) (List.cons_ne_nil _ _) ha')

lemma le_listMin {α : Type*} (f : α → ℝ) (c : ℝ) :
    ∀ (l : List α) (hl : l ≠ []), (∀ a ∈ l, c ≤ f a) → c ≤ listMin f l hl
  | [x], _, h => h x (List.mem_cons_self ..)
  | x :: y :: rest, _, h => by
    simp only [listMin]
    exact le_min (h x (List.mem_cons_self ..))
      (le_listMin f c (y :: rest) (List.cons_ne_nil _ _) (fun a ha => h a (List.mem_cons_of_mem _ ha)))

lemma listMin_exists {α : Type*} (f : α → ℝ) :
    ∀ (l : List α) (hl : l ≠ []), ∃ a ∈ l, f a = listMin f l hl
  | [x], _ => ⟨x, List.mem_cons_self .., rfl⟩
  | x :: y :: rest, _ => by
    obtain ⟨b, hb, hfb⟩ := listMin_exists f (y :: rest) (List.cons_ne_nil _ _)
    simp only [listMin]
    rcases le_total (f x) (listMin f (y :: rest) (List.cons_ne_nil _ _)) with h | h
    · exact ⟨x, List.mem_cons_self .., (min_eq_left h).symm⟩
    · exact ⟨b, List.mem_cons_of_mem _ hb, hfb.trans (min_eq_right h).symm⟩

lemma listMin_mono {α : Type*} {f g : α → ℝ} (hfg : ∀ a, f a ≤ g a)
    (l : List α) (hl : l ≠ []) : listMin f l hl ≤ listMin g l hl :=
  le_listMin g _ l hl fun a ha => (listMin_le f l hl ha).trans (hfg a)

lemma listMin_add_const {α : Type*} (f : α → ℝ) (c : ℝ) :
    ∀ (l : List α) (hl : l ≠ []), listMin (fun a => f a + c) l hl = listMin f l hl + c
  | [_], _ => rfl
  | _ :: y :: rest, _ => by
    simp only [listMin, listMin_add_const f c (y :: rest) (List.cons_ne_nil _ _), min_add_add_right]

/-- Concavity of `listMin`: sum of minima ≤ minimum of sums. -/
lemma sum_listMin_le {ι α : Type*} (s : Finset ι) (f : ι → α → ℝ)
    (l : List α) (hl : l ≠ []) :
    ∑ i ∈ s, listMin (f i) l hl ≤ listMin (fun a => ∑ i ∈ s, f i a) l hl :=
  le_listMin _ _ l hl fun _ ha => Finset.sum_le_sum fun i _ => listMin_le (f i) l hl ha

/-- Step cost under an edge cost table `edgeCost`. -/
def chosenTableCost {d₁ G B : ℕ}
    (edgeCost : Fin (d₁ + 1) → (Fin (d₁ + 1) → Fin G) → (Fin (d₁ + 2) → Fin B) → ℝ)
    (chosen : List (Fin (d₁ + 1))) (gs : Fin (d₁ + 1) → Fin G) (ys : Fin (d₁ + 2) → Fin B) : ℝ :=
  (chosen.map fun v => edgeCost v gs ys).sum

/-- Total table cost of a fixed walk `(states, choices)` of length `k` on `(z₀, w)`. -/
def walkTableCost {d₁ G B : ℕ}
    (edgeCost : Fin (d₁ + 1) → (Fin (d₁ + 1) → Fin G) → (Fin (d₁ + 2) → Fin B) → ℝ) :
    ∀ {k : ℕ}, Window d₁ G B → (Fin k → Label G B) → (Fin k → List (Fin (d₁ + 1))) → ℝ
  | 0, _, _, _ => 0
  | _ + 1, z₀, w, ch =>
    let w' := fun i => w i.castSucc
    let z := runWindow z₀ w'
    let x := w (Fin.last _)
    walkTableCost edgeCost z₀ w' (fun i => ch i.castSucc) +
      chosenTableCost edgeCost (ch (Fin.last _)) (fullGaps z x) (fullHeights z x)

/-- Optimal DP cost after `AG.reachSteps + m` arrivals, initialized at `m = 0` via `AG.reachWalk`. -/
noncomputable def optDP {d₁ U G B : ℕ} (AG : AutomatonGraph d₁ U)
    (edgeCost : Fin (d₁ + 1) → (Fin (d₁ + 1) → Fin G) → (Fin (d₁ + 2) → Fin B) → ℝ) :
    ∀ (m : ℕ), Window d₁ G B → (Fin (AG.reachSteps + m) → Label G B) → Fin U → ℝ
  | 0, z₀, w, u =>
    let ch := (AG.reachWalk u).choose_spec.choose
    walkTableCost edgeCost z₀ w ch
  | m + 1, z₀, w, u' =>
    let w' : Fin (AG.reachSteps + m) → Label G B := fun i => w i.castSucc
    let z := runWindow z₀ w'
    let x := w (Fin.last _)
    listMin (fun p =>
      optDP AG edgeCost m z₀ w' p.1 +
        chosenTableCost edgeCost p.2 (fullGaps z x) (fullHeights z x))
      (AG.preds u') (AG.preds_ne u')

/-- Every value of `optDP AG edgeCost m z₀ w u` is achieved by an actual valid automaton walk
from `AG.initIdx` to `u` of length `AG.reachSteps + m`. -/
theorem optDP_achieved {d₁ U G B : ℕ} (AG : AutomatonGraph d₁ U)
    (edgeCost : Fin (d₁ + 1) → (Fin (d₁ + 1) → Fin G) → (Fin (d₁ + 2) → Fin B) → ℝ) :
    ∀ (m : ℕ) (z₀ : Window d₁ G B) (w : Fin (AG.reachSteps + m) → Label G B) (u : Fin U),
      ∃ (states : Fin (AG.reachSteps + m + 1) → Fin U)
        (choices : Fin (AG.reachSteps + m) → List (Fin (d₁ + 1))),
        states 0 = AG.initIdx ∧
        states (Fin.last _) = u ∧
        (∀ t : Fin (AG.reachSteps + m), (states t.castSucc, choices t) ∈ AG.preds (states t.succ)) ∧
        walkTableCost edgeCost z₀ w choices = optDP AG edgeCost m z₀ w u
  | 0, z₀, w, u => by
    refine ⟨(AG.reachWalk u).choose, (AG.reachWalk u).choose_spec.choose, ?_, ?_, ?_, rfl⟩
    · exact (AG.reachWalk u).choose_spec.choose_spec.1
    · exact (AG.reachWalk u).choose_spec.choose_spec.2.1
    · exact (AG.reachWalk u).choose_spec.choose_spec.2.2
  | m + 1, z₀, w, u' => by
    let w' : Fin (AG.reachSteps + m) → Label G B := fun i => w i.castSucc
    let z := runWindow z₀ w'
    let x := w (Fin.last _)
    obtain ⟨p, hp_mem, hp_eq⟩ := listMin_exists
      (fun p => optDP AG edgeCost m z₀ w' p.1 +
        chosenTableCost edgeCost p.2 (fullGaps z x) (fullHeights z x))
      (AG.preds u') (AG.preds_ne u')
    obtain ⟨st, ch, hst0, hst_last, hst_step, hcost⟩ := optDP_achieved AG edgeCost m z₀ w' p.1
    let st' : Fin (AG.reachSteps + m + 1 + 1) → Fin U := snocND st u'
    let ch' : Fin (AG.reachSteps + m + 1) → List (Fin (d₁ + 1)) := snocND ch p.2
    refine ⟨st', ch', ?_, ?_, ?_, ?_⟩
    · have h0 : (0 : Fin (AG.reachSteps + m + 1 + 1)) = (0 : Fin (AG.reachSteps + m + 1)).castSucc :=
        Fin.ext rfl
      rw [h0]; simp only [st', snocND_castSucc]; exact hst0
    · exact snocND_last st u'
    · intro t
      refine Fin.lastCases ?_ ?_ t
      · have h2 : (Fin.last (AG.reachSteps + m)).succ = Fin.last (AG.reachSteps + m + 1) := Fin.ext (by simp)
        change (snocND st u' (Fin.last (AG.reachSteps + m)).castSucc,
                snocND ch p.2 (Fin.last (AG.reachSteps + m))) ∈
          AG.preds (snocND st u' (Fin.last (AG.reachSteps + m)).succ)
        rw [h2, snocND_castSucc, snocND_last, snocND_last, hst_last]
        exact hp_mem
      · intro j
        have h1 : st' j.castSucc.castSucc = st j.castSucc := snocND_castSucc st u' j.castSucc
        have h2 : j.castSucc.succ = j.succ.castSucc := Fin.ext (by simp)
        have h3 : st' j.castSucc.succ = st j.succ := by rw [h2]; exact snocND_castSucc st u' j.succ
        have h4 : ch' j.castSucc = ch j := snocND_castSucc ch p.2 j
        rw [h1, h3, h4]
        exact hst_step j
    · dsimp only [walkTableCost, optDP]
      have hch' : (fun i : Fin (AG.reachSteps + m) => ch' i.castSucc) = ch :=
        funext fun i => snocND_castSucc ch p.2 i
      have hch_last : ch' (Fin.last (AG.reachSteps + m)) = p.2 := snocND_last ch p.2
      change walkTableCost edgeCost z₀ w' (fun i : Fin (AG.reachSteps + m) => ch' i.castSucc) +
          chosenTableCost edgeCost (ch' (Fin.last (AG.reachSteps + m))) (fullGaps z x) (fullHeights z x) = _
      rw [hch', hch_last, hcost]
      exact hp_eq

/-- Concave DP operator `T V u' z'`, averaging over forgotten oldest labels `old : Label G B`. -/
noncomputable def dpOp {d₁ U G B : ℕ} (AG : AutomatonGraph d₁ U)
    (edgeCost : Fin (d₁ + 1) → (Fin (d₁ + 1) → Fin G) → (Fin (d₁ + 2) → Fin B) → ℝ)
    (V : Fin U → Window d₁ G B → ℝ) (u' : Fin U) (z' : Window d₁ G B) : ℝ :=
  (∑ old : Label G B,
    listMin (fun p =>
      V p.1 (prevWindow old z') +
        chosenTableCost edgeCost p.2 (fullGapsOf old z') (fullHeightsOf old z'))
      (AG.preds u') (AG.preds_ne u')) / ((G * B : ℕ) : ℝ)

/-- Pairs `(z₀, w)` of length `k` whose final window equals `z'`. -/
def wordsEndingAt {d₁ G B : ℕ} (k : ℕ) (z' : Window d₁ G B) :
    Finset (Window d₁ G B × (Fin k → Label G B)) :=
  Finset.univ.filter fun p => runWindow p.1 p.2 = z'

/-- Exact bijection decomposing length-(k+1) words ending at `z'` by their forgotten oldest label. -/
def wordsEndingAtEquiv {d₁ G B : ℕ} (hd : 0 < d₁) (k : ℕ) (z' : Window d₁ G B) :
    (Σ old : Label G B, {p // p ∈ wordsEndingAt k (prevWindow old z')}) ≃
      {p // p ∈ wordsEndingAt (k + 1) z'} where
  toFun := fun ⟨old, ⟨⟨z₀, w'⟩, hw'⟩⟩ =>
    ⟨(z₀, snocND w' (newestLabel hd z')), by
      simp only [wordsEndingAt, Finset.mem_filter, Finset.mem_univ, true_and] at hw' ⊢
      unfold runWindow
      have h1 : (fun i : Fin k => snocND w' (newestLabel hd z') i.castSucc) = w' :=
        funext fun i => snocND_castSucc w' _ i
      rw [h1, snocND_last, hw', advance_prevWindow hd old z']⟩
  invFun := fun ⟨⟨z₀, w⟩, hw⟩ =>
    let w' : Fin k → Label G B := fun i => w i.castSucc
    let z := runWindow z₀ w'
    ⟨oldestLabel hd z, ⟨(z₀, w'), by
      simp only [wordsEndingAt, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      unfold runWindow at hw
      rw [← hw, prevWindow_advance hd z (w (Fin.last k))]⟩⟩
  left_inv := fun ⟨old, ⟨⟨z₀, w'⟩, hw'⟩⟩ => by
    dsimp only
    simp only [wordsEndingAt, Finset.mem_filter, Finset.mem_univ, true_and] at hw'
    have h1 : (fun i : Fin k => snocND w' (newestLabel hd z') i.castSucc) = w' :=
      funext fun i => snocND_castSucc w' _ i
    have hold : oldestLabel hd (runWindow z₀ (fun i : Fin k => snocND w' (newestLabel hd z') i.castSucc)) = old := by
      rw [h1, hw', oldest_prevWindow hd old z']
    refine Sigma.ext hold ?_
    exact (Subtype.heq_iff_coe_eq (fun _ => by
      dsimp only
      rw [hold])).mpr (Prod.ext rfl h1)
  right_inv := fun ⟨⟨z₀, w⟩, hw⟩ => by
    dsimp only
    simp only [wordsEndingAt, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    unfold runWindow at hw
    apply Subtype.ext
    dsimp only
    refine Prod.ext rfl (funext fun i => ?_)
    refine Fin.lastCases ?_ ?_ i
    · simp only [snocND_last]
      rw [← hw, newestLabel_advance hd]
    · intro j; simp [snocND_castSucc]

lemma card_wordsEndingAt {d₁ G B : ℕ} (hd : 0 < d₁) :
    ∀ (k : ℕ) (z' : Window d₁ G B), (wordsEndingAt k z').card = (G * B) ^ k
  | 0, z' => by
    have heq : wordsEndingAt 0 z' = {(z', Fin.elim0)} := by
      ext ⟨z₀, w⟩
      simp only [wordsEndingAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Prod.mk.injEq, runWindow]
      exact ⟨fun h => ⟨h, funext fun i => i.elim0⟩, fun h => h.1⟩
    rw [heq, Finset.card_singleton, pow_zero]
  | k + 1, z' => by
    have hcard := Fintype.card_congr (wordsEndingAtEquiv (G := G) (B := B) hd k z')
    simp only [Fintype.card_coe, Fintype.card_sigma] at hcard
    rw [← hcard]
    have hsum : ∑ old : Label G B, (wordsEndingAt k (prevWindow old z')).card =
        ∑ _ : Label G B, (G * B) ^ k :=
      Finset.sum_congr rfl fun old _ => card_wordsEndingAt hd k (prevWindow old z')
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
        smul_eq_mul, pow_succ']

lemma sum_wordsEndingAt_succ {d₁ G B : ℕ} (hd : 0 < d₁) (k : ℕ) (z' : Window d₁ G B)
    (f : Window d₁ G B × (Fin (k + 1) → Label G B) → ℝ) :
    ∑ p ∈ wordsEndingAt (k + 1) z', f p =
      ∑ old : Label G B, ∑ q ∈ wordsEndingAt k (prevWindow old z'),
        f (q.1, snocND q.2 (newestLabel hd z')) := by
  let e := wordsEndingAtEquiv (G := G) (B := B) hd k z'
  rw [← Finset.sum_attach (wordsEndingAt (k + 1) z') f]
  have hbij := Fintype.sum_equiv e (fun s => f (e s).1) (fun x => f x.1) (fun _ => rfl)
  change ∑ x : {p // p ∈ wordsEndingAt (k + 1) z'}, f x.1 = _
  rw [← hbij, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro old _
  rw [← Finset.sum_attach (wordsEndingAt k (prevWindow old z'))
    (fun q => f (q.1, snocND q.2 (newestLabel hd z')))]
  rfl

/-- **Main Concave DP Fixed-Point Theorem (Conditional Form):**
If `dpOp AG edgeCost V u' z' ≤ V u' z' + uBound` for all `u', z'`, and the base `m = 0`
average is bounded by `V u z' + C₀`, then for ALL `m : ℕ` and ALL `u', z'`, the conditional
average of `optDP AG edgeCost m` given final window `z'` is at most
`V u' z' + m * uBound + C₀`. -/
theorem concave_dp_conditional_bound {d₁ U G B : ℕ} (hd : 0 < d₁) (hG : 0 < G) (hB : 0 < B)
    (AG : AutomatonGraph d₁ U)
    (edgeCost : Fin (d₁ + 1) → (Fin (d₁ + 1) → Fin G) → (Fin (d₁ + 2) → Fin B) → ℝ)
    (V : Fin U → Window d₁ G B → ℝ) (uBound C₀ : ℝ)
    (hfp : ∀ u' z', dpOp AG edgeCost V u' z' ≤ V u' z' + uBound)
    (hbase : ∀ u z',
      (∑ p ∈ wordsEndingAt AG.reachSteps z', optDP AG edgeCost 0 p.1 p.2 u) /
        (((G * B) ^ AG.reachSteps : ℕ) : ℝ) ≤ V u z' + C₀) :
    ∀ (m : ℕ) (u' : Fin U) (z' : Window d₁ G B),
      (∑ p ∈ wordsEndingAt (AG.reachSteps + m) z', optDP AG edgeCost m p.1 p.2 u') /
        (((G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ) ≤ V u' z' + (m : ℝ) * uBound + C₀ := by
  have hGB_pos : (0 : ℝ) < ((G * B : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hG hB
  intro m
  induction m with
  | zero =>
    intro u' z'
    simpa using hbase u' z'
  | succ m ih =>
    intro u' z'
    have hpow_pos : (0 : ℝ) < (((G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ) := by positivity
    have hpow_succ : (((G * B) ^ (AG.reachSteps + (m + 1)) : ℕ) : ℝ) =
        (((G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ) * ((G * B : ℕ) : ℝ) := by
      rw [← Nat.add_assoc, pow_succ]; push_cast; ring
    have hsplit := sum_wordsEndingAt_succ hd (AG.reachSteps + m) z'
      (fun p => optDP AG edgeCost (m + 1) p.1 p.2 u')
    change (∑ p ∈ wordsEndingAt ((AG.reachSteps + m) + 1) z', optDP AG edgeCost (m + 1) p.1 p.2 u') /
        (((G * B) ^ (AG.reachSteps + (m + 1)) : ℕ) : ℝ) ≤ _
    rw [hsplit]
    have hstep_old : ∀ old : Label G B,
        (∑ q ∈ wordsEndingAt (AG.reachSteps + m) (prevWindow old z'),
          optDP AG edgeCost (m + 1) q.1 (snocND q.2 (newestLabel hd z')) u') /
            (((G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ) ≤
          listMin (fun p =>
            V p.1 (prevWindow old z') +
              chosenTableCost edgeCost p.2 (fullGapsOf old z') (fullHeightsOf old z'))
            (AG.preds u') (AG.preds_ne u') + ((m : ℝ) * uBound + C₀) := by
      intro old
      have heq_sum :
          ∑ q ∈ wordsEndingAt (AG.reachSteps + m) (prevWindow old z'),
            optDP AG edgeCost (m + 1) q.1 (snocND q.2 (newestLabel hd z')) u' =
          ∑ q ∈ wordsEndingAt (AG.reachSteps + m) (prevWindow old z'),
            listMin (fun p =>
              optDP AG edgeCost m q.1 q.2 p.1 +
                chosenTableCost edgeCost p.2 (fullGapsOf old z') (fullHeightsOf old z'))
              (AG.preds u') (AG.preds_ne u') := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [wordsEndingAt, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        dsimp only [optDP]
        have h1 : (fun i : Fin (AG.reachSteps + m) => snocND q.2 (newestLabel hd z') i.castSucc) = q.2 :=
          funext fun i => snocND_castSucc q.2 _ i
        simp only [h1, snocND_last, hq, fullGaps_eq_fullGapsOf hd old z',
          fullHeights_eq_fullHeightsOf hd old z']
      rw [heq_sum, div_le_iff₀ hpow_pos]
      have hconc := sum_listMin_le (wordsEndingAt (AG.reachSteps + m) (prevWindow old z'))
        (fun q p => optDP AG edgeCost m q.1 q.2 p.1 +
          chosenTableCost edgeCost p.2 (fullGapsOf old z') (fullHeightsOf old z'))
        (AG.preds u') (AG.preds_ne u')
      refine hconc.trans ?_
      rw [← listMin_add_const]
      have hcard := card_wordsEndingAt (G := G) (B := B) hd (AG.reachSteps + m) (prevWindow old z')
      refine (listMin_mono
        (f := fun p => ∑ q ∈ wordsEndingAt (AG.reachSteps + m) (prevWindow old z'),
          (optDP AG edgeCost m q.1 q.2 p.1 +
            chosenTableCost edgeCost p.2 (fullGapsOf old z') (fullHeightsOf old z')))
        (g := fun p => (V p.1 (prevWindow old z') +
            chosenTableCost edgeCost p.2 (fullGapsOf old z') (fullHeightsOf old z') +
            ((m : ℝ) * uBound + C₀)) * (((G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ))
        (fun p => by
          rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
          have hih := (div_le_iff₀ hpow_pos).mp (ih p.1 (prevWindow old z'))
          linarith)
        (AG.preds u') (AG.preds_ne u')).trans ?_
      obtain ⟨a, ha, hfa⟩ := listMin_exists
        (fun p => V p.1 (prevWindow old z') +
          chosenTableCost edgeCost p.2 (fullGapsOf old z') (fullHeightsOf old z') +
          ((m : ℝ) * uBound + C₀))
        (AG.preds u') (AG.preds_ne u')
      rw [← hfa]
      exact listMin_le _ (AG.preds u') (AG.preds_ne u') ha
    have hsum_old := Finset.sum_le_sum (s := (Finset.univ : Finset (Label G B))) fun old _ => hstep_old old
    rw [← Finset.sum_div] at hsum_old
    have hdiv_all :
        (∑ old : Label G B, ∑ q ∈ wordsEndingAt (AG.reachSteps + m) (prevWindow old z'),
          optDP AG edgeCost (m + 1) q.1 (snocND q.2 (newestLabel hd z')) u') /
            (((G * B) ^ (AG.reachSteps + (m + 1)) : ℕ) : ℝ) ≤
        dpOp AG edgeCost V u' z' + ((m : ℝ) * uBound + C₀) := by
      rw [hpow_succ, ← div_div, div_le_iff₀ hGB_pos]
      refine hsum_old.trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
      unfold dpOp
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hGB_pos)]
      push_cast; ring_nf; exact le_rfl
    have hfp' := hfp u' z'
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith

/-- **Unconditional Average Bound:** Averaging uniformly over ALL `(z₀, w)` of length `AG.reachSteps + m`
gives at most `m * uBound + avg_z V(u', z) + C₀`. -/
theorem concave_dp_total_bound {d₁ U G B : ℕ} (hd : 0 < d₁) (hG : 0 < G) (hB : 0 < B)
    (AG : AutomatonGraph d₁ U)
    (edgeCost : Fin (d₁ + 1) → (Fin (d₁ + 1) → Fin G) → (Fin (d₁ + 2) → Fin B) → ℝ)
    (V : Fin U → Window d₁ G B → ℝ) (uBound C₀ : ℝ)
    (hfp : ∀ u' z', dpOp AG edgeCost V u' z' ≤ V u' z' + uBound)
    (hbase : ∀ u z',
      (∑ p ∈ wordsEndingAt AG.reachSteps z', optDP AG edgeCost 0 p.1 p.2 u) /
        (((G * B) ^ AG.reachSteps : ℕ) : ℝ) ≤ V u z' + C₀)
    (m : ℕ) (u' : Fin U) :
    (∑ p : Window d₁ G B × (Fin (AG.reachSteps + m) → Label G B),
      optDP AG edgeCost m p.1 p.2 u') /
        ((Fintype.card (Window d₁ G B) * (G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ) ≤
      (∑ z' : Window d₁ G B, V u' z') / (Fintype.card (Window d₁ G B) : ℝ) +
        (m : ℝ) * uBound + C₀ := by
  have hW_pos : (0 : ℝ) < (Fintype.card (Window d₁ G B) : ℝ) := by
    have : 0 < Fintype.card (Window d₁ G B) := by
      simp [Window, Fintype.card_prod, Fintype.card_pi, hG, hB]
    exact_mod_cast this
  have hpow_pos : (0 : ℝ) < (((G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ) := by
    have : 0 < G * B := Nat.mul_pos hG hB
    positivity
  have hpart :
      ∑ p : Window d₁ G B × (Fin (AG.reachSteps + m) → Label G B),
        optDP AG edgeCost m p.1 p.2 u' =
      ∑ z' : Window d₁ G B,
        ∑ p ∈ wordsEndingAt (AG.reachSteps + m) z', optDP AG edgeCost m p.1 p.2 u' := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => runWindow p.1 p.2)
      (fun _ _ => Finset.mem_univ _)]
    rfl
  rw [hpart]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Window d₁ G B))) fun z' _ =>
    concave_dp_conditional_bound hd hG hB AG edgeCost V uBound C₀ hfp hbase m u' z'
  rw [← Finset.sum_div] at hsum
  have hden : ((Fintype.card (Window d₁ G B) * (G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ) =
      (((G * B) ^ (AG.reachSteps + m) : ℕ) : ℝ) * (Fintype.card (Window d₁ G B) : ℝ) := by
    push_cast; ring
  rw [hden, ← div_div, div_le_iff₀ hW_pos]
  refine hsum.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  rw [add_mul, add_mul, div_mul_cancel₀ _ (ne_of_gt hW_pos)]
  linarith

end BHHBounds.Upper
