/-
Running a plan: after `runPlan`, every slot holds the least cost of its paths, and the sum of the
slots `C a b` is the sum of the minima over all orders (`configSum_abs`).
-/
import TSPBound.Correct.Steps

namespace Correct
open Spec Impl

/-! ## The least of the sums of a compiled list of terms -/

theorem foldl_min_eq_minOf (l : List Nat) (z : Nat) :
    l.foldl (fun b x => min b x) z = minOf (z :: l) := by
  induction l generalizing z with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    cases l with
    | nil => simp [minOf]
    | cons w l => simp only [minOf]; rw [Nat.min_assoc]

/-- The positions `[x_0, y_0, x_1, y_1, …]` of a list of pairs. -/
def flat (ps : List (Nat × Nat)) : List Nat := ps.flatMap (fun xy => [xy.1, xy.2])

theorem length_flat (ps : List (Nat × Nat)) : (flat ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons xy ps ih => simp [flat] at ih ⊢; omega

theorem minTermsGo_eq (val : Array Nat) (ps : List (Nat × Nat)) (pre : List Nat) (best : Nat) :
    minTermsGo val (pre ++ flat ps).toArray ps.length pre.length best
      = (ps.map (fun xy => val.getD xy.1 0 + val.getD xy.2 0)).foldl (fun b x => min b x) best := by
  induction ps generalizing pre best with
  | nil => rfl
  | cons xy ps ih =>
    have h1 : (pre ++ flat (xy :: ps)).toArray.getD pre.length 0 = xy.1 := by
      simp [flat, Array.getD_eq_getD_getElem?]
    have h2 : (pre ++ flat (xy :: ps)).toArray.getD (pre.length + 1) 0 = xy.2 := by
      simp [flat, Array.getD_eq_getD_getElem?]
    have h3 : pre ++ flat (xy :: ps) = (pre ++ [xy.1, xy.2]) ++ flat ps := by simp [flat]
    simp only [List.length_cons, minTermsGo, h1, h2, List.map_cons, List.foldl_cons]
    rw [h3]
    have := ih (pre ++ [xy.1, xy.2]) (min best (val.getD xy.1 0 + val.getD xy.2 0))
    simpa using this

theorem minTerms_eq (val : Array Nat) (ps : List (Nat × Nat)) (hne : ps ≠ []) :
    minTerms val (flat ps).toArray = minOf (ps.map (fun xy => val.getD xy.1 0 + val.getD xy.2 0)) := by
  cases ps with
  | nil => exact absurd rfl hne
  | cons xy ps =>
    have h0 : (flat (xy :: ps)).toArray.getD 0 0 = xy.1 := by simp [flat, Array.getD_eq_getD_getElem?]
    have h1 : (flat (xy :: ps)).toArray.getD 1 0 = xy.2 := by simp [flat, Array.getD_eq_getD_getElem?]
    have hsize : (flat (xy :: ps)).toArray.size / 2 - 1 = ps.length := by
      simp only [List.size_toArray, length_flat, List.length_cons]; omega
    have h3 : flat (xy :: ps) = [xy.1, xy.2] ++ flat ps := by simp [flat]
    unfold minTerms
    rw [h0, h1, hsize, h3]
    have := minTermsGo_eq val ps [xy.1, xy.2] (val.getD xy.1 0 + val.getD xy.2 0)
    simp only [List.length_cons, List.length_nil] at this
    rw [this, foldl_min_eq_minOf]
    rfl

theorem compileTerms_eq (slots : List Slot) (ts : List (Slot × Slot)) :
    compileTerms slots ts = (flat (ts.map (fun ab => (slots.idxOf ab.1, slots.idxOf ab.2)))).toArray := by
  simp [compileTerms, flat, List.flatMap_map]

theorem minTerms_compile (val : Array Nat) (slots : List Slot) (ts : List (Slot × Slot)) (hne : ts ≠ []) :
    minTerms val (compileTerms slots ts)
      = minOf (ts.map (fun ab => val.getD (slots.idxOf ab.1) 0 + val.getD (slots.idxOf ab.2) 0)) := by
  rw [compileTerms_eq, minTerms_eq _ _ (fun h => hne (List.map_eq_nil_iff.mp h)), List.map_map]
  rfl

/-! ## The invariant of `runPlan` -/

theorem getElem_idxOf (l : List Slot) (a : Slot) (h : l.idxOf a < l.length) : l[l.idxOf a] = a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb; simp
    · have h1 : (b :: l).idxOf a = l.idxOf a + 1 := by
        have hba : (b == a) = false := beq_eq_false_iff_ne.mpr hb
        rw [List.idxOf_cons, hba]; rfl
      have h2 : l.idxOf a < l.length := by rw [h1] at h; simpa using h
      simp only [h1, List.getElem_cons_succ]
      exact ih h2

theorem getElem_of_prefix {l pre rest : List Slot} (hs : l = pre ++ rest) (i : Nat)
    (hi : i < pre.length) (hl : i < l.length) : l[i] = pre[i] := by
  subst hs; exact List.getElem_append_left hi

theorem getD_push_lt (val : Array Nat) (x i : Nat) (h : i < val.size) :
    (val.push x).getD i 0 = val.getD i 0 := by
  have hne : i ≠ val.size := Nat.ne_of_lt h
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hne]

theorem getD_push_eq (val : Array Nat) (x : Nat) : (val.push x).getD val.size 0 = x := by
  simp [Array.getD_eq_getD_getElem?]

theorem array_foldl_toArray {α β : Type} (f : β → α → β) (init : β) (l : List α) :
    l.toArray.foldl f init = l.foldl f init := by
  simp

theorem run_good (k : Nat) (hk : 2 ≤ k) (ein st en : Nat → Nat → Nat)
    (hsym : ∀ x y, ein x y = ein y x) (slots : List Slot) :
    ∀ (tgs pre : List Slot) (val : Array Nat), slots = pre ++ tgs →
      checkFrom k slots tgs pre.length = true →
      val.size = pre.length →
      (∀ i (h : i < pre.length), Good k ein st en pre[i] (val.getD i 0)) →
      (tgs.foldl (fun val s => val.push (minTerms val (compileTerms slots (terms k s)))) val).size
          = slots.length ∧
        ∀ i (h : i < slots.length), Good k ein st en slots[i]
          ((tgs.foldl (fun val s => val.push (minTerms val (compileTerms slots (terms k s)))) val).getD i 0) := by
  intro tgs
  induction tgs with
  | nil =>
    intro pre val hs _ hsize hgood
    simp only [List.append_nil] at hs
    subst hs
    exact ⟨hsize, hgood⟩
  | cons s rest ih =>
    intro pre val hs hcheck hsize hgood
    simp only [checkFrom, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨⟨hvalid, hne⟩, hidx⟩, hrest⟩ := hcheck
    have hne' : terms k s ≠ [] := by
      intro h; simp [h] at hne
    -- the numbers of the terms are good
    have hv : ∀ ab ∈ terms k s,
        Good k ein st en ab.1 (val.getD (slots.idxOf ab.1) 0) ∧
        Good k ein st en ab.2 (val.getD (slots.idxOf ab.2) 0) := by
      intro ab hab
      have h12 := hidx ab hab
      have key : ∀ a : Slot, slots.idxOf a < pre.length → Good k ein st en a (val.getD (slots.idxOf a) 0) := by
        intro a ha
        have hlen : slots.length = pre.length + (s :: rest).length := by rw [hs, List.length_append]
        have hlt : slots.idxOf a < slots.length := by omega
        have h1 := getElem_idxOf slots a hlt
        have h2 : slots[slots.idxOf a] = pre[slots.idxOf a] := getElem_of_prefix hs _ ha hlt
        have h3 := hgood (slots.idxOf a) ha
        rw [← h2, h1] at h3
        exact h3
      exact ⟨key ab.1 h12.1, key ab.2 h12.2⟩
    have hstep := good_step k hk ein st en hsym s (fun a => val.getD (slots.idxOf a) 0) hvalid hne' hv
    rw [← minTerms_compile val slots (terms k s) hne'] at hstep
    -- continue with one more slot
    simp only [List.foldl_cons]
    apply ih (pre ++ [s]) (val.push (minTerms val (compileTerms slots (terms k s))))
    · rw [hs]; simp
    · simpa using hrest
    · simp [hsize]
    · intro i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      by_cases hlt : i < pre.length
      · have h1 : (pre ++ [s])[i] = pre[i] := List.getElem_append_left hlt
        have h2 : (val.push (minTerms val (compileTerms slots (terms k s)))).getD i 0 = val.getD i 0 :=
          getD_push_lt val _ i (by omega)
        rw [h1, h2]; exact hgood i hlt
      · have hi' : i = pre.length := by omega
        subst hi'
        have h1 : (pre ++ [s])[pre.length] = s := by simp
        have h2 : (val.push (minTerms val (compileTerms slots (terms k s)))).getD pre.length 0
            = minTerms val (compileTerms slots (terms k s)) := by
          rw [← hsize]; exact getD_push_eq val _
        rw [h1, h2]; exact hstep

/-! ## The sum of the slots `C a b` -/

/-- The cost of a block for the heights `a` and `b` of its end points: the minimum over all orders of
the interior points. -/
def costC (k : Nat) (ein st en : Nat → Nat → Nat) (a b : Nat) : Nat :=
  minOf ((orders (interior k)).map
    (fun π => st a (π.headD 0) + pathLen ein π + en b (π.getLastD 0)))

theorem good_costC (k : Nat) (ein st en : Nat → Nat → Nat) (a b : Nat) :
    Good k ein st en (.C a b) (costC k ein st en a b) := by
  have hne : (orders (interior k)).map
      (fun π => st a (π.headD 0) + pathLen ein π + en b (π.getLastD 0)) ≠ [] := by
    have : interior k ∈ orders (interior k) := mem_orders.mpr (List.Perm.refl _)
    intro h
    simp only [List.map_eq_nil_iff] at h
    rw [h] at this; simp at this
  obtain ⟨hmem, hle⟩ := minOf_spec _ hne
  constructor
  · obtain ⟨π, hπ, heq⟩ := List.mem_map.mp hmem
    exact ⟨π, mem_orders.mp hπ, heq⟩
  · intro π hπ
    exact hle _ (List.mem_map.mpr ⟨π, mem_orders.mpr hπ, rfl⟩)

theorem foldl_add_eq_sum {α : Type} (l : List α) (f : α → Nat) (z : Nat) :
    l.foldl (fun acc x => acc + f x) z = z + (l.map f).sum := by
  induction l generalizing z with
  | nil => simp
  | cons x l ih => simp [ih]; omega

theorem sum_outSlots (n : Nat) (f : Slot → Nat) :
    ((outSlots n).map f).sum = ∑ a < n, ∑ b < n, f (.C a b) := by
  have h1 : ∀ (a : Nat), (((List.range n).map (fun b => Slot.C a b)).map f).sum = ∑ b < n, f (.C a b) := by
    intro a; rw [sum_eq_list, List.map_map]; rfl
  have h2 : ∀ (cnt : Nat) (L : Nat → List Slot),
      (((List.range cnt).flatMap L).map f).sum = ∑ a < cnt, ((L a).map f).sum := by
    intro cnt L
    induction cnt with
    | zero => rfl
    | succ c ih => simp [List.range_succ, Spec.sum, ih]
  unfold outSlots
  rw [h2]
  exact sum_congr (fun a _ => h1 a)

/-- The result of running the plan on the values of the input slots. -/
theorem configSum_abs (k n : Nat) (hok : (mkPlan k n).ok = true) (ein st en : Nat → Nat → Nat)
    (hsym : ∀ x y, ein x y = ein y x) (val0 : Array Nat)
    (hval0 : val0 = ((inputSlots k n).map (inputValA ein st en)).toArray) :
    (mkPlan k n).out.foldl (fun acc i => acc + (runPlan (mkPlan k n).prog val0).getD i 0) 0
      = ∑ a < n, ∑ b < n, costC k ein st en a b := by
  simp only [mkPlan, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨hk, hin⟩, hcheck⟩, hout⟩ := hok
  have hrun := run_good k hk ein st en hsym (inputSlots k n ++ targetSlots k n)
    (targetSlots k n) (inputSlots k n) val0 rfl hcheck (by simp [hval0])
    (by
      intro i hi
      have h1 : val0.getD i 0 = inputValA ein st en (inputSlots k n)[i] := by
        simp [hval0, Array.getD_eq_getD_getElem?, hi]
      rw [h1]
      exact good_input k n ein st en _ (hin _ (List.getElem_mem hi)))
  obtain ⟨_, hgood⟩ := hrun
  have hprog : (mkPlan k n).prog = ((targetSlots k n).map
      (fun s => compileTerms (inputSlots k n ++ targetSlots k n) (terms k s))).toArray := rfl
  have hout' : (mkPlan k n).out = ((outSlots n).map
      (fun s => (inputSlots k n ++ targetSlots k n).idxOf s)).toArray := rfl
  rw [hprog, hout']
  unfold runPlan
  rw [array_foldl_toArray, array_foldl_toArray, List.foldl_map, List.foldl_map]
  rw [foldl_add_eq_sum, Nat.zero_add, ← sum_outSlots n (fun s => match s with
    | .C a b => costC k ein st en a b
    | _ => 0)]
  congr 1
  apply List.map_congr_left
  intro s hs
  have hlt := hout s hs
  have h1 := hgood _ hlt
  rw [getElem_idxOf _ _ hlt] at h1
  simp only [outSlots, List.mem_flatMap, List.mem_map, List.mem_range] at hs
  obtain ⟨a, _, b, _, rfl⟩ := hs
  exact good_unique h1 (good_costC k ein st en a b)

end Correct
