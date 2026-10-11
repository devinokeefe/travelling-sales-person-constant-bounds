/-
The cell sums by units of gap tuples with the same interior gaps (`Impl/Shared.lean`) are the cell
sums of the recipe (`sharedSums_eq`), and `AofShared` gives the values `A_j` of Section 8
(`AofShared_eq`).

What is new against `Correct/CellSum.lean` and `Correct/Sym.lean`:

* the edges between interior points do not depend on the first and the last gap, the edges at the
  point 0 not on the last gap, the edges at the point `k` not on the first gap (`keyOf_mid`,
  `keyOf_first`, `keyOf_last`);
* the plan for the slots `A` and `H` alone keeps the invariant of `run_good` (`planH_good`);
* the direct loops for `L` and `C` compute the least of the sums over the terms of these slots
  (`lVal_good`, `cVal_eq`), so that `good_L` and `good_C` of `Correct/Steps.lean` apply.
-/
import TSPShared.Impl
import TSPBound.Correct.Sym

namespace Correct
open Spec Impl

/-! ## Loops -/

theorem minLoop_le_best (f : Nat → Nat) (cnt i best : Nat) : minLoop f cnt i best ≤ best := by
  induction cnt generalizing i best with
  | zero => exact Nat.le_refl _
  | succ cnt ih => exact Nat.le_trans (ih _ _) (Nat.min_le_left _ _)

theorem minLoop_le (f : Nat → Nat) (cnt i best j : Nat) (h1 : i ≤ j) (h2 : j < i + cnt) :
    minLoop f cnt i best ≤ f j := by
  induction cnt generalizing i best with
  | zero => omega
  | succ cnt ih =>
    simp only [minLoop]
    by_cases hij : j = i
    · subst hij; exact Nat.le_trans (minLoop_le_best _ _ _ _) (Nat.min_le_right _ _)
    · exact ih _ _ (by omega) (by omega)

theorem minLoop_mem (f : Nat → Nat) (cnt i best : Nat) :
    minLoop f cnt i best = best ∨ ∃ j, i ≤ j ∧ j < i + cnt ∧ minLoop f cnt i best = f j := by
  induction cnt generalizing i best with
  | zero => exact Or.inl rfl
  | succ cnt ih =>
    simp only [minLoop]
    rcases ih (i + 1) (min best (f i)) with h | ⟨j, h1, h2, h3⟩
    · rcases Nat.le_total best (f i) with hle | hle
      · left; rw [h, Nat.min_eq_left hle]
      · right; exact ⟨i, Nat.le_refl _, by omega, by rw [h, Nat.min_eq_right hle]⟩
    · right; exact ⟨j, by omega, by omega, h3⟩

theorem pushLoop_eq {α : Type} (f : Nat → α) (cnt i : Nat) (acc : Array α) :
    pushLoop f cnt i acc = acc ++ ((List.range' i cnt).map f).toArray := by
  induction cnt generalizing i acc with
  | zero => simp [pushLoop]
  | succ cnt ih => simp [pushLoop, ih, List.range'_succ]

theorem tabN_eq {α : Type} (n : Nat) (f : Nat → α) : tabN n f = ((List.range n).map f).toArray := by
  unfold tabN
  rw [pushLoop_eq]
  simp [List.range_eq_range']

theorem getD_tabN {α : Type} (n : Nat) (f : Nat → α) (i : Nat) (d : α) (h : i < n) :
    (tabN n f).getD i d = f i := by
  rw [tabN_eq]
  simp [h]

theorem getD_map_range {α : Type} (n : Nat) (f : Nat → α) (i : Nat) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## Sums entry by entry -/

theorem getD_addV (x y : List Nat) (j : Nat) : (addV x y).getD j 0 = x.getD j 0 + y.getD j 0 := by
  induction x generalizing y j with
  | nil => simp [addV]
  | cons a x ih =>
    cases y with
    | nil => simp [addV]
    | cons b y =>
      cases j with
      | zero => simp [addV]
      | succ j => simpa [addV] using ih y j

theorem at2_nil (i j : Nat) : at2 [] i j = 0 := by simp [at2]

theorem at2_addVV (x y : List (List Nat)) (i j : Nat) :
    at2 (addVV x y) i j = at2 x i j + at2 y i j := by
  induction x generalizing y i with
  | nil => simp [addVV, at2]
  | cons a x ih =>
    cases y with
    | nil => simp [addVV, at2]
    | cons b y =>
      cases i with
      | zero => simpa [addVV, at2] using getD_addV a b j
      | succ i =>
        have := ih y i
        simpa [addVV, at2] using this

theorem at2_sumLoopVV (f : Nat → List (List Nat)) (n lo : Nat) (acc : List (List Nat)) (i j : Nat) :
    at2 (sumLoopVV f n lo acc) i j = sumLoop (fun x => at2 (f x) i j) n lo (at2 acc i j) := by
  induction n generalizing lo acc with
  | zero => rfl
  | succ n ih => rw [sumLoopVV, sumLoop, ih, at2_addVV]

theorem at2_sumTuplesVV (n len : Nat) (f : List Nat → List (List Nat)) (i j : Nat) :
    at2 (sumTuplesVV n len f) i j = sumTuples n len (fun t => at2 (f t) i j) := by
  induction len generalizing f with
  | zero => rfl
  | succ len ih =>
    rw [sumTuplesVV, sumTuples, at2_sumLoopVV, at2_nil]
    have h : (fun x => at2 (sumTuplesVV n len (fun t => f (x :: t))) i j)
        = (fun x => sumTuples n len (fun t => at2 (f (x :: t)) i j)) := by
      funext x; exact ih _
    rw [h]

theorem at2_sumHalfVV (n : Nat) (f : Nat → List (List Nat)) (i j : Nat) :
    at2 (sumHalfVV n f) i j = sumHalf n (fun x => at2 (f x) i j) := by
  unfold sumHalfVV sumHalf
  simp only [at2_addVV, at2_sumLoopVV, at2_nil]
  split
  · omega
  · rw [at2_nil]; omega

theorem sumHalf_congr {n : Nat} {f g : Nat → Nat} (h : ∀ x, x < n → f x = g x) :
    sumHalf n f = sumHalf n g := by
  unfold sumHalf
  rw [sumLoop_eq, sumLoop_eq]
  have e : Spec.sum (n / 2) (fun i => f (0 + i)) = Spec.sum (n / 2) (fun i => g (0 + i)) :=
    sum_congr (fun i hi => h _ (by omega))
  rw [e]
  split
  · rename_i h1; rw [h (n / 2) (by omega)]
  · rfl

/-! ## The edges that do not depend on the first or the last gap -/

theorem keyOf_congr (p : Params) (g g' : List Nat) (i j : Nat)
    (h : (g.drop i).take (j - i) = (g'.drop i).take (j - i)) : keyOf p g i j = keyOf p g' i j := by
  unfold keyOf; rw [h]

/-- Between interior points the key does not depend on the first and the last gap. -/
theorem keyOf_mid (p : Params) (mid : List Nat) (g1 gk g1' gk' i j : Nat) (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ mid.length + 1) :
    keyOf p (g1 :: (mid ++ [gk])) i j = keyOf p (g1' :: (mid ++ [gk'])) i j := by
  apply keyOf_congr
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp only [List.drop_succ_cons]
  rw [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega), List.take_append_of_le_length (by simp; omega)]

/-- From the point 0 to an interior point the key does not depend on the last gap. -/
theorem keyOf_first (p : Params) (mid : List Nat) (g1 gk gk' j : Nat) (hj : j ≤ mid.length + 1) :
    keyOf p (g1 :: (mid ++ [gk])) 0 j = keyOf p (g1 :: (mid ++ [gk'])) 0 j := by
  apply keyOf_congr
  cases j with
  | zero => rfl
  | succ j' =>
    simp only [List.drop_zero, Nat.sub_zero, List.take_succ_cons]
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]

/-- From an interior point on the key does not depend on the first gap. -/
theorem keyOf_last (p : Params) (rest : List Nat) (g1 g1' i j : Nat) (hi : 1 ≤ i) :
    keyOf p (g1 :: rest) i j = keyOf p (g1' :: rest) i j := by
  apply keyOf_congr
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp only [List.drop_succ_cons]

theorem einOf_shared (p : Params) (mid c : List Nat) (g1 gk g1' gk' u v : Nat) (hu1 : 1 ≤ u)
    (hu : u ≤ mid.length + 1) (hv1 : 1 ≤ v) (hv : v ≤ mid.length + 1) :
    einOf p (g1 :: (mid ++ [gk])) c u v = einOf p (g1' :: (mid ++ [gk'])) c u v := by
  unfold einOf Ef
  rw [keyOf_mid p mid g1 gk g1' gk' (min u v) (max u v) (by omega) (by omega) (by omega)]

theorem stOf_shared (p : Params) (mid c : List Nat) (g1 gk gk' a u : Nat) (hu : u ≤ mid.length + 1) :
    stOf p (g1 :: (mid ++ [gk])) c a u = stOf p (g1 :: (mid ++ [gk'])) c a u := by
  unfold stOf Ef
  have h0 : min 0 u = 0 := by omega
  have h1 : max 0 u = u := by omega
  rw [h0, h1, keyOf_first p mid g1 gk gk' u hu]

theorem enOf_shared (p : Params) (rest c : List Nat) (g1 g1' b v : Nat) (hv1 : 1 ≤ v) (hv : v ≤ p.k) :
    enOf p (g1 :: rest) c b v = enOf p (g1' :: rest) c b v := by
  unfold enOf Ef
  rw [keyOf_last p rest g1 g1' (min v p.k) (max v p.k) (by omega)]

/-! ## The plan for the slots `A` and `H` -/

theorem mem_interior {k u : Nat} : u ∈ interior k ↔ 1 ≤ u ∧ u < k := by
  unfold interior
  rw [List.mem_range'_1]
  omega

/-- After the plan for `A` and `H` has run on the values of its input slots, the slot `H u v` holds
the least cost of a path through all interior points from `u` to `v`. -/
theorem planH_good (k n : Nat) (hok : (mkPlanH k n).ok = true) (ein st en : Nat → Nat → Nat)
    (hsym : ∀ x y, ein x y = ein y x) (val0 : Array Nat)
    (hval0 : val0 = ((inputSlotsH k).map (inputValA ein st en)).toArray) (u v : Nat)
    (hu : u ∈ interior k) (hv : v ∈ interior k) (huv : u ≠ v) :
    Good k ein st en (.H u v)
      ((runPlan (mkPlanH k n).prog val0).getD ((inputSlotsH k ++ targetSlotsH k).idxOf (hSlot u v)) 0) := by
  simp only [mkPlanH, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨hk, hin⟩, hcheck⟩, hout⟩ := hok
  have hrun := run_good k (by omega) ein st en hsym (inputSlotsH k ++ targetSlotsH k)
    (targetSlotsH k) (inputSlotsH k) val0 rfl hcheck (by simp [hval0])
    (by
      intro i hi
      have h1 : val0.getD i 0 = inputValA ein st en (inputSlotsH k)[i] := by
        simp [hval0, Array.getD_eq_getD_getElem?, hi]
      rw [h1]
      exact good_input k n ein st en _ (hin _ (List.getElem_mem hi)))
  obtain ⟨_, hgood⟩ := hrun
  have hs : hSlot u v = Slot.H u v := by simp [hSlot, huv]
  have hlt : (inputSlotsH k ++ targetSlotsH k).idxOf (hSlot u v)
      < (inputSlotsH k ++ targetSlotsH k).length := hout u hu v hv
  rw [hs] at hlt ⊢
  have h1 := hgood _ hlt
  rw [getElem_idxOf _ _ hlt] at h1
  have hprog : (mkPlanH k n).prog = ((targetSlotsH k).map
      (fun s => compileTerms (inputSlotsH k ++ targetSlotsH k) (terms k s))).toArray := rfl
  rw [hprog]
  unfold runPlan
  rw [array_foldl_toArray, List.foldl_map]
  exact h1

theorem getD_map_tab {α : Type} (n : Nat) (f : Nat → Array Nat) (g : Array Nat → α) (i : Nat) (d : α)
    (h : i < n) : ((tab n f).map g).getD i d = g (f i) := by
  simp [tab, h]

theorem getD_map_tab' (n : Nat) (f : Nat → Nat) (g : Nat → Nat) (i : Nat) (d : Nat)
    (h : i < n) : ((tab n f).map g).getD i d = g (f i) := by
  simp [tab, h]

/-- The entry `(v - 1, u - 1)` of `hRows` is the slot `H u v` after the run of the plan. -/
theorem hRows_get (k n : Nat) (eT : Array (Array (Array (Array Nat)))) (ca : Array Nat) (u v : Nat)
    (hu1 : 1 ≤ u) (hu : u < k) (hv1 : 1 ≤ v) (hv : v < k) :
    ((hRows (mkPlanH k n) eT k ca).getD (v - 1) #[]).getD (u - 1) 0
      = (runPlan (mkPlanH k n).prog
            (pushInputs eT ca k (inputSlotsH k) (Array.mkEmpty (mkPlanH k n).size))).getD
          ((inputSlotsH k ++ targetSlotsH k).idxOf (hSlot u v)) 0 := by
  have hpos : (mkPlanH k n).hpos = tab (k - 1) (fun v => tab (k - 1) (fun u =>
      (inputSlotsH k ++ targetSlotsH k).idxOf (hSlot (u + 1) (v + 1)))) := rfl
  have hins : (mkPlanH k n).inputs = inputSlotsH k := rfl
  unfold hRows
  simp only [hpos, hins]
  rw [getD_map_tab _ _ _ _ _ (by omega), getD_map_tab' _ _ _ _ _ (by omega)]
  have e1 : u - 1 + 1 = u := by omega
  have e2 : v - 1 + 1 = v := by omega
  rw [e1, e2]

/-! ## The direct loops for `L` and `C` -/

theorem good_st (k : Nat) (ein st en : Nat → Nat → Nat) (a u : Nat) :
    Good k ein st en (.st a u) (st a u) :=
  ⟨⟨[u], rfl, rfl⟩, fun π hπ => by
    simp only [Paths] at hπ; subst hπ; exact Nat.le_refl _⟩

theorem good_en (k : Nat) (ein st en : Nat → Nat → Nat) (b v : Nat) :
    Good k ein st en (.en b v) (en b v) :=
  ⟨⟨[v], rfl, rfl⟩, fun π hπ => by
    simp only [Paths] at hπ; subst hπ; exact Nat.le_refl _⟩

/-- The loop for `L a w`: with the row `sa` of the edges from the point 0 at height `a` and the
column `hc` of the numbers `H · w`. -/
theorem lVal_good (k : Nat) (hk : 3 ≤ k) (ein st en : Nat → Nat → Nat) (a w : Nat)
    (hw1 : 1 ≤ w) (hw : w < k) (sa hc : Array Nat)
    (hsa : ∀ u, 1 ≤ u → u < k → sa.getD (u - 1) 0 = st a u)
    (hh : ∀ u, 1 ≤ u → u < k → u ≠ w → Good k ein st en (.H u w) (hc.getD (u - 1) 0)) :
    Good k ein st en (.L a w) (lVal sa hc (k - 1) (w - 1)) := by
  let vv : Slot → Nat := fun s => match s with
    | .st a' u => st a' u
    | .H u _ => hc.getD (u - 1) 0
    | _ => 0
  have hterms : terms k (.L a w)
      = ((interior k).filter (fun u => u != w)).map (fun u => (Slot.st a u, Slot.H u w)) := by
    have hk2 : k ≠ 2 := by omega
    simp [terms, hk2]
  have hmemf : ∀ u, u ∈ (interior k).filter (fun u => u != w) ↔ (1 ≤ u ∧ u < k) ∧ u ≠ w := by
    intro u
    simp [List.mem_filter, mem_interior]
  have hne : terms k (.L a w) ≠ [] := by
    rw [hterms]
    intro h
    have h2 : (if w = 1 then 2 else 1) ∈ (interior k).filter (fun u => u != w) := by
      rw [hmemf]; split <;> omega
    rw [List.map_eq_nil_iff] at h
    rw [h] at h2
    exact absurd h2 (List.not_mem_nil)
  have hv : ∀ ab ∈ terms k (.L a w),
      Good k ein st en ab.1 (vv ab.1) ∧ Good k ein st en ab.2 (vv ab.2) := by
    intro ab hab
    rw [hterms] at hab
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hab
    have := (hmemf u).mp hu
    exact ⟨good_st k ein st en a u, hh u this.1.1 this.1.2 this.2⟩
  have hvalid : (Slot.L a w).valid k = true := by
    simp [Slot.valid, mem_interior]; omega
  have hgood := good_L k ein st en a w vv hvalid hne hv
  have hlist : (terms k (.L a w)).map (fun ab => vv ab.1 + vv ab.2)
      = ((interior k).filter (fun u => u != w)).map (fun u => st a u + hc.getD (u - 1) 0) := by
    rw [hterms, List.map_map]; rfl
  rw [hlist] at hgood
  -- the loop gives the least element of this list
  have key : lVal sa hc (k - 1) (w - 1)
      = minOf (((interior k).filter (fun u => u != w)).map (fun u => st a u + hc.getD (u - 1) 0)) := by
    symm
    -- the term of the interior point `j + 1`
    have hterm : ∀ j, j < k - 1 → j ≠ w - 1 →
        sa.getD j 0 + hc.getD j 0 ∈ ((interior k).filter (fun u => u != w)).map
          (fun u => st a u + hc.getD (u - 1) 0) := by
      intro j hj hjw
      refine List.mem_map.mpr ⟨j + 1, (hmemf _).mpr (by omega), ?_⟩
      have := hsa (j + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this ⊢
      rw [this]
    apply minOf_eq
    · unfold lVal
      simp only []
      have hs : (if w - 1 = 0 then 1 else 0) < k - 1 ∧ (if w - 1 = 0 then 1 else 0) ≠ w - 1 := by
        split <;> omega
      rcases minLoop_mem (fun u => if u = w - 1 then
          sa.getD (if w - 1 = 0 then 1 else 0) 0 + hc.getD (if w - 1 = 0 then 1 else 0) 0
          else sa.getD u 0 + hc.getD u 0) (k - 1) 0
          (sa.getD (if w - 1 = 0 then 1 else 0) 0 + hc.getD (if w - 1 = 0 then 1 else 0) 0)
        with h | ⟨j, _, hj, h⟩
      · rw [h]; exact hterm _ hs.1 hs.2
      · rw [h]
        by_cases hjw : j = w - 1
        · simp only [hjw, if_true]; exact hterm _ hs.1 hs.2
        · simp only [hjw, if_false]; exact hterm j (by omega) hjw
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
      have hu' := (hmemf u).mp hu
      unfold lVal
      simp only []
      have hle := minLoop_le (fun u => if u = w - 1 then
          sa.getD (if w - 1 = 0 then 1 else 0) 0 + hc.getD (if w - 1 = 0 then 1 else 0) 0
          else sa.getD u 0 + hc.getD u 0) (k - 1) 0
          (sa.getD (if w - 1 = 0 then 1 else 0) 0 + hc.getD (if w - 1 = 0 then 1 else 0) 0)
          (u - 1) (Nat.zero_le _) (by omega)
      have hne' : u - 1 ≠ w - 1 := by omega
      simp only [hne', if_false] at hle
      rw [hsa u hu'.1.1 hu'.1.2] at hle
      exact hle
  rw [key]
  exact hgood

/-- The loop for `C a b`: with the row `la` of the numbers `L a ·` and the row `eb` of the edges to
the point `k` at height `b`. -/
theorem cVal_eq (k : Nat) (hk : 2 ≤ k) (ein st en : Nat → Nat → Nat) (a b : Nat) (la eb : Array Nat)
    (hl : ∀ v, 1 ≤ v → v < k → Good k ein st en (.L a v) (la.getD (v - 1) 0))
    (he : ∀ v, 1 ≤ v → v < k → eb.getD (v - 1) 0 = en b v) :
    cVal la eb (k - 1) = costC k ein st en a b := by
  let vv : Slot → Nat := fun s => match s with
    | .L _ v => la.getD (v - 1) 0
    | .en b' v => en b' v
    | _ => 0
  have hterms : terms k (.C a b) = (interior k).map (fun v => (Slot.L a v, Slot.en b v)) := rfl
  have h1mem : 1 ∈ interior k := mem_interior.mpr (by omega)
  have hne : terms k (.C a b) ≠ [] := by
    rw [hterms]
    intro h
    rw [List.map_eq_nil_iff] at h
    rw [h] at h1mem
    exact absurd h1mem (List.not_mem_nil)
  have hv : ∀ ab ∈ terms k (.C a b),
      Good k ein st en ab.1 (vv ab.1) ∧ Good k ein st en ab.2 (vv ab.2) := by
    intro ab hab
    rw [hterms] at hab
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hab
    have := mem_interior.mp hv
    exact ⟨hl v this.1 this.2, good_en k ein st en b v⟩
  have hgood := good_C k hk ein st en a b vv hne hv
  have hlist : (terms k (.C a b)).map (fun ab => vv ab.1 + vv ab.2)
      = (interior k).map (fun v => la.getD (v - 1) 0 + en b v) := by
    rw [hterms, List.map_map]; rfl
  rw [hlist] at hgood
  have hterm : ∀ j, j < k - 1 →
      la.getD j 0 + eb.getD j 0 ∈ (interior k).map (fun v => la.getD (v - 1) 0 + en b v) := by
    intro j hj
    refine List.mem_map.mpr ⟨j + 1, mem_interior.mpr (by omega), ?_⟩
    have := he (j + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at this ⊢
    rw [this]
  have key : cVal la eb (k - 1) = minOf ((interior k).map (fun v => la.getD (v - 1) 0 + en b v)) := by
    symm
    apply minOf_eq
    · unfold cVal
      rcases minLoop_mem (fun v => la.getD v 0 + eb.getD v 0) (k - 1 - 1) 1
          (la.getD 0 0 + eb.getD 0 0) with h | ⟨j, _, hj, h⟩
      · rw [h]; exact hterm 0 (by omega)
      · rw [h]; exact hterm j (by omega)
    · intro y hy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      have hv' := mem_interior.mp hv
      unfold cVal
      rw [← he v hv'.1 hv'.2]
      by_cases hv1 : v = 1
      · subst hv1
        exact minLoop_le_best _ _ _ _
      · exact minLoop_le (fun v => la.getD v 0 + eb.getD v 0) (k - 1 - 1) 1
          (la.getD 0 0 + eb.getD 0 0) (v - 1) (by omega) (by omega)
  rw [key]
  exact good_unique hgood (good_costC k ein st en a b)

/-! ## One tuple of interior heights -/

theorem stRows_get (eT : Array (Array (Array (Array Nat)))) (k n : Nat) (ca : Array Nat) (a u : Nat)
    (ha : a < n) (hu1 : 1 ≤ u) (hu : u < k) :
    ((stRows eT k n ca).getD a #[]).getD (u - 1) 0 = get4 eT 0 u a (ca.getD (u - 1) 0) := by
  unfold stRows
  rw [getD_tabN _ _ _ _ ha, getD_tabN _ _ _ _ (by omega)]
  have e : u - 1 + 1 = u := by omega
  rw [e]

theorem enRows_get (eT : Array (Array (Array (Array Nat)))) (k n : Nat) (ca : Array Nat) (b v : Nat)
    (hb : b < n) (hv1 : 1 ≤ v) (hv : v < k) :
    ((enRows eT k n ca).getD b #[]).getD (v - 1) 0 = get4 eT v k (ca.getD (v - 1) 0) b := by
  unfold enRows
  rw [getD_tabN _ _ _ _ hb, getD_tabN _ _ _ _ (by omega)]
  have e : v - 1 + 1 = v := by omega
  rw [e]

theorem lRows_get (st hT : Array (Array Nat)) (k n a w : Nat) (ha : a < n) (hw1 : 1 ≤ w) (hw : w < k) :
    ((lRows st hT k n).getD a #[]).getD (w - 1) 0
      = lVal (st.getD a #[]) (hT.getD (w - 1) #[]) (k - 1) (w - 1) := by
  unfold lRows
  rw [getD_tabN _ _ _ _ ha, getD_tabN _ _ _ _ (by omega)]

theorem cSum_eq (l en : Array (Array Nat)) (k n : Nat) :
    cSum l en k n = ∑ a < n, ∑ b < n, cVal (l.getD a #[]) (en.getD b #[]) (k - 1) := by
  unfold cSum
  rw [sumLoop_eq, Nat.zero_add]
  apply sum_congr
  intro a _
  rw [sumLoop_eq, Nat.zero_add]
  simp only [Nat.zero_add]

theorem at2_map {α β : Type} (l1 : List α) (l2 : List β) (G : α → β → Nat) (i j : Nat) (x : α) (y : β)
    (hx : l1[i]? = some x) (hy : l2[j]? = some y) :
    at2 (l1.map (fun a => l2.map (G a))) i j = G x y := by
  simp [at2, List.getD_eq_getElem?_getD, hx, hy]

theorem configShared_at2 (planH : PlanH) (eT0 : Array (Array (Array (Array Nat))))
    (eTs eTe : List (Array (Array (Array (Array Nat))))) (k n : Nat) (c : List Nat) (i j : Nat)
    (eS eE : Array (Array (Array (Array Nat)))) (hS : eTs[i]? = some eS) (hE : eTe[j]? = some eE) :
    at2 (configShared planH eT0 eTs eTe k n c) i j
      = cSum (lRows (stRows eS k n c.toArray) (hRows planH eT0 k c.toArray) k n)
          (enRows eE k n c.toArray) k n := by
  unfold configShared
  exact at2_map eTs (eTe.map (fun eT => enRows eT k n c.toArray))
    (fun eT en => cSum (lRows (stRows eT k n c.toArray) (hRows planH eT0 k c.toArray) k n) en k n)
    i j eS (enRows eE k n c.toArray) hS (by simp [hE])

/-- For the heights `c` of the interior points, the entry `(g_1, g_k)` of `configShared` is the sum of
the cost of the recipe over the heights of the two end points, for the gap tuple `(g_1, mid, g_k)`. -/
theorem configShared_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (hok : (mkPlanH p.k p.n).ok = true) (mid : List Nat) (hmid : mid.length + 2 = p.k)
    (c : List Nat) (hc : c ∈ tuples (p.k - 1) p.n) (g1 gk : Nat) (hg1 : g1 < m p) (hgk : gk < m p) :
    at2 (configShared (mkPlanH p.k p.n) (edgeTab p rows (0 :: (mid ++ [0])))
          ((List.range (m p)).map (fun g1 => edgeTab p rows (g1 :: (mid ++ [0]))))
          ((List.range (m p)).map (fun gk => edgeTab p rows (0 :: (mid ++ [gk])))) p.k p.n c) g1 gk
      = endSum p (g1 :: (mid ++ [gk])) c := by
  have hok' := hok
  simp only [mkPlanH, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok'
  obtain ⟨⟨⟨hk, hin⟩, _⟩, _⟩ := hok'
  have hget : ∀ i, c.toArray.getD i 0 = c.getD i 0 := by
    intro i; simp [List.getD_eq_getElem?_getD]
  have hsym : ∀ x y, einOf p (g1 :: (mid ++ [gk])) c x y = einOf p (g1 :: (mid ++ [gk])) c y x :=
    fun x y => Ef_symm p _ x y _ _
  -- the values of the input slots of the plan for `A` and `H`
  have hval0 : pushInputs (edgeTab p rows (0 :: (mid ++ [0]))) c.toArray p.k (inputSlotsH p.k)
        (Array.mkEmpty (mkPlanH p.k p.n).size)
      = ((inputSlotsH p.k).map (inputValA (einOf p (g1 :: (mid ++ [gk])) c)
          (stOf p (g1 :: (mid ++ [gk])) c) (enOf p (g1 :: (mid ++ [gk])) c))).toArray := by
    rw [pushInputs_eq]
    simp only [Array.mkEmpty_eq, Array.empty_append]
    congr 1
    apply List.map_congr_left
    intro s hs
    have hr := hin s hs
    rw [inputVal_eq p rows h _ c hc s hr]
    cases s with
    | zero => simp only [inputValA]
    | ein u v =>
      simp only [Slot.inRange, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
      obtain ⟨⟨⟨⟨hu1, hu2⟩, hv1⟩, hv2⟩, _⟩ := hr
      simp only [inputValA]
      exact einOf_shared p mid c 0 0 g1 gk u v hu1 (by omega) hv1 (by omega)
    | st a u => simp [inputSlotsH] at hs
    | en b v => simp [inputSlotsH] at hs
    | A S u => simp [Slot.inRange] at hr
    | H u v => simp [Slot.inRange] at hr
    | L a v => simp [Slot.inRange] at hr
    | C a b => simp [Slot.inRange] at hr
  rw [configShared_at2 _ _ _ _ _ _ _ g1 gk (edgeTab p rows (g1 :: (mid ++ [0])))
    (edgeTab p rows (0 :: (mid ++ [gk]))) (by simp [hg1]) (by simp [hgk]), cSum_eq]
  unfold endSum
  apply sum_congr; intro a ha
  apply sum_congr; intro b hb
  rw [← costC_eq_cost p (g1 :: (mid ++ [gk])) c (by omega) hc a b]
  apply cVal_eq p.k (by omega) _ _ _ a b
  · -- the numbers `L a w`
    intro w hw1 hw
    rw [lRows_get _ _ _ _ a w ha hw1 hw]
    apply lVal_good p.k hk _ _ _ a w hw1 hw
    · intro u hu1 hu
      rw [stRows_get _ _ _ _ a u ha hu1 hu, hget, show c.getD (u - 1) 0 = hgt c u from rfl,
        get4_edgeTab p rows h _ 0 u _ _ (by omega) (by omega) (by omega) ha (hgt_lt hc hu1 hu)]
      exact stOf_shared p mid c g1 0 gk a u (by omega)
    · intro u hu1 hu huw
      rw [hRows_get p.k p.n _ _ u w hu1 hu hw1 hw, hval0]
      exact planH_good p.k p.n hok _ _ _ hsym _ rfl u w (mem_interior.mpr ⟨hu1, hu⟩)
        (mem_interior.mpr ⟨hw1, hw⟩) huw
  · -- the edges at the point `k`
    intro v hv1 hv
    rw [enRows_get _ _ _ _ b v hb hv1 hv, hget, show c.getD (v - 1) 0 = hgt c v from rfl,
      get4_edgeTab p rows h _ v p.k _ _ (by omega) (by omega) (by omega) (hgt_lt hc hv1 hv) hb]
    exact enOf_shared p (mid ++ [gk]) c 0 g1 b v hv1 (by omega)

/-! ## One unit -/

/-- The sum over the heights of the interior points, with the reflection used, is the cell sum (the
second half of the proof of `cellSumFlip_eq`). -/
theorem sumHalf_endSum (p : Params) (g : List Nat) (hk : 2 ≤ p.k) :
    sumHalf p.n (fun x => ((tuples (p.k - 2) p.n).map (fun c => endSum p g (x :: c))).sum) = S p g := by
  have hcons : ∀ x, x < p.n → ∀ c ∈ tuples (p.k - 2) p.n,
      (x :: c).length = p.k - 1 ∧ ∀ y ∈ x :: c, y < p.n := by
    intro x hx c hc
    obtain ⟨hl, ha⟩ := mem_tuples.mp hc
    refine ⟨by simp [hl]; omega, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact ha y hy
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
  rw [sumHalf_eq _ _ hsym]
  have hk1 : p.k - 1 = (p.k - 2) + 1 := by omega
  have hk' : p.k + 1 = (p.k - 1) + 2 := by omega
  unfold S
  rw [hk', sum_tuples_ends, hk1, sum_tuples_head]
  rfl

/-- The entry `(g_1, g_k)` of a unit is the cell sum of the gap tuple `(g_1, mid, g_k)`. -/
theorem sharedSums_eq (p : Params) (rows : List (List Nat × Array Nat)) (h : RowsOK p rows)
    (mid : List Nat) (g1 gk : Nat) (hg1 : g1 < m p) (hgk : gk < m p) :
    at2 (sharedSums p rows (mkPlanH p.k p.n) mid) g1 gk = S p (g1 :: (mid ++ [gk])) := by
  unfold sharedSums
  simp only []
  split
  · rename_i hcond
    obtain ⟨hok, hmid⟩ := hcond
    have hk : 3 ≤ p.k := by
      have hok' := hok
      simp only [mkPlanH, Bool.and_eq_true, decide_eq_true_eq] at hok'
      exact hok'.1.1.1
    rw [at2_sumHalfVV, ← sumHalf_endSum p _ (by omega)]
    apply sumHalf_congr
    intro x hx
    rw [at2_sumTuplesVV, sumTuples_eq]
    refine congrArg List.sum ?_
    apply List.map_congr_left
    intro c hc
    obtain ⟨hl, ha⟩ := mem_tuples.mp hc
    have hxc : (x :: c) ∈ tuples (p.k - 1) p.n := by
      refine mem_tuples.mpr ⟨by simp [hl]; omega, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ha y hy
    exact configShared_eq p rows h hok mid hmid (x :: c) hxc g1 gk hg1 hgk
  · rw [at2_map (List.range (m p)) (List.range (m p))
      (fun g1 gk => cellSumFlip p rows (mkPlan p.k p.n) (g1 :: (mid ++ [gk]))) g1 gk g1 gk
      (by simp [hg1]) (by simp [hgk])]
    exact cellSumFlip_eq p rows h _

/-! ## Several threads -/

theorem parWaveG_eq {α : Type} (r : Nat → Nat → List α)
    (hr : ∀ lo a b, r lo a ++ r (lo + a) b = r lo (a + b))
    (hr0 : ∀ lo, r lo 0 = []) (threads chunk lo cnt : Nat) (acc : List α) :
    parWaveG r threads chunk lo cnt acc = acc ++ r lo (min cnt (threads * chunk)) := by
  unfold parWaveG
  induction threads with
  | zero => simp [hr0]
  | succ T ih =>
    simp only [] at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [List.append_assoc, task_get_spawn, hr]
    congr 2
    rw [Nat.succ_mul]; omega

theorem parWavesG_eq {α : Type} (r : Nat → Nat → List α)
    (hr : ∀ lo a b, r lo a ++ r (lo + a) b = r lo (a + b))
    (hr0 : ∀ lo, r lo 0 = []) (threads chunk fuel lo cnt : Nat) (acc : List α) :
    parWavesG r threads chunk fuel lo cnt acc = acc ++ r lo cnt := by
  induction fuel generalizing lo cnt acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [parWavesG]
    split
    · rename_i h0; subst h0; simp [hr0]
    · rw [ih, parWaveG_eq r hr hr0, List.append_assoc, hr]
      congr 2
      omega

theorem poolMap_eq {α β : Type} (f : α → β) (xs : List α) : poolMap f xs = xs.map f := by
  unfold poolMap
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  rfl

theorem unitsMap_eq {α : Type} (f : Nat → α) (threads count : Nat) :
    unitsMap f threads count = (List.range count).map f := by
  unfold unitsMap
  split
  · exact poolMap_eq f _
  · rw [parWavesG_eq (fun lo cnt => (List.range' lo cnt).map f)
        (fun lo a b => by
          show (List.range' lo a).map f ++ (List.range' (lo + a) b).map f = (List.range' lo (a + b)).map f
          rw [← List.map_append, List.range'_append_1])
        (fun lo => by simp), List.nil_append, List.range_eq_range']

theorem vMemoPool_ok (p : Params) (wA : Array (Array Nat)) (hw : IsTab2 wA (W p)) :
    ∀ e ∈ vMemoPool p wA, IsTab e.2 (V p e.1) := by
  have gen : ∀ (ss : List Nat) (memo : List (List Nat × Array Nat)),
      (∀ e ∈ memo, IsTab e.2 (V p e.1)) →
      ∀ e ∈ ss.foldl (fun memo s =>
          poolMap (fun κ => (κ, vNew p wA memo κ)) ((keys p).filter (fun κ => κ.sum = s + 1)) ++ memo)
        memo, IsTab e.2 (V p e.1) := by
    intro ss
    induction ss with
    | nil => intro memo hm; exact hm
    | cons s ss ih =>
      intro memo hm
      simp only [List.foldl_cons]
      apply ih
      intro e he
      rw [poolMap_eq] at he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨κ, _, rfl⟩ := List.mem_map.mp he
        show IsTab (vNew p wA memo κ) (V p κ)
        rw [vNew_eq p wA hw memo hm]; exact isTab_tab _ _
      · exact hm e he
  exact gen (List.range p.k) [] (by intro e he; simp at he)

theorem tableRowsPool_eq (p : Params) (parts : Nat) :
    tableRowsPool p parts = (keys p).map (fun κ => (κ, tab p.n (Tab p κ))) := by
  unfold tableRowsPool
  simp only []
  rw [poolMap_eq]
  apply List.map_congr_left
  intro κ _
  rw [tabRow_eq p κ _ (isTab_vRowOf p _ (vMemoPool_ok p _ (isTab2_wArrs p)) κ) _ (gTab_ok p parts)]

theorem rowsOK_tableRowsPool (p : Params) (parts : Nat) : RowsOK p (tableRowsPool p parts) := by
  rw [tableRowsPool_eq]
  intro e he
  obtain ⟨κ, _, rfl⟩ := List.mem_map.mp he
  exact isTab_tab _ _

/-! ## `A_j(g_1, t)` for all first gaps -/

theorem digits_idx (mm : Nat) (u : List Nat) (hu : ∀ x ∈ u, x < mm) :
    digits mm u.length (idx mm u) = u := by
  apply List.ext_getElem
  · simp [digits]
  · intro i h1 h2
    simp only [digits, List.getElem_map, List.getElem_range]
    exact idx_digit mm u hu i h2

/-- The recursion of Section 8 from values `f` that are right for the gap tuples that begin with `g`. -/
theorem Afrom_ext (p : Params) (j : Nat) (f : List Nat → Nat) (hj : j ≤ p.k) (g : List Nat)
    (hlen : g.length ≤ j) (hmem : ∀ x ∈ g, x < m p)
    (hf : ∀ u : List Nat, g.length + u.length = j → (∀ x ∈ u, x < m p) → f (g ++ u) = A p (g ++ u)) :
    Afrom p (massArr p) j f g = A p g := by
  generalize hd : j - g.length = d
  induction d generalizing g with
  | zero =>
    have h1 : j ≤ g.length := by omega
    rw [Afrom, if_pos h1]
    have := hf [] (by simp; omega) (by simp)
    simpa using this
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
    rw [look_eq (isTab_massArr p), ih (g ++ [c]) (by simp; omega) hmem' (by
      intro u hu hx
      have := hf (c :: u) (by simp at hu ⊢; omega) (by
        intro x hx'
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact hc
        · exact hx x hx')
      simpa using this) (by simp; omega)]

/-- `AofShared` computes the values `A_j(g_1, t)` for all first gaps `g_1`. -/
theorem AofShared_eq (p : Params) (threads parts : Nat) (t : List Nat) :
    AofShared p threads parts t = (List.range (m p)).map (fun g1 => A p (g1 :: t)) := by
  unfold AofShared
  simp only []
  split
  · rename_i hcond
    obtain ⟨hlen, hall⟩ := hcond
    have ht : ∀ x ∈ t, x < m p := by simpa using hall
    apply List.map_congr_left
    intro g1 hg1
    have hg1' : g1 < m p := List.mem_range.mp hg1
    rw [unitsMap_eq]
    apply Afrom_ext p p.k _ (Nat.le_refl _) (g1 :: t) (by simp; omega)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hg1'
      · exact ht x hx
    · intro w hw hwm
      simp only [List.length_cons] at hw
      have hk : p.k ≤ ((g1 :: t) ++ w).length := by simp; omega
      rw [A, if_pos hk]
      -- `w` is `u` and the last gap
      have hne : w ≠ [] := by
        intro h0; subst h0; simp at hw; omega
      obtain ⟨gk, hgk⟩ : ∃ gk, w.getLast? = some gk := by
        cases hl : w.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
        | some x => exact ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := List.getLast?_eq_some_iff.mp hgk
      have hur : u.length = p.k - 1 - (t.length + 1) := by
        simp at hw; omega
      have hum : ∀ x ∈ u, x < m p := fun x hx => hwm x (by simp [hx])
      have hgk' : gk < m p := hwm gk (by simp)
      unfold sharedLeaf
      have e1 : (((g1 :: t) ++ (u ++ [gk])).drop (t.length + 1)).take (p.k - 1 - (t.length + 1)) = u := by
        rw [← hur]
        rw [List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp), List.nil_append,
          List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      have e2 : ((g1 :: t) ++ (u ++ [gk])).headD 0 = g1 := rfl
      have e3 : ((g1 :: t) ++ (u ++ [gk])).getD (t.length + 1 + (p.k - 1 - (t.length + 1))) 0 = gk := by
        have hidx : t.length + 1 + (p.k - 1 - (t.length + 1)) = ((g1 :: t) ++ u).length := by
          simp; omega
        rw [← List.append_assoc, List.getD_eq_getElem?_getD, hidx, List.getElem?_concat_length]
        rfl
      rw [e1, e2, e3, indexOf_eq]
      have hlt : idx (m p) u < (m p) ^ (p.k - 1 - (t.length + 1)) := by
        have := idx_lt (m p) u hum
        rwa [hur] at this
      have hx : (((List.range ((m p) ^ (p.k - 1 - (t.length + 1)))).map
            (sharedUnit p (tableRowsPool p parts) t (p.k - 1 - (t.length + 1)))).toArray).getD
              (idx (m p) u) []
          = sharedSums p (tableRowsPool p parts) (mkPlanH p.k p.n) (t ++ u) := by
        unfold sharedUnit
        simp [hlt]
        rw [← hur, digits_idx (m p) u hum]
      rw [hx, sharedSums_eq p _ (rowsOK_tableRowsPool p parts) (t ++ u) g1 gk hg1' hgk']
      simp
  · rfl

end Correct
