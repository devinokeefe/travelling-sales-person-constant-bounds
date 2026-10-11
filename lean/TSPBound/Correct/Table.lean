/-
The table: `Impl.tableRows` consists of the keys of the recipe, each with the row of `Spec.Tab`
(`tableRows_eq`).  Sections 2 to 6 of RECIPE.md in turn.
-/
import TSPBound.Correct.Total

namespace Correct
open Spec Impl

theorem look_tab (n : Nat) (f : Nat → Nat) (i : Nat) : look (tab n f) f i = f i :=
  look_eq (isTab_tab n f) i

/-! ## Section 2: the powers `Rup` -/

theorem isTab_push {acc : Array Nat} {f : Nat → Nat} (h : IsTab acc f) {x : Nat}
    (hx : x = f acc.size) : IsTab (acc.push x) f := by
  intro i hi
  rw [Array.getElem_push]
  split
  · exact h i _
  · have hi' : i = acc.size := by
      rw [Array.size_push] at hi; omega
    rw [hi']; exact hx

theorem isTab_iterArr (step : Nat → Nat) (f : Nat → Nat) (hf : ∀ i, f (i + 1) = step (f i)) :
    ∀ (n : Nat) (acc : Array Nat) (x : Nat), IsTab acc f → x = f acc.size →
      IsTab (iterArr step n acc x) f
  | 0, acc, x, h, hx => by
    rw [iterArr]; exact isTab_push h hx
  | n + 1, acc, x, h, hx => by
    rw [iterArr]
    apply isTab_iterArr step f hf n
    · exact isTab_push h hx
    · rw [Array.size_push, hf, hx]

theorem isTab_rupArr (M I : Nat) : IsTab (rupArr M I) (Rup M) := by
  show IsTab (iterArr (fun r => cdiv (r * up M 1) Q) I (Array.mkEmpty (I + 1)) Q) (Rup M)
  exact isTab_iterArr _ (Rup M) (fun _ => rfl) I _ Q (isTab_empty _) rfl

/-! ## Section 3: the weights -/

theorem wArrs_eq (p : Params) : wArrs p = tab (m p) (fun c => tab (ncell p c + 1) (W p c)) := by
  unfold wArrs
  simp only [look_fun (isTab_rupArr _ _)]
  rfl

theorem isTab2_wArrs (p : Params) : IsTab2 (wArrs p) (W p) := by
  rw [wArrs_eq]; exact isTab2_tab _ _ _

theorem isTab_getD {wA : Array (Array Nat)} {f : Nat → Nat → Nat} (h : IsTab2 wA f) (c : Nat) :
    IsTab (wA.getD c #[]) (f c) := by
  by_cases hc : c < wA.size
  · have e : wA.getD c #[] = wA[c] := by simp [hc]
    rw [e]; exact h c hc
  · have e : wA.getD c #[] = #[] := by simp [hc]
    rw [e]; exact isTab_empty _

/-! ## Section 4: the weight vectors -/

theorem isTab_found (rows : List (List Nat × Array Nat)) (f : List Nat → Nat → Nat)
    (h : ∀ e ∈ rows, IsTab e.2 (f e.1)) (κ : List Nat) (r : Array Nat)
    (hf : findRow rows κ = some r) : IsTab r (f κ) := by
  simp only [findRow, Option.map_eq_some_iff] at hf
  obtain ⟨e, he, rfl⟩ := hf
  have hmem := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  have hκ : e.1 = κ := by simpa using hp
  rw [← hκ]; exact h e hmem

theorem isTab_vRowOf (p : Params) (memo : List (List Nat × Array Nat))
    (h : ∀ e ∈ memo, IsTab e.2 (V p e.1)) (κ : List Nat) : IsTab (vRowOf p memo κ) (V p κ) := by
  unfold vRowOf
  cases hf : findRow memo κ with
  | none => exact isTab_tab _ _
  | some r => exact isTab_found memo (V p) h κ r hf

/-- The product of two numbers from their parts in base `b`. -/
theorem split_mul (b x y : Nat) :
    x / b * (y / b) * b * b + (x / b * (y % b) + x % b * (y / b)) * b + x % b * (y % b) = x * y := by
  have hx := Nat.div_add_mod x b
  have hy := Nat.div_add_mod y b
  generalize x / b = x1 at hx ⊢
  generalize x % b = x0 at hx ⊢
  generalize y / b = y1 at hy ⊢
  generalize y % b = y0 at hy ⊢
  subst hx hy
  grind

theorem sum_split4 (n : Nat) (a b c d : Nat → Nat) (B : Nat) :
    Spec.sum n a * B * B + (Spec.sum n b + Spec.sum n c) * B + Spec.sum n d
      = Spec.sum n (fun i => a i * B * B + (b i + c i) * B + d i) := by
  induction n with
  | zero => simp [Spec.sum]
  | succ n ih =>
    simp only [Spec.sum]
    rw [← ih]
    grind

theorem conv_inner (fv fw : Nat → Nat) (nc s i : Nat) :
    (∑ j < nc + 1, if i + j = s then fv i * fw j else 0)
      = if i ≤ s ∧ s - i < nc + 1 then fv i * fw (s - i) else 0 := by
  have h1 : ∀ j, j < nc + 1 → (if i + j = s then fv i * fw j else 0)
      = (if j = s - i then (if i ≤ s then fv i * fw j else 0) else 0) := by
    intro j _
    by_cases h : i + j = s
    · have h2 : j = s - i := by omega
      have h3 : i ≤ s := by omega
      rw [if_pos h, if_pos h2, if_pos h3]
    · by_cases h2 : j = s - i
      · have h3 : ¬ i ≤ s := by omega
        rw [if_neg h, if_pos h2, if_neg h3]
      · rw [if_neg h, if_neg h2]
  rw [sum_congr h1, sum_single]
  by_cases ha : i ≤ s <;> by_cases hb : s - i < nc + 1 <;> simp [ha, hb]

/-- The convolution as a single sum over the indices that contribute. -/
theorem conv_eq (fv fw : Nat → Nat) (len' nc s : Nat) :
    (∑ i < len', ∑ j < nc + 1, if i + j = s then fv i * fw j else 0)
      = ∑ i < min (s + 1) len' - (s - min s nc),
          fv ((s - min s nc) + i) * fw (s - ((s - min s nc) + i)) := by
  have h1 : ∀ i, i < len' → (∑ j < nc + 1, if i + j = s then fv i * fw j else 0)
      = if (s - min s nc) ≤ i ∧ i < (s - min s nc) + (min (s + 1) len' - (s - min s nc))
          then fv i * fw (s - i) else 0 := by
    intro i hi
    rw [conv_inner]
    have hiff : (i ≤ s ∧ s - i < nc + 1)
        ↔ ((s - min s nc) ≤ i ∧ i < (s - min s nc) + (min (s + 1) len' - (s - min s nc))) := by
      omega
    simp only [hiff]
  rw [sum_congr h1]
  by_cases hlo : s - min s nc ≤ len'
  · exact sum_interval len' _ _ (by omega) (fun i => fv i * fw (s - i))
  · have hz : ∀ i, i < len' →
        (if (s - min s nc) ≤ i ∧ i < (s - min s nc) + (min (s + 1) len' - (s - min s nc))
          then fv i * fw (s - i) else 0) = 0 := by
      intro i hi
      rw [if_neg (by omega)]
    rw [sum_congr hz, sum_zero]
    have h0 : min (s + 1) len' - (s - min s nc) = 0 := by omega
    rw [h0]; rfl

theorem convRow_eq (v w : Array Nat) (fv fw : Nat → Nat) (hv : IsTab v fv) (hw : IsTab w fw)
    (len' nc len : Nat) :
    convRow v w fv fw len' nc len
      = tab len (fun s => cdiv (∑ i < len', ∑ j < nc + 1, if i + j = s then fv i * fw j else 0) D) := by
  unfold convRow
  simp only [look_eq hv, look_eq hw, look_tab, sumLoop_eq, Nat.zero_add]
  congr 1
  funext s
  rw [sum_split4, conv_eq]
  congr 1
  apply sum_congr
  intro i _
  exact split_mul _ _ _

theorem V_eq_W (p : Params) (κ : List Nat) (h : κ.sum ≤ 1) (s : Nat) :
    V p κ s = W p (lastCell κ) s := by
  rw [V, dif_pos h]

theorem V_eq_conv (p : Params) (κ : List Nat) (h : ¬ κ.sum ≤ 1) (s : Nat) :
    V p κ s = cdiv (∑ i < lenKey p (reduce κ (lastCell κ)), ∑ j < ncell p (lastCell κ) + 1,
      if i + j = s then V p (reduce κ (lastCell κ)) i * W p (lastCell κ) j else 0) D := by
  rw [V, dif_neg h]

theorem vNew_eq (p : Params) (wA : Array (Array Nat)) (hw : IsTab2 wA (W p))
    (memo : List (List Nat × Array Nat)) (hm : ∀ e ∈ memo, IsTab e.2 (V p e.1)) (κ : List Nat) :
    vNew p wA memo κ = tab (lenKey p κ) (V p κ) := by
  unfold vNew
  split
  · rename_i h
    congr 1
    funext s
    rw [look2_eq hw, V_eq_W p κ h]
  · rename_i h
    simp only []
    rw [convRow_eq _ _ _ _ (isTab_vRowOf p memo hm _) (isTab_getD hw _)]
    congr 1
    funext s
    rw [V_eq_conv p κ h]

theorem vMemo_ok (p : Params) (wA : Array (Array Nat)) (hw : IsTab2 wA (W p)) :
    ∀ e ∈ vMemo p wA, IsTab e.2 (V p e.1) := by
  have gen : ∀ (ks : List (List Nat)) (memo : List (List Nat × Array Nat)),
      (∀ e ∈ memo, IsTab e.2 (V p e.1)) →
      ∀ e ∈ ks.foldl (fun memo κ => (κ, vNew p wA memo κ) :: memo) memo, IsTab e.2 (V p e.1) := by
    intro ks
    induction ks with
    | nil => intro memo hm; exact hm
    | cons κ ks ih =>
      intro memo hm
      simp only [List.foldl_cons]
      apply ih
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsTab (vNew p wA memo κ) (V p κ)
        rw [vNew_eq p wA hw memo hm]; exact isTab_tab _ _
      · exact hm e he
  exact gen (keys p) [] (by intro e he; simp at he)

/-! ## Section 5: `ceil_sqrt`, `χ`, `Dist`, `G` -/

theorem leastFrom_spec (P : Nat → Bool) : ∀ (fuel u₀ : Nat),
    (∃ u, u₀ ≤ u ∧ u ≤ u₀ + fuel ∧ P u = true) →
    P (leastFrom P fuel u₀) = true ∧ ∀ u, u₀ ≤ u → P u = true → leastFrom P fuel u₀ ≤ u
  | 0, u₀, ⟨u, h1, h2, h3⟩ => by
    have hu : u = u₀ := by omega
    subst hu
    simp only [leastFrom]
    exact ⟨h3, fun v hv _ => hv⟩
  | fuel + 1, u₀, ⟨u, h1, h2, h3⟩ => by
    simp only [leastFrom]
    split
    · rename_i h; exact ⟨h, fun v hv _ => hv⟩
    · rename_i h
      have hne : u ≠ u₀ := by intro he; subst he; exact h h3
      have ih := leastFrom_spec P fuel (u₀ + 1) ⟨u, by omega, by omega, h3⟩
      refine ⟨ih.1, fun v hv hP => ?_⟩
      have hv' : v ≠ u₀ := by intro he; subst he; exact h hP
      exact ih.2 v (by omega) hP

/-- `ceilSqrt A` is the least `u` with `u² ≥ A`. -/
theorem ceilSqrt_spec (A : Nat) : (ceilSqrt A) ^ 2 ≥ A ∧ ∀ u, u ^ 2 ≥ A → ceilSqrt A ≤ u := by
  have hA : (fun u => decide (u ^ 2 ≥ A)) A = true := by
    simp only [decide_eq_true_eq]; rw [Nat.pow_two]; exact Nat.le_mul_self A
  have h := leastFrom_spec (fun u => decide (u ^ 2 ≥ A)) A 0 ⟨A, Nat.zero_le _, by omega, hA⟩
  unfold ceilSqrt
  constructor
  · simpa using h.1
  · intro u hu
    exact h.2 u (Nat.zero_le _) (by simpa using hu)

theorem ceilSqrt_unique (A c : Nat) (h1 : c ^ 2 ≥ A) (h2 : c = 0 ∨ (c - 1) ^ 2 < A) :
    c = ceilSqrt A := by
  obtain ⟨hr, hmin⟩ := ceilSqrt_spec A
  have hle : ceilSqrt A ≤ c := hmin c h1
  rcases Nat.lt_or_ge (ceilSqrt A) c with hlt | hge
  · rcases h2 with h0 | h3
    · omega
    · have h4 : ceilSqrt A ≤ c - 1 := by omega
      have h5 := Nat.pow_le_pow_left h4 2
      omega
  · omega

theorem check_eq (A c : Nat) :
    (if c ^ 2 ≥ A ∧ (c = 0 ∨ (c - 1) ^ 2 < A) then c else ceilSqrt A) = ceilSqrt A := by
  split
  · rename_i h; exact ceilSqrt_unique A c h.1 h.2
  · rfl

theorem ceilSqrtFast_eq (A : Nat) : ceilSqrtFast A = ceilSqrt A := by
  unfold ceilSqrtFast
  exact check_eq A _

theorem chiL_eq (p : Params) (t : Int) : chiL p (chiArr p) t = chi p t := by
  unfold chiL
  split
  · rename_i h
    rw [look_eq (show IsTab (chiArr p) (fun u => chi p (-(p.nu : Int) + (u : Int))) from
      isTab_tab _ _)]
    show chi p (-(p.nu : Int) + ((t + (p.nu : Int)).toNat : Int)) = chi p t
    rw [Int.toNat_of_nonneg h]
    congr 1
    omega
  · rfl

theorem distRow_eq (p : Params) (j : Nat) : distRow p j = tab (p.n * p.nu + 1) (Dist p j) := by
  unfold distRow
  simp only [ceilSqrtFast_eq]
  rfl

theorem gRow_eq (p : Params) (j : Nat) : gRow p (chiArr p) j = tab p.n (G p j) := by
  unfold gRow
  simp only [chiL_eq, distRow_eq, look_tab]
  rfl

/-- Every row stored in a table of `G` is the row of its index. -/
def GOK (p : Params) (gT : GTab) : Prop :=
  ∀ t (h : t < gT.parts.size) i (h2 : i < gT.parts[t].size),
    IsTab gT.parts[t][i] (G p (t * gT.size + i))

theorem lookG_eq (p : Params) (gT : GTab) (h : GOK p gT) (j d : Nat) : lookG p gT j d = G p j d := by
  unfold lookG
  simp only []
  split
  · split
    · rename_i h1 h2
      have h3 := h _ h1 _ h2
      rw [Nat.div_add_mod' j gT.size] at h3
      exact look_eq h3 d
    · rfl
  · rfl

theorem gok_of (p : Params) (size n : Nat) (f : Nat → Array (Array Nat))
    (hf : ∀ t i (h2 : i < (f t).size), IsTab (f t)[i] (G p (t * size + i))) :
    GOK p { size := size, parts := ((List.range n).map f).toArray } := by
  intro t h i
  have ht : (((List.range n).map f).toArray)[t]'h = f t := by simp
  show ∀ (h2 : i < ((((List.range n).map f).toArray)[t]'h).size),
    IsTab ((((List.range n).map f).toArray)[t]'h)[i] (G p (t * size + i))
  rw [ht]
  exact hf t i

theorem gPart_ok (p : Params) (lo cnt i : Nat) (h2 : i < (gPart p (chiArr p) lo cnt).size) :
    IsTab (gPart p (chiArr p) lo cnt)[i] (G p (lo + i)) := by
  have e : (gPart p (chiArr p) lo cnt)[i] = gRow p (chiArr p) (lo + i) := getElem_tab _ _ _ _
  rw [e, gRow_eq]; exact isTab_tab _ _

theorem gTab_ok (p : Params) (parts : Nat) : GOK p (gTab p parts) := by
  unfold gTab
  simp only [List.map_map]
  exact gok_of p _ parts _ (fun t i h2 => gPart_ok p _ _ i h2)

/-! ## Section 6: the table -/

theorem tabRow_eq (p : Params) (κ : List Nat) (vrow : Array Nat) (hv : IsTab vrow (V p κ))
    (gT : GTab) (hg : GOK p gT) : tabRow p vrow gT (ET p) κ = tab p.n (Tab p κ) := by
  unfold tabRow
  simp only [look_eq hv, lookG_eq p gT hg]
  rfl

/-- The table of the implementation: the keys of the recipe, in order, each with its row of `Tab`. -/
theorem tableRows_eq (p : Params) (parts : Nat) :
    tableRows p parts = (keys p).map (fun κ => (κ, tab p.n (Tab p κ))) := by
  unfold tableRows
  simp only []
  apply List.map_congr_left
  intro κ _
  rw [tabRow_eq p κ _ (isTab_vRowOf p _ (vMemo_ok p _ (isTab2_wArrs p)) κ) _ (gTab_ok p parts)]

theorem rowsOK_tableRows (p : Params) (parts : Nat) : RowsOK p (tableRows p parts) := by
  rw [tableRows_eq]
  intro e he
  obtain ⟨κ, _, rfl⟩ := List.mem_map.mp he
  exact isTab_tab _ _

end Correct
