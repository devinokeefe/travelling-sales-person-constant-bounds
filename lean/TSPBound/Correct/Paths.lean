/-
What the slots of a plan mean, and the recurrences between them.

Every slot stands for a set of paths and a cost on them; a number is *good* for the slot if it is the
least cost of such a path.  The main result here (`good_step`) is that the least of the sums over the
terms of a slot is good for the slot if the numbers of the terms are good for their slots.
-/
import TSPBound.Correct.Basic

namespace Correct
open Spec Impl

/-! ## Lengths of paths -/

theorem pathLen_append (E : Nat → Nat → Nat) (l₁ : List Nat) (x : Nat) (l₂ : List Nat) :
    pathLen E (l₁ ++ x :: l₂) = pathLen E (l₁ ++ [x]) + pathLen E (x :: l₂) := by
  induction l₁ with
  | nil => simp [pathLen]
  | cons y l₁ ih =>
    cases l₁ with
    | nil => simp [pathLen]
    | cons z l₁ =>
      simp only [List.cons_append, pathLen] at ih ⊢
      omega

theorem pathLen_reverse (E : Nat → Nat → Nat) (hsym : ∀ u v, E u v = E v u) :
    ∀ l : List Nat, pathLen E l.reverse = pathLen E l
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
    have ih := pathLen_reverse E hsym (y :: l)
    have h : (x :: y :: l).reverse = l.reverse ++ y :: [x] := by simp
    rw [h, pathLen_append]
    have h2 : l.reverse ++ [y] = (y :: l).reverse := by simp
    rw [h2, ih]
    simp only [pathLen]
    rw [hsym y x]; omega

/-! ## The paths and the cost of a slot -/

/-- The paths that a slot stands for.  `k - 1` is the last interior point. -/
def Paths (k : Nat) : Slot → List Nat → Prop
  | .zero, π => π = []
  | .ein u v, π => π = [u, v]
  | .st _ u, π => π = [u]
  | .en _ v, π => π = [v]
  | .A S u, π => ∃ σ, σ.Perm (S.erase u) ∧ π = u :: (σ ++ [k - 1])
  | .H u v, π => π.Perm (interior k) ∧ π.head? = some u ∧ π.getLast? = some v
  | .L _ v, π => π.Perm (interior k) ∧ π.getLast? = some v
  | .C _ _, π => π.Perm (interior k)

/-- The cost of a path for a slot.  `ein u v` is the edge between interior points, `st a u` the edge
from the point 0 at height `a`, and `en b v` the edge to the point `k` at height `b`. -/
def Cost (ein st en : Nat → Nat → Nat) : Slot → List Nat → Nat
  | .zero, _ => 0
  | .ein _ _, π => pathLen ein π
  | .st a _, π => st a (π.headD 0)
  | .en b _, π => en b (π.headD 0)
  | .A _ _, π => pathLen ein π
  | .H _ _, π => pathLen ein π
  | .L a _, π => st a (π.headD 0) + pathLen ein π
  | .C a b, π => st a (π.headD 0) + pathLen ein π + en b (π.getLastD 0)

/-- `x` is the least cost of a path of the slot `s`. -/
def Good (k : Nat) (ein st en : Nat → Nat → Nat) (s : Slot) (x : Nat) : Prop :=
  (∃ π, Paths k s π ∧ Cost ein st en s π = x) ∧ ∀ π, Paths k s π → x ≤ Cost ein st en s π

theorem good_unique {k : Nat} {ein st en : Nat → Nat → Nat} {s : Slot} {x y : Nat}
    (hx : Good k ein st en s x) (hy : Good k ein st en s y) : x = y := by
  obtain ⟨⟨π, hπ, rfl⟩, hlx⟩ := hx
  obtain ⟨⟨σ, hσ, rfl⟩, hly⟩ := hy
  exact Nat.le_antisymm (hlx σ hσ) (hly π hπ)

/-- The value of an input slot. -/
def inputValA (ein st en : Nat → Nat → Nat) : Slot → Nat
  | .zero => 0
  | .ein u v => ein u v
  | .st a u => st a u
  | .en b v => en b v
  | _ => 0

theorem good_input (k n : Nat) (ein st en : Nat → Nat → Nat) (s : Slot) (h : s.inRange k n = true) :
    Good k ein st en s (inputValA ein st en s) := by
  cases s <;> simp [Slot.inRange] at h <;> simp [Good, Paths, Cost, inputValA, pathLen]

/-- The general step: soundness and completeness of the terms give a good number. -/
theorem good_of {k : Nat} {ein st en : Nat → Nat → Nat} {s : Slot} {ts : List (Slot × Slot)}
    (v : Slot → Nat) (hne : ts ≠ [])
    (hv : ∀ ab ∈ ts, Good k ein st en ab.1 (v ab.1) ∧ Good k ein st en ab.2 (v ab.2))
    (sound : ∀ ab ∈ ts, ∀ πa πb, Paths k ab.1 πa → Paths k ab.2 πb →
      ∃ π, Paths k s π ∧ Cost ein st en s π ≤ Cost ein st en ab.1 πa + Cost ein st en ab.2 πb)
    (complete : ∀ π, Paths k s π → ∃ ab ∈ ts, ∃ πa πb, Paths k ab.1 πa ∧ Paths k ab.2 πb ∧
      Cost ein st en ab.1 πa + Cost ein st en ab.2 πb ≤ Cost ein st en s π) :
    Good k ein st en s (minOf (ts.map (fun ab => v ab.1 + v ab.2))) := by
  have hne' : ts.map (fun ab => v ab.1 + v ab.2) ≠ [] := by simpa using hne
  obtain ⟨hmem, hle⟩ := minOf_spec _ hne'
  have lower : ∀ π, Paths k s π → minOf (ts.map (fun ab => v ab.1 + v ab.2)) ≤ Cost ein st en s π := by
    intro π hπ
    obtain ⟨ab, hab, πa, πb, ha, hb, hc⟩ := complete π hπ
    have h1 := hle (v ab.1 + v ab.2) (List.mem_map.mpr ⟨ab, hab, rfl⟩)
    have h2 := (hv ab hab).1.2 πa ha
    have h3 := (hv ab hab).2.2 πb hb
    omega
  refine ⟨?_, lower⟩
  obtain ⟨ab, hab, heq⟩ := List.mem_map.mp hmem
  obtain ⟨⟨πa, ha, hca⟩, _⟩ := (hv ab hab).1
  obtain ⟨⟨πb, hb, hcb⟩, _⟩ := (hv ab hab).2
  obtain ⟨π, hπ, hc⟩ := sound ab hab πa πb ha hb
  refine ⟨π, hπ, ?_⟩
  have := lower π hπ
  omega

/-! ## Facts about the interior points -/

theorem interior_eq (k : Nat) (hk : 2 ≤ k) : interior k = others k ++ [k - 1] := by
  unfold interior others
  have h : k - 1 = (k - 2) + 1 := by omega
  rw [h, List.range'_concat]
  simp; omega

theorem nodup_interior (k : Nat) : (interior k).Nodup := by
  unfold interior; exact List.nodup_range'

theorem nodup_others (k : Nat) : (others k).Nodup := by
  unfold others; exact List.nodup_range'

theorem last_not_mem_others (k : Nat) : k - 1 ∉ others k := by
  unfold others; simp [List.mem_range'_1]; omega

theorem mem_others_of {k u : Nat} (hk : 2 ≤ k) (hu : u ∈ interior k) (hne : u ≠ k - 1) : u ∈ others k := by
  rw [interior_eq k hk] at hu
  simpa [hne] using hu

theorem mem_interior_of_others {k u : Nat} (hk : 2 ≤ k) (hu : u ∈ others k) : u ∈ interior k := by
  rw [interior_eq k hk]; simp [hu]

end Correct
