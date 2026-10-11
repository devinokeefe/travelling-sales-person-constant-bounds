/-
The top-level theorems about the routine of `TSPShared/Impl.lean`, which evaluates together the gap tuples
that differ only in the first and the last gap.  As in `Theorems.lean`, none of them has a hypothesis
on the parameter set: wherever the plan could fail its check, the implementation falls back on the
routine of `Impl/Sym.lean`, and where the given beginning of a gap tuple is not one, on the
definitions of `Spec`.
-/
import TSPShared.Correct

namespace Correct
open Spec Impl

/-- The table computed with tasks of Lean's pool (`tableRowsPool`) is the table of the recipe:
the keys in order, each with the row `Tab(κ, 0), …, Tab(κ, n - 1)`. -/
theorem tablePool_eq (p : Params) (parts : Nat) :
    tableRowsPool p parts = (keys p).map (fun κ => (κ, tab p.n (Tab p κ))) :=
  tableRowsPool_eq p parts

/-- The sums of one unit.  For interior gaps `mid = (g_2, …, g_{k-1})`, the entry `(g_1, g_k)` of the
result of `sharedSums` is the cell sum of the recipe for the gap tuple `(g_1, mid, g_k)`. -/
theorem sharedSums_eq_S (p : Params) (parts : Nat) (mid : List Nat) (g1 gk : Nat)
    (hg1 : g1 < m p) (hgk : gk < m p) :
    at2 (sharedSums p (tableRowsPool p parts) (mkPlanH p.k p.n) mid) g1 gk
      = S p (g1 :: (mid ++ [gk])) :=
  sharedSums_eq p _ (rowsOK_tableRowsPool p parts) mid g1 gk hg1 hgk

/-- `AofShared p threads parts t` is the list of the values `A_j(g_1, t)` of Section 8 for the first
gaps `g_1 = 0, …, m - 1`, whatever the numbers `threads` and `parts` and the list `t`. -/
theorem AofShared_eq_A (p : Params) (threads parts : Nat) (t : List Nat) :
    AofShared p threads parts t = (List.range (m p)).map (fun g1 => A p (g1 :: t)) :=
  AofShared_eq p threads parts t

/-- One value out of the list that a piece of an evaluation proves. -/
theorem A_of_list (p : Params) (t vals : List Nat)
    (h : (List.range (m p)).map (fun g1 => A p (g1 :: t)) = vals) (g1 : Nat) (hg1 : g1 < m p) :
    A p (g1 :: t) = vals.getD g1 0 := by
  rw [← h]
  simp [List.getD_eq_getElem?_getD, hg1]

end Correct
