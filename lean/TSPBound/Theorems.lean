/-
The top-level theorems about the implementation.  None of them has a hypothesis: they hold for every
parameter set (wherever a table could be too short, or the plan could fail its check, the
implementation falls back on the definitions of `Spec`).
-/
import TSPBound.Correct.Table
import TSPBound.Correct.Sym

namespace Correct
open Spec Impl

/-- The table of the implementation is the table of the recipe: the keys in order, each with the
row `Tab(κ, 0), …, Tab(κ, n - 1)`. -/
theorem table_eq (p : Params) (parts : Nat) :
    tableRows p parts = (keys p).map (fun κ => (κ, tab p.n (Tab p κ))) :=
  tableRows_eq p parts

/-- The cell sum of the implementation (dynamic programme, heights of the end points summed inside)
is the cell sum of the recipe (minimum over all orders, sum over all height tuples). -/
theorem cellSum_eq_S (p : Params) (parts : Nat) (g : List Nat) :
    cellSum p (tableRows p parts) (mkPlan p.k p.n) g = S p g :=
  cellSum_eq p _ (rowsOK_tableRows p parts) g

/-- A range of the list of cell sums, as the executable computes it. -/
theorem sumsRange_eq_S (p : Params) (parts lo cnt : Nat) :
    sumsRange p (tableRows p parts) lo cnt
      = (List.range' lo cnt).map (fun index => S p (gapOfIndex p index)) :=
  sumsRange_eq p _ (rowsOK_tableRows p parts) lo cnt

/-- The total from the list of all cell sums, as the executable computes it. -/
theorem totalOfSums_cellSums (p : Params) : totalOfSums p (cellSums p).toArray = Spec.total p :=
  totalOfSums_eq p

/-- The total of the implementation is the total of the recipe. -/
theorem total_eq (p : Params) : Impl.total p = Spec.total p :=
  total_eq_of p (rowsOK_tableRows p 1)

/-- The same for the implementation on several threads. -/
theorem totalPar_eq (p : Params) (threads : Nat) : Impl.totalPar p threads = Spec.total p :=
  totalPar_eq_of p threads (rowsOK_tableRows p 1)

/-! ## With the symmetry of the heights, and in pieces -/

/-- The cell sum with the height of the first interior point restricted to the lower half is the
cell sum of the recipe. -/
theorem cellSumFlip_eq_S (p : Params) (parts : Nat) (g : List Nat) :
    cellSumFlip p (tableRows p parts) (mkPlan p.k p.n) g = S p g :=
  cellSumFlip_eq p _ (rowsOK_tableRows p parts) g

/-- The cell sums of the gap tuples with indices `base + step·t`, as the executable computes them
(with `base = 0` and `step = 1`). -/
theorem sumsStep_eq_S (p : Params) (parts base step lo cnt : Nat) :
    sumsStep p (tableRows p parts) base step lo cnt
      = (List.range' lo cnt).map (fun t => S p (gapOfIndex p (base + step * t))) :=
  sumsStep_eq p _ (rowsOK_tableRows p parts) base step lo cnt

/-- `A_j(g)` of Section 8 for the beginning `g` of a gap tuple, computed on several threads. -/
theorem AofPar_eq_A (p : Params) (threads : Nat) (g : List Nat) : AofPar p threads g = A p g :=
  AofPar_eq p threads g

/-- In particular the total. -/
theorem AofPar_nil (p : Params) (threads : Nat) : AofPar p threads [] = Spec.total p :=
  AofPar_eq p threads []

/-- The total from the values `A_j(g)` of all beginnings `g` of length `j`. -/
theorem totalFrom_eq_total (p : Params) (j : Nat) (vals : List (List Nat × Nat)) (hj : j ≤ p.k)
    (h : vals = (tuples j (m p)).map (fun g => (g, A p g))) : totalFrom p j vals = Spec.total p :=
  totalFrom_eq p j vals hj h

end Correct
