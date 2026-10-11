/-
The cell sums and the total (RECIPE.md Sections 7 and 8).
-/
import TSPBound.Impl.Table
import TSPBound.Impl.Plan

namespace Impl
open Spec

/-- The row of the table for a key (or the row by the definition, if the key is missing). -/
def rowOf (p : Params) (rows : List (List Nat × Array Nat)) (κ : List Nat) : Array Nat :=
  match findRow rows κ with
  | some r => r
  | none => tab p.n (Tab p κ)

/-- The edge between the points `i` and `j` of a block with gap tuple `g`, at heights `x` and `y`. -/
def Ef (p : Params) (g : List Nat) (i j x y : Nat) : Nat :=
  Tab p (keyOf p g (min i j) (max i j)) (absDiff x y)

/-- `Ef p g i j x y` for `0 ≤ i, j ≤ k`, `i ≠ j`, and all heights. -/
def edgeTab (p : Params) (rows : List (List Nat × Array Nat)) (g : List Nat) :
    Array (Array (Array (Array Nat))) :=
  tab (p.k + 1) (fun i => tab (p.k + 1) (fun j =>
    if i = j then #[]
    else
      let κ := keyOf p g (min i j) (max i j)
      let row := rowOf p rows κ
      tab p.n (fun x => tab p.n (fun y => look row (Tab p κ) (absDiff x y)))))

/-- `Σ f(t)` over all tuples `t` of length `len` with entries below `n`. -/
@[specialize] def sumTuples (n : Nat) : (len : Nat) → (f : List Nat → Nat) → Nat
  | 0, f => f []
  | len + 1, f => sumLoop (fun x => sumTuples n len (fun t => f (x :: t))) n 0 0

/-- The cell sum `S_g`.  `plan` is `mkPlan p.k p.n`. -/
def cellSum (p : Params) (rows : List (List Nat × Array Nat)) (plan : Plan) (g : List Nat) : Nat :=
  if plan.ok then
    let eT := edgeTab p rows g
    let k := p.k
    sumTuples p.n (k - 1) (fun c => configSum plan eT k c)
  else S p g

/-- `A_j(g)` as in Section 8. -/
def Arec (p : Params) (rows : List (List Nat × Array Nat)) (plan : Plan) (mass : Array Nat)
    (g : List Nat) : Nat :=
  if p.k ≤ g.length then cellSum p rows plan g
  else cdiv (∑ c < m p, look mass (P p) c * Arec p rows plan mass (g ++ [c])) D
termination_by p.k - g.length
decreasing_by simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- `A_j(g)` for the table `rows`. -/
def Aof (p : Params) (rows : List (List Nat × Array Nat)) (g : List Nat) : Nat :=
  Arec p rows (mkPlan p.k p.n) (massArr p) g

/-- The total `A_0`, computed on one thread. -/
def total (p : Params) : Nat := Aof p (tableRows p 1) []

/-! ## The list of cell sums, as the executable computes it -/

/-- The cell sums with indices `lo, …, lo + cnt - 1`. -/
def sumsRange (p : Params) (rows : List (List Nat × Array Nat)) (lo cnt : Nat) : List Nat :=
  let plan := mkPlan p.k p.n
  (List.range' lo cnt).map (fun index => cellSum p rows plan (gapOfIndex p index))

/-- The total from the list of all cell sums in index order: `A_j(g)` is found at the position
`g_1 + g_2·m + … + g_j·m^{j-1}` of level `j`. -/
def totalRec (p : Params) (mass : Array Nat) (sums : Array Nat) : (rest len index : Nat) → Nat
  | 0, _, index => sums.getD index 0
  | rest + 1, len, index =>
    cdiv (∑ c < m p, look mass (P p) c * totalRec p mass sums rest (len + 1) (index + c * (m p) ^ len)) D

/-- The total from the list of all cell sums. -/
def totalOfSums (p : Params) (sums : Array Nat) : Nat :=
  totalRec p (massArr p) sums p.k 0 0

/-! ## The same on several threads -/

/-- One wave: `acc ++ sumsRange p rows lo (min cnt (threads * chunk))`, computed by `threads` tasks,
each for at most `chunk` indices. -/
def sumsWave (p : Params) (rows : List (List Nat × Array Nat)) (threads chunk lo cnt : Nat)
    (acc : List Nat) : List Nat :=
  let tasks := (List.range threads).map (fun t =>
    Task.spawn (prio := .dedicated)
      (fun _ => sumsRange p rows (lo + min cnt (t * chunk)) (min chunk (cnt - min cnt (t * chunk)))))
  tasks.foldl (fun acc t => acc ++ t.get) acc

/-- `acc ++ sumsRange p rows lo cnt`, computed in at most `fuel` waves (the rest, if any, on one
thread). -/
def sumsWaves (p : Params) (rows : List (List Nat × Array Nat)) (threads chunk : Nat) :
    (fuel lo cnt : Nat) → (acc : List Nat) → List Nat
  | 0, lo, cnt, acc => acc ++ sumsRange p rows lo cnt
  | fuel + 1, lo, cnt, acc =>
    if cnt = 0 then acc
    else
      sumsWaves p rows threads chunk fuel (lo + min cnt (threads * chunk))
        (cnt - min cnt (threads * chunk)) (sumsWave p rows threads chunk lo cnt acc)

/-- The total `A_0`, computed on `threads` threads. -/
def totalPar (p : Params) (threads : Nat) : Nat :=
  let rows := tableRows p 1
  let count := (m p) ^ p.k
  let chunk := max 1 (min 64 (count / (4 * threads)))
  totalOfSums p (sumsWaves p rows threads chunk count 0 count []).toArray

end Impl
