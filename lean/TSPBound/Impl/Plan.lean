/-
The plan for the cost of a block with fixed heights of the interior points.

The points of a block are `0, …, k`; the interior points are `1, …, k - 1`, and `j = k - 1` is the
last of them.  For fixed heights of the interior points, every number below is the least of some sums
of two numbers found earlier:

* `A S u`, for a set `S` of interior points other than `j` and `u ∈ S`: the cheapest path that starts
  at `u`, visits the rest of `S` and ends at `j`;
* `H u v`: the cheapest path through all interior points that starts at `u` and ends at `v`;
* `L a v`: the cheapest path from the point 0 at height `a` through all interior points to `v`;
* `C a b`: the cheapest path from the point 0 at height `a` through all interior points to the
  point `k` at height `b`, that is `cost(g, ·)`.

A path from `u` to `v` (both different from `j`) passes through `j`, which cuts it into two paths
that end at `j`; this is the scheme of the C checker.  The numbers are kept in one array of *slots*.
Which sums are compared does not depend on the heights, so the list is made once (`mkPlan`).  When
the plan is made, it is tested that every slot refers to earlier slots only; the proof of correctness
uses this test and the recurrences, and nothing else about the order of the slots.
-/
import TSPBound.Impl.Basic

namespace Impl

/-- The numbers computed for fixed heights of the interior points. -/
inductive Slot where
  /-- the number 0 -/
  | zero
  /-- the edge between the interior points `u` and `v` -/
  | ein (u v : Nat)
  /-- the edge between the point 0 at height `a` and the interior point `u` -/
  | st (a u : Nat)
  /-- the edge between the interior point `v` and the point `k` at height `b` -/
  | en (b v : Nat)
  | A (S : List Nat) (u : Nat)
  | H (u v : Nat)
  | L (a v : Nat)
  | C (a b : Nat)
  deriving DecidableEq, Repr

/-- All sublists of a list. -/
def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: l => subsets l ++ (subsets l).map (x :: ·)

/-- The interior points `1, …, k - 1`. -/
def interior (k : Nat) : List Nat := List.range' 1 (k - 1)

/-- The interior points other than the last, `1, …, k - 2`. -/
def others (k : Nat) : List Nat := List.range' 1 (k - 2)

/-- The slots that are read from the table. -/
def inputSlots (k n : Nat) : List Slot :=
  [Slot.zero]
  ++ (interior k).flatMap (fun u => ((interior k).filter (fun v => v != u)).map (fun v => Slot.ein u v))
  ++ (List.range n).flatMap (fun a => (interior k).map (fun u => Slot.st a u))
  ++ (List.range n).flatMap (fun b => (interior k).map (fun v => Slot.en b v))

/-- The slots that are computed, in the order in which they are computed. -/
def targetSlots (k n : Nat) : List Slot :=
  let oth := others k
  let j := k - 1
  (List.range oth.length).flatMap (fun sz =>
      ((subsets oth).filter (fun S => S.length == sz + 1)).flatMap (fun S => S.map (fun u => Slot.A S u)))
  ++ oth.flatMap (fun u => [Slot.H u j, Slot.H j u])
  ++ oth.flatMap (fun u => (oth.filter (fun v => u < v)).map (fun v => Slot.H u v))
  ++ oth.flatMap (fun u => (oth.filter (fun v => u < v)).map (fun v => Slot.H v u))
  ++ (List.range n).flatMap (fun a => (interior k).map (fun v => Slot.L a v))
  ++ (List.range n).flatMap (fun a => (List.range n).map (fun b => Slot.C a b))

/-- The value of a computed slot is the least of the sums `x + y` over these pairs of slots. -/
def terms (k : Nat) : Slot → List (Slot × Slot)
  | .A S u =>
    if S = [u] then [(.ein u (k - 1), .zero)]
    else (S.erase u).map (fun y => (.ein u y, .A (S.erase u) y))
  | .H u v =>
    if v = k - 1 then [(.A (others k) u, .zero)]
    else if u = k - 1 then [(.A (others k) v, .zero)]
    else if u < v then
      (subsets ((others k).filter (fun x => x != u && x != v))).map (fun R =>
        (.A ((others k).filter (fun x => (R.contains x || x == u) && x != v)) u,
         .A ((others k).filter (fun x => !((R.contains x || x == u) && x != v))) v))
    else [(.H v u, .zero)]
  | .L a v =>
    if k = 2 then [(.st a v, .zero)]
    else ((interior k).filter (fun u => u != v)).map (fun u => (.st a u, .H u v))
  | .C a b => (interior k).map (fun v => (.L a v, .en b v))
  | _ => []

/-- Whether a slot is read from the table, with points and heights in their ranges. -/
def Slot.inRange (k n : Nat) : Slot → Bool
  | .zero => true
  | .ein u v => decide (1 ≤ u) && decide (u < k) && decide (1 ≤ v) && decide (v < k) && u != v
  | .st a u => decide (a < n) && decide (1 ≤ u) && decide (u < k)
  | .en b v => decide (b < n) && decide (1 ≤ v) && decide (v < k)
  | _ => false

/-- The conditions on a computed slot that the proof uses. -/
def Slot.valid (k : Nat) : Slot → Bool
  | .A .. => true
  | .H u v => (interior k).contains u && (interior k).contains v && u != v
  | .L _ v => (interior k).contains v
  | .C .. => true
  | _ => false

/-- The test of the order: the slot at position `i` is valid, has terms, and they are found before `i`. -/
def checkFrom (k : Nat) (slots : List Slot) : (targets : List Slot) → (i : Nat) → Bool
  | [], _ => true
  | s :: rest, i =>
    s.valid k && !(terms k s).isEmpty
      && (terms k s).all (fun ab => slots.idxOf ab.1 < i && slots.idxOf ab.2 < i)
      && checkFrom k slots rest (i + 1)

/-- The terms of a slot as positions in the list of slots: `[x_0, y_0, x_1, y_1, …]`. -/
def compileTerms (slots : List Slot) (ts : List (Slot × Slot)) : Array Nat :=
  (ts.flatMap (fun ab => [slots.idxOf ab.1, slots.idxOf ab.2])).toArray

/-- The positions of the slots `C a b`, `0 ≤ a, b < n`. -/
def outSlots (n : Nat) : List Slot :=
  (List.range n).flatMap (fun a => (List.range n).map (fun b => Slot.C a b))

structure Plan where
  /-- whether the tests succeeded -/
  ok : Bool
  inputs : List Slot
  /-- for each computed slot, its terms as positions -/
  prog : Array (Array Nat)
  /-- the positions of the slots `C a b` -/
  out : Array Nat
  /-- the number of slots -/
  size : Nat

def mkPlan (k n : Nat) : Plan :=
  let ins := inputSlots k n
  let tgs := targetSlots k n
  let slots := ins ++ tgs
  { ok := decide (2 ≤ k) && ins.all (Slot.inRange k n) && checkFrom k slots tgs ins.length
          && (outSlots n).all (fun s => slots.idxOf s < slots.length)
    inputs := ins
    prog := (tgs.map (fun s => compileTerms slots (terms k s))).toArray
    out := ((outSlots n).map (fun s => slots.idxOf s)).toArray
    size := slots.length }

/-! ## Running a plan -/

/-- The least of `val[ts[i]] + val[ts[i+1]]` over `i = 2, 4, …` (`fuel` of them) and `best`. -/
def minTermsGo (val ts : Array Nat) : (fuel i best : Nat) → Nat
  | 0, _, best => best
  | fuel + 1, i, best =>
    minTermsGo val ts fuel (i + 2) (min best (val.getD (ts.getD i 0) 0 + val.getD (ts.getD (i + 1) 0) 0))

/-- The least of `val[x] + val[y]` over the pairs `(x, y)` listed in `ts`. -/
def minTerms (val ts : Array Nat) : Nat :=
  minTermsGo val ts (ts.size / 2 - 1) 2 (val.getD (ts.getD 0 0) 0 + val.getD (ts.getD 1 0) 0)

/-- Appends the computed slots to the array of the input slots. -/
def runPlan (prog : Array (Array Nat)) (val : Array Nat) : Array Nat :=
  prog.foldl (fun val ts => val.push (minTerms val ts)) val

/-- Entry `(i, j, x, y)` of a four-fold table (0 outside it). -/
@[inline] def get4 (t : Array (Array (Array (Array Nat)))) (i j x y : Nat) : Nat :=
  if h : i < t.size then
    if h2 : j < t[i].size then
      if h3 : x < t[i][j].size then t[i][j][x].getD y 0 else 0
    else 0
  else 0

/-- The value of an input slot.  `eT` holds the edges of the block for all heights, and `ca` the
heights of the interior points `1, …, k - 1`. -/
def inputVal (eT : Array (Array (Array (Array Nat)))) (ca : Array Nat) (k : Nat) : Slot → Nat
  | .zero => 0
  | .ein u v => get4 eT u v (ca.getD (u - 1) 0) (ca.getD (v - 1) 0)
  | .st a u => get4 eT 0 u a (ca.getD (u - 1) 0)
  | .en b v => get4 eT v k (ca.getD (v - 1) 0) b
  | _ => 0

/-- Appends the values of the input slots. -/
def pushInputs (eT : Array (Array (Array (Array Nat)))) (ca : Array Nat) (k : Nat) :
    List Slot → Array Nat → Array Nat
  | [], acc => acc
  | s :: rest, acc => pushInputs eT ca k rest (acc.push (inputVal eT ca k s))

/-- The sum of the slots `C a b` over `0 ≤ a, b < n`, for the heights `c` of the interior points. -/
def configSum (plan : Plan) (eT : Array (Array (Array (Array Nat)))) (k : Nat) (c : List Nat) : Nat :=
  let val0 := pushInputs eT c.toArray k plan.inputs (Array.mkEmpty plan.size)
  let val := runPlan plan.prog val0
  plan.out.foldl (fun acc i => acc + val.getD i 0) 0

end Impl
