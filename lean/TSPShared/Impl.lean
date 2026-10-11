/-
Cell sums with the fact "shared paths" of RECIPE.md Section 7 used in full.

The two end points `0` and `k` of a block are joined only to interior points.  So, for fixed heights
of the interior points `1, …, k - 1`:

* the numbers `A S u` and `H u v` of the plan (`Impl/Plan.lean`) depend only on the interior gaps
  `(g_2, …, g_{k-1})`, not on `g_1`, on `g_k` or on the heights of the end points;
* the numbers `L a v` depend on `g_1` as well, but not on `g_k`;
* only the numbers `C a b` depend on both.

Here one unit of work is a tuple `mid = (g_2, …, g_{k-1})` of interior gaps.  It gives the cell sums
of all gap tuples `(g_1, mid, g_k)` at once: the slots `A` and `H` are computed once for each tuple of
interior heights (by the plan `mkPlanH`), the numbers `L` once for each `g_1`, the numbers `C` for
each pair `(g_1, g_k)`.  The reflection of the heights is used as in `Impl/Sym.lean`.

`AofShared p threads t` gives the values `A_j(g_1, t)` of Section 8 for all `g_1`, on several threads.
-/
import TSPBound.Impl.Sym

namespace Impl
open Spec

/-! ## Loops -/

/-- The least of `best`, `f i`, …, `f (i + cnt - 1)`. -/
@[specialize] def minLoop (f : Nat → Nat) : (cnt i best : Nat) → Nat
  | 0, _, best => best
  | cnt + 1, i, best => minLoop f cnt (i + 1) (min best (f i))

/-- `acc` with `f i`, …, `f (i + cnt - 1)` appended. -/
@[specialize] def pushLoop {α : Type} (f : Nat → α) : (cnt i : Nat) → (acc : Array α) → Array α
  | 0, _, acc => acc
  | cnt + 1, i, acc => pushLoop f cnt (i + 1) (acc.push (f i))

/-- The table `[f 0, …, f (n-1)]`, built by a loop. -/
@[specialize] def tabN {α : Type} (n : Nat) (f : Nat → α) : Array α :=
  pushLoop f n 0 (Array.mkEmpty n)

/-! ## Sums of lists of lists of numbers, entry by entry

The cell sums of one unit are kept as a list (over `g_1`) of lists (over `g_k`).  A missing entry
counts as 0, so that the entry of a sum is the sum of the entries without any condition. -/

/-- The sum of two lists, entry by entry (the longer one decides the length). -/
def addV : List Nat → List Nat → List Nat
  | [], y => y
  | x :: xs, [] => x :: xs
  | a :: x, b :: y => (a + b) :: addV x y

/-- The sum of two lists of lists, entry by entry. -/
def addVV : List (List Nat) → List (List Nat) → List (List Nat)
  | [], y => y
  | x :: xs, [] => x :: xs
  | a :: x, b :: y => addV a b :: addVV x y

/-- Entry `(i, j)` of a list of lists (0 if there is none). -/
def at2 (x : List (List Nat)) (i j : Nat) : Nat := (x.getD i []).getD j 0

/-- `acc + f lo + f (lo + 1) + … + f (lo + n - 1)`, entry by entry. -/
@[specialize] def sumLoopVV (f : Nat → List (List Nat)) :
    (n lo : Nat) → (acc : List (List Nat)) → List (List Nat)
  | 0, _, acc => acc
  | n + 1, lo, acc => sumLoopVV f n (lo + 1) (addVV acc (f lo))

/-- `Σ f(t)` over all tuples `t` of length `len` with entries below `n`, entry by entry. -/
@[specialize] def sumTuplesVV (n : Nat) : (len : Nat) → (f : List Nat → List (List Nat)) → List (List Nat)
  | 0, f => f []
  | len + 1, f => sumLoopVV (fun x => sumTuplesVV n len (fun t => f (x :: t))) n 0 []

/-- `sumHalf` (`Impl/Sym.lean`), entry by entry: twice the sum over `x < n/2`, and the middle term if
`n` is odd. -/
@[specialize] def sumHalfVV (n : Nat) (f : Nat → List (List Nat)) : List (List Nat) :=
  let lower := sumLoopVV f (n / 2) 0 []
  addVV (addVV lower lower) (if n % 2 = 1 then f (n / 2) else [])

/-! ## The plan for the slots `A` and `H` -/

/-- The slots that are read from the table: 0 and the edges between interior points. -/
def inputSlotsH (k : Nat) : List Slot :=
  [Slot.zero]
  ++ (interior k).flatMap (fun u => ((interior k).filter (fun v => v != u)).map (fun v => Slot.ein u v))

/-- The slots `A S u` and `H u v`, in the order in which they are computed (the first four parts of
`targetSlots`). -/
def targetSlotsH (k : Nat) : List Slot :=
  let oth := others k
  let j := k - 1
  (List.range oth.length).flatMap (fun sz =>
      ((subsets oth).filter (fun S => S.length == sz + 1)).flatMap (fun S => S.map (fun u => Slot.A S u)))
  ++ oth.flatMap (fun u => [Slot.H u j, Slot.H j u])
  ++ oth.flatMap (fun u => (oth.filter (fun v => u < v)).map (fun v => Slot.H u v))
  ++ oth.flatMap (fun u => (oth.filter (fun v => u < v)).map (fun v => Slot.H v u))

/-- The slot whose value stands at the place `(u, v)` of the matrix of the `H`: `H u v`, and the
slot `zero` on the diagonal (where no path exists; the entry is never used). -/
def hSlot (u v : Nat) : Slot := if u = v then Slot.zero else Slot.H u v

structure PlanH where
  /-- whether the tests succeeded -/
  ok : Bool
  inputs : List Slot
  /-- for each computed slot, its terms as positions -/
  prog : Array (Array Nat)
  /-- `hpos[v - 1][u - 1]` is the position of the slot `H u v` -/
  hpos : Array (Array Nat)
  /-- the number of slots -/
  size : Nat

def mkPlanH (k n : Nat) : PlanH :=
  let ins := inputSlotsH k
  let tgs := targetSlotsH k
  let slots := ins ++ tgs
  { ok := decide (3 ≤ k) && ins.all (Slot.inRange k n) && checkFrom k slots tgs ins.length
          && (interior k).all (fun u => (interior k).all (fun v =>
                slots.idxOf (hSlot u v) < slots.length))
    inputs := ins
    prog := (tgs.map (fun s => compileTerms slots (terms k s))).toArray
    hpos := tab (k - 1) (fun v => tab (k - 1) (fun u => slots.idxOf (hSlot (u + 1) (v + 1))))
    size := slots.length }

/-! ## One tuple of interior heights -/

/-- `L a v` from the row `st a ·` and the column `H · v` (both with the interior points counted from
0, `K` of them, `K ≥ 2`): the least of `st a u + H u v` over `u ≠ v`. -/
@[inline] def lVal (st h : Array Nat) (K v : Nat) : Nat :=
  let s := if v = 0 then 1 else 0
  let x := st.getD s 0 + h.getD s 0
  minLoop (fun u => if u = v then x else st.getD u 0 + h.getD u 0) K 0 x

/-- `C a b` from the rows `L a ·` and `en b ·`: the least of `L a v + en b v` over all `v`. -/
@[inline] def cVal (l en : Array Nat) (K : Nat) : Nat :=
  minLoop (fun v => l.getD v 0 + en.getD v 0) (K - 1) 1 (l.getD 0 0 + en.getD 0 0)

/-- The matrix of the `H` for the heights `ca` of the interior points: `hT[v - 1][u - 1] = H u v`.
`eT` holds the edges of a block with the given interior gaps. -/
def hRows (planH : PlanH) (eT : Array (Array (Array (Array Nat)))) (k : Nat) (ca : Array Nat) :
    Array (Array Nat) :=
  let val := runPlan planH.prog (pushInputs eT ca k planH.inputs (Array.mkEmpty planH.size))
  planH.hpos.map (fun row => row.map (fun i => val.getD i 0))

/-- The edges at the point 0 for the heights `ca` of the interior points: entry `[a][u - 1]` is the
edge between the point 0 at height `a` and the interior point `u`. -/
def stRows (eT : Array (Array (Array (Array Nat)))) (k n : Nat) (ca : Array Nat) : Array (Array Nat) :=
  tabN n (fun a => tabN (k - 1) (fun u => get4 eT 0 (u + 1) a (ca.getD u 0)))

/-- The edges at the point `k`: entry `[b][v - 1]` is the edge between the interior point `v` and the
point `k` at height `b`. -/
def enRows (eT : Array (Array (Array (Array Nat)))) (k n : Nat) (ca : Array Nat) : Array (Array Nat) :=
  tabN n (fun b => tabN (k - 1) (fun v => get4 eT (v + 1) k (ca.getD v 0) b))

/-- The numbers `L a v`: entry `[a][v - 1]`, from the edges `st` at the point 0 and the matrix `hT` of
the `H`. -/
def lRows (st hT : Array (Array Nat)) (k n : Nat) : Array (Array Nat) :=
  tabN n (fun a =>
    let sa := st.getD a #[]
    tabN (k - 1) (fun v => lVal sa (hT.getD v #[]) (k - 1) v))

/-- The sum of the numbers `C a b` over `0 ≤ a, b < n`, from the numbers `L` and the edges `en` at the
point `k`. -/
def cSum (l en : Array (Array Nat)) (k n : Nat) : Nat :=
  sumLoop (fun a =>
    let la := l.getD a #[]
    sumLoop (fun b => cVal la (en.getD b #[]) (k - 1)) n 0 0) n 0 0

/-- For the heights `c` of the interior points: the sum of the cost over the heights of the two end
points, for every first gap (outer list) and every last gap (inner list).  `eT0` holds the edges
between interior points, the tables in `eTs` the edges at the point 0 for each first gap, the tables
in `eTe` the edges at the point `k` for each last gap. -/
def configShared (planH : PlanH) (eT0 : Array (Array (Array (Array Nat))))
    (eTs eTe : List (Array (Array (Array (Array Nat))))) (k n : Nat) (c : List Nat) : List (List Nat) :=
  let ca := c.toArray
  let hT := hRows planH eT0 k ca
  let ens := eTe.map (fun eT => enRows eT k n ca)
  eTs.map (fun eT =>
    let l := lRows (stRows eT k n ca) hT k n
    ens.map (fun en => cSum l en k n))

/-! ## One unit: all gap tuples with the same interior gaps -/

/-- The cell sums `S_g` of the gap tuples `g = (g_1, mid, g_k)`: entry `(g_1, g_k)` of the result.
`planH` is `mkPlanH p.k p.n`. -/
def sharedSums (p : Params) (rows : List (List Nat × Array Nat)) (planH : PlanH) (mid : List Nat) :
    List (List Nat) :=
  let mm := m p
  if planH.ok ∧ mid.length + 2 = p.k then
    let eT0 := edgeTab p rows (0 :: (mid ++ [0]))
    let eTs := (List.range mm).map (fun g1 => edgeTab p rows (g1 :: (mid ++ [0])))
    let eTe := (List.range mm).map (fun gk => edgeTab p rows (0 :: (mid ++ [gk])))
    let k := p.k
    sumHalfVV p.n (fun x =>
      sumTuplesVV p.n (k - 2) (fun c => configShared planH eT0 eTs eTe k p.n (x :: c)))
  else
    (List.range mm).map (fun g1 => (List.range mm).map (fun gk =>
      cellSumFlip p rows (mkPlan p.k p.n) (g1 :: (mid ++ [gk]))))

/-- The digits of `q` in base `mm`, the lowest first, `len` of them. -/
def digits (mm len q : Nat) : List Nat := (List.range len).map (fun i => q / mm ^ i % mm)

/-- The unit with the interior gaps `t ++ u`, where `u` is the tuple of length `r` with the index `q`.
The plan is built here, so that a task that computes a unit shares nothing with the other tasks but
the table. -/
def sharedUnit (p : Params) (rows : List (List Nat × Array Nat)) (t : List Nat) (r q : Nat) :
    List (List Nat) :=
  sharedSums p rows (mkPlanH p.k p.n) (t ++ digits (m p) r q)

/-! ## Several threads -/

/-- `xs.map f`, each value computed by a task of Lean's pool of threads (the size of the pool is not
set here: it is the number given to `lean -j`, or `LEAN_NUM_THREADS` for the executable). -/
def poolMap {α β : Type} (f : α → β) (xs : List α) : List β :=
  (xs.map (fun x => Task.spawn (fun _ => f x))).map Task.get

/-- One wave: `acc ++ r lo (min cnt (threads * chunk))`, computed by `threads` dedicated tasks, each for
at most `chunk` indices (as `parWave` of `Impl/Sym.lean`, for any type of results). -/
def parWaveG {α : Type} (r : Nat → Nat → List α) (threads chunk lo cnt : Nat) (acc : List α) : List α :=
  let tasks := (List.range threads).map (fun t =>
    Task.spawn (prio := .dedicated)
      (fun _ => r (lo + min cnt (t * chunk)) (min chunk (cnt - min cnt (t * chunk)))))
  tasks.foldl (fun acc t => acc ++ t.get) acc

/-- `acc ++ r lo cnt`, computed in at most `fuel` waves (the rest, if any, on one thread). -/
def parWavesG {α : Type} (r : Nat → Nat → List α) (threads chunk : Nat) :
    (fuel lo cnt : Nat) → (acc : List α) → List α
  | 0, lo, cnt, acc => acc ++ r lo cnt
  | fuel + 1, lo, cnt, acc =>
    if cnt = 0 then acc
    else
      parWavesG r threads chunk fuel (lo + min cnt (threads * chunk))
        (cnt - min cnt (threads * chunk)) (parWaveG r threads chunk lo cnt acc)

/-- `(List.range count).map f`.  With `threads = 0` each value is computed by a task of Lean's pool;
otherwise the values are computed in waves of `threads` dedicated tasks, one value each. -/
def unitsMap {α : Type} (f : Nat → α) (threads count : Nat) : List α :=
  if threads = 0 then poolMap f (List.range count)
  else parWavesG (fun lo cnt => (List.range' lo cnt).map f) threads 1 count 0 count []

/-- The weight vectors of all keys, as `vMemo` of `Impl/Table.lean`, but level by level: the vector of
a key with the sum `s + 1` needs the vector of a key with the sum `s`, so the keys of one level are
computed by tasks of Lean's pool. -/
def vMemoPool (p : Params) (wA : Array (Array Nat)) : List (List Nat × Array Nat) :=
  (List.range p.k).foldl (fun memo s =>
    poolMap (fun κ => (κ, vNew p wA memo κ)) ((keys p).filter (fun κ => κ.sum = s + 1)) ++ memo) []

/-- The table, as `tableRows` of `Impl/Table.lean`, with the weight vectors by `vMemoPool`, the table of
`G` in `parts` tasks, and the rows of the keys computed by tasks of Lean's pool. -/
def tableRowsPool (p : Params) (parts : Nat) : List (List Nat × Array Nat) :=
  let memo := vMemoPool p (wArrs p)
  let gT := gTab p parts
  let et := ET p
  poolMap (fun κ => (κ, tabRow p (vRowOf p memo κ) gT et κ)) (keys p)

/-! ## `A_j(g_1, t)` for all first gaps `g_1` -/

/-- The cell sum of the gap tuple `g = (g_1, t, u, g_k)` in the results `xs` of the units, where `t`
has `J - 1` entries and `u` has `r`: the unit with the index of `u`, its entry `(g_1, g_k)`. -/
def sharedLeaf (mm J r : Nat) (xs : Array (List (List Nat))) (g : List Nat) : Nat :=
  at2 (xs.getD (indexOf mm ((g.drop J).take r)) []) (g.headD 0) (g.getD (J + r) 0)

/-- The values `A_j(g_1, t)` of Section 8 for `g_1 = 0, …, m - 1`, where `t = (g_2, …, g_j)` is given:
the cell sums of all gap tuples `(g_1, t, …)` by units, then the recursion of Section 8 for each
`g_1`.  With `threads = 0` the units are computed by tasks of Lean's pool, one unit each; otherwise in
waves of `threads` dedicated tasks.  The table is computed in `parts` parts. -/
def AofShared (p : Params) (threads parts : Nat) (t : List Nat) : List Nat :=
  let mm := m p
  if t.length + 2 ≤ p.k ∧ t.all (fun x => x < mm) then
    let rows := tableRowsPool p parts
    let J := t.length + 1
    let r := p.k - 1 - J
    let xs := (unitsMap (sharedUnit p rows t r) threads (mm ^ r)).toArray
    let mass := massArr p
    (List.range mm).map (fun g1 => Afrom p mass p.k (sharedLeaf mm J r xs) (g1 :: t))
  else (List.range mm).map (fun g1 => A p (g1 :: t))

end Impl
