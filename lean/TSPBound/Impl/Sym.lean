/-
The cell sums with the symmetry of the heights used, and the total in pieces.

Replacing every height `a_i` by `n - 1 - a_i` leaves all differences of heights, and so the cost,
unchanged.  Hence it is enough to let the height of the first interior point run over the lower half.
-/
import TSPBound.Impl.CellSum

namespace Impl
open Spec

/-- `Σ_{x<n} f(x)` for an `f` with `f(n - 1 - x) = f(x)`: twice the sum over `x < n/2`, and the middle
term if `n` is odd. -/
@[specialize] def sumHalf (n : Nat) (f : Nat → Nat) : Nat :=
  2 * sumLoop f (n / 2) 0 0 + (if n % 2 = 1 then f (n / 2) else 0)

/-- The cell sum `S_g`, with the height of the first interior point restricted to the lower half.
`plan` is `mkPlan p.k p.n`. -/
def cellSumFlip (p : Params) (rows : List (List Nat × Array Nat)) (plan : Plan) (g : List Nat) : Nat :=
  if plan.ok then
    let eT := edgeTab p rows g
    let k := p.k
    sumHalf p.n (fun x => sumTuples p.n (k - 2) (fun c => configSum plan eT k (x :: c)))
  else S p g

/-- The index `g_1 + g_2·m + … + g_j·m^{j-1}` of a gap tuple (or of the beginning of one). -/
def indexOf (mm : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => x + mm * indexOf mm l

/-- The cell sums `S_g` for the gap tuples with indices `base + step·t`, `lo ≤ t < lo + cnt`. -/
def sumsStep (p : Params) (rows : List (List Nat × Array Nat)) (base step lo cnt : Nat) : List Nat :=
  let plan := mkPlan p.k p.n
  (List.range' lo cnt).map (fun t => cellSumFlip p rows plan (gapOfIndex p (base + step * t)))

/-! ## Several threads -/

/-- One wave: `acc ++ r lo (min cnt (threads * chunk))`, computed by `threads` tasks, each for at most
`chunk` indices.  Here `r lo cnt` is a list of `cnt` values that belong to `lo, …, lo + cnt - 1`. -/
def parWave (r : Nat → Nat → List Nat) (threads chunk lo cnt : Nat) (acc : List Nat) : List Nat :=
  let tasks := (List.range threads).map (fun t =>
    Task.spawn (prio := .dedicated)
      (fun _ => r (lo + min cnt (t * chunk)) (min chunk (cnt - min cnt (t * chunk)))))
  tasks.foldl (fun acc t => acc ++ t.get) acc

/-- `acc ++ r lo cnt`, computed in at most `fuel` waves (the rest, if any, on one thread). -/
def parWaves (r : Nat → Nat → List Nat) (threads chunk : Nat) :
    (fuel lo cnt : Nat) → (acc : List Nat) → List Nat
  | 0, lo, cnt, acc => acc ++ r lo cnt
  | fuel + 1, lo, cnt, acc =>
    if cnt = 0 then acc
    else
      parWaves r threads chunk fuel (lo + min cnt (threads * chunk))
        (cnt - min cnt (threads * chunk)) (parWave r threads chunk lo cnt acc)

/-- `A_j(g)` for the beginning `g = (g_1, …, g_j)` of a gap tuple, computed on `threads` threads:
the cell sums of all gap tuples that begin with `g`, then the recursion of Section 8. -/
def AofPar (p : Params) (threads : Nat) (g : List Nat) : Nat :=
  if g.length ≤ p.k ∧ g.all (fun x => x < m p) then
    let rows := tableRows p 1
    let j := g.length
    let count := (m p) ^ (p.k - j)
    let chunk := max 1 (min 64 (count / (4 * threads)))
    let sums := parWaves (sumsStep p rows (indexOf (m p) g) ((m p) ^ j)) threads chunk count 0 count []
    totalRec p (massArr p) sums.toArray (p.k - j) 0 0
  else A p g

/-! ## The total from the values of `A_j` -/

/-- The recursion of Section 8, started from given values `f g` of `A_j(g)`. -/
def Afrom (p : Params) (mass : Array Nat) (j : Nat) (f : List Nat → Nat) (g : List Nat) : Nat :=
  if j ≤ g.length then f g
  else cdiv (∑ c < m p, look mass (P p) c * Afrom p mass j f (g ++ [c])) D
termination_by j - g.length
decreasing_by simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- The value listed for `g` (0 if there is none). -/
def valOf (vals : List (List Nat × Nat)) (g : List Nat) : Nat :=
  match vals.find? (fun e => e.1 == g) with
  | some e => e.2
  | none => 0

/-- The total `A_0` from a list of the values `A_j(g)` for all `g` of length `j`. -/
def totalFrom (p : Params) (j : Nat) (vals : List (List Nat × Nat)) : Nat :=
  Afrom p (massArr p) j (valOf vals) []

end Impl
