/-
Tools of the implementation: tables with a fall-back, loops, and a fast `ceil_sqrt`.

A table lookup `look t f i` returns entry `i` of the array `t`, or `f i` if `t` is too short.  The
tables are built so that the fall-back is never taken for sane parameters; it is there so that the
correctness theorems hold without hypotheses about ranges.
-/
import TSPBound.Spec

namespace Impl
open Spec

/-- The table `[f 0, …, f (n-1)]`. -/
@[specialize] def tab {α : Type} (n : Nat) (f : Nat → α) : Array α :=
  Array.ofFn (n := n) (fun i => f i.val)

/-- Entry `i` of a table of `f`; `f i` itself if the table is too short. -/
@[inline] def look (t : Array Nat) (f : Nat → Nat) (i : Nat) : Nat :=
  if h : i < t.size then t[i] else f i

/-- Entry `(i, j)` of a table of tables of `f`. -/
@[inline] def look2 (t : Array (Array Nat)) (f : Nat → Nat → Nat) (i j : Nat) : Nat :=
  if h : i < t.size then look t[i] (f i) j else f i j

/-- Entry `(i, j, x, y)` of a four-fold table of `f`. -/
@[inline] def look4 (t : Array (Array (Array (Array Nat)))) (f : Nat → Nat → Nat → Nat → Nat)
    (i j x y : Nat) : Nat :=
  if h : i < t.size then
    if h2 : j < t[i].size then look2 t[i][j] (f i j) x y else f i j x y
  else f i j x y

/-- `acc + f lo + f (lo + 1) + … + f (lo + n - 1)`, as a loop. -/
@[specialize] def sumLoop (f : Nat → Nat) : (n lo acc : Nat) → Nat
  | 0, _, acc => acc
  | n + 1, lo, acc => sumLoop f n (lo + 1) (acc + f lo)

/-- `[x, step x, step (step x), …]` with `n + 1` entries, appended to `acc`. -/
@[specialize] def iterArr (step : Nat → Nat) : (n : Nat) → (acc : Array Nat) → (x : Nat) → Array Nat
  | 0, acc, x => acc.push x
  | n + 1, acc, x => iterArr step n (acc.push x) (step x)

/-- Newton's iteration for the square root of `A`, started above the root. -/
def sqrtIter (A : Nat) : (fuel x : Nat) → Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := (x + A / x) / 2
    if y < x then sqrtIter A fuel y else x

/-- `ceil_sqrt(A)`.  A candidate is found by Newton's iteration and then tested against the
definition; if the test failed, the slow search of `Spec.ceilSqrt` would be used. -/
def ceilSqrtFast (A : Nat) : Nat :=
  let r := sqrtIter A 300 (2 ^ (Nat.log2 A / 2 + 1))
  let c := if r * r ≥ A then r else r + 1
  if c ^ 2 ≥ A ∧ (c = 0 ∨ (c - 1) ^ 2 < A) then c else ceilSqrt A

end Impl
