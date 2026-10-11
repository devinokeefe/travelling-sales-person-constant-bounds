/-
The table of RECIPE.md Sections 2 to 6, computed with arrays.
-/
import TSPBound.Impl.Basic

namespace Impl
open Spec

/-! ## Sections 2 and 3 -/

/-- `Rup[0..I]`. -/
def rupArr (M I : Nat) : Array Nat :=
  let u := up M 1
  iterArr (fun r => cdiv (r * u) Q) I (Array.mkEmpty (I + 1)) Q

/-- `Spec.num` with `Rup`, `C_λ`, `C_μ` supplied. -/
def numG (p : Params) (rup : Nat → Nat) (cl cm : Nat) (c i : Nat) : Nat :=
  (if i < ncell p c then rup i * cl else 0) + (if i ≥ 1 then rup (i - 1) * cm else 0)

/-- `Spec.W` with `Rup`, `C_λ`, `C_μ` supplied. -/
def WG (p : Params) (rup : Nat → Nat) (cl cm : Nat) (c i : Nat) : Nat :=
  if c + 1 < m p then
    cdiv (cdiv (numG p rup cl cm c i) (2 ^ 14)) (Q - rup (ncell p c))
  else
    cdiv (numG p rup cl cm c i) (2 ^ 76) + (if i = NT p then cdiv (rup (NT p)) (2 ^ 14) else 0)

/-- The weights `W_c(i)`, `0 ≤ i ≤ n_c`, for every cell `c`. -/
def wArrs (p : Params) : Array (Array Nat) :=
  let rupA := rupArr p.M (max (bd p (m p - 1)) (NT p))
  let cl := Clam p
  let cm := Cmu p
  tab (m p) (fun c => tab (ncell p c + 1) (WG p (look rupA (Rup p.M)) cl cm c))

/-- The cell masses. -/
def massArr (p : Params) : Array Nat := tab (m p) (P p)

/-! ## Section 4 -/

/-- The row stored for a key, if there is one. -/
def findRow (rows : List (List Nat × Array Nat)) (κ : List Nat) : Option (Array Nat) :=
  (rows.find? (fun e => e.1 == κ)).map (·.2)

/-- The weight vector of `κ` from the memo (or from the definition, if it is missing). -/
def vRowOf (p : Params) (memo : List (List Nat × Array Nat)) (κ : List Nat) : Array Nat :=
  match findRow memo κ with
  | some r => r
  | none => tab (lenKey p κ) (V p κ)

/-- The base in which the factors of a convolution are split, so that the partial sums stay small. -/
def B : Nat := 2 ^ 24

/-- `ceil((Σ_{i+j=s} v(i)·w(j)) / D)` for `0 ≤ s < len`, where `0 ≤ i < len'` and `0 ≤ j ≤ nc`.
Every factor is split as `x = x₁·B + x₀`, and the sums of the products of the parts are formed
separately; for the parameters of the paper they fit into machine words. -/
def convRow (v w : Array Nat) (fv fw : Nat → Nat) (len' nc len : Nat) : Array Nat :=
  let v0 := tab len' (fun i => look v fv i % B)
  let v1 := tab len' (fun i => look v fv i / B)
  let w0 := tab (nc + 1) (fun j => look w fw j % B)
  let w1 := tab (nc + 1) (fun j => look w fw j / B)
  tab len (fun s =>
    let lo := s - min s nc
    let cnt := min (s + 1) len' - lo
    let s11 := sumLoop (fun i => look v1 (fun i => fv i / B) i * look w1 (fun j => fw j / B) (s - i)) cnt lo 0
    let s10 := sumLoop (fun i => look v1 (fun i => fv i / B) i * look w0 (fun j => fw j % B) (s - i)) cnt lo 0
    let s01 := sumLoop (fun i => look v0 (fun i => fv i % B) i * look w1 (fun j => fw j / B) (s - i)) cnt lo 0
    let s00 := sumLoop (fun i => look v0 (fun i => fv i % B) i * look w0 (fun j => fw j % B) (s - i)) cnt lo 0
    cdiv (s11 * B * B + (s10 + s01) * B + s00) D)

/-- The weight vector of `κ`, given those of the keys before it. -/
def vNew (p : Params) (wA : Array (Array Nat)) (memo : List (List Nat × Array Nat))
    (κ : List Nat) : Array Nat :=
  if κ.sum ≤ 1 then
    tab (lenKey p κ) (fun s => look2 wA (W p) (lastCell κ) s)
  else
    let c := lastCell κ
    let κ' := reduce κ c
    convRow (vRowOf p memo κ') (wA.getD c #[]) (V p κ') (W p c) (lenKey p κ') (ncell p c) (lenKey p κ)

/-- The weight vectors of all keys (the last key first). -/
def vMemo (p : Params) (wA : Array (Array Nat)) : List (List Nat × Array Nat) :=
  (keys p).foldl (fun memo κ => (κ, vNew p wA memo κ) :: memo) []

/-! ## Section 5 -/

/-- `χ(-ν), …, χ(ν)`. -/
def chiArr (p : Params) : Array Nat :=
  tab (2 * p.nu + 1) (fun u => chi p (-(p.nu : Int) + (u : Int)))

/-- `χ(t)` from the table. -/
@[inline] def chiL (p : Params) (chiA : Array Nat) (t : Int) : Nat :=
  if 0 ≤ t + (p.nu : Int) then
    look chiA (fun u => chi p (-(p.nu : Int) + (u : Int))) (t + (p.nu : Int)).toNat
  else chi p t

/-- `Dist(j, τ)` for `0 ≤ τ ≤ n·ν`. -/
def distRow (p : Params) (j : Nat) : Array Nat :=
  let al := alpha p
  let ga := gamma p
  tab (p.n * p.nu + 1) (fun tau =>
    cdiv (ceilSqrtFast (((al * j) ^ 2 + (ga * tau) ^ 2) * F ^ 2)) (al * p.M))

/-- `G(j, d)` for `0 ≤ d ≤ n - 1`. -/
def gRow (p : Params) (chiA : Array Nat) (j : Nat) : Array Nat :=
  let dr := distRow p j
  tab p.n (fun d =>
    cdiv (∑ t from -(p.nu : Int) to (p.nu : Int),
            chiL p chiA t * look dr (Dist p j) (Int.natAbs ((d * p.nu : Nat) + t)))
         (4 * p.nu ^ 2))

/-- `G(j, d)` for `lo ≤ j < lo + cnt`. -/
def gPart (p : Params) (chiA : Array Nat) (lo cnt : Nat) : Array (Array Nat) :=
  tab cnt (fun i => gRow p chiA (lo + i))

/-- `G(j, d)` for `0 ≤ j ≤ J = k·(b_{m-1} + N_T)`, in parts of `size` values of `j`. -/
structure GTab where
  size : Nat
  parts : Array (Array (Array Nat))

/-- The table of `G`, computed in `parts` tasks. -/
def gTab (p : Params) (parts : Nat) : GTab :=
  let chiA := chiArr p
  let total := p.k * (bd p (m p - 1) + NT p) + 1
  let size := total / parts + 1
  let tasks := (List.range parts).map (fun t =>
    Task.spawn (fun _ => gPart p chiA (t * size) (min size (total - t * size))))
  { size := size, parts := (tasks.map Task.get).toArray }

/-- `G(j, d)` from the table. -/
@[inline] def lookG (p : Params) (gT : GTab) (j d : Nat) : Nat :=
  let t := j / gT.size
  let i := j % gT.size
  if h : t < gT.parts.size then
    if h2 : i < gT.parts[t].size then look gT.parts[t][i] (G p j) d else G p j d
  else G p j d

/-! ## Section 6 -/

/-- `Tab(κ, d)` for `0 ≤ d ≤ n - 1`. -/
def tabRow (p : Params) (vrow : Array Nat) (gT : GTab) (et : Nat) (κ : List Nat) :
    Array Nat :=
  let bk := bKey p κ
  tab p.n (fun d =>
    cdiv (∑ s < lenKey p κ, look vrow (V p κ) s * lookG p gT (bk + s) d) D
      + κ.getD (m p - 1) 0 * et)

/-- The table: the keys in order, each with its row. -/
def tableRows (p : Params) (parts : Nat) : List (List Nat × Array Nat) :=
  let memo := vMemo p (wArrs p)
  let gT := gTab p parts
  let et := ET p
  (keys p).map (fun κ => (κ, tabRow p (vRowOf p memo κ) gT et κ))

end Impl
