/-!
# Executable Fixed-Point Certificate Kernel (Pure, Monad-Free, Zero Mathlib)

Pure Lean 4 integer fixed-point evaluators (`SCALE = 10^6`) written with clean
structural/tail recursion (no `Id.run do` / `let mut`) so that:
1. All 24 certificate shards compile in parallel with zero Mathlib startup cost and
   run at native C loop speed under `native_decide`.
2. Every function admits straightforward induction proofs in `BHHBounds.Cert.Soundness`.
-/

namespace BHHBounds.Cert

/-- Fixed-point scale `S = 10^6`. -/
def S : Int := 1000000
def piLo : Int := 3141592
def piHi : Int := 3141593
/-- Certified bounds on `exp(-1/4)` scaled by `10^6`: `0.778800 ≤ e^(-1/4) ≤ 0.778801`. -/
def eQtrLo : Int := 778800
def eQtrHi : Int := 778801

/-! ## Pure Integer Square Root (Zero Mathlib Dependencies) -/

/-- Exact integer square root `⌊√n⌋` via binary search on `[lo, hi]` with invariant
`lo * lo ≤ n < hi * hi` (verified directly in `Soundness.lean`). -/
def natSqrtBin (n lo hi : Nat) : Nat :=
  if hi ≤ lo + 1 then lo
  else
    let mid := (lo + hi) / 2
    if mid * mid ≤ n then natSqrtBin n mid hi
    else natSqrtBin n lo mid
termination_by hi - lo
decreasing_by all_goals omega

/-- Find an upper bound `hi` with `n < hi * hi` via doubling (falling back to `n + 1`). -/
def natSqrtUpper (n : Nat) : Nat → Nat → Nat
  | 0, _ => n + 1
  | fuel + 1, hi =>
    if n < hi * hi then hi
    else natSqrtUpper n fuel (hi * 2)

/-- Exact integer square root `⌊√n⌋`. -/
@[inline] def natSqrt (n : Nat) : Nat :=
  if n == 0 then 0
  else
    let hi := natSqrtUpper n 64 1
    natSqrtBin n 0 hi

/-! ## Basic Fixed-Point Rounding Operations -/

/-- Floor of `(a * b) / S` for `a, b ≥ 0`. -/
@[inline] def mulLo (a b : Int) : Int := (a * b) / S

/-- Ceiling of `(a * b) / S` for `a, b ≥ 0`. -/
@[inline] def mulHi (a b : Int) : Int := (a * b + S - 1) / S

/-- Ceiling of `(a * S) / b` for `a ≥ 0, b > 0`. -/
@[inline] def divHi (a b : Int) : Int := (a * S + b - 1) / b

/-- Floor of `√n` for `n : Int` (returns `0` if `n ≤ 0`). -/
@[inline] def sqrtSqLo (n : Int) : Int :=
  if n ≤ 0 then 0 else Int.ofNat (natSqrt n.toNat)

/-- Ceiling of `√n` for `n : Int` (returns `0` if `n ≤ 0`). -/
@[inline] def sqrtSqHi (n : Int) : Int :=
  if n ≤ 0 then 0
  else
    let m := n.toNat
    let r := natSqrt m
    if r * r == m then Int.ofNat r else Int.ofNat (r + 1)

/-- Mathematical floor division `⌊a / b⌋` for `b > 0`. -/
@[inline] def fdiv (a b : Int) : Int := Int.fdiv a b

/-- Mathematical ceiling division `⌈a / b⌉` for `b > 0`. -/
@[inline] def cdiv (a b : Int) : Int := Int.fdiv (a + b - 1) b

/-! ## Certified `exp(-x / S)` via `1/4`-Splitting & Degree-5/6 Taylor Polynomials -/

def powLo : Nat → Int → Int
  | 0, _ => S
  | n + 1, b => mulLo b (powLo n b)

def powHi : Nat → Int → Int
  | 0, _ => S
  | n + 1, b => mulHi b (powHi n b)

/-- Certified LOWER bound on `exp(-x / S) * S` for `x ≥ 0`. -/
def expNegLo (x : Int) : Int :=
  if x ≤ 0 then S
  else
    let q := (x / 250000).toNat
    if q > 64 then 0
    else
      let r := x % 250000
      let r2Lo := mulLo r r
      let r2Hi := mulHi r r
      let r3Hi := mulHi r2Hi r
      let r4Lo := mulLo r2Lo r2Lo
      let r5Hi := mulHi (mulHi r2Hi r2Hi) r
      let t2 := r2Lo / 2
      let t3 := (r3Hi + 5) / 6
      let t4 := r4Lo / 24
      let t5 := (r5Hi + 119) / 120
      let poly := S - r + t2 - t3 + t4 - t5
      if poly ≤ 0 then 0 else mulLo poly (powLo q eQtrLo)

/-- Certified UPPER bound on `exp(-x / S) * S` for `x ≥ 0`. -/
def expNegHi (x : Int) : Int :=
  if x ≤ 0 then S
  else
    let q := (x / 250000).toNat
    if q > 64 then 1
    else
      let r := x % 250000
      let r2Lo := mulLo r r
      let r2Hi := mulHi r r
      let r3Lo := mulLo r2Lo r
      let r4Hi := mulHi r2Hi r2Hi
      let r5Lo := mulLo (mulLo r2Lo r2Lo) r
      let r6Hi := mulHi r4Hi r2Hi
      let t2 := (r2Hi + 1) / 2
      let t3 := r3Lo / 6
      let t4 := (r4Hi + 23) / 24
      let t5 := r5Lo / 120
      let t6 := (r6Hi + 719) / 720
      let poly := min S (S - r + t2 - t3 + t4 - t5 + t6)
      mulHi poly (powHi q eQtrHi)

/-! ## Midpoint-Tangent Upper Bound Table for `segArea` (`nHalf = 256`) -/

def segNHalf : Nat := 256
def segNTot : Nat := 512

/-- Midpoint-tangent area upper bound on bin `k ∈ {0, ..., 511}` covering `[(k-256)/256, (k-255)/256]`. -/
def segBinAreaHi (k : Nat) : Int :=
  let denom : Int := 512
  let numM : Int := Int.ofNat (2 * k + 1) - denom
  let rad2 : Int := denom * denom - numM * numM
  let srHi := sqrtSqHi (rad2 * S * S)
  let nh2 : Int := 256 * 256
  (srHi + nh2 - 1) / nh2

/-- Slope upper bound on `2 √(1 - t²)` on bin `k ∈ {0, ..., 511}`, scaled by `S`. -/
def segBinSlopeHi (k : Nat) : Int :=
  let aI : Int := Int.ofNat k - 256
  let bI : Int := aI + 1
  let tMinAbs : Int := if aI ≤ 0 ∧ 0 ≤ bI then 0 else min aI.natAbs bI.natAbs
  let sRad2 : Int := 256 * 256 - tMinAbs * tMinAbs
  let srHi := sqrtSqHi (4 * sRad2 * S * S)
  (srHi + 255) / 256

/-- Pure recursive suffix sum of `segBinAreaHi k` for `k = idx .. 511`. -/
def segSuffixSum (idx : Nat) : Int :=
  if idx ≥ segNTot then 0
  else segBinAreaHi idx + segSuffixSum (idx + 1)
termination_by segNTot - idx

/-- Build suffix-sum array `[segSuffixSum 0, ..., segSuffixSum 512]` in O(N) time. -/
def buildSegTabAux : Nat → List Int → List Int
  | 0, acc => acc
  | k + 1, acc =>
    let prev := acc.headD 0
    buildSegTabAux k ((prev + segBinAreaHi k) :: acc)

def segTabHiArr : Array Int :=
  (buildSegTabAux segNTot [0]).toArray

def segSlopeHiArr : Array Int :=
  Array.ofFn (n := segNTot) fun i => segBinSlopeHi i.val

/-- Certified UPPER bound on `segArea (c / S) * S` for `c ∈ [-S, S]`. -/
@[inline] def segEvalHi (c : Int) : Int :=
  if c ≥ S then 0
  else if c ≤ -S then piHi
  else
    let num := (c + S) * 256
    let idx := (num / S).toNat
    let remNum := (Int.ofNat (idx + 1)) * S - num
    let denom : Int := 256 * S
    let slope := segSlopeHiArr.getD idx (2 * S)
    let base := segTabHiArr.getD (idx + 1) 0
    let extra := (slope * remNum + denom - 1) / denom
    min piHi (base + extra)

/-- Certified UPPER bound on `diskInterArea (d/S) (r1/S) (r2/S) * S` for `d, r1, r2 ≥ 0`. -/
@[inline] def circleInterHi (d r1 r2 : Int) : Int :=
  if r1 ≤ 0 ∨ r2 ≤ 0 ∨ d ≥ r1 + r2 then 0
  else
    let rmin := min r1 r2
    let rmax := max r1 r2
    if d ≤ rmax - rmin then mulHi piHi (mulHi rmin rmin)
    else
      let d2 := d * d
      let r1sq := r1 * r1
      let r2sq := r2 * r2
      let c1Lo := max (-S) (min S (fdiv ((d2 + r1sq - r2sq) * S) (2 * d * r1)))
      let c2Lo := max (-S) (min S (fdiv ((d2 + r2sq - r1sq) * S) (2 * d * r2)))
      let t1 := mulHi (mulHi r1 r1) (segEvalHi c1Lo)
      let t2 := mulHi (mulHi r2 r2) (segEvalHi c2Lo)
      min (mulHi piHi (mulHi rmin rmin)) (t1 + t2)

/-! ## Three-Disk Union Area Upper Bound (`chordPoly6Hi`, `excessXHi`, `triAreaHi`) -/

@[inline] def chordPoly6Hi (d : Int) : Int :=
  let d := max 0 (min S d)
  let d2 := mulLo d d
  let d3 := mulLo d2 d
  let d5 := mulLo d3 d2
  let d7 := mulLo d5 d2
  let d9 := mulLo d7 d2
  let d11 := mulLo d9 d2
  let d13 := mulLo d11 d2
  2 * d - d3 / 12 - d5 / 320 - d7 / 3584 - (5 * d9) / 147456 - (7 * d11) / 1441792
    - (21 * d13) / 27262976

def excessXBin (r0 r1 x0 x1 y0 : Int) (i : Nat) : Int :=
  let dt : Int := 125000
  let ta : Int := Int.ofNat i * dt
  let tb : Int := ta + dt
  let mHi : Int :=
    if ta ≤ 500000 ∧ 500000 ≤ tb then 500000
    else max (min ta (S - ta)) (min tb (S - tb))
  let rmHi := mulHi r1 mHi
  let lowerSq := sqrtSqLo (S * S - rmHi * rmHi)
  let distTx : Int :=
    if tb < x0 then x0 - tb
    else if ta > x1 then ta - x1
    else 0
  let rdLo := mulLo r0 distTx
  let upperSq := sqrtSqHi (S * S - rdLo * rdLo)
  let diff := upperSq - mulLo r0 y0 - lowerSq
  if diff > 0 then mulHi diff dt else 0

def excessXSum (r0 r1 x0 x1 y0 : Int) : Nat → Int
  | 0 => 0
  | n + 1 => excessXSum r0 r1 x0 x1 y0 n + excessXBin r0 r1 x0 x1 y0 n

def excessXHi (r0 r1 x0 x1 y0 : Int) : Int :=
  let baseMin := sqrtSqLo (S * S - (r1 * r1 + 3) / 4)
  if S - mulLo r0 y0 - baseMin ≤ 0 then 0
  else mulHi r1 (excessXSum r0 r1 x0 x1 y0 8)

def triAreaHi (l0 l1 x0 x1 y0 y1 rad : Int) : Int :=
  let r0 := (l0 * S) / rad
  let r1 := divHi l1 rad
  let e0 := min S r1
  let n1Hi := sqrtSqHi (x1 * x1 + y1 * y1)
  let e1 := min S (mulHi r1 n1Hi)
  let omx0 := S - x0
  let n2Hi := sqrtSqHi (omx0 * omx0 + y1 * y1)
  let e2 := min S (mulHi r1 n2Hi)
  let triTerm := (mulHi (mulHi r1 r1) y1 + 1) / 2
  let chordTerm := (chordPoly6Hi e0 + chordPoly6Hi e1 + chordPoly6Hi e2 + 1) / 2
  let exTerm := excessXHi r0 r1 x0 x1 y0
  mulHi (mulHi rad rad) (piHi + triTerm + chordTerm + exTerm)

/-! ## Exact Cubic Radial Integral Numerator -/

@[inline] def intDPosNum (a b c : Int) : Int :=
  if c ≤ a then 0
  else
    let u := min b c
    (u - a) * (3 * c * (u + a) - 2 * (u * u + u * a + a * a))

/-! ## 1D Base Term Pure Recursive Integer Verifier -/

@[inline] def jointSurvHi (d r1 r2 : Int) (k1 k2 : Bool) : Int :=
  let a1Lo := mulLo piLo (mulLo r1 r1)
  let a2Lo := mulLo piLo (mulLo r2 r2)
  let interHi := min (min a1Lo a2Lo) (circleInterHi d r1 r2)
  let a10 := max 0 (a1Lo - interHi)
  let a01 := max 0 (a2Lo - interHi)
  let au := a1Lo + a2Lo - interHi
  let eHi := expNegHi au
  match k1, k2 with
  | false, false => eHi
  | true, false => mulHi (S + a10) eHi
  | false, true => mulHi (S + a01) eHi
  | true, true => mulHi (mulHi (S + a10) (S + a01) + interHi) eHi

def baseTerm1Loop (rho w : Array Int) (i : Nat) (acc : Int) : Int :=
  if i ≥ rho.size then acc
  else
    let ri := rho.getD i 0
    let wi := w.getD i 0
    let wprev := if i == 0 then 0 else w.getD (i - 1) 0
    let dw := wi - wprev
    let aHi := mulHi piHi (mulHi ri ri)
    let eLo := expNegLo aHi
    let pLo := mulLo (S + aHi) eLo
    baseTerm1Loop rho w (i + 1) (acc + (2 * dw * pLo) / 1000)
termination_by rho.size - i

def basePenMargLoop (rho w : Array Int) (i : Nat) (acc : Int) : Int :=
  if i ≥ rho.size then acc
  else
    let denMarg : Int := 3000000000000000000000
    let ri := rho.getD i 0
    let wi := w.getD i 0
    let wprev := if i == 0 then 0 else w.getD (i - 1) 0
    let aLo := mulLo piLo (mulLo ri ri)
    let pLoHi := expNegHi aLo
    let pHiHi := mulHi (S + aLo) pLoHi
    let intLo := intDPosNum 0 ri wi - intDPosNum 0 ri wprev
    let intHi := if wi > ri then intDPosNum ri wi wi - intDPosNum ri wi wprev else 0
    let numTot := pLoHi * intLo + pHiHi * intHi
    let term := (piHi * numTot + denMarg - 1) / denMarg
    basePenMargLoop rho w (i + 1) (acc + term)
termination_by rho.size - i

def basePenInterJ (rho w : Array Int) (da db : Int) (i : Nat) (ri wi wip : Int) (k1 : Bool)
    (j : Nat) (acc : Int) : Int :=
  if j ≥ rho.size then acc
  else
    let wj := w.getD j 0
    let acc' :=
      if wi + wj > da then
        let wjp := if j == 0 then 0 else w.getD (j - 1) 0
        let coeffNum := intDPosNum da db (wi + wj)
          - intDPosNum da db (wip + wj)
          - intDPosNum da db (wi + wjp)
          + intDPosNum da db (wip + wjp)
        if coeffNum > 0 then
          let rj := rho.getD j 0
          let k2 := decide (db > rj)
          let jsHi := jointSurvHi da ri rj k1 k2
          let mult : Int := if i == j then 1 else 2
          acc + (mult * coeffNum * jsHi + 999999999999) / 1000000000000
        else acc
      else acc
    basePenInterJ rho w da db i ri wi wip k1 (j + 1) acc'
termination_by rho.size - j

def basePenInterI (rho w : Array Int) (da db wMax : Int) (i : Nat) (acc : Int) : Int :=
  if i ≥ rho.size then acc
  else
    let wi := w.getD i 0
    let acc' :=
      if wi + wMax > da then
        let wip := if i == 0 then 0 else w.getD (i - 1) 0
        let ri := rho.getD i 0
        let k1 := decide (db > ri)
        basePenInterJ rho w da db i ri wi wip k1 i acc
      else acc
    basePenInterI rho w da db wMax (i + 1) acc'
termination_by rho.size - i

def basePenInterKnots (rho w : Array Int) (wMax : Int) : List Int → Int → Int
  | [], acc => acc
  | [_], acc => acc
  | da :: db :: rest, acc =>
    let acc' := if db > da then basePenInterI rho w da db wMax 0 acc else acc
    basePenInterKnots rho w wMax (db :: rest) acc'

/-- Merge two sorted `List Int`s into a strictly increasing `List Int`. -/
def mergeSortedLists : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x < y then x :: mergeSortedLists xs (y :: ys)
    else if y < x then y :: mergeSortedLists (x :: xs) ys
    else x :: mergeSortedLists xs ys

/-- Build the `d`-knot list containing uniform `nDUniform` knots merged with `rho` knots `< dMax`. -/
def buildDKnots (rho : Array Int) (dMax : Int) (nDUniform : Nat) : List Int :=
  let unif := (List.range (nDUniform + 1)).map fun m => (dMax * Int.ofNat m) / Int.ofNat nDUniform
  let rhoList := rho.toList.filter fun r => 0 < r ∧ r < dMax
  mergeSortedLists unif rhoList

/-- Exact integer lower bound on the 1D base term scaled by `10^9`. -/
def baseVerifyInt (rho w : Array Int) (nDUniform : Nat) : Int :=
  if rho.size == 0 ∨ w.size != rho.size ∨ nDUniform == 0 then 0
  else
    let term1_9 := baseTerm1Loop rho w 0 0
    let penMarg_9 := basePenMargLoop rho w 0 0
    let wMax := w.getD (rho.size - 1) 0
    let knots := buildDKnots rho (2 * wMax) nDUniform
    let penInterRaw := basePenInterKnots rho w wMax knots 0
    let penInter_9 := (piHi * penInterRaw + 5999999999) / 6000000000
    term1_9 - penMarg_9 - penInter_9

/-! ## Triangle Box Pure Recursive Integer Verifier -/

structure AngleTable where
  nT : Nat
  dtHi : Int
  chLo : Int
  shHi : Int
  cmLo : Array Int
  cmHi : Array Int
  smLo : Array Int
  smHi : Array Int

structure BoxCert where
  l0 : Int
  l1 : Int
  x0 : Int
  x1 : Int
  y0 : Int
  y1 : Int
  cx : Int
  cy : Int
  levels : List (Int × Int)

def evalStepPotAux (rho w : Array Int) (r : Int) (i : Nat) (cur : Int) : Int :=
  if i ≥ rho.size then cur
  else if r > rho.getD i 0 then evalStepPotAux rho w r (i + 1) (w.getD i 0)
  else cur
termination_by rho.size - i

@[inline] def evalStepPot (rho w : Array Int) (r : Int) : Int :=
  evalStepPotAux rho w r 0 0

@[inline] def boxNorm2LoHi (x0 x1 y0 y1 : Int) : Int × Int :=
  let xl : Int := if x0 ≤ 0 ∧ 0 ≤ x1 then 0 else min x0.natAbs x1.natAbs
  let yl : Int := if y0 ≤ 0 ∧ 0 ≤ y1 then 0 else min y0.natAbs y1.natAbs
  let xh : Int := max x0.natAbs x1.natAbs
  let yh : Int := max y0.natAbs y1.natAbs
  (xl * xl + yl * yl, xh * xh + yh * yh)

@[inline] def cornerDotLoHi (qx qy clo chi slo shi ch sh : Int) : Int × Int :=
  let p1l := min (qx * clo) (qx * chi)
  let p1h := max (qx * clo) (qx * chi)
  let p2l := min (qy * slo) (qy * shi)
  let p2h := max (qy * slo) (qy * shi)
  let aLo := fdiv (p1l + p2l) S
  let aHi := cdiv (p1h + p2h) S
  let b1l := min (-qx * slo) (-qx * shi)
  let b1h := max (-qx * slo) (-qx * shi)
  let b2l := min (qy * clo) (qy * chi)
  let b2h := max (qy * clo) (qy * chi)
  let bSumLo := b1l + b2l
  let bSumHi := b1h + b2h
  let bAbsMax : Int := max bSumLo.natAbs bSumHi.natAbs
  let bAbsHi := (bAbsMax + S - 1) / S
  let acLo := if aLo ≥ 0 then (aLo * ch) / S else aLo
  let acHi := if aHi ≥ 0 then aHi else -(((-aHi) * ch) / S)
  let bTerm := (bAbsHi * sh + S - 1) / S
  (acLo - bTerm, acHi + bTerm)

@[inline] def dotIntervalInt (x0 x1 y0 y1 clo chi slo shi ch sh : Int) : Int × Int :=
  let (l00, h00) := cornerDotLoHi x0 y0 clo chi slo shi ch sh
  let (l01, h01) := cornerDotLoHi x0 y1 clo chi slo shi ch sh
  let (l10, h10) := cornerDotLoHi x1 y0 clo chi slo shi ch sh
  let (l11, h11) := cornerDotLoHi x1 y1 clo chi slo shi ch sh
  (min (min l00 l01) (min l10 l11), max (max h00 h01) (max h10 h11))

/-- Precomputed box geometry independent of clearance level `r_j`. -/
structure BoxGeom where
  pi01Max : Int
  pi2Max : Int
  radB : Int
  boxWeight12 : Int
  q2Lo01 : Int
  q2Hi01 : Int
  q2Lo02 : Int
  q2Hi02 : Int
  q2Lo12 : Int
  q2Hi12 : Int
  cq2Lo0 : Int
  cq2Lo1 : Int
  cq2Lo2 : Int
  mLo01 : Array Int
  mHi01 : Array Int
  mLo02 : Array Int
  mHi02 : Array Int
  mLo10 : Array Int
  mHi10 : Array Int
  mLo12 : Array Int
  mHi12 : Array Int
  mLo20 : Array Int
  mHi20 : Array Int
  mLo21 : Array Int
  mHi21 : Array Int
  mcHi0 : Array Int
  mcHi1 : Array Int
  mcHi2 : Array Int

def buildBoxGeom (rho w : Array Int) (ang : AngleTable) (b : BoxCert) : BoxGeom :=
  let omx0 := S - b.x0
  let pi01Max := evalStepPot rho w (b.l1 - 1)
  let d12Max := mulHi b.l1 (sqrtSqHi (omx0 * omx0 + b.y1 * b.y1))
  let pi2Max := evalStepPot rho w d12Max
  let qx0_2 := mulLo b.l0 b.x0
  let qx1_2 := mulHi b.l1 b.x1
  let qy0_2 := mulLo b.l0 b.y0
  let qy1_2 := mulHi b.l1 b.y1
  let dx0 : Int := b.cx.natAbs
  let dy0 : Int := b.cy.natAbs
  let r0 := sqrtSqHi (dx0 * dx0 + dy0 * dy0)
  let dx1 : Int := max (b.cx - b.l0).natAbs (b.l1 - b.cx).natAbs
  let r1 := sqrtSqHi (dx1 * dx1 + dy0 * dy0)
  let dx2 : Int := max (b.cx - qx0_2).natAbs (qx1_2 - b.cx).natAbs
  let dy2 : Int := max (b.cy - qy0_2).natAbs (qy1_2 - b.cy).natAbs
  let r2 := sqrtSqHi (dx2 * dx2 + dy2 * dy2)
  let radB := max r0 (max r1 r2)
  let r12x0 := -mulHi b.l1 omx0
  let r12x1 := -mulLo b.l0 (S - b.x1)
  let (q2Lo01, q2Hi01) := boxNorm2LoHi b.l0 b.l1 0 0
  let (q2Lo02, q2Hi02) := boxNorm2LoHi qx0_2 qx1_2 qy0_2 qy1_2
  let (q2Lo12, q2Hi12) := boxNorm2LoHi r12x0 r12x1 qy0_2 qy1_2
  let crx0_0 := b.cx; let crx1_0 := b.cx; let cry0_0 := b.cy; let cry1_0 := b.cy
  let crx0_1 := b.cx - b.l1; let crx1_1 := b.cx - b.l0; let cry0_1 := b.cy; let cry1_1 := b.cy
  let crx0_2 := b.cx - qx1_2; let crx1_2 := b.cx - qx0_2
  let cry0_2 := b.cy - qy1_2; let cry1_2 := b.cy - qy0_2
  let (cq2Lo0, _) := boxNorm2LoHi crx0_0 crx1_0 cry0_0 cry1_0
  let (cq2Lo1, _) := boxNorm2LoHi crx0_1 crx1_1 cry0_1 cry1_1
  let (cq2Lo2, _) := boxNorm2LoHi crx0_2 crx1_2 cry0_2 cry1_2
  let l1_4 := b.l1 * b.l1 * b.l1 * b.l1
  let l0_4 := b.l0 * b.l0 * b.l0 * b.l0
  let dxy := (b.x1 - b.x0) * (b.y1 - b.y0)
  let w1 := ((l1_4 - l0_4) * dxy) / 1000000000000000000
  let boxWeight12 := (w1 * piLo) / 1000000000000
  let nT := ang.nT
  let ch := ang.chLo
  let sh := ang.shHi
  let mkDot (x0 x1 y0 y1 : Int) : Array Int × Array Int :=
    let pairs := Array.ofFn (n := nT) fun it =>
      dotIntervalInt x0 x1 y0 y1 (ang.cmLo.getD it.val 0) (ang.cmHi.getD it.val 0)
        (ang.smLo.getD it.val 0) (ang.smHi.getD it.val 0) ch sh
    (pairs.map Prod.fst, pairs.map Prod.snd)
  let (mLo01, mHi01) := mkDot b.l0 b.l1 0 0
  let (mLo02, mHi02) := mkDot qx0_2 qx1_2 qy0_2 qy1_2
  let (mLo10, mHi10) := mkDot (-b.l1) (-b.l0) 0 0
  let (mLo12, mHi12) := mkDot r12x0 r12x1 qy0_2 qy1_2
  let (mLo20, mHi20) := mkDot (-qx1_2) (-qx0_2) (-qy1_2) (-qy0_2)
  let (mLo21, mHi21) := mkDot (-r12x1) (-r12x0) (-qy1_2) (-qy0_2)
  let (_, mcHi0) := mkDot crx0_0 crx1_0 cry0_0 cry1_0
  let (_, mcHi1) := mkDot crx0_1 crx1_1 cry0_1 cry1_1
  let (_, mcHi2) := mkDot crx0_2 crx1_2 cry0_2 cry1_2
  { pi01Max, pi2Max, radB, boxWeight12,
    q2Lo01, q2Hi01, q2Lo02, q2Hi02, q2Lo12, q2Hi12,
    cq2Lo0, cq2Lo1, cq2Lo2,
    mLo01, mHi01, mLo02, mHi02, mLo10, mHi10,
    mLo12, mHi12, mLo20, mHi20, mLo21, mHi21,
    mcHi0, mcHi1, mcHi2 }

/-- Inner `ki` loop over step-potential levels on a single radial shell `[sa, sb]`. -/
def shellPenLoop (rho w : Array Int) (pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin : Int)
    (ki : Nat) (prevInt acc : Int) : Int :=
  if ki ≥ rho.size then acc
  else
    let wk := w.getD ki 0
    if pu + yj + wk ≤ sa then
      shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin (ki + 1) prevInt acc
    else
      let curInt := intDPosNum sa sb (pu + yj + wk) - intDPosNum sa sb (pu + yPrev + wk)
      let da := curInt - prevInt
      let acc' :=
        if da > 0 then
          let rk := rho.getD ki 0
          let qHi : Int :=
            if rk == 0 then S
            else
              let g0 : Nat := if sb ≤ rk then 1 else 0
              let g1 : Nat := if dMaxA ≤ rk then 1 else 0
              let g2 : Nat := if dMaxB ≤ rk then 1 else 0
              let guar := g0 + g1 + g2
              if guar ≥ 2 then 0
              else
                let aRkLo := mulLo piLo (mulLo rk rk)
                let vc := max 0 (aRkLo - circleInterHi dcMin rk rEnc)
                let iu := circleInterHi sa rk rj + circleInterHi dMinA rk rj + circleInterHi dMinB rk rj
                let vu := max 0 (aRkLo - iu)
                let vLo := max vc vu
                let ev := expNegHi vLo
                if guar == 1 then ev else mulHi (S + vLo) ev
          let daScaled := (da + 999999) / 1000000
          acc + (daScaled * qHi + 999999) / 1000000
        else acc
      shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin (ki + 1) curInt acc'
termination_by rho.size - ki

/-- Walk `rho`-split radial shells `[sa, sb] ⊆ [sStart, sMax]` for a single `(u, it)` sector. -/
def sectorShellsLoop (rho w : Array Int)
    (pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo : Int)
    (kIdx : Nat) (sa acc : Int) : Int :=
  if sa ≥ sMax then acc
  else if kIdx < rho.size ∧ rho.getD kIdx 0 ≤ sa then
    sectorShellsLoop rho w pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo
      (kIdx + 1) sa acc
  else
    let nextRho := if kIdx < rho.size then rho.getD kIdx 0 else sMax
    let sb := min sMax nextRho
    let sStarA := max sa (min sb maHi)
    let d2MnA := max 0 (sStarA * sStarA - 2 * sStarA * maHi + q2aLo)
    let d2MxA := max 0 (max (sa * sa - 2 * sa * maLo + q2aHi) (sb * sb - 2 * sb * maLo + q2aHi))
    let dMinA := max rj (sqrtSqLo d2MnA)
    let dMaxA := sqrtSqHi d2MxA
    let sStarB := max sa (min sb mbHi)
    let d2MnB := max 0 (sStarB * sStarB - 2 * sStarB * mbHi + q2bLo)
    let d2MxB := max 0 (max (sa * sa - 2 * sa * mbLo + q2bHi) (sb * sb - 2 * sb * mbLo + q2bHi))
    let dMinB := max rj (sqrtSqLo d2MnB)
    let dMaxB := sqrtSqHi d2MxB
    let sStarC := max sa (min sb mch)
    let dc2 := max 0 (sStarC * sStarC - 2 * sStarC * mch + cq2Lo)
    let dcMin := sqrtSqLo dc2
    let acc' := shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin 0 0 acc
    if sb ≥ sMax ∨ kIdx ≥ rho.size then acc'
    else
      sectorShellsLoop rho w pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo
        (kIdx + 1) sb acc'
termination_by rho.size + 1 - kIdx

/-- Loop over all `nT` angular sectors for a fixed vertex `u ∈ {0, 1, 2}`. -/
def vertexSectorsLoop (rho w : Array Int) (g : BoxGeom) (nT : Nat)
    (u : Nat) (pu yPrev yj rj rEnc sMax : Int) (it : Nat) (acc : Int) : Int :=
  if it ≥ nT then acc
  else
    let q2aLo := if u == 0 then g.q2Lo01 else if u == 1 then g.q2Lo01 else g.q2Lo02
    let q2aHi := if u == 0 then g.q2Hi01 else if u == 1 then g.q2Hi01 else g.q2Hi02
    let q2bLo := if u == 0 then g.q2Lo02 else if u == 1 then g.q2Lo12 else g.q2Lo12
    let q2bHi := if u == 0 then g.q2Hi02 else if u == 1 then g.q2Hi12 else g.q2Hi12
    let cq2Lo := if u == 0 then g.cq2Lo0 else if u == 1 then g.cq2Lo1 else g.cq2Lo2
    let maLo := if u == 0 then g.mLo01.getD it 0 else if u == 1 then g.mLo10.getD it 0 else g.mLo20.getD it 0
    let maHi := if u == 0 then g.mHi01.getD it 0 else if u == 1 then g.mHi10.getD it 0 else g.mHi20.getD it 0
    let mbLo := if u == 0 then g.mLo02.getD it 0 else if u == 1 then g.mLo12.getD it 0 else g.mLo21.getD it 0
    let mbHi := if u == 0 then g.mHi02.getD it 0 else if u == 1 then g.mHi12.getD it 0 else g.mHi21.getD it 0
    let mch := if u == 0 then g.mcHi0.getD it 0 else if u == 1 then g.mcHi1.getD it 0 else g.mcHi2.getD it 0
    let r2 := rj * rj
    let discA := maLo * maLo + r2 - q2aHi
    let sA := if discA > 0 then maLo + sqrtSqLo discA else rj
    let discB := mbLo * mbLo + r2 - q2bHi
    let sB := if discB > 0 then mbLo + sqrtSqLo discB else rj
    let sStart := max rj (max sA sB)
    let acc' :=
      if sStart < sMax then
        sectorShellsLoop rho w pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo
          0 sStart acc
      else acc
    vertexSectorsLoop rho w g nT u pu yPrev yj rj rEnc sMax (it + 1) acc'
termination_by nT - it

/-- Compute penalty upper bound (scaled by `S`) for one telescoping level `(rj, yj)`. -/
def levelPenaltyHi (rho w : Array Int) (ang : AngleTable) (g : BoxGeom) (wMax yPrev rj yj : Int) : Int :=
  if 2 * wMax ≤ rj then 0
  else
    let rEnc := rj + g.radB
    let p0 :=
      let sMax := g.pi01Max + yj + wMax
      if sMax > rj then vertexSectorsLoop rho w g ang.nT 0 g.pi01Max yPrev yj rj rEnc sMax 0 0 else 0
    let p1 :=
      let sMax := g.pi01Max + yj + wMax
      if sMax > rj then vertexSectorsLoop rho w g ang.nT 1 g.pi01Max yPrev yj rj rEnc sMax 0 p0 else p0
    let p2 :=
      let sMax := g.pi2Max + yj + wMax
      if sMax > rj then vertexSectorsLoop rho w g ang.nT 2 g.pi2Max yPrev yj rj rEnc sMax 0 p1 else p1
    (ang.dtHi * p2 + 5999999999999) / 6000000000000

/-- Walk all active levels of a `BoxCert`, checking invariants and summing certified gains (scaled by `10^9`). -/
def boxLevelsLoop (rho w : Array Int) (ang : AngleTable) (b : BoxCert) (g : BoxGeom) (wMax : Int) :
    List (Int × Int) → Int → Int → Int → Int
  | [], _, _, acc => acc
  | (rj, yj) :: rest, rPrev, yPrev, acc =>
    if rj ≤ rPrev ∨ yj ≤ yPrev ∨ 2 * (g.pi01Max + yj) > rj then 0
    else
      let areaHi := triAreaHi b.l0 b.l1 b.x0 b.x1 b.y0 b.y1 rj
      let survLo := expNegLo areaHi
      let dy := yj - yPrev
      let penHi := levelPenaltyHi rho w ang g wMax yPrev rj yj
      let bracketLo := max 0 (2 * dy - penHi)
      let gain9 :=
        if bracketLo > 0 then (g.boxWeight12 * survLo * bracketLo) / 1000000000000000 else 0
      boxLevelsLoop rho w ang b g wMax rest rj yj (acc + gain9)

/-- Exact integer lower bound (scaled by `10^9`) for a single `BoxCert`. Returns `0` if invalid. -/
def verifyBoxInt (rho w : Array Int) (ang : AngleTable) (b : BoxCert) : Int :=
  let k := rho.size
  if k == 0 ∨ w.size != k then 0
  else if b.l0 < 0 ∨ b.l1 ≤ b.l0 ∨ b.x0 < 0 ∨ b.x1 ≤ b.x0 ∨ b.x1 > 500000 then 0
  else if b.y0 < 0 ∨ b.y1 ≤ b.y0 then 0
  else
    let omx0 := S - b.x0
    if omx0 * omx0 + b.y1 * b.y1 > S * S then 0
    else
      let wMax := w.getD (k - 1) 0
      let g := buildBoxGeom rho w ang b
      boxLevelsLoop rho w ang b g wMax b.levels b.l1 0 0

/-- Sum certified lower bounds over a list of `BoxCert`s. -/
def verifyShardInt (rho w : Array Int) (ang : AngleTable) (boxes : List BoxCert) : Int :=
  boxes.foldl (fun acc b => acc + verifyBoxInt rho w ang b) 0

end BHHBounds.Cert
