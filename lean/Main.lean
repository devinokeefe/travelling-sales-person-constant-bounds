/-
`tspcheck SPEC [-j THREADS] [--log FILE] [--plain] [--shared] [--levels J FILE]`

Reads a spec file and its values file, recomputes everything with the verified functions of
`Impl`, compares the results with the values file and applies the test of RECIPE.md Section 8.
Output and exit status follow RECIPE.md Section 10.

Nothing in this file is verified: the reading of the files, the comparison, the division of the
work among threads, the log and the printing.  The numbers themselves come from `Impl.tableRows`,
`Impl.massArr`, `Spec.ET`, `Impl.sumsStep` (or `Impl.sumsRange` with `--plain`) and
`Impl.totalOfSums`, which are proved equal to the definitions in `Spec` (`TSPBound/Theorems.lean`).

`--log FILE`: the cell sums are appended to FILE as they are found, and a run that was interrupted
is continued by repeating the command; sums found in FILE are then not recomputed.
`--plain`: the cell sums are computed without the symmetry of the heights (twice the work).
`--shared`: the cell sums are computed by units of gap tuples with the same interior gaps
(`Impl.sharedSums`, `TSPShared/Impl.lean`), sixteen at a time for four gap cells.
`--levels J FILE`: the values `A_J(g_1, …, g_J)` of RECIPE.md Section 8 are written to FILE.
-/
import TSPShared.Impl

open Spec Impl

/-- Status 2: a bad command line, a malformed file, parameters outside the allowed ranges. -/
def bad {α : Type} (msg : String) : IO α := throw (IO.userError msg)

/-- The lines of a text file as arrays of fields, by the rules of Section 10. -/
def readLines (path : String) : IO (Array (Array String)) := do
  let data ← IO.FS.readBinFile path
  let n := data.size
  let mut lines : Array (Array String) := #[]
  let mut fields : Array String := #[]
  let mut cur : String := ""
  let mut lineOpen := false
  let mut i := 0
  while i < n do
    let b := data[i]!
    if b == 13 then
      if i + 1 < n && data[i + 1]! == 10 then
        i := i + 1
        continue
      else bad s!"{path}: a byte that is not allowed in a text file"
    if b == 10 then
      if cur != "" then
        fields := fields.push cur
        cur := ""
      if fields.isEmpty then bad s!"{path}: empty line"
      lines := lines.push fields
      fields := #[]
      lineOpen := false
    else if b == 9 || b == 32 then
      if cur != "" then
        fields := fields.push cur
        cur := ""
      lineOpen := true
    else if 33 ≤ b && b ≤ 126 then
      cur := cur.push (Char.ofNat b.toNat)
      lineOpen := true
    else bad s!"{path}: a byte that is not allowed in a text file"
    i := i + 1
  if lineOpen then
    if cur != "" then fields := fields.push cur
    if fields.isEmpty then bad s!"{path}: empty line"
    lines := lines.push fields
  if lines.isEmpty then bad s!"{path}: no lines"
  return lines

/-- A number below 2^128, written with decimal digits; leading zeros are allowed. -/
def parseNumber (place field : String) : IO Nat := do
  let cs := field.toList
  if cs.isEmpty || !cs.all Char.isDigit then bad s!"{place}: '{field.take 50}' is not a number below 2^128"
  let digits := cs.dropWhile (· == '0')
  if digits.length > 39 then bad s!"{place}: '{field.take 50}' is not a number below 2^128"
  let v : Nat := digits.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
  if v ≥ 2 ^ 128 then bad s!"{place}: '{field.take 50}' is not a number below 2^128"
  return v

/-- The line at `pos`: the name (if not empty), then `count` numbers (any number of them if `none`). -/
def numbersLine (lines : Array (Array String)) (pos : Nat) (name : String) (count : Option Nat)
    (place : String) : IO (Array Nat) := do
  if h : pos < lines.size then
    let line := lines[pos]
    let fields ←
      if name != "" then
        if line[0]! != name then bad s!"{place}: expected a line '{name}'"
        pure (line.extract 1 line.size)
      else pure line
    match count with
    | some c => if fields.size != c then bad s!"{place}: wrong number of numbers in a line '{name}'"
    | none => pure ()
    fields.mapM (parseNumber place)
  else bad s!"{place}: expected a line '{name}'"

/-- The seven parameter lines shared by spec files and values files, starting at `pos`. -/
def parameterNumbers (lines : Array (Array String)) (pos : Nat) (place : String) :
    IO (Array (Array Nat)) := do
  let names : List (String × Option Nat) :=
    [("k", some 1), ("h", some 2), ("mesh", some 1), ("gaps", none), ("heights", some 1),
     ("height_mesh", some 1), ("tail", some 1)]
  let mut out := #[]
  let mut q := pos
  for (name, count) in names do
    out := out.push (← numbersLine lines q name count place)
    q := q + 1
  return out

structure SpecFile where
  par : Params
  given : Array (Array Nat)
  values : String

def increasing : List Nat → Bool
  | x :: y :: l => x < y && increasing (y :: l)
  | _ => true

def readSpec (path : String) : IO SpecFile := do
  let lines ← readLines path
  let given ← parameterNumbers lines 0 path
  let th ← numbersLine lines 7 "threshold" (some 2) path
  if lines.size != 9 || lines[8]!.size != 2 || lines[8]![0]! != "values" then
    bad s!"{path}: expected a last line 'values PATH'"
  let relative := lines[8]![1]!
  if relative.startsWith "/" || relative.contains '\\' || relative.contains ':' then
    bad s!"{path}: the path of the values file must be relative, with '/' between its parts"
  let par : Params :=
    { k := given[0]![0]!, h1 := given[1]![0]!, h2 := given[1]![1]!, M := given[2]![0]!,
      b := given[3]!.toList, n := given[4]![0]!, nu := given[5]![0]!, T := given[6]![0]!,
      theta1 := th[0]!, theta2 := th[1]! }
  let small := [par.h1, par.h2, par.theta1, par.theta2].all (fun x => 0 < x && x < 2 ^ 64)
    && par.b.all (fun x => 0 < x && x < 2 ^ 64)
  if !(2 ≤ par.k && par.k ≤ 9 && small && Nat.gcd par.h1 par.h2 == 1 && 2 ≤ par.M && par.M ≤ 1024
      && increasing (0 :: par.b) && m par ≤ 8 && 1 ≤ par.n && par.n ≤ 16 && 1 ≤ par.nu && par.nu ≤ 256
      && 1 ≤ par.T && par.T ≤ 40) then
    bad s!"{path}: a parameter is outside the allowed range"
  let dir := (System.FilePath.mk path).parent.getD (System.FilePath.mk ".")
  let valuesPath := (relative.splitOn "/").foldl (fun (acc : System.FilePath) (part : String) => acc / part) dir
  return { par := par, given := given, values := valuesPath.toString }

structure Stored where
  given : Array (Array Nat)
  masses : Array Nat
  et : Nat
  rows : Array (Array Nat)
  sums : Array Nat
  total : Nat

/-- The numbers of a values file; only its form is checked here (step 2 of Section 10). -/
def readValues (path : String) : IO Stored := do
  let lines ← readLines path
  if lines[0]! != #["tsp-block-values", "1"] then bad s!"{path}: the first line must be 'tsp-block-values 1'"
  let given ← parameterNumbers lines 1 path
  let masses ← numbersLine lines 8 "masses" none path
  let et ← numbersLine lines 9 "tail_term" (some 1) path
  let nrows := (← numbersLine lines 10 "table" (some 1) path)[0]!
  if 11 + nrows > lines.size then bad s!"{path}: fewer lines than the line 'table' states"
  let mut rows := Array.mkEmpty nrows
  for i in [0:nrows] do
    rows := rows.push (← numbersLine lines (11 + i) "" none path)
  let q := 11 + nrows
  let nsums := (← numbersLine lines q "sums" (some 1) path)[0]!
  if q + 1 + nsums > lines.size then bad s!"{path}: fewer lines than the line 'sums' states"
  let mut sums := Array.mkEmpty nsums
  for i in [0:nsums] do
    sums := sums.push (← numbersLine lines (q + 1 + i) "" (some 1) path)[0]!
  let r := q + 1 + nsums
  let total := (← numbersLine lines r "total" (some 1) path)[0]!
  if lines.size != r + 1 then bad s!"{path}: lines after the total"
  return { given := given, masses := masses, et := et[0]!, rows := rows, sums := sums, total := total }

def binomial (n k : Nat) : Nat := Id.run do
  let mut r := 1
  for i in [0:k] do
    r := r * (n - i) / (i + 1)
  return r

def parameterLines (p : Params) : List String :=
  [s!"k {p.k}", s!"h {p.h1} {p.h2}", s!"mesh {p.M}",
   " ".intercalate ("gaps" :: p.b.map toString), s!"heights {p.n}", s!"height_mesh {p.nu}",
   s!"tail {p.T}"]

/-- A check value of the table and the masses, for the head of the log. -/
def tableMark (rows : List (List Nat × Array Nat)) (mass : Array Nat) : UInt64 :=
  let h := rows.foldl (fun h e => e.2.foldl (fun h x => mixHash h (hash x)) (e.1.foldl (fun h x => mixHash h (hash x)) h)) 7
  mass.foldl (fun h x => mixHash h (hash x)) h

/-- The cell sums already in the log; the log is created with its head if it does not exist. -/
def openLog (path : String) (head : List String) (count : Nat) : IO (Array (Option Nat)) := do
  let mut done : Array (Option Nat) := Array.replicate count none
  if ← System.FilePath.pathExists path then
    let text ← IO.FS.readFile path
    -- a last line without a line end, left by an interrupted run, is dropped
    let complete := (text.splitOn "\n").dropLast
    if complete.take head.length != head then bad s!"{path}: this log belongs to another computation"
    for line in complete.drop head.length do
      match line.splitOn " " with
      | ["sum", i, v] =>
        let index ← parseNumber path i
        let value ← parseNumber path v
        if index ≥ count then bad s!"{path}: inconsistent line '{line}'"
        match done[index]! with
        | some old => if old != value then bad s!"{path}: inconsistent line '{line}'"
        | none => done := done.set! index (some value)
      | _ => bad s!"{path}: malformed line '{line}'"
    -- rewrite the log without the incomplete last line
    IO.FS.writeFile path ("".intercalate (complete.map (· ++ "\n")))
  else
    IO.FS.writeFile path ("".intercalate (head.map (· ++ "\n")))
  return done

/-- All cell sums in index order, computed `threads` chunks at a time. -/
def computeSums (p : Params) (rows : List (List Nat × Array Nat)) (threads : Nat) (plain : Bool)
    (logPath : Option String) (mass : Array Nat) : IO (Array Nat) := do
  let count := (m p) ^ p.k
  let head := "tspcheck-log 1" :: parameterLines p ++ [s!"table {tableMark rows mass}"]
  let mut done : Array (Option Nat) := Array.replicate count none
  if let some path := logPath then
    done ← openLog path head count
    let have_ : Nat := done.foldl (fun c x => if x.isSome then c + 1 else c) 0
    if have_ > 0 then IO.eprintln s!"  {have_} cell sums taken from {path}"
  -- chunks of consecutive indices that are still to be computed
  let chunk := max 1 (min (min 64 (2 ^ 22 / p.n ^ (p.k - 1))) (count / (4 * threads)))
  let mut ranges : Array (Nat × Nat) := #[]
  let mut lo := 0
  while lo < count do
    if done[lo]!.isSome then
      lo := lo + 1
    else
      let mut cnt := 1
      while lo + cnt < count && cnt < chunk && done[lo + cnt]!.isNone do
        cnt := cnt + 1
      ranges := ranges.push (lo, cnt)
      lo := lo + cnt
  let start ← IO.monoMsNow
  let mut finished := count - ranges.foldl (fun c r => c + r.2) 0
  let mut next := 0
  let mut shown := start
  while next < ranges.size do
    let wave := ranges.extract next (min ranges.size (next + threads))
    let tasks := wave.map (fun r =>
      (r, Task.spawn (prio := .dedicated) (fun _ =>
        if plain then sumsRange p rows r.1 r.2 else sumsStep p rows 0 1 r.1 r.2)))
    let mut text := ""
    for (r, t) in tasks do
      let res ← IO.wait t
      let mut index := r.1
      for v in res do
        done := done.set! index (some v)
        text := text ++ s!"sum {index} {v}\n"
        index := index + 1
      finished := finished + r.2
    if let some path := logPath then
      let h ← IO.FS.Handle.mk path IO.FS.Mode.append
      h.putStr text
      h.flush
    next := next + wave.size
    let now ← IO.monoMsNow
    if now - shown ≥ 10000 || next ≥ ranges.size then
      shown := now
      IO.eprintln s!"  cell sums {finished} of {count}, {(now - start) / 1000} s"
  return done.map (fun x => x.getD 0)

/-- All cell sums in index order, computed by units with `Impl.sharedSums` (option `--shared`):
one unit is the `m²` gap tuples `(g_1, mid, g_k)` with the same interior gaps `mid`; `threads` units
at a time. -/
def computeSumsShared (p : Params) (rows : List (List Nat × Array Nat)) (threads : Nat)
    (logPath : Option String) (mass : Array Nat) : IO (Array Nat) := do
  if p.k < 2 then bad "--shared needs k ≥ 2"
  let mm := m p
  let count := mm ^ p.k
  let units := mm ^ (p.k - 2)
  let top := mm ^ (p.k - 1)
  let head := "tspcheck-log 1" :: parameterLines p ++ [s!"table {tableMark rows mass}"]
  let mut done : Array (Option Nat) := Array.replicate count none
  if let some path := logPath then
    done ← openLog path head count
    let have_ : Nat := done.foldl (fun c x => if x.isSome then c + 1 else c) 0
    if have_ > 0 then IO.eprintln s!"  {have_} cell sums taken from {path}"
  -- the units that are still to be computed
  let mut todo : Array Nat := #[]
  for q in [0:units] do
    let mut all := true
    for g1 in [0:mm] do
      for gk in [0:mm] do
        if done[g1 + mm * q + top * gk]!.isNone then all := false
    if !all then todo := todo.push q
  let planH := mkPlanH p.k p.n
  if !planH.ok then
    IO.eprintln "  warning: the plan for the slots A and H failed its test; the routine without sharing is used"
  let start ← IO.monoMsNow
  let mut next := 0
  let mut shown := start
  while next < todo.size do
    let wave := todo.extract next (min todo.size (next + threads))
    let tasks := wave.map (fun q =>
      (q, Task.spawn (prio := .dedicated) (fun _ => sharedUnit p rows [] (p.k - 2) q)))
    let mut text := ""
    for (q, t) in tasks do
      let res ← IO.wait t
      for g1 in [0:mm] do
        for gk in [0:mm] do
          let index := g1 + mm * q + top * gk
          let v := at2 res g1 gk
          done := done.set! index (some v)
          text := text ++ s!"sum {index} {v}\n"
    if let some path := logPath then
      let h ← IO.FS.Handle.mk path IO.FS.Mode.append
      h.putStr text
      h.flush
    next := next + wave.size
    let now ← IO.monoMsNow
    if now - shown ≥ 5000 || next ≥ todo.size then
      shown := now
      IO.eprintln s!"  units {units - todo.size + next} of {units}, {now - start} ms"
  return done.map (fun x => x.getD 0)

/-- `numerator / denominator` rounded up to 12 decimals. -/
def decimalUp (numerator denominator : Nat) : String :=
  let scaled := cdiv (numerator * 10 ^ 12) denominator
  let frac := toString (scaled % 10 ^ 12)
  s!"{scaled / 10 ^ 12}." ++ "".pushn '0' (12 - frac.length) ++ frac

/-- The options after the name of the spec file. -/
structure Options where
  threads : Nat := 1
  log : Option String := none
  plain : Bool := false
  shared : Bool := false
  levels : Option (Nat × String) := none

def usage : String :=
  "usage: tspcheck SPEC [-j THREADS] [--log FILE] [--plain] [--shared] [--levels J FILE]"

/-- A number written with digits, capped at `cap`. -/
def smallNumber (text : String) (cap : Nat) : Option Nat :=
  let cs := text.toList
  if cs.isEmpty || !cs.all Char.isDigit then none
  else
    let digits := cs.dropWhile (· == '0')
    if digits.length > 9 then some cap
    else some (min cap (digits.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0))

partial def parseOptions : List String → Options → IO Options
  | [], o => pure o
  | "-j" :: nstr :: rest, o =>
    match smallNumber nstr 64 with
    | some v => if v = 0 then bad "-j needs a positive number of threads, written with digits"
                else parseOptions rest { o with threads := v }
    | none => bad "-j needs a positive number of threads, written with digits"
  | "--log" :: f :: rest, o => parseOptions rest { o with log := some f }
  | "--plain" :: rest, o => parseOptions rest { o with plain := true }
  | "--shared" :: rest, o => parseOptions rest { o with shared := true }
  | "--levels" :: jstr :: f :: rest, o =>
    match smallNumber jstr 9 with
    | some j => parseOptions rest { o with levels := some (j, f) }
    | none => bad "--levels needs a number J and a file name"
  | _, _ => bad usage

/-- The lines `A g_1 … g_j value` for all beginnings `(g_1, …, g_j)` of gap tuples: the values
`A_j` of RECIPE.md Section 8, from the list of all cell sums. -/
def levelLines (p : Params) (mass sums : Array Nat) (j : Nat) : List String :=
  let mm := m p
  (tuples j mm).map (fun g =>
    let base := indexOf mm g
    let sub := (List.range (mm ^ (p.k - j))).map (fun t => sums.getD (base + mm ^ j * t) 0)
    let value := totalRec p mass sub.toArray (p.k - j) 0 0
    "A " ++ " ".intercalate (g.map toString) ++ s!" {value}")

def run (args : List String) : IO UInt32 := do
  let (specPath, rest) ← match args with
    | s :: rest => pure (s, rest)
    | [] => bad usage
  let opts ← parseOptions rest {}
  let threads := opts.threads
  let logPath := opts.log
  let spec ← readSpec specPath
  let p := spec.par
  let stored ← readValues spec.values
  -- step 3
  if stored.given != spec.given then
    IO.println "REJECTED: the parameters of the values file are not those of the spec file"
    return 1
  -- step 4
  let mm := m p
  if stored.masses.size != mm || stored.rows.size != binomial (mm + p.k) p.k - 1
      || stored.rows.any (fun r => r.size != mm + p.n) || stored.sums.size != mm ^ p.k then
    bad "the values file has the wrong number of masses, table lines, table entries or cell sums"
  if bd p (mm - 1) > 2 ^ 20 then bad "the last boundary is above 2^20; this program does not provide the memory"
  -- the computation
  let start ← IO.monoMsNow
  let mass := massArr p
  let et := ET p
  let rows := tableRows p threads
  IO.eprint s!"  table of {rows.length} keys done"
  let tableDone ← IO.monoMsNow
  IO.eprintln s!", {(tableDone - start) / 1000} s"
  let plan := mkPlan p.k p.n
  if !plan.ok then IO.eprintln "  warning: the plan failed its test; the slow definition is used"
  let sums ← if opts.shared then computeSumsShared p rows threads logPath mass
             else computeSums p rows threads opts.plain logPath mass
  let total := totalOfSums p sums
  if let some (j, file) := opts.levels then
    if j ≤ p.k then
      IO.FS.writeFile file ("".intercalate ((levelLines p mass sums j).map (· ++ "
")))
  IO.eprintln s!"  time {((← IO.monoMsNow) - start) / 1000} s, {threads} thread(s)"
  -- step 5
  if stored.masses != mass then
    IO.println "REJECTED: the masses differ"
    return 1
  if stored.et != et then
    IO.println "REJECTED: the tail term differs"
    return 1
  let mut i := 0
  for (key, row) in rows do
    if stored.rows[i]! != (key.toArray ++ row) then
      IO.println ("REJECTED: the table differs at the key " ++ " ".intercalate (key.map toString))
      return 1
    i := i + 1
  for index in [0:sums.size] do
    if sums[index]! != stored.sums[index]! then
      IO.println s!"REJECTED: the cell sum of gap tuple {index} differs"
      return 1
  if stored.total != total then
    IO.println "REJECTED: the total differs"
    return 1
  IO.println "the stored values agree with the recomputed values"
  -- step 6
  let denominator := p.n ^ (p.k + 1) * F * p.k * p.h1
  let numerator := total * p.h2
  IO.println s!"total {total}"
  IO.println s!"bound {decimalUp numerator denominator} (rounded up)"
  let accepted := numerator * p.theta2 ≤ p.theta1 * denominator
  IO.println s!"bound {if accepted then "<=" else ">"} {p.theta1}/{p.theta2}"
  if accepted then
    IO.println "ACCEPTED"
    return 0
  else
    IO.println "REJECTED: the bound exceeds the threshold"
    return 1

def main (args : List String) : IO UInt32 := do
  try
    let status ← run args
    return status
  catch e =>
    IO.eprintln s!"tspcheck: {e}"
    return (2 : UInt32)
