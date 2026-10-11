# The integer recipe in Lean 4

This folder holds a Lean 4 development for the integer computation of `../RECIPE.md` (Sections 1 to 8;
Steps 1 to 7 of Section 4.1 of the paper). The equality of the efficient functions (`Impl`) and the
definitions (`Spec`) is checked by the Lean kernel for all parameters; the values of the totals rest on
evaluations by compiled code (`native_decide`), not on the kernel; the link between the recipe and the
constant β is proved in the paper and is not formalised. Below, a section cited by its number alone is
a section of `../RECIPE.md`; the sections of this file are cited by their titles.

## Files

| File | Content |
|---|---|
| `TSPBound/Spec.lean` | the recipe (Sections 1 to 8), nothing else |
| `TSPBound/Impl/*.lean` | the table (Sections 2 to 6), the dynamic programme of Section 7 as a straight-line plan, cell sums one gap tuple at a time, the recursion of Section 8 |
| `TSPBound/Correct/*.lean`, `TSPBound/Theorems.lean` | the proofs for these, and their top-level theorems |
| `TSPShared/Impl.lean` | the routine used for every k: the cell sums of all gap tuples with the same interior gaps at once |
| `TSPShared/Correct.lean`, `TSPShared/Theorems.lean` | its proofs, and its top-level theorems |
| `Results/Params.lean` | the parameter sets `tiny`, `k4`, `k5`, …, `k9`, and that they are in the allowed ranges |
| `Results/Exact.lean` | for `k5`, …, `k9`: in Sections 1 to 3 no subtraction is truncated and no divisor is zero, two places excepted (see "From RECIPE.md to Lean") |
| `Results/K5S.lean` … `Results/K9S.lean`, `Results/K5S/` … `Results/K9S/` | the results for k = 5 to 9 by the routine of `TSPShared`, in pieces |
| `Results/Small.lean`, `Results/K5.lean` … `Results/K8.lean`, `Results/K8/`, `Results/K5P.lean`, `Results/K5P/` | the test cases; the results for k = 5 to 8 by the older routine (the last section of this file) |
| `Results/Axioms.lean` | prints the axioms of the theorems (see "Axioms") |
| `Main.lean` | the executable (not verified: files, comparison, printing, log, threads) |
| `TSPBound.lean`, `TSPShared.lean`, `Results.lean` | the root modules of the three libraries (imports only) |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | the libraries and the executable, the version of Lean, and the (empty) list of dependencies |
| `runs/` | the records of the runs (see "The recorded runs") and the scripts: `gen_shared.py` and `gen_pieces.py` wrote the piece files, `run_pieces.py` builds pieces one by one, `convert_python_log.py` made the list of candidates for k = 9, `build_all.sh` is the whole build |

The sources are frozen: a change to a file, even to a comment, would make lake build again every
evaluation that imports it. Four comments are therefore left inexact: `TSPBound/Theorems.lean`
says that none of its theorems has a hypothesis (`totalFrom_eq_total` has two), `TSPShared/Correct.lean`
names a file "Impl/Shared.lean" (it is `TSPShared/Impl.lean`), `TSPShared/Impl.lean` writes
`AofShared p threads t` without the argument `parts`, and `lakefile.toml` lists the options of the
executable without `--plain` and `--levels`.

## Building and checking

Needed: Lean 4.31.0 with `lake` (`leanprover/lean4:v4.31.0`), for example through `elan`, which reads
the file `lean-toolchain`. Only the core library that ships with Lean is used, so nothing is downloaded.
In this folder (`lean/` of the repository; a build writes only into `.lake/`):

```sh
export LEAN_NUM_THREADS=1     # lake then builds one module at a time
lake build                    # Spec, Impl, the proofs of both libraries, the executable: about 1 min
lake build Results.K5S Results.K6S Results.K7S Results.K8S    # k = 5 to 8: 4.4 min, 22 s, 70 s, 21 min at 16 threads
lake build Results.K9S        # k = 9: 64 pieces of about 11 minutes each at 16 threads
lake build Results            # everything, with the evaluations by the older routine (7 hours more, at 4 threads)
lake build Results.Axioms     # prints the axioms (see "Axioms")
lake exe tspcheck ../data/specs/k7.txt -j 4 --shared
```

`sh runs/build_all.sh` does all of this in order and prints a log (`sh runs/build_all.sh quick` stops
after k = 5). A build succeeds only if every proof is accepted; there is no `sorry` in the sources
(`grep -rn sorry TSPBound TSPShared Results Main.lean` finds nothing). A clean build of the libraries
and the executable prints no warning.

*Pieces.* An evaluation is cut into pieces, each a file of its own with one `native_decide`, so that
lake keeps every finished piece. The piece files were written by `runs/gen_shared.py` (its head has the
commands), and the driver `runs/run_pieces.py` built them one after the other and recorded each in
`runs/k9s_done.txt` and the like. To build again, use the `lake build` commands above and not the
driver: it needs a file with the number of threads, rewrites `lakefile.toml` and adds to the stored
records (the head of the script says which files it reads and writes).

*Threads.* A piece computes its units of work as tasks in the thread pool of the `lean` process. `lean`
takes the size of that pool from its option `-j`, not from `LEAN_NUM_THREADS`; without the option the
pool has one thread for each processor. The line `weakLeanArgs = ["-j16"]` of `lakefile.toml` sets it: a
weak argument, which lake does not count among the inputs of a build, so the number can be changed
without anything being built again (the file is among the hashed sources of "The recorded runs",
though). The statements of the theorems do not contain the number.

*Compiled code.* Both libraries are compiled (`precompileModules`), so that `native_decide` runs
compiled functions.

*The executable.* `lake exe tspcheck SPEC [-j THREADS] [--log FILE] [--plain] [--shared] [--levels J FILE]`
reads a spec file and its values file, recomputes the cell masses, the tail term, the table, all cell
sums and the total, compares every stored number, and prints the five lines of Section 10, with the exit
status 0, 1 or 2 as there. `--shared` computes the cell sums with the routine of `TSPShared`; without it
the older routine is used, and with `--plain` that routine without the reflection of the heights. With
`--log FILE` the cell sums are appended to FILE as they are found, and sums found in FILE are not
recomputed. `--levels J FILE` writes the values `A_J` of Section 8 to FILE. The executable is not
verified (item 8 of "What is not proved, and what has to be trusted").

## What is proved

### (a) The implementation computes what the recipe defines (kernel-checked, for all parameters)

```lean
-- the table: the keys of Section 4 in order, each with its row Tab(κ, 0), …, Tab(κ, n-1)
theorem Correct.tablePool_eq (p : Params) (parts : Nat) :
    tableRowsPool p parts = (keys p).map (fun κ => (κ, tab p.n (Tab p κ)))

-- one unit of work: for interior gaps mid = (g_2, …, g_{k-1}), entry (g_1, g_k) is the cell sum
theorem Correct.sharedSums_eq_S (p : Params) (parts : Nat) (mid : List Nat) (g1 gk : Nat)
    (hg1 : g1 < m p) (hgk : gk < m p) :
    at2 (sharedSums p (tableRowsPool p parts) (mkPlanH p.k p.n) mid) g1 gk
      = S p (g1 :: (mid ++ [gk]))

-- one piece: the values A_j(g_1, t) of Section 8 for all first gaps g_1, where t = (g_2, …, g_j)
theorem Correct.AofShared_eq_A (p : Params) (threads parts : Nat) (t : List Nat) :
    AofShared p threads parts t = (List.range (m p)).map (fun g1 => A p (g1 :: t))

-- the total from the values A_j(g) of all beginnings g of length j
theorem Correct.totalFrom_eq_total (p : Params) (j : Nat) (vals : List (List Nat × Nat)) (hj : j ≤ p.k)
    (h : vals = (tuples j (m p)).map (fun g => (g, A p g))) : totalFrom p j vals = Spec.total p
```

`p` is an arbitrary parameter set (`Spec.Params`), and there is **no hypothesis on `p`**, not even that
it lies in the allowed ranges: the implementation looks its tables up with a fall-back on the definition
of `Spec`, runs its dynamic programme only if the plan passes a test, and evaluates `Spec.A` itself when
the list handed to `AofShared` is not part of a gap tuple. For sane parameters no fall-back is taken; if
one were, the program would be slow, not wrong. The hypotheses that occur are about indices and lists:
the entry asked for exists (`hg1`, `hgk`), and the values handed over are those of all beginnings of
length `j`, in the order of `tuples` (`hj`, `h`). Also kernel-checked are the helper
`Correct.A_of_list` (`TSPShared/Theorems.lean`), which takes one value `A p (g1 :: t)` with `g1 < m p`
out of the list that a piece proves, the theorems of the older routine (the last section of this file)
and six facts about auxiliary definitions of `Spec` (see "From RECIPE.md to Lean").

*The routine.* For fixed heights of the interior points `1, …, k-1`, a straight-line plan computes, over
the semiring (min, +), the least cost `H u v` of a path through all interior points from `u` to `v`;
these numbers depend only on the interior gaps `(g_2, …, g_{k-1})`. The first and the last edge are then
added for every first gap, every last gap and all heights of the two end points, so one unit of work, a
tuple of interior gaps, gives the cell sums of `m²` gap tuples. Of the three identities at the end of
Section 7, *shared paths* is thus used in full and proved (`sharedSums_eq_S`); *reflection* is used (the
height of the first interior point runs over the lower half, counted twice) and proved
(`Correct.cost_flip`); *reversal* is neither used nor proved. All arithmetic is in `Nat` (unbounded):
there is no overflow to exclude.

### (b) The results (the logical steps kernel-checked, the evaluations by `native_decide`)

```lean
theorem Results.k5s_total : Spec.total k5 = 1761033937996622
theorem Results.k6s_total : Spec.total k6 = 12593568504391125
theorem Results.k7s_total : Spec.total k7 = 92054418307910785
theorem Results.k8s_total : Spec.total k8 = 628708228549677266
theorem Results.k9s_total : Spec.total k9 = 4430997795015293889

theorem Results.k9s_accepts : Spec.Accepts k9     -- likewise k5s, …, k8s
theorem Results.k9_allowed  : Spec.Allowed k9     -- likewise k5, …, k8
theorem Results.k9_exact    : Exact k9            -- likewise k5, …, k8 (see "From RECIPE.md to Lean")
```

`Spec.Accepts p` is the test of Section 8, `total p * p.h2 * p.theta2 ≤ p.theta1 * p.n ^ (p.k + 1) * F * p.k * p.h1`,
with the thresholds 8789/10000, 8729/10000, 8681/10000, 8647/10000, 8618/10000 of the spec files.
`…_accepts` follows from `…_total` by `decide` (kernel arithmetic), and `…_allowed` is by `decide`.

`k9s_total` rests on **65** evaluations. Each of the 64 files `Results/K9S/P000.lean`, …, `P333.lean`
has one theorem `Results.k9s_P_x_y_z`: the list of the four values `Spec.A k9 [g₁, x, y, z]`,
`g₁ = 0, …, 3`, equals a list of four numbers. It is proved by rewriting with `Correct.AofShared_eq_A`
and one `native_decide`, which computes the table and 256 units of work, that is 4096 cell sums.
`Results.k9s_level4`, which the kernel checks, puts the 256 values together as hypothesis `h` of
`Correct.totalFrom_eq_total` (`hj` is by `decide`). That theorem rewrites the goal to
`totalFrom k9 4 [the 256 pairs] = 4430997795015293889`, and a 65th `native_decide` evaluates the four
remaining steps of the recursion of Section 8 (which needs the masses `P_c`, hence Sections 2 and 3, but
no cell sum). `k5s_total` is proved in the same way, and `k6s_total`, `k7s_total`, `k8s_total` with four
pieces each (the sixteen values `A_2`): five evaluations.

The right-hand sides were known before the evaluations. For k = 9 they were computed from the list of
cell sums that the Python checker of this repository had written. That checker computes one gap tuple of
each pair `(g, reversed g)`, so the list rests on the reversal, which Lean neither uses nor proves
(`runs/convert_python_log.py`; the executable then took the sums from the list, recomputing none, and
wrote `runs/k9s_levels4.txt`; record `runs/k9s_cand.txt`). A right-hand side is only a candidate: each
theorem is proved by its own evaluation, which starts from the ten parameters alone and reads no file,
and a wrong candidate makes its piece fail. With one of the 256 values of k = 5 raised by 1,
`native_decide` reported that the proposition is false, and the build of that piece failed
(`runs/k5w_run.out`, `runs/k5w_P001.out`). So the agreement of the Lean totals with the values files is
by construction, not a coincidence observed afterwards.

## Axioms

`lake build Results.Axioms` prints the axioms of every top-level theorem of this file; its output is
`runs/axioms.txt`. In Lean 4.31 each use of `native_decide` adds one axiom of its own, named
`<theorem>._native.native_decide.ax_1_1`, which states `decide (P) = true` for the proposition `P` that
was evaluated, so the output shows exactly which evaluations a theorem rests on.

The result: the theorems of part (a) of "What is proved", the theorems of the older routine and the six
facts about `Spec` rest on `propext`, `Classical.choice`, `Quot.sound` or a subset of them, and
`k5_allowed`, …, `k9_allowed` on no axiom. Every `…_total` and `…_accepts` rests on those three and on
one `native_decide` axiom for each of its evaluations: 65 for `k5s` and `k9s`, 5 for `k6s`, `k7s`,
`k8s`, 17 for `k8` and `k5p`, 1 for `k5`, `k6`, `k7`, `k4` and `tiny`; each `…_exact` rests on one. No
other axiom occurs, and no `sorryAx`.

A text search agrees with this: in `TSPBound/`, `TSPShared/`, `Results/` and `Main.lean` there is no
`sorry`, no declaration `axiom`, no `unsafe`, `implemented_by`, `extern`, `csimp` or `opaque`;
`partial def` occurs once, in `Main.lean`; `set_option` five times (`maxRecDepth`, for the
kernel-checked lists in `Results/K5S.lean`, …, `Results/K9S.lean`); `native_decide` is used 189 times,
always in `Results/`.

## From RECIPE.md to Lean

All names are in `TSPBound/Spec.lean`, namespace `Spec`; the file imports nothing.

| `RECIPE.md` | Lean names |
|---|---|
| preamble | `a / b` (floor), `cdiv` (ceiling), `ceilSqrt`, `∑ i < n, f i` (`sum`), `∑ t from a to b, f t` (`sumZ`) |
| Section 1 | `Params` (`k h1 h2 M b n nu T theta1 theta2`), `Allowed`, `m`, `bd` (`b_c`, with `b_0 = 0`), `Q`, `D`, `F`, `NT`, `ncell` |
| Section 2 | `lo M j`, `up M j`, `Rup M i`, `Rlo M i` |
| Section 3 | `Clam`, `Cmu`, `num`, `W` (bounded cells and the last cell are the two branches of its `if`), `P`, `ET` |
| Section 4 | `keys` (from `tuples`), `bKey`, `lenKey`, `lastCell`, `reduce`, `V` |
| Section 5 | `eta`, `chi`, `alpha`, `gamma`, `Dist`, `G` |
| Section 6 | `Tab` |
| Section 7 | height and gap tuples are lists, all of them `tuples`; `keyOf`, `E`, `pathLen`, `orders`, `cost` (`minOf` of a list), `S`, `gapOfIndex` (entry `i`, counted from 0, is `index / m^i % m`), `cellSums` |
| Section 8 | `A` (the list `g` has length `j`), `total`, `Accepts`; the bound `B` is not transcribed, only the test |
| Sections 9, 10 | not needed (unbounded integers); `Main.lean` (not verified) |

Six kernel-checked facts say that auxiliary definitions are what their names promise (`cdiv_spec` and
`nodup_tuples` are used by no other proof):

```lean
theorem Correct.cdiv_spec {a b : Nat} (hb : 0 < b) : a ≤ b * cdiv a b ∧ ∀ q, a ≤ b * q → cdiv a b ≤ q
theorem Correct.ceilSqrt_spec (A : Nat) : (ceilSqrt A) ^ 2 ≥ A ∧ ∀ u, u ^ 2 ≥ A → ceilSqrt A ≤ u
theorem Correct.minOf_spec : ∀ (l : List Nat), l ≠ [] → minOf l ∈ l ∧ ∀ x ∈ l, minOf l ≤ x
theorem Correct.mem_tuples {len n : Nat} {a : List Nat} : a ∈ tuples len n ↔ a.length = len ∧ ∀ x ∈ a, x < n
theorem Correct.nodup_tuples (len n : Nat) : (tuples len n).Nodup
theorem Correct.mem_orders {l π : List Nat} : π ∈ orders l ↔ π.Perm l
```

`mem_tuples` and `mem_orders` are about membership only; with `nodup_tuples`, each tuple occurs exactly
once in `tuples len n`, which is needed where a sum is taken. Not stated as theorems: that `tuples` is
in lexicographic order (it matters for the order of the table, not for any sum), and how often a
rearrangement occurs in `orders` (irrelevant for a minimum).

*Natural numbers.* `x - y` on natural numbers is 0 when `x < y`, and `x / 0` is 0, whereas `RECIPE.md`
means ordinary integer arithmetic and never divides by zero. The header of `TSPBound/Spec.lean` lists
every subtraction and every divisor of the file, with the reason why the two readings agree there. Most
of those of Sections 1 to 3 (and the divisors `α·M` and `4ν²` of Section 5) are covered by
`Results.Exact`: proved for `k5`, …, `k9` only, by `native_decide`, as a separate theorem that the
theorems `…_total` do not use; that `Exact p` holds for every allowed `p` is not proved. For `b - 1` in
`cdiv a b` there is a kernel-checked theorem, `Correct.cdiv_spec`: `cdiv a b` is the ceiling of `a / b`
whenever `b > 0` (it says nothing for `b = 0`; that a divisor is positive is part of `Exact`, or the
divisor is a power of 2). The others, among them the guarded `i - 1` in `num` of Section 3, are harmless
by inspection of the definitions, not by a theorem.

*Choices made in transcribing.* Sums over an empty range are 0; `V_κ` for a key with a single gap is
recognised by `κ_0 + … + κ_{m-1} ≤ 1`; the recursion for `lo`, `up` is written upwards from `j` and
stops at 13; in `A` the base case is `k ≤ |g|`, and the cell `c` is appended at the end of `g`.

*Outside the recipe's domain.* A Lean function is total, so a value had to be chosen where the recipe
defines none: `cdiv a 0 = 0` and `x / 0 = 0`; `minOf [] = 0`; list lookups with default 0 (`bd c` for
`c ≥ m`, entries beyond the length of a key or of a height tuple, `keyOf` at indices outside the gap
tuple); `ncell c = N_T` and the last-cell branch of `W` and `P` for every `c ≥ m - 1`; `W c i` for
`i > n_c` and `V κ s` for `s ≥ len_κ`; `lastCell κ = 0` for a key without a positive entry; `lo`, `up`
for `j = 0` and `j ≥ 13`; and `Params` outside the allowed ranges, for which the theorems of part (a)
of "What is proved" still hold but the recipe says nothing. That none of these values is reached for
allowed parameters is by reading, not a Lean theorem.

A review of `Spec.lean` compared it with `RECIPE.md` by reading, and ran a literal Python translation
of it with counters for uses outside the domain: in full on the four small spec files, for `k5` on the
whole table and six cell sums, for `k6` to `k9` on the cell masses and the tail term, and for `k8` and
`k9` on twenty rows of the tables. It found no difference and recorded no such use. Its report and
scripts are not part of this repository.

## What is not proved, and what has to be trusted

1. **The recipe bounds the constant.** That an accepted total implies β ≤ θ is proved in Sections 2 to 4
   of the paper; nothing of the real analysis is formalised.
2. **The Lean kernel** checks every proof of part (a) of "What is proved" and the logical steps of
   part (b). Its trusted base is the kernel itself and the three standard axioms `propext`,
   `Classical.choice`, `Quot.sound`.
3. **The evaluations.** Each `native_decide` in `Results` is an axiom (see "Axioms") asserting the
   outcome of a computation that the kernel did not check. Behind it stand the Lean compiler (from the
   definitions of `Impl` and `Spec` to C), the Lean interpreter (which starts each evaluation and calls
   the compiled functions), the C compiler and linker shipped with Lean, the Lean runtime (arithmetic
   on large natural numbers, arrays, reference counting, tasks and threads), the operating system, and
   the hardware of the machine on which the build ran. **For k = 9 there is one evaluation in Lean**,
   by one routine (each of its 64 pieces was evaluated once, and none was started a second time); for
   k = 5 to 8 each total was evaluated by both routines (see the last section of this file), by each of
   them once, and for k = 5 a second time by the older one, in sixteen pieces. (For k = 5 the first
   start of the first piece failed before the piece was built; see "The recorded runs".)
4. **`Spec` is `RECIPE.md`.** The meaning of `Spec.total k9` depends on `Spec.lean`, on the parameter
   set, and on the Lean core library. Checking it is a reading, and it includes reading Lean: the
   precedence of the `∑` notation, the argument order of the list functions of the core library
   (`getD`, `set`, `count`, `drop`, `take`, `range'`), and where a natural number is turned into an
   integer. The section "From RECIPE.md to Lean" is the aid, and it describes a review. How this
   development was written and how that review was made is said in the top-level `../README.md`, in
   its section on the tools used.
5. **The ten numbers of each parameter set are those of the spec file.** `Results/Params.lean` writes
   them out by hand; that they equal `../data/specs/k5.txt`, … is checked by reading, not by Lean. In
   the repository, `../tools/paper_numbers.py --check` compares them, and the stated totals, with the
   spec files and with the records of the checkers.
6. **Natural-number arithmetic is integer arithmetic here**, and **no Lean function is used outside the
   recipe's domain.** Both rest on `Results.k5_exact`, …, `k9_exact` (evaluations, not kernel proofs,
   which the reader has to combine with `…_total`) and on the inspection and reading described in "From
   RECIPE.md to Lean".
7. **Not covered at all:** the spec files `bhh.txt` and `rounding.txt` have no parameter set in Lean;
   `tiny` and `k4` have `…_allowed` and a total (`Results/Small.lean`) but no `Exact`.
8. **The executable** (`Main.lean`) adds unverified parsing, comparing, printing, logging and
   distribution over threads around the verified functions; its agreement with the stored values is
   evidence, not proof, and sums that it takes from a log are not recomputed in that run. The theorems
   of part (b) of "What is proved" do not depend on it. It was run in full on `k5`, `k6`, `k7`, with
   both routines (see "The recorded runs"). It was not run in full on `k8`, and not on `k9`: the output
   in `runs/k9s_cand.txt` ends with ACCEPTED, but that run took all cell sums from the list and is not
   a check of k = 9.

## The recorded runs

All runs were made on one machine (under Windows 11, in Git Bash, with Lean installed by elan), which
was running other jobs; the development was not built under another system. Every run in the table was
made once.

"Lean" is a theorem `Spec.total … = N`; the number in brackets is the number of its evaluations
(`native_decide`). "exe" is a run of `tspcheck` in which every stored number (masses, tail term, table,
all cell sums, total) agreed and the test passed. Times are wall-clock and include the table; for the
Lean runs by `TSPShared` the time is the sum over the pieces (the last step takes 2 to 5 s more).

| k | total `A_0` | run | threads | time | record |
|---|---|---|---|---|---|
| 5 | 1761033937996622 | Lean, `TSPShared`: 64 pieces and the recursion (65) | 16 | 263 s | `runs/k5s_done.txt` |
| | | Lean, older routine (1); the same in sixteen pieces (17) | 4; 1 | 31 s; 425 s | `runs/final_build3.out` |
| | | exe, `TSPShared`; exe, older routine | 16 | 22 s; 21 s | `runs/exe_k5_shared.out`, `runs/exe_k5.out` |
| 6 | 12593568504391125 | Lean, `TSPShared`: 4 pieces and the recursion (5) | 16 | 22 s | `runs/k6s_done.txt` |
| | | Lean, older routine (1) | 4 | 59 s | `runs/final_build3.out` |
| | | exe, `TSPShared`; exe, older routine | 16 | 32 s; 31 s | `runs/exe_k6_shared.out`, `runs/exe_k6.out` |
| 7 | 92054418307910785 | Lean, `TSPShared`: 4 pieces and the recursion (5) | 16 | 70 s | `runs/k7s_done.txt` |
| | | Lean, older routine (1) | 4 | 613 s | `runs/final_build3.out` |
| | | exe, `TSPShared`; exe, older routine | 16 | 86 s; 171 s | `runs/exe_k7_shared.out`, `runs/exe_k7.out` |
| 8 | 628708228549677266 | Lean, `TSPShared`: 4 pieces and the recursion (5) | 16 | 1282 s (21 min) | `runs/k8s_done.txt` |
| | | Lean, older routine: sixteen pieces and the recursion (17) | 4 | 24569 s (6.8 h) | `runs/final_build3.out` |
| 9 | 4430997795015293889 | Lean, `TSPShared`: 64 pieces and the recursion (65) | 16 (55 pieces), 15 (9 pieces) | 42042 s (11.7 h); 646 to 721 s a piece | `runs/k9s_done.txt` |

`runs/sources_at_end.txt` was written when all of these runs had ended: the versions of Lean and lake,
the output of `lake build Results Results.Axioms` (preceded by the same command with `--no-build`,
followed by one with `--no-build --rehash`), and the SHA-256 of every source file. Lake built nothing in
these calls: it found every module up to date. So the recorded results are those of exactly these
sources, to the extent that lake's test of what is up to date is right. The file is not a second
evaluation.

The records of the driver for k = 9 are `runs/k9s_run.out` (its output, which ends with the build of
`Results.K9S` and the axioms of its theorems) and `runs/k9s_done.txt` (one line for each piece: name,
threads, seconds, SHA-256 of the source and of the `.olean`, date and time of its end); its inputs are
`runs/k9s_pieces.txt` (the pieces) and, for the generator, `runs/k9s_levels4.txt` (the candidates);
likewise for the other k (`runs/k5_levels.txt` belongs to `Results/K5P/`). The output for k = 5 is in
three parts (`runs/k5s_run1.out`, `runs/k5s_run2.out`, `runs/k5s_run3.out`): the first start, at one
thread, failed after 6 seconds, before a piece was built (the output that it names was written over when
the piece was built at the second start), and the second was stopped on purpose after six pieces.
`runs/final_build3.out`, the log of the build by the older routine, also holds a run of the executable
with that routine on each of `k5`, `k6`, `k7`, at 4 threads.

In the copies of the records the path of the project folder was replaced by `.` and that of the home
directory by `~`; nothing else was changed. Some records name files that are not kept here: the outputs
of single pieces (`runs/…_pieces/`), a log of cell sums (`runs/k9s_stored.log`), an executable under
`runs/bin/`, and spec files under `../../repo/`, which is the top folder of this repository. The records
for k = 5 and k = 9 were made with an earlier form of `runs/run_pieces.py`, which differed only in how
it found `lake` and listed the processes and in printing its folder in its first line.

## The older routine: a second evaluation for k = 5 to 8

`TSPBound/Impl/Sym.lean` treats every gap tuple by itself: the plan is run anew for each, so of *shared
paths* it uses only the part about the heights of the two end points. It uses the reflection. Its
theorems are kernel-checked and have no hypothesis on `p`. `TSPBound/Theorems.lean` states them. Each
says that a function of the implementation gives the quantity that `Spec` defines: `Correct.table_eq`
(the table), `cellSum_eq_S` and `cellSumFlip_eq_S` (a cell sum, without and with the reflection),
`sumsRange_eq_S` and `sumsStep_eq_S` (the cell sums of a range of indices, as the executable computes
them), `totalOfSums_cellSums` (the total from the list of all cell sums), `total_eq` and `totalPar_eq`
(the total, on one thread and on several). The results use two more:

```lean
-- A_j(g) for the beginning g of a gap tuple, on several threads (one piece of an evaluation)
theorem Correct.AofPar_eq_A (p : Params) (threads : Nat) (g : List Nat) : AofPar p threads g = A p g
theorem Correct.AofPar_nil (p : Params) (threads : Nat) : AofPar p threads [] = Spec.total p
```

`Results.k5_total`, `k6_total`, `k7_total` (one evaluation each), `k8_total` (sixteen pieces
`Results.k8_A_i_j : Spec.A k8 [i, j] = v` and the recursion: seventeen evaluations) and `k5p_total`
(k = 5 again, in sixteen pieces) state the same totals as part (b) of "What is proved", each with
`…_accepts`. Here the number of worker threads is a numeral in the proof (the `4` in
`Correct.AofPar_nil k7 4`). The sixteen values `A_2` of k = 8 are right-hand sides for both routines
(`runs/k8_levels_stored.txt`); the piece files of this routine were written by `runs/gen_pieces.py`.

The two routines are not independent pieces of code. Both use the functions of `TSPBound/Impl` for the
table, for the edges and for a step of the plan, and the same recursion of Section 8. `TSPShared` has
its own plan for `A` and `H`, its own loops for `L` and `C`, another unit of work and another order of
summation, and it computes the table in the thread pool.
