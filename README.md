# An upper bound for the Euclidean travelling salesman constant: programs and data

This repository accompanies the paper *An upper bound for the Euclidean travelling salesman constant*
(`paper/main.pdf`), which proves β < 0.8618 for the constant β of Beardwood, Halton and Hammersley. The
paper defines a number by integer arithmetic alone (its Section 4.1, restated here in `RECIPE.md`) and
proves that it is an upper bound for β (Theorem 4.1). That the number is below 0.8618 is the result of a
finite computation, and that computation is the subject of this repository: three programs that carry it
out, the numbers they agree on, the controls, and a Lean development of the computation. To repeat the
computation, build the C or the Rust program and run it once; on a desktop computer this takes an hour
or two (see "Checking").

Six terms are used with fixed meanings below. A *checker* is one of the three programs. A *spec file*
(in `data/specs/`) gives the parameters of one computation and a *threshold*, the number with which a
checker compares the bound. A *values file* (in `data/values/`) holds the integers of that computation
that the checkers compare: the cell masses P_c (the paper calls them probabilities), the tail term E_T,
the table, the cell sums and the total (Section 4.1 of the paper). The *controls* are computations that
are not part of the proof: floating-point computations and simulations (Sections 5.3 and 6.1 of the
paper; `controls/README.md`), and `controls/plain_sums.c`, which recomputes some cell sums cell by cell,
in integers. The *tests* are tests of the checkers: unit tests, the test inputs in `data/tests/`, and the
mutation tests.

## Checking

<!-- times:begin -->
To check the computation on which Theorem 1.1 rests, one checker and one run are enough: build the C or
the Rust checker as shown below and run it on `data/specs/k9.txt`. On our desktop computer, which was
running other jobs at the time, this took 76 minutes with the C checker built with MSVC under Windows (96
and 98 minutes built with gcc under Linux) and 65 minutes with the Rust checker, on 8 threads each, and
3.3 hours with the Python checker on 12 processes. The spec files up to `k7.txt` take less than a minute
and `k8.txt` takes between 2 and 22 minutes (`runs/times.txt`). The run has succeeded if it prints the
five lines shown below and ends with status 0. No checker needs another: each is built and run on its
own.
<!-- times:end -->

All commands are run from the top folder, in a POSIX shell: bash under Linux or macOS, Git Bash or WSL
under Windows. We ran the checkers under Windows 11 (the C checker built with MSVC, the Rust checker, the
Python checker with numpy) and under Ubuntu 24.04 in WSL 2 (the C checker built with gcc 13.3, up to
k = 9; the Python checker without numpy, on the small spec files). The Rust checker was not run under
Linux by us, and nothing was run under macOS. Every checker was run at least twice on each of `k5.txt`
to `k9.txt`, except the Python checker on `k9.txt`, which was run once; all runs printed the same lines
(`runs/times.txt`). The Python interpreter is called `python` below; if yours is `python3`, use that
name, and set `PYTHON=python3` for the shell scripts. Install numpy with
`python -m pip install numpy`; where the Python of the system does not allow that, as under Debian and
Ubuntu, use a virtual environment or the package of the system (`python3-numpy`).

Each checker takes a spec file (any file in `data/specs/`), recomputes everything, compares the result
with the values file that the spec file names, and prints on standard output

```
the stored values agree with the recomputed values
total 4430997795015293889
bound 0.861715646305 (rounded up)
bound <= 8618/10000
ACCEPTED
```

(this is the output for `data/specs/k9.txt`; progress and times go to standard error, and from the Rust
checker also the sizes of the largest values). The exit status is 0 if the checker accepts, 1 if a number
differs or the bound exceeds the threshold, and 2 if a file is malformed or an arithmetic bound is
violated; Section 10 of `RECIPE.md` says what is printed in each case, and gives the formats of the two
kinds of file and the order in which a checker checks its input. If the Python checker stops with a
traceback (under Python 3.9, for example), its status is also 1, but that is a failure of the program
and not a verdict: with a verdict of status 1 the last line of the standard output begins with
`REJECTED:`. The option `-j N` sets the number of threads or processes; the output does not depend on
it.

**C.** Needs a C11 compiler with its library (the program calls `timespec_get`); OpenMP is optional.
```
gcc -std=c11 -O2 -fopenmp checkers/cchk.c -o cchk
./cchk data/specs/k7.txt -j 4
./cchk data/specs/k8.txt -j 6
./cchk data/specs/k9.txt -j 8
```
Without OpenMP leave out `-fopenmp`; the program then uses one thread. With MSVC, run
`cl -O2 -openmp checkers/cchk.c` in a developer command prompt opened in the top folder, and go on in Git
Bash: the command makes `cchk.exe`, which `./cchk` runs there.

**Rust.** Needs cargo 1.88 or later (rustup installs a current one; the package of a system may be
older); the crate has no dependencies.
```
cargo build --release --manifest-path checkers/rust/Cargo.toml
checkers/rust/target/release/rchk data/specs/k7.txt -j 4
checkers/rust/target/release/rchk data/specs/k8.txt -j 6
checkers/rust/target/release/rchk data/specs/k9.txt -j 8
```

**Python.** Needs Python 3.10 or later and numpy.
```
python checkers/check_bound.py data/specs/k7.txt -j 4
python checkers/check_bound.py data/specs/k8.txt -j 4
python checkers/check_bound.py data/specs/k9.txt -j 12 --log k9.log
```
With `--log FILE` the cell sums are written to FILE as they are computed, and an interrupted run is
continued by repeating the command. The sums already in FILE are then taken as they stand, so start
without the file if the check is to rest on one run alone. If the system kills one of the processes (too
little memory), the Python checker does not end: stop it and repeat the command with fewer processes;
with `--log` the cell sums already found are kept. Without numpy the checker evaluates every height
tuple in a loop of its own, which is practical only for the small spec files (`tiny`, `rounding`, `bhh`,
`k4`).

Each record of a checker run in `runs/` (`python_*.txt`, `c_*.txt`, `rust_*.txt`) holds the five lines
that the checker printed, with LF line ends, and the SHA-256 in `runs/times.txt` is that of these five
lines. To compare a run with its record:
```
./cchk data/specs/k7.txt -j 4 | tr -d '\r' | cmp - runs/c_k7.txt
```
(`tr` removes the carriage returns with which the Python and the C checker end their lines under
Windows). The records were made with `checkers/record.sh`, which needs GNU coreutils.

## Results

<!-- results:begin -->
| Spec file | k | h | Total A₀ | Bound (rounded up) | Threshold |
|---|---|---|---|---|---|
| `data/specs/k5.txt` | 5 | 2 | 1761033937996622 | 0.878820870371 | 8789/10000 |
| `data/specs/k6.txt` | 6 | 2 | 12593568504391125 | 0.872868757138 | 8729/10000 |
| `data/specs/k7.txt` | 7 | 21/10 | 92054418307910785 | 0.868075379727 | 8681/10000 |
| `data/specs/k8.txt` | 8 | 21/10 | 628708228549677266 | 0.864607001369 | 8647/10000 |
| `data/specs/k9.txt` | 9 | 11/5 | 4430997795015293889 | 0.861715646305 | 8618/10000 |
<!-- results:end -->

The bound is A₀·h₂ / (n^(k+1)·2^32·k·h₁) for the strip height h = h₁/h₂ and n = 6 height cells
(`RECIPE.md`, Section 8). The last row is Theorem 1.1 of the paper. A checker accepts if the bound is at
most the threshold. For `k9.txt` the threshold is the 0.8618 of Theorem 1.1; the bound, 0.86171…, is
smaller, so the inequality of the theorem is strict. The spec files `tiny.txt` (a small example),
`rounding.txt`, `k4.txt` and `bhh.txt` (the strip bound; `controls/README.md`) are used for tests and
controls.

## What is proved, and how it was checked

Theorem 4.1 of the paper is about the number defined in Section 4.1 of the paper, and `RECIPE.md`
restates that definition for the programs. That the two texts define the same integers was checked only
by reading them side by side. That the number is below the threshold is what the checkers establish.

The three checkers share no code. They share the text that they follow (`RECIPE.md`) and the values file
with which they compare; none relies on the program that wrote that file, because each recomputes every
number in it from the parameters, in integer arithmetic alone. Each compares every number with the file,
so the three agree on every table entry and every cell sum, not only on the total. Their agreement is
evidence against errors of implementation, but not against a misreading of `RECIPE.md` that the three
have in common; nor is it evidence that `RECIPE.md` defines an upper bound for β, which is proved in the
paper. The section on the tools used, near the end of this file, says how the programs were written and
how the comparisons by reading named in this section were made. The controls that concern the table (the
segments, the bracket and the simulated blocks) take the table from the values file, as
`controls/plain_sums.c` does, and the scripts of the controls use some routines of the Python checker,
which read the files and list the keys and the pairs of points; `controls/README.md` names them.

- The C and the Rust checker were each first written from `RECIPE.md` alone, without access to the Python
  checker or to the other one. The sum over the cells is by far the longest step, and each checker
  shortens it by the three identities of Section 7 of `RECIPE.md` (reversal of a cell, reflection of the
  heights, paths shared by cells that differ only at the two end points; the first two are symmetries
  that Dong and Cao use as well). The routines that use these identities were added later, in each
  checker without access to the corresponding routines of the other two.
- For k = 5, 6 and 7 every cell sum was also computed by the versions of the three checkers from before
  these routines were added, and for k = 8 by that version of the C checker. These versions use neither
  the reversal nor the reflection, and only the C version uses a part of the third identity. The versions
  and what they printed are in `runs/earlier/` (`runs/earlier/README.md` says exactly what each version
  shares between cells).
- For k = 9 there is no such computation: by our estimate from the run for k = 8 it would take some
  hundreds of hours of processor time. The cell sums for k = 9 therefore rest on the identities, in the
  routines whose results for k ≤ 8 were confirmed in this way. As a control, `controls/plain_sums.c`
  recomputed 22 of them: the cell sums of the gap tuples (0, …, 0) and (3, …, 3), which are the least
  and the greatest, of ten gap tuples drawn at random, and of the reverses of these ten. It is a
  separate program that uses none of the identities. It takes the table from the values file and shares
  nothing between cells: for every cell separately it finds the least cost by dynamic programming over
  the sets of interior points, and for every 100003rd cell (605 of the 60,466,176 cells of a gap tuple)
  a second time by going through all 40,320 orders. The 22 equal the stored ones (`runs/plain_k9.txt`).
  An error that affected a share p of the gap tuples would escape ten tuples drawn at random with
  probability (1 − p)^10, which is 0.11 for p = 1/5: the sample would probably show an error that
  affects most gap tuples, and would not show one that is confined to a few.
- The Python checker still contains a routine that uses none of the identities (`cell_sum_plain`), and
  the unit tests compare the fast routine with it on small cases.
- For k = 5 to 9 the equations for the totals are also proved in Lean 4 (`lean/`), with steps that
  the Lean kernel does not check. The definitions of `RECIPE.md` are transcribed there, and an efficient
  evaluation is proved equal to them for all parameters; the kernel checks that proof. The evaluation
  itself is run as compiled code (`native_decide`); the kernel does not check it, and Lean records it as
  an axiom. The evaluation for k = 9 in Lean was run once, in 64 pieces and a last step. The numbers
  that the theorems state were known beforehand (the totals are those of the checkers), so their
  agreement with the values files is by construction; what Lean adds is that each equation follows from
  evaluations that start from the parameters, read no file and do not use the reversal. The agreement
  of the Lean definitions with `RECIPE.md` was checked only by reading the two side by side.
- The proofs of Sections 2 to 4 of the paper are not formalised, and no program here checks them. They
  were checked by reading, and they have not been through peer review. The controls test them
  numerically (`controls/README.md`): the numerical integration tests the inequalities of Section 3
  without using them, and the simulated tour could show a gross error in the construction of Section 2
  and no more.

## What is where

| Folder or file | Contents |
|---|---|
| `RECIPE.md` | the computation, defined by integer arithmetic alone (Section 4 of the paper) |
| `checkers/` | the three programs: `check_bound.py` (Python), `cchk.c` (C), `rust/` (Rust); their tests, described in `checkers/TESTS.md` |
| `data/specs/` | the spec files |
| `data/values/` | the values files, one for each spec file |
| `data/tests/` | test inputs for the checkers, most of them with one fault each |
| `controls/` | the controls, described in `controls/README.md`: numerical integration, two-sided bracket, simulations, the cells of Dong and Cao, arXiv:2610.02809; a plain recomputation of some cell sums |
| `lean/` | the computation in Lean 4: its definitions, an efficient evaluation, the proof that the two agree, and the evaluations for k = 5 to 9 (Section 5.2 of the paper; `lean/README.md`) |
| `tools/` | `paper_numbers.py` (the numbers of the paper, from the records) and `make_sums.sh` |
| `paper/` | LaTeX source, the script that draws the figure, `main.pdf` |
| `runs/` | records of the runs (the section "Records" says which record belongs to which claim) |

`SHA256SUMS.txt` lists the SHA-256 of every other file; `sha256sum -c SHA256SUMS.txt` in the top folder
checks them (`tools/make_sums.sh` writes the list). `.github/workflows/check.yml` is set up to run on
GitHub the unit tests, the test inputs and, up to k = 8, the three checkers, and to compare what the
checkers print with the records in `runs/`. It does not run the mutation tests, the controls other than
`plain_sums` for k = 5, or the Lean development. `ruff.toml` holds the settings of the linter that it
runs on the Python files.

## Tests of the checkers

```
python checkers/test_check_bound.py
python checkers/make_tests.py
bash checkers/test_checkers.sh
cargo test --release --manifest-path checkers/rust/Cargo.toml
python checkers/mutation_test.py
python checkers/mutation_test_compiled.py c
python checkers/mutation_test_compiled.py rust
```

Each command ends with status 0 on success. Build the C and the Rust checker before the third command,
which tests the checkers that it finds; the last three commands are the mutation tests. What the first
four printed is in `runs/tests.txt`, and what the last three printed in `runs/mutation_test.txt`. The
first two take seconds, `test_checkers.sh` up to three minutes, and `cargo test` as long as the crate
takes to build. Each of the three mutation tests takes between a few minutes and half an hour and runs
four test inputs at a time. `checkers/TESTS.md` describes each test, and says which wrong versions of
the checkers are not detected and what the tests do not reach.

## Making the values files

With `--write` the Python checker creates the values file named in the spec file instead of comparing
with it; the file must not exist yet. To make one again, copy the spec file with its last line changed to
a file name that is not in use (the name is relative to the folder of the spec file), and run the checker
on the copy. For `k5.txt`:
```
sed '$ s|.*|values ../values/COPY.txt|' data/specs/k5.txt > data/specs/COPY.txt
python checkers/check_bound.py data/specs/COPY.txt -j 8 --write
cmp data/values/COPY.txt data/values/k5.txt
rm data/specs/COPY.txt data/values/COPY.txt
```
The first line printed is then `wrote` with the name of the file, and the new file equals the one in
`data/values/` byte for byte. Without numpy take `k4.txt` for this trial: the Python checker is then
slow.

## The controls

`controls/README.md` says what each control does, what it found and what it cannot show. To repeat them:
```
bash controls/make_records.sh strip bracket segments blocks second tour limits dongcao
bash controls/make_records.sh plain
```
The first command repeats the controls that use floating-point arithmetic or simulation. It needs numpy,
numba, scipy and mpmath (`python -m pip install numpy numba scipy mpmath`) and took about seven hours on
our computer, nearly six of them for the simulations `blocks`, `second` and `limits`; `strip` takes about
ten minutes and prints nothing meanwhile. The scripts use as many threads as `NUMBA_NUM_THREADS` allows;
we used 2 to 8. The header of `controls/make_records.sh` says which record belongs to which control, how
long each took, and how to make the records for a single k, to run the simulations with fewer blocks and
to continue an interrupted bracket for k = 7 from its log.

The command writes over the records in `runs/`: keep a copy of `runs/` to compare with, or restore the
stored records afterwards with `git checkout runs`. A repeated record can differ from the stored one in
two places even if every result agrees: its first line, which names the versions of Python, numpy and
numba (ours are in the stored records; scipy was 1.15.3 and mpmath 1.3.0), and the line with its running
time. The simulations use fixed seeds, but their last digits can depend on the versions of the libraries.

The second command needs a C compiler and no Python. It recomputes the 22 cell sums for k = 9 named
above, which takes about three hours of processor time; `PLAIN_THREADS` sets the number of threads (4 if
it is not set). The compiler is gcc unless `CC` names another, and `PLAIN_OPENMP` is the option that
turns OpenMP on (`-fopenmp` if it is not set). With MSVC, set `CC=cl` and `PLAIN_OPENMP=-openmp` in a
bash started from a developer command prompt; `cl` then warns about the options `-std=c11` and `-o`,
which does no harm. This record has no running time: a repeated record must equal the stored one except
in its first two lines, which name the compiler and the command with its number of threads. To try the
program first on k = 5, where it recomputes all 1024 cell sums in a few seconds:
```
gcc -std=c11 -O2 -fopenmp controls/plain_sums.c -o plain_sums
./plain_sums data/values/k5.txt 1024 1 -j 4
```
The last line must read `1024 cell sums of 46656 cells each: 1024 equal to the stored sums, 0 different`.

## The Lean development

`lean/` holds the computation of `RECIPE.md` in Lean 4, and `lean/README.md` describes it in full: what
is proved, on which axioms each theorem rests, how the definitions correspond to `RECIPE.md`, what has
to be trusted, and the records of the runs. The bullet on Lean in the section "What is proved, and how
it was checked" is the summary. The development needs Lean 4.31.0 (named in `lean/lean-toolchain`; if
Lean was installed with elan, elan fetches that version) and no library beyond the one that comes with
Lean.
```
cd lean
export LEAN_NUM_THREADS=1   # lake then builds one module at a time
lake build                  # the definitions and the proofs: about a minute
lake build Results.K5S      # the total for k = 5: about five minutes on 16 threads
lake build Results.K9S      # the total for k = 9: 64 pieces of about 11 minutes each on 16 threads
lake build Results          # everything, with the older evaluations (about seven hours more, on 4 threads)
lake build Results.Axioms   # prints the axioms of the theorems
cd ..
```
A build succeeds only if Lean accepts every proof. The last command prints, for each theorem, the axioms
on which it rests; `lean/runs/axioms.txt` is what it printed in our build. An evaluation computes in the
thread pool of the `lean` process, whose size is the `-j16` in `lean/lakefile.toml` (`lean/README.md`
says how to change it).

For k = 9 the evaluation was made in 64 pieces, each of which proves four of the values A_4 of
Section 8 of `RECIPE.md`, and a last step from these 256 values to the total. The pieces took 11.7
hours in all on 15 or 16 threads, and each was evaluated once. For k = 5 to 8 the totals were also
evaluated by an older routine, which shares code with this one. We built the development under Windows
only, and the evaluation for k = 9 was run once. The workflow in `.github/` does not build it.

## The paper

`bash paper/build.sh` builds `paper/main.pdf` and writes over the stored file; the new file differs from
it at least in its date. It needs pdflatex and bibtex with the class amsart and the packages named at the
head of `paper/tex/main.tex`, all of which TeX Live and MiKTeX provide.
`python paper/figures/make_figures.py` draws the figure again and writes over the stored one (needs
numpy, numba and matplotlib; about a minute). `bash paper/make_arxiv.sh` makes the source bundle for
arXiv in `paper/build/`, from files that `paper/build.sh` leaves there, so it must be run after that
script.

`python tools/paper_numbers.py --check` needs no packages. It derives the numbers of the paper from the
records (`paper/tex/numbers.tex`, the tables `paper/tex/*_table.tex`, and in this file the table of
results and the paragraph on running times) and compares them with these files as they stand; without
`--check` it writes the files instead. It also checks a list of sentences of the paper's source, of this
file, of `controls/README.md` and of `checkers/TESTS.md` that repeat parameters or values of the records
(the function `stated` of the script), and nothing else of the text, and it compares the records of the
Lean development with the Lean sources and with the records of the checkers. It cannot tell whether a
record is the output of the run that it names, and it does not compare `paper/main.pdf` with the source.
With `--check` it has succeeded if it prints five lines `agrees with the records:`, one for each file
(`paper/tex/numbers.tex`, the three tables and this file), and ends with status 0; a line that begins
with `MISSING`, `DIFFERS` or `paper_numbers:` names what does not agree.

## Records

| Claim, and where it is made | Record in `runs/` |
|---|---|
| Theorem 5.1, the totals | `python_k5.txt`, `c_k5.txt`, `rust_k5.txt`, and likewise for `k6` to `k9` |
| Section 5.2, repeated runs; this file, running times | `times.txt`: one line for each run of a checker (its first line names the columns; the SHA-256 is that of the lines printed on standard output, with LF line ends) |
| Section 5.2, the earlier versions of the checkers | `earlier/` |
| This file and `controls/README.md` only, cell sums for k = 9 recomputed by a separate program | `plain_k9.txt` |
| Section 5.2, the check in Lean | not in `runs/` but in `lean/runs/`: `k5s_done.txt` to `k9s_done.txt` with the outputs `…_run.out` (for k = 5 in three parts, `k5s_run1.out` to `k5s_run3.out`), `axioms.txt`, `sources_at_end.txt`; `final_build3.out` for the older routine (`lean/README.md` describes them all) |
| Section 5.3, the segments by numerical integration | `segments_k5.txt` to `segments_k9.txt` |
| Section 5.3 and Table 5.1, the bracket | `bracket_k5.txt` to `bracket_k9.txt`; for k = 8 and 9 the bracket of the rule also uses `blocks_k8.txt`, `blocks_k9.txt` and the totals (`controls/README.md`) |
| Section 5.3 and Table 5.1, simulated blocks | `blocks_k5.txt` to `blocks_k9.txt` |
| `controls/README.md` only, the second sample of simulated blocks | `blocks_k8_second.txt`, `blocks_k9_second.txt` |
| `controls/README.md` only, the strip bound | `python_bhh.txt`, `c_bhh.txt`, `rust_bhh.txt`, `strip_integral.txt` |
| `controls/README.md` only, the tour of the proof on simulated points | `tour_k9_2000.txt`, `tour_k9_8000.txt` |
| Section 6.1 and `controls/README.md`, the cells of Dong and Cao | `dongcao_setting.txt` |
| Table 6.1 and `controls/README.md`, shortest paths | `limits.txt` |
| The small spec files (not in the paper) | `python_NAME.txt`, `c_NAME.txt`, `rust_NAME.txt` for `tiny`, `rounding`, `k4` |
| Tests and mutation tests (`checkers/TESTS.md`) | `tests.txt`, `mutation_test.txt` |

## Use of AI tools

The author made significant use of Claude Opus 5.5, GPT-6 Pro and GPT-6.1 Sol in developing the method,
writing the code and the Lean formalisation, and drafting the paper. The author reviewed the content,
edited it as needed, and takes full responsibility for it. The three checkers, the controls and the Lean
development were written with the first of these models, so the agreement of the three checkers is no
evidence against a misreading of `RECIPE.md` that the model makes each time. The comparison of
`RECIPE.md` with Section 4.1 of the paper and the review of the Lean definitions against `RECIPE.md`
were made with the same model. The proofs of Sections 2 to 4 of the paper were checked by reading, with
models named above.

## Licence, citation and reports of errors

The programs and scripts (in `checkers/`, `controls/`, `tools/`, `lean/`, `runs/earlier/sources/` and
`paper/`, and the workflow) are released under the MIT licence (`LICENSE`). Everything else (the paper,
`RECIPE.md`, this file and the other documents, `data/`, and the records in `runs/` and `lean/runs/`) is
released under the Creative Commons Attribution 4.0 licence (`LICENSE-CC-BY-4.0`;
https://creativecommons.org/licenses/by/4.0/). `CITATION.cff` says how to cite the paper and this
repository.

Reports of errors, in the paper, in `RECIPE.md` or in the programs, are welcome: as an issue at
https://github.com/devinokeefe/travelling-sales-person-constant-bounds/issues or by mail to the address in `CITATION.cff`.
