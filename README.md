# An upper bound for the Euclidean travelling salesman constant

**Paper:** [An upper bound for the Euclidean travelling salesman constant](paper/main.pdf) (PDF)

By a theorem of Beardwood, Halton and Hammersley, the length of a shortest tour through n independent
uniform random points in the unit square, divided by √n, converges almost surely to a constant β. The
paper proves β < 0.8618. The best earlier upper bound was 0.8810, by Dong and Cao
([arXiv:2610.02809](https://arxiv.org/abs/2610.02809)).

The proof ends in a finite computation. The paper defines a number by integer arithmetic alone (Section
4.1) and proves that it is an upper bound for β (Theorem 4.1); that the number is below 0.8618 is the
result of the computation. This repository holds the computation as the programs follow it
([RECIPE.md](RECIPE.md)), three programs that carry it out (the *checkers*), what they printed, and the
further checks that were made.

## Checking the computation

To check the computation on which the theorem rests, one checker and one run are enough. With gcc, from
the top folder (under Windows in WSL; [checkers/README.md](checkers/README.md) says how to build with
MSVC):

```
gcc -std=c11 -O2 -fopenmp checkers/cchk.c -o cchk
./cchk data/specs/k9.txt -j 8
```

The checker recomputes every number from the parameters in the spec file `data/specs/k9.txt`, compares
the results with the values file `data/values/k9.txt`, and prints

```
the stored values agree with the recomputed values
total 4430997795015293889
bound 0.861715646305 (rounded up)
bound <= 8618/10000
ACCEPTED
```

The check has succeeded if it prints these five lines and ends with status 0. Progress goes to standard
error, and `-j` sets the number of threads or processes, on which the output does not depend. The other
two checkers are run in the same way and print the same lines:

```
cargo build --release --manifest-path checkers/rust/Cargo.toml
checkers/rust/target/release/rchk data/specs/k9.txt -j 8
```

```
python checkers/check_bound.py data/specs/k9.txt -j 12
```

<!-- times:begin -->
On a desktop computer the check of `k9.txt` took 76 minutes with the C checker built with MSVC under
Windows (96 and 98 minutes built with gcc under Linux) and 65 minutes with the Rust checker, on 8 threads
each, and 3.3 hours with the Python checker on 12 processes. The spec files up to `k7.txt` take less than
a minute, and `k8.txt` takes about 3 minutes with the C or the Rust checker and 22 with the Python
checker (`runs/times.txt`).
<!-- times:end -->

The C checker needs a C11 compiler, the Rust checker cargo 1.88 or later, and the Python checker Python
3.10 or later with numpy. No checker needs another. [checkers/README.md](checkers/README.md) has the
rest: other compilers, the options, the exit statuses, and how to compare a run with its record.

## Results

The method cuts the square into strips of height h/√n and visits the points of each strip in blocks of
k + 1 consecutive points. Each row is one computation, and the last row is Theorem 1.1 of the paper.

<!-- results:begin -->
| Spec file | k | h | Total A₀ | Bound (rounded up) | Threshold |
|---|---|---|---|---|---|
| `data/specs/k5.txt` | 5 | 2 | 1761033937996622 | 0.878820870371 | 8789/10000 |
| `data/specs/k6.txt` | 6 | 2 | 12593568504391125 | 0.872868757138 | 8729/10000 |
| `data/specs/k7.txt` | 7 | 21/10 | 92054418307910785 | 0.868075379727 | 8681/10000 |
| `data/specs/k8.txt` | 8 | 21/10 | 628708228549677266 | 0.864607001369 | 8647/10000 |
| `data/specs/k9.txt` | 9 | 11/5 | 4430997795015293889 | 0.861715646305 | 8618/10000 |
<!-- results:end -->

The bound is A₀·h₂ / (6^(k+1)·2^32·k·h₁) for h = h₁/h₂ (`RECIPE.md`, Section 8), and a checker accepts
if the bound is at most the threshold. For `k9.txt` the bound, 0.86171…, is below the threshold 0.8618,
so the inequality of the theorem is strict.

Every checker was run at least twice on each of `k5.txt` to `k9.txt`, except the Python checker on
`k9.txt`, which was run once; all runs printed the same lines (`runs/times.txt`).

## What has been checked, and what has not

- **The proof.** That the number of Section 4.1 is an upper bound for β is proved in Sections 2 to 4 of
  the paper. These proofs were checked by reading. They are not formalised, no program here checks them,
  and they have not been through peer review.
- **The definition.** `RECIPE.md` restates Section 4.1 for the programs. That the two texts define the
  same integers was checked only by reading them side by side.
- **The checkers.** The three share no code, and the C and the Rust checker were each first written from
  `RECIPE.md` alone. Each recomputes every number of the values file from the parameters, in integer
  arithmetic, and compares it with the file, so the three agree on every intermediate number and not
  only on the total. This is evidence against errors of implementation, not against a misreading of
  `RECIPE.md` that the three have in common.
- **The cell sums.** The total is formed from cell sums, each a sum over many cells: for k = 9 there are
  262,144 sums over 60,466,176 cells each. This is by far the longest step, and the checkers shorten it
  by three identities: reversal, reflection and shared paths (`RECIPE.md`, Section 7). For k = 5, 6 and
  7 every cell sum was also computed by earlier versions of the three checkers, and for k = 8 by the
  earlier version of the C checker. These versions use neither the reversal nor the reflection, and only
  the C version uses a part of the third identity ([runs/earlier/README.md](runs/earlier/README.md)).
  For k = 9 there is no such computation: by an estimate from the run for k = 8 it would take some
  hundreds of hours of processor time. There the cell sums rest on the identities, in routines whose
  results for k ≤ 8 were confirmed in this way. As a control, a separate program that uses none of the
  identities (`controls/plain_sums.c`) recomputed 22 of them, and they equal the stored ones. A sample
  of this size would probably show an error that affects most of the cell sums, and would not show one
  that is confined to a few ([controls/README.md](controls/README.md)).
- **Lean.** For k = 5 to 9 the totals are also proved in Lean 4, with steps that the Lean kernel does
  not check. The definitions of `RECIPE.md` are transcribed there, and an efficient evaluation is proved
  equal to them for all parameters; the kernel checks that proof. The evaluation itself runs as compiled
  code (`native_decide`), which the kernel does not check and Lean records as an axiom; for k = 9 it was
  run once, in 64 pieces that took 11.7 hours on 15 or 16 threads. That the Lean definitions agree with
  `RECIPE.md` was checked only by reading ([lean/README.md](lean/README.md)).
- **The controls.** Floating-point computations and simulations test the proofs and the programs
  numerically, among them numerical integration of the segment lengths, simulated blocks, and the tour
  of the proof built on simulated points. They are not part of the proof.
  [controls/README.md](controls/README.md) says what each control found and what it cannot show.

The section on the tools used, below, says how the programs were written and how the readings named
here were made.

## Contents

| Folder or file | Contents |
|---|---|
| [paper/](paper/) | the paper (`main.pdf`), its LaTeX source, and how to build it |
| [RECIPE.md](RECIPE.md) | the computation, defined by integer arithmetic alone |
| [checkers/](checkers/) | the three checkers, in Python, C and Rust, and their tests |
| [data/](data/) | `specs/`: the parameters and the threshold of each computation; `values/`: the integers that the checkers compare; `tests/`: test inputs |
| [runs/](runs/) | what the programs printed; [runs/README.md](runs/README.md) says which record belongs to which claim |
| [controls/](controls/) | the controls |
| [lean/](lean/) | the computation in Lean 4 |
| [tools/](tools/) | `paper_numbers.py`, which checks the numbers of the paper and of these documents against the records ([paper/README.md](paper/README.md)), and `make_sums.sh`, which writes `SHA256SUMS.txt` |

`SHA256SUMS.txt` lists the SHA-256 of every other file (`sha256sum -c SHA256SUMS.txt`). The workflow in
`.github/` runs the unit tests, the test inputs and, up to k = 8, the three checkers, and compares what
the checkers print with the records. It runs neither the mutation tests nor the Lean development, and of
the controls only `plain_sums` for k = 5. `ruff.toml` holds the settings of the linter that it runs on
the Python files.

## Tests

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
which tests the checkers that it finds. The last three are the mutation tests: they make wrong versions
of the checkers and report which of them the tests detect. [checkers/TESTS.md](checkers/TESTS.md)
describes each test, and says which wrong versions are not detected and what the tests do not reach.

## Use of AI tools

The author made significant use of Claude Opus 5.5, GPT-6 Pro and GPT-6.1 Sol in developing the method,
writing the code and the Lean formalisation, and drafting the paper. The author reviewed the content,
edited it as needed, and takes full responsibility for it.

The three checkers, the controls and the Lean development were written with the first of these models,
so a misreading of `RECIPE.md` could be common to all of them. The comparison of `RECIPE.md` with
Section 4.1 of the paper and the review of the Lean definitions against `RECIPE.md` were made with the
same model. The proofs of Sections 2 to 4 of the paper were checked by reading, with models named above.

## Licence and citation

The programs and scripts (in `checkers/`, `controls/`, `tools/`, `lean/`, `runs/earlier/sources/` and
`paper/`, and the workflow) are released under the MIT licence ([LICENSE](LICENSE)). Everything else
(the paper, `RECIPE.md`, the documents, `data/`, and the records in `runs/` and `lean/runs/`) is
released under the Creative Commons Attribution 4.0 licence ([LICENSE-CC-BY-4.0](LICENSE-CC-BY-4.0)).
[CITATION.cff](CITATION.cff) says how to cite the paper and this repository.

Reports of errors are welcome, as an
[issue](https://github.com/devinokeefe/travelling-sales-person-constant-bounds/issues) or by mail to
the address in `CITATION.cff`.
