# Tests of the checkers

The section "Tests of the checkers" of the top-level `README.md` gives the commands, says where their
output is recorded and how long they take. This file says what each test does, which wrong versions of
the checkers the tests do not detect, and what the tests do not reach. The commands are run from the
top folder; a script named without a folder is in `checkers/`.

- `test_check_bound.py` compares the parts of the Python checker with their definitions, evaluated in
  exact rational arithmetic or with 60-digit decimals: every rounded integer must lie on the right side
  of the exact value and within a few units of it (the script states the number for each test). One test
  continues a run from a log of cell sums. Without numpy the comparisons with the numpy routine are left
  out, and the script says so. Its checks are `assert` statements, so it must not be run with `python -O`
  or with PYTHONOPTIMIZE set: it would then report success without testing.
- `make_tests.py` writes 62 test inputs to `data/tests/`: values files with one number changed,
  thresholds at and just below the bound, and files that break the rules for text or for the form of a
  file; `EXPECTED.txt` there gives the exit status that each must produce. The files are in the
  repository already, and the script writes the same files again.
- `test_checkers.sh` runs every checker it finds on the small spec files and on the test inputs, and
  compares each exit status with the expected one and the lines printed by the checkers with one another.
  A line of `EXPECTED.txt` whose status is not 0, 1 or 2 counts as a failed test. Build the C and the
  Rust checker first: the script tests what it finds, and its first line names the checkers that it
  found. With `JOBS=N` in the environment it calls every checker with `-j N`; the results must be the
  same.
- `mutation_test.py` makes 64 wrong versions of the Python checker and confirms that the tests above
  detect every one. Each wrong version has one rounding reversed, one bound replaced by the wrong one,
  one term left out, the final test reversed, a printed line changed, one check of the input or of the
  log weakened, or one of the three identities applied wrongly. One change of this kind is not in the
  list, because we know no input that shows it: the inner of the two divisions for the weights of a
  bounded cell (`RECIPE.md`, Section 3) rounded down. The list of the Rust checker has this change,
  marked as not detected (see below). The script needs numpy and stops with a message without it.
- `python checkers/mutation_test_compiled.py c` and `python checkers/mutation_test_compiled.py rust` do
  the same for the C and the Rust checker, with the wrong versions listed in `checkers/mutants_c.json`
  and `checkers/rust/mutants.json`. The first needs gcc, or another C compiler named by `CC`; with MSVC,
  start it from a developer command prompt, or from a bash started in one, with `CC=cl`. The second
  needs cargo and builds the crate once for each wrong version. A wrong version of the Rust checker that
  the inputs do not detect is also given to the unit tests of the crate. `runs/mutation_test.txt` holds
  both runs of the C test: under Linux with gcc and under Windows with MSVC.
- Of the 61 wrong versions of the C checker 6 are not detected under Linux and 5 under Windows, and of
  the 90 of the Rust checker 1. They are marked in the lists with the reason, and the scripts report
  them as not detected. Three of the C versions lack a check of Section 9 of `RECIPE.md` that no input
  in `data/` reaches; no input on which all checkers are required to agree can make such a check fail.
  One allows the bytes 127 to 255 in the text of a file, which the rules for names and numbers reject
  anyway, and one allows a backslash in the path of a values file, which separates folders only under
  Windows, where it is detected. The sixth C version and the Rust version are wrong roundings in the
  weights of a bounded cell (`RECIPE.md`, Section 3). The C version that divides by Q − Rlo[n_c] in
  place of Q − Rup[n_c] changes the weights by about one unit of 2^-48, which no stored number of the
  test inputs shows: the tests of the C checker do not detect this error (the unit tests of the Python
  and the Rust checker compare the weights themselves). The Rust version that rounds the inner quotient
  down changes a weight only if that quotient is a multiple of the divisor, which is of the order of
  2^60, and no parameters are known for which it is: no weight changed for any that we tried.
- What these tests do not reach. Their inputs are small. `test_checkers.sh` and the mutation tests run
  the checkers on blocks of at most five gaps and with one thread (`test_checkers.sh` with more if `JOBS`
  is set), and the mutation test builds the C checker without OpenMP. The unit tests of the search over
  the orders go up to seven gaps in Python; in the Rust crate they go up to nine gaps, but with small
  random tables and at most two height cells. One test of the Rust crate compares some cell sums for
  nine gaps with the values file; it is left out unless asked for:
  `cargo test --release --manifest-path checkers/rust/Cargo.toml -- --ignored --nocapture nine_gaps`
  (about half a minute; a measurement of running times runs with it).
  An error that shows only with the parameters of k = 8 or 9, or only with several threads, would
  therefore have to show in the runs themselves, where the three checkers agree on every table entry
  and every cell sum, in every run.
- `data/specs/rounding.txt` exists for these tests. With the parameters of the theorem a rounding of
  Section 2 of the recipe that goes the wrong way changes few of the stored numbers or none, because the
  bounds for the exponentials are carried at scale 2^62 and the stored numbers at 2^48 and 2^32. With
  mesh 1023 and the boundaries of `rounding.txt`, each such rounding changes one of the cell masses P_c
  (`RECIPE.md`, Section 3).
