# The checkers

The three checkers carry out the computation of [RECIPE.md](../RECIPE.md): `check_bound.py` (Python),
`cchk.c` (C) and the crate in `rust/` (Rust). Each takes a spec file from `data/specs/`, which gives the
parameters of one computation and a threshold. It recomputes every number from the parameters and
compares the results with the values file that the spec file names (in `data/values/`): the cell masses
P_c (the paper calls them probabilities), the tail term E_T, the table, the cell sums and the total
(Section 4.1 of the paper). It accepts if every number agrees and the bound is at most the threshold.

Each checker is built and run on its own. All commands are run from the top folder, in a POSIX shell:
bash under Linux or macOS, Git Bash or WSL under Windows. The tests are described in
[TESTS.md](TESTS.md).

## Building and running

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

**Python.** Needs Python 3.10 or later and numpy. The interpreter is called `python` here; if yours is
`python3`, use that name, and set `PYTHON=python3` for the shell scripts.
```
python checkers/check_bound.py data/specs/k7.txt -j 4
python checkers/check_bound.py data/specs/k8.txt -j 4
python checkers/check_bound.py data/specs/k9.txt -j 12 --log k9.log
```

The option `-j N` sets the number of threads, or of processes for the Python checker; the output does
not depend on it. The numbers above are those of the recorded runs under Windows.

With `--log FILE` the Python checker writes the cell sums to FILE as they are computed, and an
interrupted run is continued by repeating the command. The sums already in FILE are then taken as they
stand, so start without the file if the check is to rest on one run alone. If the system kills one of
the processes (too little memory), the Python checker does not end: stop it and repeat the command with
fewer processes; with `--log` the cell sums already found are kept. Without numpy the checker evaluates
every height tuple in a loop of its own, which is practical only for the small spec files.

Besides `k5.txt` to `k9.txt` there are four small spec files for tests and controls: `tiny.txt` (a small
example), `rounding.txt`, `k4.txt` and `bhh.txt` (the strip bound; `controls/README.md`).

## Output and exit status

A checker that accepts prints five lines on standard output; the top-level `README.md` shows them for
`k9.txt`.
Progress and times go to standard error, and from the Rust checker also the sizes of the largest values.

The exit status is 0 if the checker accepts, 1 if a number differs or the bound exceeds the threshold,
and 2 if a file is malformed or an arithmetic bound is violated. Section 10 of `RECIPE.md` says what is
printed in each case, and gives the formats of the two kinds of file and the order in which a checker
checks its input. If the Python checker stops with a traceback (under Python 3.9, for example), its
status is also 1, but that is a failure of the program and not a verdict: with a verdict of status 1
the last line of the standard output begins with `REJECTED:`.

## Comparing a run with its record

Each record of a checker run in `runs/` (`python_*.txt`, `c_*.txt`, `rust_*.txt`) holds the five lines
that the checker printed, with LF line ends. To compare a run with its record:
```
./cchk data/specs/k7.txt -j 4 | tr -d '\r' | cmp - runs/c_k7.txt
```
(`tr` removes the carriage returns with which the Python and the C checker end their lines under
Windows). The records were made with `checkers/record.sh`, which needs GNU coreutils and adds a line to
`runs/times.txt` for each run.

## Making a values file

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
`data/values/` byte for byte. Without numpy take `k4.txt` for this trial.

## Where the checkers were run

The records are from runs under Windows 11 (the C checker built with MSVC, the Rust checker, the Python
checker with numpy) and under Ubuntu 24.04 in WSL 2 (the C checker built with gcc 13.3, up to k = 9; the
Python checker without numpy, on the small spec files). The workflow in `.github/` runs all three
checkers under Ubuntu 24.04 up to k = 8 and compares what they print with the records. The Rust checker
and the Python checker with numpy have not been run on `k9.txt` under Linux, and nothing was run under
macOS.

## How the checkers were written

The three checkers share no code. They share the text that they follow (`RECIPE.md`) and the values file
with which they compare; none relies on the program that wrote that file, because each recomputes every
number in it.

The C and the Rust checker were each first written from `RECIPE.md` alone, without access to the Python
checker or to the other one. The sum over the cells is by far the longest step, and each checker
shortens it by the three identities of Section 7 of `RECIPE.md`: reversal of a cell, reflection of the
heights, and paths shared by cells that differ only at the two end points. The first two are symmetries
that Dong and Cao use as well (arXiv:2610.02809). The routines that use these identities were added
later, in each checker without access to the corresponding routines of the other two. The versions from
before are in `runs/earlier/sources/`, and `runs/earlier/README.md` says what their runs confirm. The
Python checker still contains a routine that uses none of the identities (`cell_sum_plain`), and the
unit tests compare the fast routine with it on small cases.
