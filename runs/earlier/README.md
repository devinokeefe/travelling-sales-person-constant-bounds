# Runs of earlier versions of the checkers

The checkers in `checkers/` shorten the sum over the cells by the three identities of Section 7 of
`RECIPE.md` (reversal, reflection, shared paths). The versions in `sources/` are the three checkers as
they stood before these routines were added. They go through every gap tuple and every height tuple of
the interior points, and accept k up to 8. This folder holds what they printed.

What these versions share between cells:

- The Python version shares nothing: it runs the whole recursion for every height tuple.
- The Rust version uses none of the three identities. It runs the recursion from point 0 and shares its
  first steps among the height tuples that begin with the same heights.
- The C version uses neither the reversal nor the reflection. It does use one part of the shared paths:
  for fixed heights of the interior points it computes the least costs H(u, v) once, for the n² cells
  that differ only in the heights a_0 and a_k of the two end points. It shares nothing between gap
  tuples.

The files `python_k5.txt`, `c_k5.txt`, `rust_k5.txt` and the like hold the five lines printed for
`data/specs/k5.txt` and the like. There are files for k = 5, 6 and 7 from all three versions and for
k = 8 from the C version only: so the runs for k = 5, 6 and 7 confirm the cell sums without any of the
three identities (Python and Rust), and the run for k = 8 confirms them without the reversal, the
reflection and the sharing between gap tuples. Each of these files equals the record of the present
checkers in `runs/` byte for byte (`tools/paper_numbers.py` checks that).

`times.txt` has one row for each run made with `checkers/record.sh`, in the format of `runs/times.txt`,
with the rows of the small spec files (`tiny`, `rounding`, `bhh`, `k4`), whose printed lines are not
kept here. The run of the C version for k = 8 was not made with that script and has no row; the program
reported 3,076 seconds for the cell sums on 6 threads.

`sources/` holds `check_bound.py`, `cchk.c` and the Rust crate as they were for these runs; they are not
maintained. They are built and run like the checkers in `checkers/` (see `checkers/README.md`), and
read the values files in `data/values/`. Build them outside the repository, so that the tests do not
take them for the present checkers and `tools/make_sums.sh` does not list what a build leaves behind:
for example
`gcc -std=c11 -O2 -fopenmp runs/earlier/sources/cchk.c -o ../cchk_earlier` and
`cargo build --release --manifest-path runs/earlier/sources/rust/Cargo.toml --target-dir ../rchk_earlier`.
