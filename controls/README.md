# The controls

The controls are not part of the proof. All but one use floating-point arithmetic or simulation
(`plain_sums.c` recomputes cell sums in integers), and they serve to detect a mistake in Sections 2 to 4
of the paper or in the checkers. Each can show some mistakes and not others: this file says what each
control does, what it found and what it cannot show. Sections 5.3 and 6.1 of the paper state the results
of most of them in brief; the strip bound, the tour and the second sample of blocks are described here
only, and the cell sums recomputed cell by cell here and, in brief, in the top-level `README.md`. The
last section says how to repeat the controls, and the header of `make_records.sh` says which record
belongs to which control. A script named without a folder is in `controls/` and a record in `runs/`;
other paths are relative to the top folder.

The controls that concern the table (the segments, the bracket and the simulated blocks) take the table
from the values file, as `plain_sums.c` does. Of the checkers the scripts use only routines of the
Python checker that read the files and that list the keys and the pairs of points (`read_spec`,
`read_values`, `stored_table`, `all_keys`, `pairs` and the scale `F` of `checkers/check_bound.py`).

## The segments (`segment_integral.py`)

For every key κ and every difference d of the height cells, the script computes the conditional expected
length of a segment by numerical integration, without the lemmas of Section 3 of the paper. For each of
the five results, every table entry Tab(κ, d)/F lies above the integral, by a relative margin between
4.8·10^-8 and 1.9·10^-4.

The script tests its own integration in two ways, and each record gives the results. The density of the
sum of the gaps of every key must have total mass 1; the largest error was 1.9·10^-15. For the 14 keys
with one gap or two gaps the integral was computed a second time, as a double integral without the
piecewise polynomials and without the closed form for the mean over the heights; the two values differ
by at most 3.0·10^-15 in relative terms.

This is the control that would show a lemma of Section 3 whose inequality pointed the wrong way. The
bracket below would not, because its upper end rests on the same lemmas as the proof, and the
simulations are too coarse. The control concerns the table, that is Proposition 3.5 and Steps 1 to 5;
the cell sums and the total do not enter it. The errors of the integration have not been bounded, and
for the keys with three or more gaps there is no second evaluation: a table entry that lay below the
true value by much less than the smallest margin could escape this control.

## The bracket (`bracket.py`)

The script computes two bounds for every table entry on a mesh twice as fine as that of the computation:
the upper bound of Proposition 3.5 and the matching lower bound from Jensen's inequality, which places
the mass of each mesh interval at its mean and, in the last gap cell, leaves out the event that the gap
exceeds the left end of the cell by more than T. Every integral of the previous control lies between
the two, and every table entry lies above the upper one, by a relative margin between 3.6·10^-8 and
1.4·10^-4, as it must: halving the mesh does not increase the bound of Proposition 3.5, and the
rounding of Section 4 only adds to it.

Summing the lower bounds, and likewise the upper bounds, along the path that the rule takes in a cell,
averaging over the cells with their probabilities and dividing by k·h gives two numbers below and above
the value of the rule: the ends of the bracket in Table 5.1. They are computed in floating-point
arithmetic, and the rounding errors have not been bounded.

For k ≤ 7 the average is over all cells. The routine that forms it is separate from the checkers, and
its sums of table entries reproduced every cell sum of the values files. For k > 7 the sums over all
cells would take days. There, the amounts by which the table entries along the path exceed the two bounds
are averaged over the cells of the simulated blocks (next section), with standard errors below 10^-9,
and subtracted from the bound of Theorem 5.1. For k > 7 the bracket is therefore computed from the total
A₀ of the checkers, and it would not show an error in the cell sums. For k ≤ 7, where both ways of
forming the bracket exist, the sample averages agree with the averages over all cells to within 10^-9
(`bracket_k5.txt` to `bracket_k7.txt` against the lines `table - lower` and `table - upper` of
`blocks_k5.txt` to `blocks_k7.txt`).

In each case the bound exceeds the lower end of the bracket by less than 10^-5. So the mesh, the
truncation at the level T and the rounding together add less than 10^-5 to the bound.

## Simulated blocks (`simulate.py`, records `blocks_k5.txt` to `blocks_k9.txt`)

The script draws 4·10^8 independent blocks for each k and measures, in each block, the length of the
path chosen by the rule and the length of a shortest path (the last two columns of Table 5.1). The
samples for the different k were drawn with one seed, so they are not independent of each other.

The simulated values of the rule lie within two standard errors of their brackets. For k = 5, 6 and 8
they lie above the bound of Theorem 5.1, none by more than about one standard error. This is to be
expected in some cases: the bound exceeds the value of the rule by less than one standard error.

Where several orders have the least cost in a cell, the simulation takes the first in the lexicographic
order, and the routine of the bracket need not take the same one. The two choices differ in value only
where the tied orders differ in the keys or the height differences of their segments.

The same blocks give a check of the totals that uses the table of the values file and none of the cell
sums. The cost of the order that the rule takes, averaged over the simulated blocks and divided by
F·k·h, estimates the bound of Theorem 5.1 itself, apart from the rounding of the cell masses P_c and of
the last step of the recipe, which is far smaller than the standard error. For k = 9 it gave
0.861722 ± 0.000008, against the bound 0.861716, and for every k it lies within two standard errors of
the bound. For k > 7 the bracket takes the total from the checkers, and this estimate does not; there a
second sample of the same size with another seed, for k = 8 and k = 9, gave 0.864599 ± 0.000009 and
0.861720 ± 0.000008, against the bounds 0.864608 and 0.861716. For these two k an error in the total
that changed the bound by 3·10^-5, which is more than three standard errors, would very probably show
in this estimate; a smaller one might not.

## Cell sums cell by cell (`plain_sums.c`)

A separate C program that uses none of the three identities of Section 7 of `RECIPE.md` recomputed 22
of the 262,144 cell sums for k = 9: the cell sums of the gap tuples (0, …, 0) and (3, …, 3), which are
the least and the greatest, of ten gap tuples drawn at random, and of the reverses of these ten. It
takes the table from the values file, so this control concerns the sum over the cells alone. It shares
nothing between cells: for every cell separately it finds the least cost by dynamic programming over
the sets of interior points, and for every 100003rd cell (605 of the 60,466,176 cells of a gap tuple) a
second time by going through all 40,320 orders. The 22 equal the stored ones (`runs/plain_k9.txt`).

The control stands in for a computation that was made for k ≤ 8 only. There earlier versions of the
checkers, which use neither the reversal nor the reflection, computed every cell sum
(`runs/earlier/README.md` says what each version shares between cells); for k = 9 that would take some
hundreds of hours of processor time, by an estimate from the run for k = 8. The
cell sums for k = 9 therefore rest on the identities, in the routines whose results for k ≤ 8 were
confirmed in this way. An error that affected a share p of the gap tuples would escape ten tuples drawn
at random with probability (1 − p)^10, which is 0.11 for p = 1/5: the sample would probably show an
error that affects most gap tuples, and would not show one that is confined to a few.

## The strip bound (`strip_integral.py`, with `data/specs/bhh.txt`)

For k = 2 there is a single order, and both segments of its path join consecutive points. With one gap
cell and one height cell the computation of `RECIPE.md` therefore bounds E|P₀P₁|/h, the expected
distance between consecutive points of a strip; this is the case k = 1 of Theorem 2.2, reached with
k = 2 because the checkers need k ≥ 2. For h = 26/15, a fraction close to √3, and ν = 256, with M = 128
and T = 16 as for the results, the three checkers gave the bound 0.921167…, and numerical integration
gave 0.921159… for the same quantity, lower by 8·10^-6. For h = √3 the integration gave 0.921160…, the
bound of Beardwood, Halton and Hammersley in Table 1.1. (As a function of h the quantity is least near
h = 1.734, not at √3.) This control involves no bounded gap cell and no choice between orders.

## The tour (`simulate.py`)

The script builds the tour of the proof of Theorem 2.2 for k = 9 on a simulated Poisson process, once
with 2000 strips and once with 8000, and measures the walks of the proof and the closed tour through the
points of the square. The records `tour_k9_2000.txt` and `tour_k9_8000.txt` hold the numbers. In both
runs the walks, divided by k and by the number of blocks used, lie within three standard errors of the
bound of Theorem 5.1; what this quotient estimates is the value of the rule, which lies below the bound
by less than 10^-5. The closed tour is shorter than the last inequality of the proof allows with that
bound; `tools/paper_numbers.py` tests both. That inequality is for the expected length, and each run is
one sample.

This control concerns the construction of Section 2 of the paper, which the other controls do not test.
It could show a gross error there and no more: the terms of order W that the proof allows are several
times larger than the amount by which the tour exceeded the bound, and the block that contains the gap
across the line x = W is one block among more than a thousand in each strip.

## The cells of Dong and Cao (`dongcao_setting.py`)

For k = 5 and h = 2, Dong and Cao use 12 gap cells and 20 height cells, all equally likely. The script
recomputes their second-moment bound for the segments on these cells and simulates the rule that it
defines, for 4·10^6 blocks. The mean of their bound over the sampled cells was 0.88093 ± 0.00012, which
agrees within the sampling error with the bound 0.8810 that they prove. The path of the rule gave the
value 0.87467 ± 0.00012, and in the same blocks the rule lost 0.000493 ± 0.000001 against the shortest
path. Section 6.1 of the paper uses the last two numbers.

This is our reading of their cells and of their bound, in a program of our own. Its only tests are two
comparisons with their paper: the mean of the bound, as above, and the shortest path in the same blocks,
0.87418 ± 0.00012 against their 0.87426. It does not repeat their proof.

## Shortest paths (`simulate.py`, record `limits.txt`)

Table 6.1 of the paper gives, for k = 5 to 10, the strip height with the smallest simulated
shortest-path value among the multiples of 1/10 that were tried, from 4·10^7 blocks (the same blocks at
all strip heights). The minimum over the strip heights is flat: for k = 7 and k = 9 the next lower
height gives a value larger by less than 0.0001. For the other k both adjacent heights give values that
are larger by between 0.0003 and 0.0015. The record `limits.txt` holds the values at all heights. The
standard errors are at most 0.00004. Three or four heights were tried for each k, so the table gives
the best of these and not the best height.

## Repeating the controls

From the top folder:
```
bash controls/make_records.sh strip bracket segments blocks second tour limits dongcao
bash controls/make_records.sh plain
```
The first command repeats the controls that use floating-point arithmetic or simulation. It needs numpy,
numba, scipy and mpmath (`python -m pip install numpy numba scipy mpmath`) and took about seven hours on
a desktop computer, nearly six of them for the simulations `blocks`, `second` and `limits`; `strip`
takes about ten minutes and prints nothing meanwhile. The scripts use as many threads as
`NUMBA_NUM_THREADS` allows; the records were made with 2 to 8. The header of `make_records.sh` says
which record belongs to which control, how long each took, and how to make the records for a single k,
to run the simulations with fewer blocks and to continue an interrupted bracket for k = 7 from its log.

The command writes over the records in `runs/`: keep a copy of `runs/` to compare with, or restore the
stored records afterwards with `git checkout runs`. A repeated record can differ from the stored one in
two places even if every result agrees: its first line, which names the versions of Python, numpy and
numba (those of the stored records are in the records; scipy was 1.15.3 and mpmath 1.3.0), and the line
with its running time. The simulations use fixed seeds, but their last digits can depend on the
versions of the libraries.

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
