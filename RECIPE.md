# The integer recipe

This file defines, by integer arithmetic alone, the number that the checkers compute and compare with the
threshold. Section 4 of the paper gives the same definitions, with the same names for the integers, and
proves that the number is an upper bound for the travelling salesman constant β. Sections 2 to 8 below are
Steps 1 to 7 of Section 4.1 of the paper. The recipe is deterministic: every program that follows it
obtains the same integers. The values files in `data/values/` record those of Sections 3, 6, 7 and 8: the
cell masses (the paper calls them probabilities), the tail term, the table, the cell sums and the total.

All quantities are non-negative integers. `floor(a/b)` and `ceil(a/b)` are the integer quotients rounded down
and up. `ceil_sqrt(A)` is the least integer u ≥ 0 with u² ≥ A.

## 1. Parameters

A spec file (Section 10) gives

| Name | Meaning | Allowed | Used in the paper |
|---|---|---|---|
| k | number of gaps in a block (a block has k + 1 points) | 2 to 9 | 5 to 9 |
| h_1, h_2 | the strip height is h = h_1/h_2 | positive, below 2^64, in lowest terms | 2/1, 21/10 and 11/5 |
| M | horizontal mesh: gaps are measured in units of 1/M | 2 to 1024 | 128 |
| b_1, …, b_{m−1} | boundaries of the m gap cells, in units of 1/M | m from 1 to 8; 1 ≤ b_1 < b_2 < … < b_{m−1} < 2^64 | 48, 112, 208 |
| n | number of height cells | 1 to 16 | 6 |
| ν | vertical mesh: each height cell is cut into ν equal parts | 1 to 256 | 64 |
| T | a gap in the last gap cell is truncated at the length T beyond the left end of the cell, that is after T·M mesh intervals | 1 to 40 | 16 |
| θ_1, θ_2 | the threshold is θ = θ_1/θ_2 | positive, below 2^64 | see the spec files |

The number m of gap cells is one more than the number of boundaries; a spec file without boundaries has
m = 1. Gap cell c is [b_c/M, b_{c+1}/M) with b_0 = 0, and the last cell is [b_{m−1}/M, ∞).

The last column gives the parameters of `k5.txt` to `k9.txt`: h is 2 for k = 5 and 6, 21/10 for k = 7 and
8, and 11/5 for k = 9. The file `bhh.txt`, for the strip bound (`controls/README.md`), has k = 2,
h = 26/15, no boundaries (m = 1), n = 1 and ν = 256, with M = 128 and T = 16; `tiny.txt`, `rounding.txt`
and `k4.txt` are small test cases.

The allowed ranges are those that the programs accept. The proof in the paper needs less: it holds for
every k ≥ 1 and every M from 2 to 2^61, without upper limits on m, n, ν, T, h_1, h_2 and the boundaries,
and it does not use that h_1/h_2 is in lowest terms. The integers of Sections 2 to 8 depend on h_1 and h_2
only through h, and so does the test of Section 8. Into the integers the two numbers enter through Dist
alone (Section 5), and there ceil(ceil(y)/a) = ceil(y/a), for real y ≥ 0 and an integer a ≥ 1, gives
Dist(j, τ) = ceil(F·sqrt(j² + (M·h²·τ/(n·ν))²) / M). Lowest terms are required so that a strip height is
written in one way only and the intermediate values are as small as they can be.

Fixed scales: Q = 2^62, D = 2^48, F = 2^32.

Derived: n_c = b_{c+1} − b_c for 0 ≤ c ≤ m − 2 (the number of mesh intervals in a bounded cell), and
n_{m−1} = N_T = T·M.

## 2. Bounds for e^{−1/M} and its powers

Put lo_13 = 0 and up_13 = Q. For j = 12, 11, …, 1 put

    up_j = Q − floor(lo_{j+1} / (M·j)),
    lo_j = Q − ceil(up_{j+1} / (M·j)).

Then lo_1 ≤ Q·e^{−1/M} ≤ up_1.

Let I = max(b_{m−1}, N_T). Put Rup[0] = Rlo[0] = Q and, for i = 1, …, I,

    Rup[i] = ceil(Rup[i−1]·up_1 / Q),
    Rlo[i] = floor(Rlo[i−1]·lo_1 / Q).

Then Rlo[i] ≤ Q·e^{−i/M} ≤ Rup[i].

## 3. Weights, cell masses and the tail term

    C_λ = Q − M·(Q − up_1),
    C_μ = M·(Q − lo_1) − lo_1.

Both are positive. For a cell c and 0 ≤ i ≤ n_c put

    num_c(i) = [i < n_c]·Rup[i]·C_λ + [i ≥ 1]·Rup[i−1]·C_μ,

where [·] is 1 if the condition holds and 0 otherwise. A term whose bracket is 0 is left out, so that
Rup[−1] does not occur.

*Bounded cells* (0 ≤ c ≤ m − 2).

    W_c(i) = ceil( ceil(num_c(i) / 2^14) / (Q − Rup[n_c]) ),      0 ≤ i ≤ n_c.

*The last cell* (c = m − 1).

    W_{m−1}(i) = ceil(num_{m−1}(i) / 2^76) + [i = N_T]·ceil(Rup[N_T] / 2^14),      0 ≤ i ≤ N_T.

*Cell masses.*

    P_c = ceil( (Rup[b_c] − Rlo[b_{c+1}]) / 2^14 )   for 0 ≤ c ≤ m − 2,
    P_{m−1} = ceil( Rup[b_{m−1}] / 2^14 ).

*Tail term.*

    E_T = ceil( Rup[N_T] / 2^30 ).

W_c(i)/D bounds the weight that the discretised gap of cell c puts on the mesh point b_c + i, P_c/D bounds
the probability of cell c, and E_T/F bounds e^{−T}.

## 4. Keys and their weight vectors

A *key* is a vector κ = (κ_0, …, κ_{m−1}) of non-negative integers with 1 ≤ κ_0 + … + κ_{m−1} ≤ k. It
records how many gaps of each cell lie between the two ends of a segment. There are C(m + k, k) − 1 keys.
They are ordered lexicographically as vectors: κ comes before κ′ if κ_c < κ′_c at the first index c where
they differ.

    b_κ = Σ_c κ_c·b_c,      len_κ = 1 + Σ_c κ_c·n_c.

The weight vector V_κ(s), 0 ≤ s < len_κ, is defined by recursion; the key κ′ below comes before κ in key
order, so the vectors can be computed in that order. If κ has a single gap, in cell c, then
V_κ = W_c. Otherwise let c be the largest index with κ_c > 0, let κ′ be κ with κ_c reduced by one, and put

    V_κ(s) = ceil( ( Σ V_κ′(i)·W_c(j) ) / D ),      0 ≤ s < len_κ,

where the sum is over all pairs (i, j) with i + j = s, 0 ≤ i < len_κ′ and 0 ≤ j ≤ n_c.

## 5. Height differences and distances

Let η_i = 1 for i = 0 and i = ν, and η_i = 2 for 0 < i < ν. For −ν ≤ t ≤ ν put

    χ(t) = Σ_{0 ≤ i, j ≤ ν, i − j = t} η_i·η_j,

so that Σ_t χ(t) = 4ν².

Let α = h_2²·n·ν and γ = M·h_1². For integers j ≥ 0 and τ ≥ 0 put

    Dist(j, τ) = ceil( ceil_sqrt( ((α·j)² + (γ·τ)²)·F² ) / (α·M) ).

Dist(j, τ)/F bounds the distance between two points whose horizontal distance is j/M and whose vertical
distance is τ·h²/(n·ν). (The factor is h², not h: a block is a piece of a strip of height h magnified by h,
so its heights range over an interval of length h²; see Section 2.2 of the paper.) For
0 ≤ j ≤ J = k·(b_{m−1} + N_T) and 0 ≤ d ≤ n − 1 put

    G(j, d) = ceil( ( Σ_{t=−ν}^{ν} χ(t)·Dist(j, |d·ν + t|) ) / (4ν²) ).

## 6. The table

For every key κ and every 0 ≤ d ≤ n − 1,

    Tab(κ, d) = ceil( ( Σ_{s=0}^{len_κ − 1} V_κ(s)·G(b_κ + s, d) ) / D ) + κ_{m−1}·E_T.

## 7. Cell sums

A *gap tuple* is g = (g_1, …, g_k) with 0 ≤ g_i ≤ m − 1, and a *height tuple* is a = (a_0, …, a_k) with
0 ≤ a_i ≤ n − 1. A *cell* is a pair (g, a). For 0 ≤ i < j ≤ k let κ(i, j) be the key κ in which κ_c is the
number of indices l with i < l ≤ j and g_l = c (the paper writes κ_{ij}), and put

    E_{ij} = E_{ji} = Tab(κ(i, j), |a_i − a_j|).

An *order* is a permutation π of {1, …, k − 1}. Its cost in the cell (g, a) is

    E_{0,π(1)} + E_{π(1),π(2)} + … + E_{π(k−2),π(k−1)} + E_{π(k−1),k},

and cost(g, a) is the least cost of an order in the cell (g, a). The *cell sum* of the gap tuple g is

    S_g = Σ_a cost(g, a)      (the sum over all n^{k+1} height tuples).

For k = 2 there is one order and cost(g, a) = E_{01} + E_{12}. Gap tuples are indexed by
g_1 + g_2·m + … + g_k·m^{k−1}.

Three identities follow from these definitions. A program may use them to shorten the computation; they
do not change any number.

*Reversal.* Let g′ = (g_k, …, g_1) and a′ = (a_k, …, a_0). The cell (g′, a′) is the cell (g, a) read from
its other end: its points i and j are the points k − i and k − j of (g, a), and the segment between them
has the same key and the same two heights. So an order has in (g′, a′) the cost that the reversed order
has in (g, a), and cost(g′, a′) = cost(g, a). Since a ↦ a′ is a bijection of the height tuples,
S_{g′} = S_g. (The list of cell sums is therefore the same if the index is taken as
g_k + g_{k−1}·m + … + g_1·m^{k−1}.)

*Reflection.* Replacing every a_i by n − 1 − a_i changes no difference |a_i − a_j|, hence no E_{ij} and
no cost. So for each position i and each y, the height tuples with a_i = y and those with
a_i = n − 1 − y contribute the same amount to S_g. This is a statement about one position: a program may
leave out the values y > n − 1 − y of one a_i and count the tuples with y < n − 1 − y twice, but it may
not do so for two positions at once.

*Shared paths.* E_{ij} depends on g only through g_{i+1}, …, g_j, and on a only through a_i and a_j. Let
k ≥ 3. The path of an order π leaves point 0 for the interior point u = π(1), goes from u through all
the interior points to v = π(k−1), which is different from u, and ends with the segment from v to point k.
Let H(u, v) be the least cost of a path from u to v through all the interior points. Then

    cost(g, a) = min over interior points u ≠ v of E_{0u} + H(u, v) + E_{vk}.

H(u, v) depends only on g_2, …, g_{k−1} and a_1, …, a_{k−1}: it is shared by the m² choices of g_1 and g_k
and by the n² choices of a_0 and a_k. (For k = 2 there is one interior point and nothing to share.)

## 8. The total and the test

Put A_k(g) = S_g, and for j = k, k − 1, …, 1

    A_{j−1}(g_1, …, g_{j−1}) = ceil( ( Σ_{c=0}^{m−1} P_c·A_j(g_1, …, g_{j−1}, c) ) / D ).

The *total* is A_0, the value at the empty tuple. The bound is

    B = A_0·h_2 / (n^{k+1}·F·k·h_1),

and a checker accepts when

    A_0·h_2·θ_2 ≤ θ_1·n^{k+1}·F·k·h_1,

that is when B ≤ θ, equality included. (The thresholds in `data/specs/` are not attained: for `k9.txt`,
B = 0.86171… < 0.8618.)

## 9. Sizes

For the spec files in `data/specs/` other than `rounding.txt`: Rup and Rlo are at most 2^62, and the
products in Section 2 are below 2^124; C_λ, C_μ < 2^57; num_c(i) < 2^120; W_c(i) and V_κ(s) are below 2^45;
P_c ≤ 2^48, with equality when there is one gap cell; a sum in Section 4 is below 2^93;
(α·j)² + (γ·τ)² < 2^59, so the argument of ceil_sqrt is below 2^123; Dist < 2^40; a sum in Section 5 is
below 2^56; a sum in Section 6 is below 2^85; Tab < 2^37 and k·max(Tab) < 2^40, so that cost < 2^40; a sum
in Section 8 is below 2^111; and both sides of the final test are below 2^78. So every intermediate value
is below 2^124 there. For `rounding.txt`, where T = 1 puts the mass e^{−1} at the truncation point, W_c(i)
and V_κ(s) are below 2^47 and a sum in Section 4 is below 2^94; the other statements hold for it as well.

The number k·max(Tab)·n^{k+1} bounds S_g and every partial sum of it. It is below 2^60 for the spec files
up to `k7.txt`, about 2^62.7 for `k8.txt` and about 2^65.6 for `k9.txt`, so it is below 2^66 for every
spec file. The cell sums themselves are smaller: the largest is about 2^59.9 for `k8.txt` and about
2^62.7 for `k9.txt`. So for `k9.txt` every cell sum is below 2^63 and fits a 64-bit integer, but no bound
that is known before the computation says so, and a program that adds the costs with 64-bit integers
must test the additions.

For other allowed parameters the values can be larger, and they can exceed 2^128 for parameters close
to those in use: the argument of ceil_sqrt grows like the fourth power of h_2, and with the other
parameters of `k9.txt` it reaches 2^128 when the denominator h_2 of the strip height is 24 or more. A
program with integers of fixed width must therefore check every operation for overflow, or check a bound
that excludes it, and stop with status 2 if the check fails. A threshold written with large θ_1 and θ_2
can have the same effect, through the two sides of the final test.

The next three paragraphs, and the limits on size in the paragraph after them, describe the three
checkers of this repository; they bind no other program.

The Python checker computes with unbounded integers except in two places. In Section 4 it obtains all
sums of a convolution from one product of packed integers, after checking a bound that keeps each sum
below 2^128. In Section 7 it uses 64-bit integers for the costs of paths and for sums of at most n^{k−2}
of them (over the heights of interior points), after checking that k·max(Tab)·n^{k−1} < 2^63; for
`k9.txt` this number is about 2^60.4. It adds these sums up to S_g with unbounded integers.

The C checker keeps every integer of the recipe in 64 bits and every sum that is formed before a division
in 128 bits. It tests each operation that the ranges of Section 1 do not keep within these widths, with
three exceptions, in which it checks a bound first. In Section 4 it adds the products of a convolution in
two 64-bit words, after checking a bound that keeps every sum below 2^128. In Section 5 it adds the
products χ(t)·Dist in 64 bits, after checking that Dist ≤ floor((2^64 − 1) / (4·ν²)). In Section 7 it
checks that max(Tab) < floor(2^63 / k), so that the cost of a path is below 2^63, and that
2·k·max(Tab)·n² < 2^64, which covers the sum of the costs over the heights of the two end points and its
double; and it tests every addition of such a sum to a cell sum.

The Rust checker keeps W, V, G and Tab in 64 bits, after checking that each value fits, and computes
with 128-bit integers elsewhere in Sections 2 to 6 and in Section 8. In Section 7 it uses 64-bit integers
for the costs of paths and for their sum over the heights of one end point, after checking that
n·k·max(Tab) < 2^64, and 128-bit integers for all larger sums.

A program may also stop with status 2 because the parameters need more memory or time than it provides.
The Python and C checkers stop when the last boundary b_{m−1} exceeds 2^20. The Rust checker stops when a
boundary, N_T, J or the number of gap tuples exceeds 2^27, or when the table of G or the weight vectors
would have more than 2^27 entries.

**When the checkers must agree.** A checker may therefore stop with status 2 where another does not, for
one of two reasons: a check of its arithmetic fails (an overflow, or a bound that would exclude one), or
one of its limits on size is exceeded. Where a stored number differs as well, the status is 1 or 2
according to which the checker meets first. The checkers are required to agree whenever none of them stops
for one of these two reasons; this is the case for every file in `data/specs/` and `data/tests/`. A
checker to which the operating system refuses memory may also be stopped by the system with a status of
its own (this happens with the Rust checker); it then prints nothing on the standard output.

## 10. Files, output and exit status

**Text.** Spec files and values files are text files in ASCII, read as sequences of bytes.

- A line ends with a line feed (byte 10). The last line may lack its line feed.
- A carriage return (byte 13) may occur only directly before a line feed, and is then ignored.
- Apart from these line ends, the only bytes allowed are the tab (byte 9) and the bytes 32 to 126.
- A line consists of *fields* separated by blanks (spaces and tabs, in any number); blanks at the ends of
  a line are ignored. Every line has at least one field, so there are no empty lines, and a file without
  lines is not allowed.
- Names such as `mesh` are fields that must be written exactly as shown, in lower case.
- A *number* is a field that consists of decimal digits and has a value below 2^128. It has no sign.
  Leading zeros are allowed, in any number.

A file that breaks one of these rules is malformed.

**Spec file.** Nine lines, in this order:

    k 9
    h 11 5
    mesh 128
    gaps 48 112 208
    heights 6
    height_mesh 64
    tail 16
    threshold 8618 10000
    values ../values/k9.txt

Each of the first eight lines is a name followed by numbers: one number, except two for `h` (h_1, h_2) and
`threshold` (θ_1, θ_2), and m − 1 numbers for `gaps` (none if m = 1). The last line is the name `values`
followed by one field, the path of the values file. The path is relative to the folder of the spec file,
with `/` between its parts. It must not begin with `/` and must not contain `\` or `:`. The folder is
that of the path by which the checker was given the spec file, as it stands: a checker appends the path
of the values file to it and does not rewrite it (a `..` after a symbolic link is for the operating
system to resolve).

**Values file.** The lines below, in this order. The first eight are shown with the parameters of
`k7.txt`; the others are shown schematically.

    tsp-block-values 1
    k 7
    h 21 10
    mesh 128
    gaps 48 112 208
    heights 6
    height_mesh 64
    tail 16
    masses P_0 … P_{m−1}
    tail_term E_T
    table <number of keys>
    κ_0 … κ_{m−1} Tab(κ, 0) … Tab(κ, n−1)        (one line for each key, in key order)
    sums <m^k>
    S_g                                           (one line for each gap tuple, in index order)
    total A_0

The first line consists of the two fields `tsp-block-values` and `1`, written exactly so: the `1` is not
read as a number, and `01` is malformed.

**What a checker does.** It is called as `CHECKER SPEC` or `CHECKER SPEC -j N`, with the arguments in
this order, and may have further options of its own after these. SPEC is the path of a spec file,
even if it begins with a hyphen. N is the number of threads or processes (1 if `-j` is absent); it is
written with decimal digits only and is at least 1, it does not affect the output, and a checker may
use fewer than N. These rules are for arguments in ASCII: an operating system may change other
characters before a program sees them (Windows does so for the C checker), and a checker is not
required to notice.

A checker recomputes everything from the parameters in the spec file. (An option of its own may say
otherwise: with `--log FILE` the Python checker takes the cell sums that an interrupted run has left in
FILE as they stand.) It takes the steps below in this order, and the first that fails decides the exit
status.

1. The command line has the form above, and the spec file can be read, has the form above and has its
   parameters in the allowed ranges of Section 1; otherwise status 2.
2. The values file can be read and has the form above: the first line; seven parameter lines with their
   names and with the right number of numbers (any number of them for `gaps`); a line `masses` followed by
   any number of numbers; a line `tail_term` with one number; a line `table` with one number, followed by
   that many lines of numbers; a line `sums` with one number, followed by that many lines of one number
   each; a line `total` with one number; and nothing after it. Otherwise status 2. Only the form is
   checked in this step: the parameters of the values file need not be in the allowed ranges, and the
   numbers after `table` and `sums` may have any value, provided that the stated number of lines follows.
3. The seven parameter lines of the values file give the same numbers as those of the spec file,
   including the same number of boundaries; otherwise status 1.
4. The values file has m masses, C(m + k, k) − 1 table lines of m + n numbers each, and m^k cell sums;
   otherwise status 2.
5. Every number of the values file equals the recomputed one: the masses, the tail term, the table lines
   (the key and the n entries), the cell sums and the total; otherwise status 1.
6. The test of Section 8 holds; otherwise status 1.

Steps 1 to 4 need no arithmetic beyond reading numbers and the two computed counts of step 4,
C(m + k, k) − 1 and m^k, and a checker
completes them before it recomputes anything. A violated arithmetic bound (Section 9) gives status 2
whenever it occurs after that.

**Output.** A checker that accepts ends with status 0 and prints exactly these five lines on the standard
output:

    the stored values agree with the recomputed values
    total 1907697663974
    bound 0.913931018519 (rounded up)
    bound <= 95/100
    ACCEPTED

(the output for `data/specs/tiny.txt`). The bound is ceil(B·10^12)/10^12, printed with its integer part
and twelve decimals. The fourth line gives θ_1 and θ_2 in decimal without leading zeros. Under Windows a
program may end its lines with a carriage return and a line feed; the records in `runs/` have line feeds.

With status 1 the last line of the standard output begins with `REJECTED:` and says what failed; what is
printed before that line is not prescribed. With status 2 nothing is printed on the standard output.
Messages about progress, running times and the reason for status 2 go to the standard error stream.
