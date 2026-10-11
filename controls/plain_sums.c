/*
 plain_sums.c -- a control: recomputes some cell sums of a values file straight from their definition.

 The checkers shorten the cell sums S_g of Section 7 of RECIPE.md by the three identities stated there
 (Reversal, Reflection, Shared paths). This program uses none of them. For each gap tuple g of a sample it
 goes through all n^(k+1) height tuples a, one after another, finds cost(g, a) for each of them on its own,
 adds the costs, and compares the sum with the number stored for g in the values file. It shares no code
 with the checkers. It is a control and not a checker: it takes the table from the values file as it stands
 (the checkers recompute the table), and it looks at a sample of the gap tuples only.

 The sample. The first and the last gap tuple, a gap tuple with the least and one with the greatest stored
 sum, COUNT gap tuples drawn from SEED by the generator next_random below, and the reverse (g_k, ..., g_1) of
 each of these; a gap tuple that occurs twice is computed once. If COUNT is at least m^k, the sample is every
 gap tuple.

 The cost of a cell. With E_{ij} as in Section 7, cost(g, a) is the least cost of a path from point 0 to
 point k through all the interior points 1, ..., k - 1. It is found by the recursion of Bellman and of Held
 and Karp over the sets S of interior points, where f(S, j) is the least cost of a path that starts at
 point 0, visits the points of S and ends at the point j of S:
     f({j}, j) = E_{0j},     f(S, j) = min over i in S, i != j, of f(S - {j}, i) + E_{ij},
     cost(g, a) = min over j of f(all, j) + E_{jk}.
 For every STEP-th height tuple the cost is found a second time, by going through all (k - 1)! orders, and
 the program stops with status 2 if the two numbers differ.

 Arithmetic. Costs are held in a uint64_t; the program checks first that k max(Tab) < 2^63. A cell sum is
 held in two uint64_t, as an integer below 2^128, and n^(k+1) costs below 2^63 cannot exceed that.

 Limits. k is at most 9, m at most 8 and n at most 16. COUNT must be below 2^31, and SEED and every stored
 sum below 2^64 - 1; the program stops with status 2 otherwise.

 Usage:  plain_sums VALUES COUNT SEED [-j THREADS]        (one thread unless -j is given)
 Standard output: one line for the sample, one line for each of its gap tuples (index, gaps g_1 ... g_k,
 the sum found, the number of height tuples for which all orders were gone through, and "equal" or
 "DIFFERENT"), and a last line with the counts. Progress goes to the standard error stream.
 Exit status: 0 if every sum found equals the stored one, 1 if one differs, 2 for a bad command line, a
 values file that this program cannot use, a cost that the two methods find differently, lack of memory or
 a standard output that cannot be written.
 Build:  gcc -std=c11 -O2 -fopenmp plain_sums.c -o plain_sums        (gcc or clang)
         cl -O2 -openmp plain_sums.c                                  (MSVC)
         Without the OpenMP option the program runs on one thread.
*/
#ifdef _MSC_VER
#pragma warning(disable : 4996) /* the advice to replace fopen by fopen_s */
#endif
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define MAXK 9             /* gaps in a block */
#define MAXM 8             /* gap cells */
#define MAXN 16            /* height cells */
#define MAXP (MAXK - 1)    /* interior points of a block */
#define STEP 100003        /* every STEP-th height tuple is also evaluated from all orders */

static int k, m, n;            /* the parameters of the values file */
static long nkeys;             /* lines of the table */
static int *keys;              /* nkeys rows of m counts */
static uint64_t *tab;          /* nkeys rows of n entries */
static long ntuples;           /* m^k */
static char **stored;          /* the stored cell sums, as decimal digits without leading zeros */
static int lowest[1 << MAXP];  /* the position of the lowest binary digit 1 of s */

/* tells compilers and analysers that a function ends the program; nothing depends on it */
#ifdef _MSC_VER
#define NORETURN __declspec(noreturn)
#else
#define NORETURN _Noreturn
#endif

/* status 2. It may be called inside the parallel loop: only one thread at a time may end the program. */
static NORETURN void die(const char *format, ...) {
#ifdef _OPENMP
#pragma omp critical(ending)
#endif
    {
        va_list args;
        va_start(args, format);
        fprintf(stderr, "plain_sums: ");
        vfprintf(stderr, format, args);
        fprintf(stderr, "\n");
        va_end(args);
        exit(2);
    }
}

/* The value of a field of decimal digits, which must be below limit. */
static uint64_t number(const char *field, uint64_t limit) {
    uint64_t value = 0;
    if (*field == 0) die("a number is missing");
    for (const char *c = field; *c; c++) {
        uint64_t digit = (uint64_t)*c - '0';
        if (*c < '0' || *c > '9') die("'%s' is not a number", field);
        if (digit >= limit || value > (limit - 1 - digit) / 10)
            die("the number %s is too large for this program", field);
        value = value * 10 + digit;
    }
    return value;
}

/* Splits a line into its fields, in place, and returns their number (at most max). */
static int split(char *line, char **fields, int max) {
    int count = 0;
    char *c = line;
    for (;;) {
        while (*c == ' ' || *c == '\t' || *c == '\r') *c++ = 0;
        if (*c == 0) return count;
        if (count == max) die("a line of the values file has more than %d fields", max);
        fields[count++] = c;
        while (*c && *c != ' ' && *c != '\t' && *c != '\r') c++;
    }
}

/* The next line of the values file, split into fields; its first field must be name (if name is given). */
static int next_line(char **cursor, const char *name, char **fields, int max) {
    char *line = *cursor, *end;
    int count;
    if (line == NULL && name) die("the values file ends before the line '%s'", name);
    if (line == NULL) die("the values file ends before the last of its numbers");
    end = strchr(line, '\n');
    if (end) {
        *end = 0;
        *cursor = end[1] ? end + 1 : NULL;
    } else {
        *cursor = NULL;
    }
    count = split(line, fields, max);
    if (count == 0) die("the values file has an empty line");
    if (name && strcmp(fields[0], name) != 0)
        die("the values file has '%s' where '%s' should be", fields[0], name);
    return count;
}

static void read_values(const char *path) {
    FILE *file = fopen(path, "rb");
    char *text, *cursor, *fields[MAXM + MAXN + 2];
    long size;
    if (file == NULL) die("cannot open %s", path);
    if (fseek(file, 0, SEEK_END) != 0 || (size = ftell(file)) < 0 || fseek(file, 0, SEEK_SET) != 0)
        die("cannot read %s", path);
    text = malloc((size_t)size + 1);
    if (text == NULL || fread(text, 1, (size_t)size, file) != (size_t)size) die("cannot read %s", path);
    fclose(file);
    text[size] = 0;
    if (strlen(text) != (size_t)size) die("%s contains a byte 0", path);
    cursor = text;

    if (next_line(&cursor, "tsp-block-values", fields, 2) != 2 || strcmp(fields[1], "1") != 0)
        die("%s is not a values file", path);
    if (next_line(&cursor, "k", fields, 2) != 2) die("the line k is malformed");
    k = (int)number(fields[1], MAXK + 1);
    if (k < 2) die("k must be at least 2");
    next_line(&cursor, "h", fields, 3);
    next_line(&cursor, "mesh", fields, 2);
    m = next_line(&cursor, "gaps", fields, MAXM); /* the name and the m - 1 boundaries of the gap cells */
    if (next_line(&cursor, "heights", fields, 2) != 2) die("the line heights is malformed");
    n = (int)number(fields[1], MAXN + 1);
    if (n < 1) die("there must be at least one height cell");
    next_line(&cursor, "height_mesh", fields, 2);
    next_line(&cursor, "tail", fields, 2);
    next_line(&cursor, "masses", fields, MAXM + 1);
    next_line(&cursor, "tail_term", fields, 2);

    if (next_line(&cursor, "table", fields, 2) != 2) die("the line table is malformed");
    nkeys = (long)number(fields[1], 1000000);
    keys = malloc((size_t)nkeys * (size_t)m * sizeof *keys);
    tab = malloc((size_t)nkeys * (size_t)n * sizeof *tab);
    if (keys == NULL || tab == NULL) die("not enough memory");
    for (long row = 0; row < nkeys; row++) {
        if (next_line(&cursor, NULL, fields, MAXM + MAXN) != m + n)
            die("line %ld of the table has not %d numbers", row + 1, m + n);
        for (int c = 0; c < m; c++) keys[row * m + c] = (int)number(fields[c], MAXK + 1);
        /* entries below 2^63 / k, so that the cost of a path, a sum of k entries, is below 2^63 */
        for (int d = 0; d < n; d++)
            tab[row * n + d] = number(fields[m + d], (UINT64_C(1) << 63) / (uint64_t)k);
    }

    ntuples = 1;
    for (int i = 0; i < k; i++) ntuples *= m;
    if (next_line(&cursor, "sums", fields, 2) != 2) die("the line sums is malformed");
    if ((long)number(fields[1], (UINT64_C(1) << 31)) != ntuples)
        die("the values file has not m^k = %ld cell sums", ntuples);
    stored = malloc((size_t)ntuples * sizeof *stored);
    if (stored == NULL) die("not enough memory");
    for (long index = 0; index < ntuples; index++) {
        if (next_line(&cursor, NULL, fields, 1) != 1) die("a line of cell sums is malformed");
        number(fields[0], UINT64_MAX); /* digits only, and below 2^64 - 1 */
        while (fields[0][0] == '0' && fields[0][1]) fields[0]++;
        stored[index] = fields[0];
    }
    next_line(&cursor, "total", fields, 2);
    if (cursor != NULL) die("the values file has lines after the total");
}

/* Compares two numbers written in decimal digits without leading zeros. */
static int compare_decimal(const char *a, const char *b) {
    size_t la = strlen(a), lb = strlen(b);
    if (la != lb) return la < lb ? -1 : 1;
    return strcmp(a, b);
}

/* Writes hi 2^64 + lo in decimal digits. */
static void to_decimal(uint64_t hi, uint64_t lo, char *out) {
    uint32_t limb[4] = {(uint32_t)(hi >> 32), (uint32_t)hi, (uint32_t)(lo >> 32), (uint32_t)lo};
    char digits[40];
    int count = 0;
    do {
        uint64_t rest = 0;
        for (int i = 0; i < 4; i++) {
            uint64_t value = (rest << 32) | limb[i];
            limb[i] = (uint32_t)(value / 10);
            rest = value % 10;
        }
        digits[count++] = (char)('0' + rest);
    } while (limb[0] | limb[1] | limb[2] | limb[3]);
    while (count) *out++ = digits[--count];
    *out = 0;
}

/* The generator SplitMix64 of Steele, Lea and Flood. */
static uint64_t next_random(uint64_t *state) {
    uint64_t z = (*state += UINT64_C(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}

/* The gaps g_1, ..., g_k of the gap tuple with a given index, as g[1], ..., g[k]. */
static void gaps_of(long index, int *g) {
    for (int i = 1; i <= k; i++) {
        g[i] = (int)(index % m);
        index /= m;
    }
}

static long reverse_of(long index) {
    int g[MAXK + 1];
    long reversed = 0;
    gaps_of(index, g);
    for (int i = 1; i <= k; i++) reversed = reversed * m + g[i];
    return reversed;
}

/* The row of the table for the key kappa(i, j), which counts the entries of (g_{i+1}, ..., g_j) by cell. */
static const uint64_t *row_of(const int *g, int i, int j) {
    int counts[MAXM] = {0};
    for (int t = i + 1; t <= j; t++) counts[g[t]]++;
    for (long row = 0; row < nkeys; row++)
        if (memcmp(keys + row * m, counts, (size_t)m * sizeof *keys) == 0) return tab + row * n;
    die("a key is missing in the table");
}

/* cost(g, a) by the recursion over sets of interior points; e[i][j] = e[j][i] = E_{ij}. */
static uint64_t cost_by_sets(uint64_t e[MAXK + 1][MAXK + 1], uint64_t f[1 << MAXP][MAXP]) {
    int p = k - 1, all = (1 << p) - 1;
    uint64_t best = UINT64_MAX;
    for (int s = 1; s <= all; s++) {
        if ((s & (s - 1)) == 0) { /* S has one point */
            f[s][lowest[s]] = e[0][lowest[s] + 1];
            continue;
        }
        for (int sj = s; sj; sj &= sj - 1) {
            int j = lowest[sj], rest = s ^ (1 << j);
            uint64_t least = UINT64_MAX;
            for (int si = rest; si; si &= si - 1) {
                int i = lowest[si];
                uint64_t value = f[rest][i] + e[i + 1][j + 1];
                least = value < least ? value : least;
            }
            f[s][j] = least;
        }
    }
    for (int j = 0; j < p; j++) {
        uint64_t value = f[all][j] + e[j + 1][k];
        best = value < best ? value : best;
    }
    return best;
}

/* The least cost of a path that has cost so_far, stands at the interior point last and has still to visit
   the interior points of the set left before it goes to point k. */
static uint64_t cost_by_orders(uint64_t e[MAXK + 1][MAXK + 1], int left, int last, uint64_t so_far) {
    uint64_t best = UINT64_MAX;
    if (left == 0) return so_far + e[last][k];
    for (int next = 1; next < k; next++) {
        if (left >> (next - 1) & 1) {
            uint64_t value = cost_by_orders(e, left ^ (1 << (next - 1)), next, so_far + e[last][next]);
            best = value < best ? value : best;
        }
    }
    return best;
}

/* S_g for the gap tuple with the given index, as hi 2^64 + lo; *orders counts the height tuples for which
   the cost was also found from all orders. */
static void cell_sum(long index, uint64_t *hi, uint64_t *lo, long *orders) {
    int g[MAXK + 1], a[MAXK + 1] = {0};
    const uint64_t *row[MAXK + 1][MAXK + 1];
    uint64_t e[MAXK + 1][MAXK + 1];
    uint64_t (*f)[MAXP] = malloc((size_t)(1 << MAXP) * sizeof *f);
    uint64_t count = 0;
    if (f == NULL) die("not enough memory");
    gaps_of(index, g);
    for (int i = 0; i < k; i++)
        for (int j = i + 1; j <= k; j++) row[i][j] = row_of(g, i, j);
    *hi = *lo = 0;
    *orders = 0;
    for (;;) {
        uint64_t cost;
        int position;
        for (int i = 0; i < k; i++)
            for (int j = i + 1; j <= k; j++)
                e[i][j] = e[j][i] = row[i][j][a[i] < a[j] ? a[j] - a[i] : a[i] - a[j]];
        cost = cost_by_sets(e, f);
        if (count % STEP == 0) {
            int interior = (1 << (k - 1)) - 1;
            uint64_t second = UINT64_MAX;
            for (int first = 1; first < k; first++) {
                uint64_t value = cost_by_orders(e, interior ^ (1 << (first - 1)), first, e[0][first]);
                if (value < second) second = value;
            }
            if (second != cost)
                die("gap tuple %ld: the recursion over sets and the orders give different costs", index);
            ++*orders;
        }
        count++;
        *lo += cost;
        if (*lo < cost) ++*hi;
        /* the next height tuple: a_0 runs fastest */
        for (position = 0; position <= k && a[position] == n - 1; position++) a[position] = 0;
        if (position > k) break;
        a[position]++;
    }
    free(f);
}

static int compare_long(const void *a, const void *b) {
    long x = *(const long *)a, y = *(const long *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    long *sample, size = 0, count, least = 0, greatest = 0, differing = 0;
    uint64_t seed, state, cells = 1;
    int threads = 1;
    char (*found)[40];
    long *orders;

    if (argc != 4 && !(argc == 6 && strcmp(argv[4], "-j") == 0))
        die("usage: plain_sums VALUES COUNT SEED [-j THREADS]");
    count = (long)number(argv[2], UINT64_C(1) << 31);
    seed = number(argv[3], UINT64_MAX);
    if (argc == 6) threads = (int)number(argv[5], 1025);
    if (threads < 1) die("the number of threads must be at least 1");
    read_values(argv[1]);
    for (int s = 1; s < 1 << MAXP; s++)
        for (int bit = MAXP - 1; bit >= 0; bit--)
            if (s >> bit & 1) lowest[s] = bit;
    for (int i = 0; i <= k; i++) cells *= (uint64_t)n;

    /* the sample: sorted, without repetitions */
    sample = malloc((size_t)(count < ntuples ? 2 * count + 8 : ntuples) * sizeof *sample);
    if (sample == NULL) die("not enough memory");
    if (count >= ntuples) {
        for (long index = 0; index < ntuples; index++) sample[size++] = index;
    } else {
        long unique = 0;
        for (long index = 1; index < ntuples; index++) {
            if (compare_decimal(stored[index], stored[least]) < 0) least = index;
            if (compare_decimal(stored[index], stored[greatest]) > 0) greatest = index;
        }
        sample[size++] = 0;
        sample[size++] = ntuples - 1;
        sample[size++] = least;
        sample[size++] = greatest;
        state = seed;
        for (long i = 0; i < count; i++) sample[size++] = (long)(next_random(&state) % (uint64_t)ntuples);
        for (long i = 0, direct = size; i < direct; i++) sample[size++] = reverse_of(sample[i]);
        qsort(sample, (size_t)size, sizeof *sample, compare_long);
        for (long i = 0; i < size; i++)
            if (unique == 0 || sample[i] != sample[unique - 1]) sample[unique++] = sample[i];
        size = unique;
    }
    found = malloc((size_t)size * sizeof *found);
    orders = malloc((size_t)size * sizeof *orders);
    if (found == NULL || orders == NULL) die("not enough memory");

#ifndef _OPENMP
    if (threads > 1) fprintf(stderr, "plain_sums: built without OpenMP, running on one thread\n");
#endif
    {
        long done = 0;
        long i;
#ifdef _OPENMP
#pragma omp parallel for num_threads(threads) schedule(dynamic, 1)
#endif
        for (i = 0; i < size; i++) {
            uint64_t hi, lo;
            cell_sum(sample[i], &hi, &lo, &orders[i]);
            to_decimal(hi, lo, found[i]);
#ifdef _OPENMP
#pragma omp critical
#endif
            if (++done == size || cells >= 1000000)
                fprintf(stderr, "plain_sums: %ld of %ld cell sums\n", done, size);
        }
    }

    printf("plain cell sums for %s: k %d, %d gap cells, %d height cells, ", argv[1], k, m, n);
    if (count >= ntuples)
        printf("every gap tuple\n");
    else
        printf("%ld gap tuples drawn from seed %s\n", count, argv[3]);
    for (long i = 0; i < size; i++) {
        int g[MAXK + 1], equal = strcmp(found[i], stored[sample[i]]) == 0;
        gaps_of(sample[i], g);
        printf("index %ld gaps", sample[i]);
        for (int t = 1; t <= k; t++) printf(" %d", g[t]);
        printf(" sum %s orders %ld %s\n", found[i], orders[i], equal ? "equal" : "DIFFERENT");
        if (!equal) differing++;
    }
    {
        char text[40];
        to_decimal(0, cells, text);
        printf("%ld cell sums of %s cells each: %ld equal to the stored sums, %ld different\n", size, text,
               size - differing, differing);
    }
    /* a record that cannot be written is no record */
    if (fflush(stdout) != 0 || ferror(stdout)) die("the standard output cannot be written");
    free(sample);
    free(found);
    free(orders);
    return differing ? 1 : 0;
}
