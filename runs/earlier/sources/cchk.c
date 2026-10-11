/*
 cchk.c -- checks the stored values for an upper bound on the travelling salesman constant of Beardwood,
 Halton and Hammersley, in exact integer arithmetic.

 RECIPE.md defines a number A_0, the total, by integer arithmetic alone, and the paper proves that
     B = A_0 h_2 / (n^(k+1) F k h_1)
 is an upper bound for the constant. This program reads a spec file with the parameters and a threshold,
 recomputes every quantity of the recipe (Sections 2 to 8), and compares the results with the values file
 named in the spec file: the parameters, the cell masses, the tail term, every line of the table, every cell
 sum S_g and the total. It accepts if all of them agree and B is at most the threshold (the test of
 Section 8). Section numbers in the comments below are those of RECIPE.md, and the steps are the six steps
 of its Section 10, which are taken in that order.

 Arithmetic. Every quantity is a non-negative integer below 2^128, held in a uint64_t or in a pair of them.
 The 128-bit operations are written in plain C and are the same for every compiler. Each operation that could
 overflow is checked where it is carried out, except in three inner loops, where a bound that covers the
 whole loop is checked before it starts: the sums of products in Section 4, the sums over t in Section 5, and
 the additions in Section 7 (there the bounds are k max(Tab) < 2^63 and k max(Tab) n^(k+1) < 2^64). A failed
 check stops the program with status 2, so that no result rests on a wrapped value.

 Cell sums. Almost all the time goes into the sums S_g of Section 7. For a gap tuple g and fixed heights of
 the k - 1 interior points, let H(u, v) be the cost of the cheapest path that starts at the interior point u,
 ends at the interior point v and visits every interior point. Then
     cost(g, a) = min over u and v of E_{0u} + H(u, v) + E_{vk},
 so that H is shared by the n^2 height tuples that differ only in a_0 and a_k. H is found by a dynamic
 programme over sets of interior points (see sum_over_ends). The gap tuples are independent of each other
 and are divided among the threads; the results do not depend on the number of threads.

 Usage:  cchk SPEC [-j THREADS]                 (one thread unless -j is given)
 Standard output, if the values are accepted:
     the stored values agree with the recomputed values
     total <A_0>
     bound <B to 12 decimals> (rounded up)
     bound <= <theta_1>/<theta_2>
     ACCEPTED
 If they are rejected it is one line, "REJECTED: reason", and with status 2 it is empty. The reason for
 status 2, the progress and the running times are reported on the standard error stream.
 Exit status: 0 if the values are accepted;
              1 if a parameter line of the values file differs from the spec file, a number of the values
                file differs from the recomputed one, or the test fails;
              2 for a bad command line, an unreadable or malformed file, parameters outside the allowed
                ranges, wrong counts in the values file, a violated arithmetic bound, or parameters that
                need more memory than there is (the last boundary may be at most 2^20).
 Build:  gcc -std=c11 -O2 -fopenmp cchk.c -o cchk          (gcc or clang)
         cl -O2 -openmp cchk.c                              (MSVC)
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
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef uint64_t u64;

/* the ranges of the parameters (Section 1) */
#define MAXK 8       /* gaps in a block */
#define MAXM 8       /* gap cells */
#define MAXN 16      /* height cells */
#define MAXMESH 1024 /* the horizontal mesh M */
#define MAXNU 256    /* the vertical mesh nu */
#define MAXTAIL 40   /* the truncation T */

/* the limits of this program */
#define MAXB ((u64)1 << 20)      /* the last boundary b_{m-1}: the tables grow with it */
#define MAXP (MAXK - 1)          /* interior points of a block */
#define MAXSUB (1 << (MAXP - 1)) /* sets of interior points other than the last one */
#define MAXTHREADS 256

/* the fixed scales Q = 2^62, D = 2^48 and F = 2^32 of Section 1, by their exponents */
#define LOG_Q 62
#define LOG_D 48
#define LOG_F 32
#define Q ((u64)1 << LOG_Q)

/* tells compilers and analysers that a function ends the program; nothing depends on it */
#ifdef _MSC_VER
#define NORETURN __declspec(noreturn)
#else
#define NORETURN _Noreturn
#endif

/* status 2: a bad command line, a malformed file, a violated arithmetic bound; nothing goes to the standard
   output */
static NORETURN void die(const char *format, ...) {
    va_list args;
    va_start(args, format);
    fprintf(stderr, "cchk: ");
    vfprintf(stderr, format, args);
    fprintf(stderr, "\n");
    va_end(args);
    exit(2);
}

/* status 1: a number that differs from the spec file or from the recomputed one, or a failed test */
static NORETURN void reject(const char *format, ...) {
    va_list args;
    va_start(args, format);
    printf("REJECTED: ");
    vprintf(format, args);
    printf("\n");
    va_end(args);
    exit(1);
}

/* room for count >= 1 objects of the given size */
static void *alloc(u64 count, size_t size) {
    void *p;
    if (count == 0) die("internal error: nothing to allocate");
    if (count > SIZE_MAX / size) die("out of memory");
    p = malloc((size_t)count * size);
    if (!p) die("out of memory");
    return p;
}

/* wall-clock time in seconds, for the progress messages only */
static double seconds(void) {
    struct timespec t;
    if (timespec_get(&t, TIME_UTC) != TIME_UTC) return 0.0;
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

/* Checked arithmetic in 64 bits. */

static u64 add_u64(u64 a, u64 b) {
    if (a > UINT64_MAX - b) die("arithmetic bound violated: a sum exceeds 64 bits");
    return a + b;
}

static u64 mul_u64(u64 a, u64 b) {
    if (b != 0 && a > UINT64_MAX / b) die("arithmetic bound violated: a product exceeds 64 bits");
    return a * b;
}

static u64 ceil_div64(u64 a, u64 b) {
    return a / b + (a % b != 0);
}

/* ceil(a / 2^s) for 0 < s < 64 */
static u64 ceil_shr64(u64 a, int s) {
    return (a >> s) + ((a & (((u64)1 << s) - 1)) != 0);
}

/* Unsigned 128-bit integers. */

typedef struct {
    u64 lo, hi;
} u128;

static inline u128 make128(u64 hi, u64 lo) {
    u128 r;
    r.lo = lo;
    r.hi = hi;
    return r;
}

static inline int lt128(u128 a, u128 b) {
    return a.hi < b.hi || (a.hi == b.hi && a.lo < b.lo);
}

/* the exact product of two 64-bit numbers, from their 32-bit halves */
static inline u128 mul64(u64 a, u64 b) {
    u64 a0 = a & 0xffffffffu, a1 = a >> 32, b0 = b & 0xffffffffu, b1 = b >> 32;
    u64 p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
    u64 middle = (p00 >> 32) + (p01 & 0xffffffffu) + (p10 & 0xffffffffu); /* below 3 * 2^32 */
    return make128(p11 + (p01 >> 32) + (p10 >> 32) + (middle >> 32), (p00 & 0xffffffffu) | (middle << 32));
}

static inline u128 add128(u128 a, u128 b) {
    u64 lo = a.lo + b.lo, carry = lo < a.lo, hi = a.hi + b.hi;
    if (hi < a.hi || hi + carry < hi) die("arithmetic bound violated: a sum exceeds 128 bits");
    return make128(hi + carry, lo);
}

static u128 mul128_u64(u128 a, u64 b) {
    u128 low = mul64(a.lo, b), high = mul64(a.hi, b);
    if (high.hi != 0) die("arithmetic bound violated: a product exceeds 128 bits");
    return add128(low, make128(high.lo, 0));
}

/* a * 2^s for 0 <= s < 128; the caller makes sure that no bit is lost */
static u128 shl128(u128 a, int s) {
    if (s == 0) return a;
    if (s >= 64) return make128(a.lo << (s - 64), 0);
    return make128((a.hi << s) | (a.lo >> (64 - s)), a.lo << s);
}

/* floor(a / 2^s) for 0 <= s < 128 */
static u128 shr128(u128 a, int s) {
    if (s == 0) return a;
    if (s >= 64) return make128(0, a.hi >> (s - 64));
    return make128(a.hi >> s, (a.lo >> s) | (a.hi << (64 - s)));
}

/* ceil(a / 2^s) for 0 < s < 128; the quotient is below 2^127, so adding 1 cannot overflow */
static u128 ceil_shr128(u128 a, int s) {
    u128 q = shr128(a, s), back = shl128(q, s);
    if (back.lo != a.lo || back.hi != a.hi) {
        q.lo++;
        if (q.lo == 0) q.hi++;
    }
    return q;
}

static u64 low64(u128 a) {
    if (a.hi != 0) die("arithmetic bound violated: a value exceeds 64 bits");
    return a.lo;
}

/* the quotient of a by b > 0, bit by bit from the top; *remainder gets a - quotient * b */
static u128 div128(u128 a, u128 b, u128 *remainder) {
    u128 q = make128(0, 0), r = make128(0, 0);
    if (b.hi == 0 && b.lo == 0) die("arithmetic bound violated: division by zero");
    for (int i = 127; i >= 0; i--) {
        u64 bit = i >= 64 ? (a.hi >> (i - 64)) & 1 : (a.lo >> i) & 1;
        u64 top = r.hi >> 63; /* the bit that the shift moves out; then 2r + bit >= 2^128 > b */
        r = make128((r.hi << 1) | (r.lo >> 63), (r.lo << 1) | bit);
        if (top || !lt128(r, b)) {
            r = make128(r.hi - b.hi - (r.lo < b.lo), r.lo - b.lo);
            if (i >= 64)
                q.hi |= (u64)1 << (i - 64);
            else
                q.lo |= (u64)1 << i;
        }
    }
    *remainder = r;
    return q;
}

/* ceil(a / b) for b > 0, which has to fit 64 bits */
static u64 ceil_div128_u64(u128 a, u64 b) {
    u128 r, q = div128(a, make128(0, b), &r);
    return add_u64(low64(q), r.lo != 0);
}

static int bit_length64(u64 x) {
    int bits = 0;
    for (int s = 32; s >= 1; s /= 2) {
        if (x >> s) {
            x >>= s;
            bits += s;
        }
    }
    return bits + (x != 0);
}

/* floor(sqrt(x)), one binary digit at a time */
static u64 floor_sqrt64(u64 x) {
    u64 root = 0, bit = (u64)1 << 62;
    while (bit > x) bit >>= 2;
    while (bit != 0) {
        if (x >= root + bit) {
            x -= root + bit;
            root = (root >> 1) + bit;
        } else {
            root >>= 1;
        }
        bit >>= 2;
    }
    return root;
}

/*
 ceil_sqrt(a): the least u with u^2 >= a, which has to fit 64 bits. An estimate is made from the leading
 64 bits of a and is then corrected by exact comparisons. The two correction loops enforce the definition, so
 the result is right whatever the estimate; a good estimate only keeps the loops short.
*/
static u64 ceil_sqrt128(u128 a) {
    int bits = a.hi != 0 ? 64 + bit_length64(a.hi) : bit_length64(a.lo);
    int shift = (128 - bits) & ~1; /* even, with 2^126 <= a 2^shift < 2^128 */
    u64 top, s, slope, u;
    if (bits == 0) return 0;
    top = shl128(a, shift).hi; /* floor(a 2^shift / 2^64), at least 2^62 */
    s = floor_sqrt64(top);     /* 2^31 <= s < 2^32 and top - s^2 <= 2 s */
    /* sqrt(a 2^shift) is close to 2^32 (s + (top - s^2) / (2 s)) */
    slope = ((top - s * s) << 31) / s;
    if (slope > 0xffffffffu) slope = 0xffffffffu;
    u = ((s << 32) + slope) >> (shift / 2);
    while (lt128(mul64(u, u), a)) {
        if (u == UINT64_MAX) die("arithmetic bound violated: a square root exceeds 64 bits");
        u++;
    }
    while (u > 0 && !lt128(mul64(u - 1, u - 1), a)) u--;
    return u;
}

/* a in decimal, for messages; text needs room for 40 characters */
static const char *decimal(u128 a, char *text) {
    char digit[40];
    int count = 0, length = 0;
    do {
        u128 r;
        a = div128(a, make128(0, 10), &r);
        digit[count++] = (char)('0' + (int)r.lo);
    } while (a.hi != 0 || a.lo != 0);
    while (count > 0) text[length++] = digit[--count];
    text[length] = 0;
    return text;
}

/* The parameters (Section 1). */

static struct {
    int k, m, n, nu;    /* gaps in a block, gap cells, height cells, the vertical mesh */
    u64 h1, h2, M, T;   /* the strip height h_1/h_2, the horizontal mesh, the truncation */
    u64 theta1, theta2; /* the threshold theta_1/theta_2 */
    u64 b[MAXM];        /* b[0] = 0 and the boundaries b_1 < ... < b_{m-1} */
    u64 len[MAXM];      /* n_c, the number of mesh intervals of cell c */
    u64 NT, I, J;       /* N_T = T M, the largest index of Section 2, the largest j of Section 5 */
} par;

/* the number of keys, C(m + k, k) - 1 (Section 4); at most C(16, 8) - 1 */
static u64 key_count(void) {
    u64 count = 1;
    for (int i = 1; i <= par.k; i++) count = count * (u64)(par.m + i) / (u64)i; /* C(m + i, i) */
    return count - 1;
}

/* The derived quantities of Sections 1, 2 and 5. The tables of Sections 2 to 6 grow with the last boundary,
   so that a long one needs more memory than can be expected; this is where the program gives up. */
static void derive(void) {
    u64 last = par.b[par.m - 1]; /* NOLINT(clang-analyzer-security.ArrayBound): m >= 1 */
    if (last > MAXB)
        die("the last boundary is %llu, and this program handles at most %llu", (unsigned long long)last,
            (unsigned long long)MAXB);
    par.NT = par.T * par.M;
    for (int c = 0; c + 1 < par.m; c++) par.len[c] = par.b[c + 1] - par.b[c];
    par.len[par.m - 1] = par.NT;
    par.I = last > par.NT ? last : par.NT;
    par.J = (u64)par.k * (last + par.NT);
}

/* Text files (Section 10). */

typedef struct {
    const char *name;      /* the file name, for messages */
    char *text;            /* the whole file */
    size_t size, next;     /* its length, and where the next line starts */
    unsigned long line;    /* the number of the current line */
    const char *cur, *end; /* the unread part of the current line */
} Reader;

/* The bytes that a text file may have: line feeds, carriage returns directly before a line feed, tabs and
   the bytes 32 to 126. A file without lines is not allowed. */
static void check_bytes(const Reader *r) {
    unsigned long line = 1;
    if (r->size == 0) die("%s: the file is empty", r->name);
    for (size_t i = 0; i < r->size; i++) {
        unsigned char c = (unsigned char)r->text[i];
        if (c == '\n') {
            line++;
        } else if (c == '\r') {
            if (i + 1 == r->size || r->text[i + 1] != '\n')
                die("%s, line %lu: a carriage return without a line feed after it", r->name, line);
        } else if (c != '\t' && (c < 32 || c > 126)) {
            die("%s, line %lu: the byte %u is not allowed", r->name, line, (unsigned)c);
        }
    }
}

/* puts the reader before the first line */
static void start_again(Reader *r) {
    r->next = 0;
    r->line = 0;
    r->cur = r->end = r->text;
}

/* reads the whole file and checks its bytes */
static void open_file(Reader *r, const char *name) {
    FILE *f = fopen(name, "rb");
    size_t room = 1 << 16;
    if (!f) die("cannot open %s", name);
    r->name = name;
    r->text = alloc(room, 1);
    r->size = 0;
    for (;;) {
        size_t wanted = room - r->size, got = fread(r->text + r->size, 1, wanted, f);
        char *larger;
        r->size += got;
        if (got < wanted) break; /* the end of the file, or an error */
        if (room > SIZE_MAX / 2) die("out of memory");
        room *= 2;
        larger = realloc(r->text, room);
        if (!larger) die("out of memory");
        r->text = larger;
    }
    if (ferror(f)) die("cannot read %s", name);
    fclose(f);
    check_bytes(r);
    start_again(r);
}

/* moves to the next line and returns 1, or returns 0 at the end of the file; the carriage return before a
   line feed is dropped */
static int next_line(Reader *r) {
    size_t start = r->next, stop = r->next;
    if (start >= r->size) return 0;
    while (stop < r->size && r->text[stop] != '\n') stop++;
    r->next = stop < r->size ? stop + 1 : stop;
    if (stop > start && r->text[stop - 1] == '\r') stop--;
    r->cur = r->text + start;
    r->end = r->text + stop;
    r->line++;
    return 1;
}

/* blanks are spaces and tabs; check_bytes has excluded every other byte that might pass for one */
static int is_blank(char c) {
    return c == ' ' || c == '\t';
}

/* the next field of the current line; returns its length, which is 0 at the end of the line */
static size_t next_field(Reader *r, const char **field) {
    const char *p = r->cur;
    while (p < r->end && is_blank(*p)) p++;
    *field = p;
    while (p < r->end && !is_blank(*p)) p++;
    r->cur = p;
    return (size_t)(p - *field);
}

static int more_fields(Reader *r) {
    while (r->cur < r->end && is_blank(*r->cur)) r->cur++;
    return r->cur < r->end;
}

/* the next field, which has to be a number: decimal digits, with a value below 2^128 */
static u128 read_number(Reader *r) {
    const char *field;
    size_t length = next_field(r, &field);
    u128 value = make128(0, 0);
    if (length == 0) die("%s, line %lu: a number is missing", r->name, r->line);
    for (size_t i = 0; i < length; i++) {
        u128 low, high;
        u64 digit, lo, hi;
        if (field[i] < '0' || field[i] > '9') die("%s, line %lu: not a number", r->name, r->line);
        digit = (u64)(field[i] - '0');
        /* 10 value + digit in two words; what is added to high.lo is at most 10 */
        low = mul64(value.lo, 10);
        high = mul64(value.hi, 10);
        lo = low.lo + digit;
        hi = high.lo + low.hi + (lo < digit);
        if (high.hi != 0 || hi < high.lo) die("%s, line %lu: a number is 2^128 or more", r->name, r->line);
        value = make128(hi, lo);
    }
    return value;
}

/* the number after "table" or "sums", which says how many lines follow; no file has 2^64 lines, so a larger
   number is replaced by 2^64 - 1 and the lines are then found to be missing */
static u64 read_count(Reader *r) {
    u128 count = read_number(r);
    return count.hi != 0 ? UINT64_MAX : count.lo;
}

static void end_of_line(Reader *r) {
    if (more_fields(r)) die("%s, line %lu: unexpected text at the end of the line", r->name, r->line);
}

/* moves to the next line, which has to begin with the given name */
static void begin_line(Reader *r, const char *word) {
    const char *field;
    size_t length;
    if (!next_line(r)) die("%s: the file ends where the line \"%s\" should be", r->name, word);
    length = next_field(r, &field);
    if (length == 0) die("%s, line %lu: a line without fields", r->name, r->line);
    if (length != strlen(word) || memcmp(field, word, length) != 0)
        die("%s, line %lu: the line should begin with \"%s\"", r->name, r->line, word);
}

static void end_of_file(Reader *r) {
    if (next_line(r)) die("%s, line %lu: unexpected line after the end", r->name, r->line);
}

/* the seven parameter lines that a spec file and a values file have in common, as they are written */
typedef struct {
    u128 k, h1, h2, mesh, heights, height_mesh, tail;
    u128 gaps[MAXM - 1]; /* the first MAXM - 1 boundaries */
    u64 ngaps;           /* how many boundaries the line has */
} Lines;

static void read_lines(Reader *r, Lines *p) {
    begin_line(r, "k");
    p->k = read_number(r);
    end_of_line(r);
    begin_line(r, "h");
    p->h1 = read_number(r);
    p->h2 = read_number(r);
    end_of_line(r);
    begin_line(r, "mesh");
    p->mesh = read_number(r);
    end_of_line(r);
    begin_line(r, "gaps");
    p->ngaps = 0;
    for (int c = 0; c < MAXM - 1; c++) p->gaps[c] = make128(0, 0);
    while (more_fields(r)) {
        u128 boundary = read_number(r);
        if (p->ngaps < MAXM - 1) p->gaps[p->ngaps] = boundary;
        p->ngaps++;
    }
    begin_line(r, "heights");
    p->heights = read_number(r);
    end_of_line(r);
    begin_line(r, "height_mesh");
    p->height_mesh = read_number(r);
    end_of_line(r);
    begin_line(r, "tail");
    p->tail = read_number(r);
    end_of_line(r);
}

/* Step 1: the spec file. */

static u64 gcd64(u64 a, u64 b) {
    while (b != 0) {
        u64 t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* whether low <= a <= high */
static int between(u128 a, u64 low, u64 high) {
    return a.hi == 0 && a.lo >= low && a.lo <= high;
}

/* checks that the parameters of the spec file are in the ranges of Section 1, and sets par */
static void set_parameters(const Lines *p, const char *name) {
    if (!between(p->k, 2, MAXK)) die("%s: k must be between 2 and %d", name, MAXK);
    if (!between(p->h1, 1, UINT64_MAX) || !between(p->h2, 1, UINT64_MAX))
        die("%s: the two numbers of h must be positive and below 2^64", name);
    if (gcd64(p->h1.lo, p->h2.lo) != 1) die("%s: h must be in lowest terms", name);
    if (!between(p->mesh, 2, MAXMESH)) die("%s: mesh must be between 2 and %d", name, MAXMESH);
    if (p->ngaps > MAXM - 1) die("%s: there must be at most %d boundaries", name, MAXM - 1);
    if (!between(p->heights, 1, MAXN)) die("%s: heights must be between 1 and %d", name, MAXN);
    if (!between(p->height_mesh, 1, MAXNU)) die("%s: height_mesh must be between 1 and %d", name, MAXNU);
    if (!between(p->tail, 1, MAXTAIL)) die("%s: tail must be between 1 and %d", name, MAXTAIL);
    par.k = (int)p->k.lo;
    par.m = (int)p->ngaps + 1;
    par.n = (int)p->heights.lo;
    par.nu = (int)p->height_mesh.lo;
    par.h1 = p->h1.lo;
    par.h2 = p->h2.lo;
    par.M = p->mesh.lo;
    par.T = p->tail.lo;
    par.b[0] = 0;
    for (int c = 1; c < par.m; c++) {
        if (p->gaps[c - 1].hi != 0 || p->gaps[c - 1].lo <= par.b[c - 1])
            die("%s: the boundaries must be positive, increasing and below 2^64", name);
        par.b[c] = p->gaps[c - 1].lo;
    }
}

static int is_separator(char c) {
#ifdef _WIN32
    if (c == '\\') return 1;
#endif
    return c == '/';
}

/* the folder of the spec file, followed by the path given in it */
static char *values_path(const char *spec_name, const char *path, size_t length) {
    size_t folder = strlen(spec_name);
    char *joined;
    while (folder > 0 && !is_separator(spec_name[folder - 1])) folder--;
    joined = alloc((u64)folder + length + 1, 1);
    memcpy(joined, spec_name, folder);
    memcpy(joined + folder, path, length);
    joined[folder + length] = 0;
    return joined;
}

/* reads the spec file, sets par and returns the path of the values file */
static char *read_spec(const char *name, Lines *lines) {
    Reader r;
    const char *path;
    size_t length;
    u128 theta1, theta2;
    char *values;
    open_file(&r, name);
    read_lines(&r, lines);
    set_parameters(lines, name);
    begin_line(&r, "threshold");
    theta1 = read_number(&r);
    theta2 = read_number(&r);
    end_of_line(&r);
    if (!between(theta1, 1, UINT64_MAX) || !between(theta2, 1, UINT64_MAX))
        die("%s: the two numbers of the threshold must be positive and below 2^64", name);
    par.theta1 = theta1.lo;
    par.theta2 = theta2.lo;
    begin_line(&r, "values");
    length = next_field(&r, &path);
    if (length == 0) die("%s, line %lu: the path of the values file is missing", name, r.line);
    end_of_line(&r);
    /* the path is relative to the folder of the spec file, with / between its parts */
    if (path[0] == '/') die("%s, line %lu: the path must not begin with /", name, r.line);
    for (size_t i = 0; i < length; i++) {
        if (path[i] == '\\' || path[i] == ':')
            die("%s, line %lu: the path must not contain \\ or :", name, r.line);
    }
    values = values_path(name, path, length);
    end_of_file(&r);
    free(r.text);
    return values;
}

/* Steps 2 to 4: the values file before anything is recomputed. */

/* what the form of a values file leaves open */
typedef struct {
    Lines lines;       /* its parameter lines */
    u64 masses;        /* how many numbers follow "masses" */
    u64 keys, sums;    /* the numbers after "table" and "sums" */
    unsigned long odd; /* the first table line whose count of numbers is not the expected one, or 0 */
} Form;

/* Step 2: the form of the values file. Only the form is checked: the numbers may have any value below
   2^128, provided that the stated numbers of lines follow "table" and "sums". `width` is the count of numbers
   that a table line should have; a line with another count is noted for step 4. */
static void read_form(Reader *r, Form *form, u64 width) {
    const char *field;
    begin_line(r, "tsp-block-values");
    if (next_field(r, &field) != 1 || field[0] != '1')
        die("%s, line 1: the first line must be \"tsp-block-values 1\"", r->name);
    end_of_line(r);
    read_lines(r, &form->lines);
    begin_line(r, "masses");
    form->masses = 0;
    while (more_fields(r)) {
        read_number(r);
        form->masses++;
    }
    begin_line(r, "tail_term");
    read_number(r);
    end_of_line(r);
    begin_line(r, "table");
    form->keys = read_count(r);
    end_of_line(r);
    form->odd = 0;
    for (u64 q = 0; q < form->keys; q++) {
        u64 numbers = 0;
        if (!next_line(r)) die("%s: the file ends inside the table", r->name);
        while (more_fields(r)) {
            read_number(r);
            numbers++;
        }
        if (numbers == 0) die("%s, line %lu: a line without fields", r->name, r->line);
        if (numbers != width && form->odd == 0) form->odd = r->line;
    }
    begin_line(r, "sums");
    form->sums = read_count(r);
    end_of_line(r);
    for (u64 g = 0; g < form->sums; g++) {
        if (!next_line(r)) die("%s: the file ends inside the cell sums", r->name);
        read_number(r);
        end_of_line(r);
    }
    begin_line(r, "total");
    read_number(r);
    end_of_line(r);
    end_of_file(r);
}

static void same_parameter(const char *name, u128 expected, u128 found) {
    char text[40], other[40];
    if (found.hi != expected.hi || found.lo != expected.lo)
        reject("parameters: %s: expected %s found %s", name, decimal(expected, text), decimal(found, other));
}

/* Step 3: the parameter lines of the values file give the same numbers as those of the spec file. */
static void check_parameters(const Lines *spec, const Lines *found) {
    same_parameter("k", spec->k, found->k);
    same_parameter("h (first number)", spec->h1, found->h1);
    same_parameter("h (second number)", spec->h2, found->h2);
    same_parameter("mesh", spec->mesh, found->mesh);
    if (found->ngaps != spec->ngaps)
        reject("parameters: gaps: expected %llu boundaries, found %llu", (unsigned long long)spec->ngaps,
               (unsigned long long)found->ngaps);
    for (u64 c = 0; c < spec->ngaps; c++) same_parameter("gaps", spec->gaps[c], found->gaps[c]);
    same_parameter("heights", spec->heights, found->heights);
    same_parameter("height_mesh", spec->height_mesh, found->height_mesh);
    same_parameter("tail", spec->tail, found->tail);
}

/* Step 4: the values file has m masses, C(m + k, k) - 1 table lines of m + n numbers, and m^k cell sums. */
static void check_counts(const char *name, const Form *form, u64 keys, u64 tuples) {
    if (form->masses != (u64)par.m)
        die("%s: there are %llu masses, and there should be %d", name, (unsigned long long)form->masses,
            par.m);
    if (form->keys != keys)
        die("%s: there are %llu table lines, and there should be %llu", name, (unsigned long long)form->keys,
            (unsigned long long)keys);
    if (form->odd != 0)
        die("%s, line %lu: a table line should have %d numbers", name, form->odd, par.m + par.n);
    if (form->sums != tuples)
        die("%s: there are %llu cell sums, and there should be %llu", name, (unsigned long long)form->sums,
            (unsigned long long)tuples);
}

/* Section 2: bounds for e^{-1/M} and its powers. */

static u64 lo_1, up_1; /* lo_1 <= Q e^{-1/M} <= up_1 */
static u64 *Rlo, *Rup; /* Rlo[i] <= Q e^{-i/M} <= Rup[i] for 0 <= i <= I */

static void exponentials(void) {
    u64 lo = 0, up = Q;
    /* 0 <= lo, up <= Q throughout, so that neither difference is negative */
    for (u64 j = 12; j >= 1; j--) {
        u64 new_up = Q - lo / (par.M * j);
        u64 new_lo = Q - ceil_div64(up, par.M * j);
        up = new_up;
        lo = new_lo;
    }
    lo_1 = lo;
    up_1 = up;
    Rlo = alloc(par.I + 1, sizeof(u64));
    Rup = alloc(par.I + 1, sizeof(u64));
    Rlo[0] = Rup[0] = Q;
    /* the factors are at most Q, so the products are at most Q^2 = 2^124 and the quotients at most Q */
    for (u64 i = 1; i <= par.I; i++) {
        Rup[i] = low64(ceil_shr128(mul64(Rup[i - 1], up_1), LOG_Q));
        Rlo[i] = low64(shr128(mul64(Rlo[i - 1], lo_1), LOG_Q));
    }
}

/* Section 3: weights, cell masses and the tail term. */

static u64 *W[MAXM];   /* W[c][i] = W_c(i) for 0 <= i <= n_c */
static u64 mass[MAXM]; /* P_c */
static u64 E_T;        /* the tail term */

static void weights(void) {
    u64 C_lambda, C_mu, t;
    t = mul_u64(par.M, Q - up_1);
    if (t > Q) die("arithmetic bound violated: C_lambda is negative");
    C_lambda = Q - t;
    t = mul_u64(par.M, Q - lo_1);
    if (t < lo_1) die("arithmetic bound violated: C_mu is negative");
    C_mu = t - lo_1;

    for (int c = 0; c < par.m; c++) {
        int bounded = c < par.m - 1;
        u64 length = par.len[c], qlo = 0;
        W[c] = alloc(length + 1, sizeof(u64));
        if (bounded) {
            if (Rup[length] >= Q) die("arithmetic bound violated: qlo is not positive");
            qlo = Q - Rup[length];
        }
        for (u64 i = 0; i <= length; i++) {
            u128 num = make128(0, 0);
            if (i < length) num = mul64(Rup[i], C_lambda);
            if (i >= 1) num = add128(num, mul64(Rup[i - 1], C_mu));
            if (bounded) { /* 2^14 = Q / D */
                W[c][i] = ceil_div128_u64(ceil_shr128(num, LOG_Q - LOG_D), qlo);
            } else { /* 2^76 = Q^2 / D; the mass beyond the truncation goes to the last mesh point */
                W[c][i] = low64(ceil_shr128(num, 2 * LOG_Q - LOG_D));
                if (i == length) W[c][i] = add_u64(W[c][i], ceil_shr64(Rup[length], LOG_Q - LOG_D));
            }
        }
        if (bounded) {
            if (Rup[par.b[c]] < Rlo[par.b[c + 1]]) die("arithmetic bound violated: a cell mass is negative");
            mass[c] = ceil_shr64(Rup[par.b[c]] - Rlo[par.b[c + 1]], LOG_Q - LOG_D);
        } else {
            mass[c] = ceil_shr64(Rup[par.b[c]], LOG_Q - LOG_D);
        }
    }
    E_T = ceil_shr64(Rup[par.NT], LOG_Q - LOG_F); /* 2^30 = Q / F */
}

/* Section 4: keys and their weight vectors. */

typedef struct {
    unsigned char count[MAXM]; /* kappa; the entries from m on are 0 */
    u64 b, len;                /* b_kappa and len_kappa */
    u64 *V;                    /* V_kappa(s) for 0 <= s < len */
} Key;

static Key *keys; /* in the order of Section 4 */
static int nkeys;

/* the keys in lexicographic order: the successor of kappa adds 1 to the last entry if the sum allows it,
   and otherwise clears the last non-zero entry and adds 1 to the entry before it */
static void make_keys(void) {
    unsigned char kappa[MAXM] = {0};
    u64 expected = key_count();
    int sum = 0;
    keys = alloc(expected, sizeof(Key));
    nkeys = 0;
    for (;;) {
        Key *key;
        if (sum < par.k) {
            kappa[par.m - 1]++;
            sum++;
        } else {
            int i = par.m - 1;
            while (i > 0 && kappa[i] == 0) i--;
            if (i <= 0) break; /* kappa = (k, 0, ..., 0) is the last key */
            sum -= kappa[i] - 1;
            kappa[i] = 0;
            kappa[i - 1]++;
        }
        if ((u64)nkeys >= expected) die("internal error: too many keys");
        key = &keys[nkeys++];
        memcpy(key->count, kappa, MAXM);
        key->b = 0;
        key->len = 1;
        for (int c = 0; c < par.m; c++) {
            key->b += kappa[c] * par.b[c];
            key->len += kappa[c] * par.len[c];
        }
        key->V = NULL;
    }
    if ((u64)nkeys != expected) die("internal error: the number of keys is not C(m + k, k) - 1");
}

/* the index of kappa among the keys, or -1; byte strings compare as the vectors do */
static int find_key(const unsigned char *kappa) {
    int low = 0, high = nkeys - 1;
    while (low <= high) {
        int middle = (low + high) / 2, order = memcmp(kappa, keys[middle].count, MAXM);
        if (order == 0) return middle;
        if (order < 0)
            high = middle - 1;
        else
            low = middle + 1;
    }
    return -1;
}

static u64 largest(const u64 *x, u64 count) {
    u64 most = 0;
    for (u64 i = 0; i < count; i++) {
        if (x[i] > most) most = x[i];
    }
    return most;
}

static void key_weights(void) {
    for (int q = 0; q < nkeys; q++) {
        Key *key = &keys[q];
        unsigned char shorter[MAXM];
        const u64 *Vs, *Wc;
        u64 slen, wlen, terms, high;
        int c = MAXM - 1, gaps = 0, qs;
        for (int i = 0; i < MAXM; i++) gaps += key->count[i];
        while (c > 0 && key->count[c] == 0) c--; /* the largest cell that occurs in the key */
        key->V = alloc(key->len, sizeof(u64));
        if (gaps == 1) {
            memcpy(key->V, W[c], (size_t)key->len * sizeof(u64));
            continue;
        }
        memcpy(shorter, key->count, MAXM);
        shorter[c]--;
        qs = find_key(shorter);
        if (qs < 0 || qs >= q) die("internal error: the keys are not in order");
        Vs = keys[qs].V;
        slen = keys[qs].len;
        Wc = W[c];
        wlen = par.len[c] + 1;
        if (key->len != slen + wlen - 1) die("internal error: the length of a weight vector is wrong");
        /* A sum has at most `terms` products, each below (high + 1) 2^64. The check gives
           terms (high + 1) < 2^64, so every sum is below 2^128 and the two words below do not overflow. */
        terms = slen < wlen ? slen : wlen;
        high = mul64(largest(Vs, slen), largest(Wc, wlen)).hi;
        if (high >= UINT64_MAX / terms) die("arithmetic bound violated: a sum of Section 4 exceeds 128 bits");
        for (u64 s = 0; s < key->len; s++) {
            u64 first = s >= wlen ? s - wlen + 1 : 0, last = s < slen ? s : slen - 1, lo = 0, hi = 0;
            for (u64 i = first; i <= last; i++) {
                u128 product = mul64(Vs[i], Wc[s - i]);
                lo += product.lo;
                hi += product.hi + (lo < product.lo);
            }
            key->V[s] = low64(ceil_shr128(make128(hi, lo), LOG_D));
        }
    }
}

/* Section 5: height differences and distances. */

static u64 *G; /* G[j * n + d] = G(j, d) for 0 <= j <= J and 0 <= d < n */

static void distances(void) {
    u64 nu = (u64)par.nu, n = (u64)par.n, taus = n * nu + 1, four_nu2 = 4 * nu * nu;
    u64 alpha = mul_u64(mul_u64(par.h2, par.h2), n * nu), gamma = mul_u64(par.M, mul_u64(par.h1, par.h1));
    u64 alpha_M = mul_u64(alpha, par.M);
    u64 limit = UINT64_MAX / four_nu2; /* Dist <= limit keeps the sums over t within 64 bits */
    u64 *chi = alloc(2 * nu + 1, sizeof(u64)), *y2 = alloc(taus, sizeof(u64));
    u64 *dist = alloc(taus, sizeof(u64)), total = 0;

    /* chi[t + nu] = chi(t) */
    for (u64 t = 0; t <= 2 * nu; t++) chi[t] = 0;
    for (u64 i = 0; i <= nu; i++) {
        for (u64 j = 0; j <= nu; j++)
            chi[i + nu - j] += (u64)(i == 0 || i == nu ? 1 : 2) * (u64)(j == 0 || j == nu ? 1 : 2);
    }
    for (u64 t = 0; t <= 2 * nu; t++) total += chi[t];
    if (total != four_nu2) die("internal error: the numbers chi(t) do not add up to 4 nu^2");

    for (u64 tau = 0; tau < taus; tau++) {
        u64 y = mul_u64(gamma, tau);
        y2[tau] = mul_u64(y, y);
    }
    G = alloc(mul_u64(par.J + 1, n), sizeof(u64));
    for (u64 j = 0; j <= par.J; j++) {
        u64 x = mul_u64(alpha, j), x2 = mul_u64(x, x);
        /* dist[tau] = Dist(j, tau); F^2 = 2^64, so the argument of the root has the sum as its high word */
        for (u64 tau = 0; tau < taus; tau++) {
            dist[tau] = ceil_div64(ceil_sqrt128(make128(add_u64(x2, y2[tau]), 0)), alpha_M);
            if (dist[tau] > limit) die("arithmetic bound violated: a sum of distances exceeds 64 bits");
        }
        for (u64 d = 0; d < n; d++) {
            u64 sum = 0, centre = d * nu;
            /* t here is t + nu in Section 5, so that the index is |d nu + t - nu| */
            for (u64 t = 0; t <= 2 * nu; t++)
                sum += chi[t] * dist[centre + t >= nu ? centre + t - nu : nu - centre - t];
            G[j * n + d] = ceil_div64(sum, four_nu2);
        }
    }
    free(chi);
    free(y2);
    free(dist);
}

/* Section 6: the table. */

static u64 *Tab;    /* Tab[q * n + d] = Tab(kappa, d) for the key kappa of index q */
static u64 max_tab; /* its largest entry */

static void make_table(void) {
    int n = par.n;
    Tab = alloc(mul_u64((u64)nkeys, (u64)n), sizeof(u64));
    max_tab = 0;
    for (int q = 0; q < nkeys; q++) {
        const Key *key = &keys[q];
        u128 sum[MAXN];
        u64 tail = mul_u64(key->count[par.m - 1], E_T);
        if (key->b + key->len - 1 > par.J) die("internal error: a weight vector is too long");
        for (int d = 0; d < n; d++) sum[d] = make128(0, 0);
        for (u64 s = 0; s < key->len; s++) {
            const u64 *row = G + (key->b + s) * (u64)n;
            for (int d = 0; d < n; d++) sum[d] = add128(sum[d], mul64(key->V[s], row[d]));
        }
        for (int d = 0; d < n; d++) {
            u64 entry = add_u64(low64(ceil_shr128(sum[d], LOG_D)), tail);
            Tab[q * n + d] = entry;
            if (entry > max_tab) max_tab = entry;
        }
    }
}

/* Section 7: cell sums. */

#define NO_PATH ((u64)1 << 63) /* stands for a path that does not exist; larger than every cost */

/*
 The interior points 1, ..., k - 1 of a block are numbered 0, ..., p - 1 here, with p = k - 1, and j = p - 1
 is the last of them. For fixed heights of the interior points, with E[u][v] the cost of the edge between u
 and v:

 A[S][u], for a set S of interior points other than j and u in S, is the cost of the cheapest path that
 starts at u, visits the rest of S and ends at j. Such a path goes from u to j if S = {u}, and otherwise
 from u to some y in S - {u}, so that
     A[{u}][u] = E[u][j],     A[S][u] = min over y of E[u][y] + A[S - {u}][y].

 H[u][v] is the cost of the cheapest path that starts at u, ends at v and visits all interior points. Such a
 path from u to j costs A[all others][u]. If neither u nor v is j, the path passes through j, which cuts it
 into a path from u to j and, read backwards, a path from v to j. These two visit complementary sets R + {u}
 and R' + {v} of other points, so that
     H[u][j] = H[j][u] = A[all others][u],     H[u][v] = min over R of A[R + {u}][u] + A[R' + {v}][v].

 All these numbers are kept in one array, at the positions given by AT_E, AT_A and AT_H, so that each of
 them is the least of some sums value[a] + value[b]. Which sums these are does not depend on the heights:
 make_plan lists them once, and sum_over_ends runs through the list for each choice of heights.
*/
#define AT_E(u, v) ((u) * MAXP + (v))
#define AT_A(S, u) (MAXP * MAXP + (S) * MAXP + (u))
#define AT_H(u, v) (MAXP * MAXP + MAXSUB * MAXP + (u) * MAXP + (v))
#define AT_ZERO (2 * MAXP * MAXP + MAXSUB * MAXP) /* a value that is always 0 */
#define VALUES (AT_ZERO + 1)

#define MAXGROUPS 16
#define MAXTARGETS 256
#define MAXTERMS 1024

/* Group g sets targets[g] values; each is the least of terms[g] sums value[a] + value[b], listed in turn. */
static struct {
    int groups, targets[MAXGROUPS], terms[MAXGROUPS];
    int target[MAXTARGETS], a[MAXTERMS], b[MAXTERMS];
    int ntargets, nterms; /* the lengths of the lists so far */
} plan;

static void new_group(int terms) {
    if (plan.groups == MAXGROUPS) die("internal error: the plan has too many groups");
    plan.targets[plan.groups] = 0;
    plan.terms[plan.groups++] = terms;
}

static void new_target(int position) {
    if (plan.ntargets == MAXTARGETS) die("internal error: the plan has too many targets");
    plan.target[plan.ntargets++] = position;
    plan.targets[plan.groups - 1]++;
}

static void new_term(int a, int b) {
    if (plan.nterms == MAXTERMS) die("internal error: the plan has too many terms");
    plan.a[plan.nterms] = a;
    plan.b[plan.nterms++] = b;
}

static int set_size(int S) {
    int size = 0;
    for (; S != 0; S >>= 1) size += S & 1;
    return size;
}

static void make_plan(void) {
    int p = par.k - 1, j = p - 1, others = (1 << j) - 1, terms = 0;
    plan.groups = plan.ntargets = plan.nterms = 0;

    /* A[S][u], the smaller sets first */
    for (int size = 1; size <= j; size++) {
        new_group(size == 1 ? 1 : size - 1);
        for (int S = 1; S <= others; S++) {
            if (set_size(S) != size) continue;
            for (int u = 0; u < j; u++) {
                if (!((S >> u) & 1)) continue;
                new_target(AT_A(S, u));
                if (size == 1) new_term(AT_E(u, j), AT_ZERO);
                for (int y = 0; y < j; y++) {
                    if (y != u && ((S >> y) & 1)) new_term(AT_E(u, y), AT_A(S ^ (1 << u), y));
                }
            }
        }
    }
    /* H[u][j] and H[j][u] */
    new_group(1);
    for (int u = 0; u < j; u++) {
        new_target(AT_H(u, j));
        new_term(AT_A(others, u), AT_ZERO);
        new_target(AT_H(j, u));
        new_term(AT_A(others, u), AT_ZERO);
    }
    /* H[u][v] for u < v < j: R runs through the subsets of the other points apart from u and v */
    if (j >= 2) {
        new_group(1 << (j - 2));
        for (int u = 0; u < j; u++) {
            for (int v = u + 1; v < j; v++) {
                int rest = others ^ (1 << u) ^ (1 << v);
                new_target(AT_H(u, v));
                for (int R = 0; R <= others; R++) {
                    if ((R & ~rest) == 0) new_term(AT_A(R | (1 << u), u), AT_A((rest ^ R) | (1 << v), v));
                }
            }
        }
        new_group(1);
        for (int u = 0; u < j; u++) {
            for (int v = u + 1; v < j; v++) {
                new_target(AT_H(v, u));
                new_term(AT_H(u, v), AT_ZERO);
            }
        }
    }
    for (int g = 0; g < plan.groups; g++) terms += plan.targets[g] * plan.terms[g];
    if (terms != plan.nterms) die("internal error: the plan is not complete");
}

typedef struct {
    /* the edge costs of a gap tuple for all heights (set_edges) */
    u64 inner[MAXP][MAXP][MAXN][MAXN]; /* inner[u][v][a][c]: between u < v at heights a and c */
    u64 first[MAXP][MAXN][MAXN];       /* first[u][a][c]: between u at height a and point 0 at height c */
    u64 last[MAXP][MAXN][MAXN];        /* last[v][a][c]: between v at height a and point k at height c */
    /* for the present heights of the interior points (sum_over_heights) */
    int height[MAXP];
    u64 value[VALUES];     /* E, A and H */
    u64 start[MAXN][MAXP]; /* start[c][u]: the edge between point 0 at height c and u */
    u64 end[MAXN][MAXP];   /* end[c][v]: the edge between v and point k at height c */
} Work;

static Work *new_work(void) {
    Work *w = alloc(1, sizeof(Work));
    int p = par.k - 1;
    memset(w, 0, sizeof(Work));
    /* a path through two or more points has two different ends; one through a single point costs nothing */
    for (int u = 0; u < MAXP; u++) w->value[AT_H(u, u)] = p == 1 ? 0 : NO_PATH;
    return w;
}

/* fills the edge costs E_{ij} = Tab(kappa(i, j), |a_i - a_j|) of the gap tuple with index g, for all
   heights; returns 0 if a key is not found, which cannot happen */
static int set_edges(Work *w, int g) {
    int cell[MAXK + 1], k = par.k, n = par.n;
    for (int i = 1; i <= k; i++) {
        cell[i] = g % par.m;
        g /= par.m;
    }
    for (int i = 0; i < k; i++) {
        unsigned char kappa[MAXM] = {0};
        for (int j = i + 1; j <= k; j++) {
            u64(*edge)[MAXN];
            const u64 *row;
            int q;
            kappa[cell[j]]++;
            if (i == 0 && j == k) continue; /* the two end points are never joined, as k >= 2 */
            q = find_key(kappa);
            if (q < 0) return 0;
            row = Tab + (size_t)q * (size_t)n;
            edge = i == 0 ? w->first[j - 1] : j == k ? w->last[i - 1] : w->inner[i - 1][j - 1];
            for (int a = 0; a < n; a++) {
                for (int c = 0; c < n; c++) edge[a][c] = row[a > c ? a - c : c - a];
            }
        }
    }
    return 1;
}

/* the least x[i] + y[i] over 0 <= i < count, for 1 <= count <= MAXP; written without a loop */
static inline u64 min_sum(const u64 *x, const u64 *y, int count) {
    /* NOLINTNEXTLINE(clang-analyzer-core.UndefinedBinaryOperatorResult): count >= 1, x[0] and y[0] are set */
    u64 best = x[0] + y[0], sum;
    switch (count) {
    case 7:
        sum = x[6] + y[6];
        best = sum < best ? sum : best;
        /* fall through */
    case 6:
        sum = x[5] + y[5];
        best = sum < best ? sum : best;
        /* fall through */
    case 5:
        sum = x[4] + y[4];
        best = sum < best ? sum : best;
        /* fall through */
    case 4:
        sum = x[3] + y[3];
        best = sum < best ? sum : best;
        /* fall through */
    case 3:
        sum = x[2] + y[2];
        best = sum < best ? sum : best;
        /* fall through */
    case 2:
        sum = x[1] + y[1];
        best = sum < best ? sum : best;
        /* fall through */
    default:
        break;
    }
    return best;
}

/*
 The sum of cost(g, a) over the heights a_0 and a_k of the two end points, for the heights of the interior
 points held in w. With H as above, cost(g, a) = min over u and v of E_{0u} + H[u][v] + E_{vk}.

 A cost is a sum of at most k table entries. The bound checked in cell_sums keeps it below NO_PATH, and keeps
 the sum of NO_PATH and one table entry, which is all that is ever added to NO_PATH, below 2^64.
*/
static u64 sum_over_ends(Work *w) {
    const int *a = plan.a, *b = plan.b, *target = plan.target;
    int p = par.k - 1, n = par.n;
    u64 *value = w->value, L[MAXP], sum = 0;

    for (int g = 0; g < plan.groups; g++) {
        int terms = plan.terms[g];
        for (int t = 0; t < plan.targets[g]; t++) {
            u64 best = value[a[0]] + value[b[0]];
            for (int i = 1; i < terms; i++) {
                u64 cost = value[a[i]] + value[b[i]];
                best = cost < best ? cost : best;
            }
            value[*target] = best;
            target++;
            a += terms;
            b += terms;
        }
    }
    for (int a0 = 0; a0 < n; a0++) {
        /* L[v]: the cheapest path from point 0 at height a0 through all interior points to v */
        for (int v = 0; v < p; v++) L[v] = min_sum(w->start[a0], value + AT_H(v, 0), p);
        for (int ak = 0; ak < n; ak++) sum += min_sum(L, w->end[ak], p);
    }
    return sum;
}

/* S_g for the gap tuple whose edge costs are in w: the heights of the interior points run through all
   tuples, the last point fastest, and d is the point whose height changes next */
static u64 sum_over_heights(Work *w) {
    int p = par.k - 1, n = par.n, d = 0;
    u64 sum = 0;
    w->height[0] = -1;
    while (d >= 0) {
        int a = ++w->height[d];
        if (a == n) { /* point d has had all its heights: back to the point before */
            d--;
            continue;
        }
        for (int u = 0; u < d; u++)
            w->value[AT_E(u, d)] = w->value[AT_E(d, u)] = w->inner[u][d][w->height[u]][a];
        for (int c = 0; c < n; c++) {
            w->start[c][d] = w->first[d][a][c];
            w->end[c][d] = w->last[d][a][c];
        }
        if (d + 1 < p)
            w->height[++d] = -1;
        else
            sum += sum_over_ends(w);
    }
    return sum;
}

/* What the threads share apart from S. It is kept on the heap: with local variables of cell_sums one compiler
   (MSVC with -O2 -openmp) was seen to give every thread a copy of its own, although they are shared. */
typedef struct {
    double start, shown; /* when the sums were begun, and when the progress was last reported */
    int done, failed;    /* gap tuples finished; set if a key was not found, which cannot happen */
} Progress;

/* S[g] = S_g for every gap tuple; the tuples are divided among the threads */
static void cell_sums(u64 *S, u64 tuples, u64 heights, int threads) {
    Work **work = (Work **)alloc((u64)threads, sizeof(Work *));
    Progress *progress = alloc(1, sizeof(Progress));
    int count = (int)tuples, g;

    /* a cost is a sum of at most k table entries, and S_g is a sum of n^(k+1) costs */
    if (max_tab >= NO_PATH / (u64)par.k) die("arithmetic bound violated: a cost exceeds 63 bits");
    if ((u64)par.k * max_tab > UINT64_MAX / heights)
        die("arithmetic bound violated: a cell sum exceeds 64 bits");

    if (threads < 1) die("internal error: no thread");
    make_plan();
    for (int t = 0; t < threads; t++) work[t] = new_work();
    progress->start = progress->shown = seconds();
    progress->done = progress->failed = 0;
#ifdef _OPENMP
#pragma omp parallel for num_threads(threads) schedule(dynamic, 1)
#endif
    for (g = 0; g < count; g++) {
#ifdef _OPENMP
        Work *w = work[omp_get_thread_num()];
#else
        Work *w = work[0];
#endif
        int found = set_edges(w, g);
        if (found) S[g] = sum_over_heights(w);
#ifdef _OPENMP
#pragma omp critical
#endif
        {
            double now = seconds();
            progress->done++;
            if (!found) progress->failed = 1;
            if (now - progress->shown >= 10.0) {
                progress->shown = now;
                fprintf(stderr, "cchk: %d of %d gap tuples after %.0f s\n", progress->done, count,
                        now - progress->start);
            }
        }
    }
    if (progress->failed) die("internal error: a key was not found");
    if (progress->done != count) die("internal error: not every gap tuple was summed");
    for (int t = 0; t < threads; t++) free(work[t]);
    free((void *)work);
    free(progress);
}

/* Section 8: the total. A[] holds the sums S_g and is overwritten. */
static u64 total_of(u64 *A, u64 tuples) {
    u64 size = tuples;
    for (int j = par.k; j >= 1; j--) {
        size /= (u64)par.m; /* m^(j-1); the tuple (g_1, ..., g_{j-1}, c) has index i + c m^(j-1) */
        for (u64 i = 0; i < size; i++) {
            u128 sum = make128(0, 0);
            /* NOLINTNEXTLINE(clang-analyzer-security.ArrayBound): i + c m^(j-1) < m^j, A has m^k entries */
            for (int c = 0; c < par.m; c++) sum = add128(sum, mul64(mass[c], A[i + (u64)c * size]));
            A[i] = low64(ceil_shr128(sum, LOG_D)); /* NOLINT(clang-analyzer-security.ArrayBound): i < m^k */
        }
    }
    return A[0];
}

/* Step 5: the numbers of the values file against the recomputed ones. The form and the counts of the file
   were checked in steps 2 and 4, so that every number is where the reader looks for it. */

static int equals(u128 found, u64 expected) {
    return found.hi == 0 && found.lo == expected;
}

/* the entries of a key or the cells of a gap tuple, as text */
static const char *list_text(const int *entry, int count, char *text, size_t room) {
    size_t used = 0;
    text[0] = 0;
    for (int i = 0; i < count && used + 8 < room; i++)
        used += (size_t)snprintf(text + used, room - used, i ? " %d" : "%d", entry[i]);
    return text;
}

static const char *key_text(const Key *key, char *text, size_t room) {
    int entry[MAXM];
    for (int c = 0; c < MAXM; c++) entry[c] = key->count[c];
    return list_text(entry, par.m, text, room);
}

static void check_masses(Reader *r) {
    char text[40];
    u128 found;
    begin_line(r, "masses");
    for (int c = 0; c < par.m; c++) {
        found = read_number(r);
        if (!equals(found, mass[c]))
            reject("masses: P_%d: expected %llu found %s", c, (unsigned long long)mass[c],
                   decimal(found, text));
    }
    begin_line(r, "tail_term");
    found = read_number(r);
    if (!equals(found, E_T))
        reject("tail_term: expected %llu found %s", (unsigned long long)E_T, decimal(found, text));
}

static void check_table(Reader *r) {
    char text[40], key[64];
    int m = par.m, n = par.n;
    begin_line(r, "table");
    for (int q = 0; q < nkeys; q++) {
        next_line(r);
        for (int c = 0; c < m; c++) {
            u128 found = read_number(r);
            if (!equals(found, keys[q].count[c]))
                reject("table: line %d: the key should be %s, and its entry %d is %s", q + 1,
                       key_text(&keys[q], key, sizeof key), c, decimal(found, text));
        }
        for (int d = 0; d < n; d++) {
            u128 found = read_number(r);
            if (!equals(found, Tab[q * n + d]))
                reject("table: key %s, d = %d: expected %llu found %s", key_text(&keys[q], key, sizeof key),
                       d, (unsigned long long)Tab[q * n + d], decimal(found, text));
        }
    }
}

static void check_sums(Reader *r, const u64 *S, u64 tuples) {
    begin_line(r, "sums");
    for (u64 g = 0; g < tuples; g++) {
        u128 found;
        next_line(r);
        found = read_number(r);
        if (!equals(found, S[g])) {
            char text[40], cells[64];
            int cell[MAXK] = {0};
            u64 rest = g;
            for (int i = 0; i < par.k; i++) {
                cell[i] = (int)(rest % (u64)par.m);
                rest /= (u64)par.m;
            }
            reject("sums: gap tuple %llu (g = %s): expected %llu found %s", (unsigned long long)g,
                   list_text(cell, par.k, cells, sizeof cells), (unsigned long long)S[g],
                   decimal(found, text));
        }
    }
}

static void check_total(Reader *r, u64 total) {
    char text[40];
    u128 found;
    begin_line(r, "total");
    found = read_number(r);
    if (!equals(found, total))
        reject("total: expected %llu found %s", (unsigned long long)total, decimal(found, text));
}

/* Step 6: the test of Section 8, and the five lines of the output. Nothing is printed before every number
   has been computed, so that a violated bound leaves the standard output empty. (The conversion of the
   whole part in the third line cannot fail: there B is at most the threshold, which is below 2^64.) */
static void verdict(u64 total, u64 heights) {
    const u64 digits = 1000000000000u; /* 10^12 */
    u128 den, lhs, rhs, q, r, whole, decimals;
    den = mul64(heights, mul_u64((u64)par.k, par.h1));
    if (den.hi >> (64 - LOG_F))
        die("arithmetic bound violated: the denominator of the bound exceeds 128 bits");
    den = shl128(den, LOG_F); /* n^(k+1) F k h_1 */
    lhs = mul128_u64(mul64(total, par.h2), par.theta2);
    rhs = mul128_u64(den, par.theta1);
    /* ceil(10^12 B), split into the whole part and 12 decimals */
    q = div128(mul128_u64(mul64(total, par.h2), digits), den, &r);
    if (r.hi != 0 || r.lo != 0) q = add128(q, make128(0, 1));
    whole = div128(q, make128(0, digits), &decimals);
    if (lt128(rhs, lhs))
        reject("the test of Section 8 fails: total %llu, bound %llu.%012llu (rounded up) exceeds %llu/%llu",
               (unsigned long long)total, (unsigned long long)low64(whole), (unsigned long long)decimals.lo,
               (unsigned long long)par.theta1, (unsigned long long)par.theta2);
    printf("the stored values agree with the recomputed values\n");
    printf("total %llu\n", (unsigned long long)total);
    printf("bound %llu.%012llu (rounded up)\n", (unsigned long long)low64(whole),
           (unsigned long long)decimals.lo);
    printf("bound <= %llu/%llu\n", (unsigned long long)par.theta1, (unsigned long long)par.theta2);
    printf("ACCEPTED\n");
}

static NORETURN void usage(void) {
    die("usage: cchk SPEC [-j THREADS]");
}

int main(int argc, char **argv) {
    char *values_name;
    int threads = 1;
    Lines lines;
    Form form;
    Reader values;
    u64 tuples = 1, heights = 1, *S, total;
    double start = seconds(), elapsed;

    /* step 1: the command line and the spec file */
    if (argc != 2 && argc != 4) usage();
    if (argc == 4) {
        const char *digits = argv[3];
        size_t length = strlen(digits);
        if (strcmp(argv[2], "-j") != 0 || length == 0 || strspn(digits, "0123456789") != length) usage();
        threads = 0;
        for (size_t d = 0; d < length; d++) {
            threads = 10 * threads + (digits[d] - '0');
            if (threads > MAXTHREADS) threads = MAXTHREADS; /* more threads than this are not used */
        }
        if (threads == 0) usage();
    }
    values_name = read_spec(argv[1], &lines);
    for (int i = 0; i < par.k; i++) tuples *= (u64)par.m;   /* m^k, at most 2^24 */
    for (int i = 0; i <= par.k; i++) heights *= (u64)par.n; /* n^(k+1), at most 2^36 */

    /* steps 2 to 4: the form of the values file, its parameter lines and its counts */
    open_file(&values, values_name);
    read_form(&values, &form, (u64)par.m + (u64)par.n);
    check_parameters(&lines, &form.lines);
    check_counts(values_name, &form, key_count(), tuples);

    /* step 5: everything is recomputed and compared, in the order of the values file */
    derive();
    if ((u64)threads > tuples) threads = (int)tuples;
#ifndef _OPENMP
    if (threads > 1) {
        fprintf(stderr, "cchk: built without OpenMP, running on one thread\n");
        threads = 1;
    }
#endif
    fprintf(stderr,
            "cchk: k = %d, m = %d, n = %d: %llu gap tuples with %llu height tuples each, %d thread%s\n",
            par.k, par.m, par.n, (unsigned long long)tuples, (unsigned long long)heights, threads,
            threads == 1 ? "" : "s");
    start_again(&values);
    for (int i = 0; i < 8; i++) next_line(&values); /* the first line and the parameter lines */
    exponentials();
    weights();
    check_masses(&values);
    make_keys();
    key_weights();
    distances();
    make_table();
    check_table(&values);
    fprintf(stderr, "cchk: masses and table of %d keys agree (%.1f s)\n", nkeys, seconds() - start);

    S = alloc(tuples, sizeof(u64));
    start = seconds();
    cell_sums(S, tuples, heights, threads);
    elapsed = seconds() - start;
    fprintf(stderr, "cchk: cell sums took %.1f s, %.2f ns for each height tuple\n", elapsed,
            1e9 * elapsed / ((double)tuples * (double)heights));
    check_sums(&values, S, tuples);
    total = total_of(S, tuples);
    check_total(&values, total);
    free(S);
    free(values.text);
    free(values_name);

    /* step 6 */
    verdict(total, heights);
    return 0;
}
