/*
 * itzamna.c - interpreter for Itzamna (no computer algebra).
 *
 * Build:  cc -O2 -Wall -Wextra -o itzamna itzamna.c -lm
 * Run:    ./itzamna [file.itz]         (no file: REPL)
 *          ./itzamna --keywords         print the keyword table
 *          ./itzamna --tokens FILE      print the tokens of a file ("INDEX WORD"), for tests
 *
 * Language summary
 *   numbers      mih jun ka ux cha ho wak huk waxak balun la   (0..10)
 *   arithmetic   tzak cham on jatz ajaw uchab, pakal ... kal (grouping)
 *   comparison   bahis lakam kukul, "machaj" in front negates
 *   output       tzib ... kal        (result in Maya notation)
 *                tzib wojol ... kal  (print the words literally)
 *   variables    wa NAME kaba ... kal   (value computed at definition time)
 *   lists        uhaj A mok B kal, A nup B, L mab INDEX, ek L kabis X kal
 *   branching    jolom COND kabis ... kal
 *   loops        xok NAME tan LIST kabis ... kal,  ichnal COND kabis ... kal
 *   strings      wa NAME wojol TEXT kal        (a list of byte codes)
 *   more math    koh (floor division), tupaj (remainder, same sign as the divisor)
 *   lists        L nah (length of a list or string), L kas I way J kal (slice from I up to J),
 *                L ut X (index of X or -1), wa L ta I kaba V kal (set element),
 *                kim L kabis I kal (delete element), ek L ta I kabis V kal
 *   functions    wa F chokte P mok Q kaba BODY kal,  call: F pakal A mok B kal
 *                (own scope per call; the result is the last statement's value)
 *   conversion   X jel   a number becomes its Maya text (as tzib prints it), a string holding a
 *                number in Maya notation becomes the number
 *   parallel     wa A mok B kaba X mok Y kal   (all values are computed first)
 *   text output  ti TEXT kal         print one line of text, without the ">>> " prefix;
 *                TEXT is literal words, wojol ... for text with keywords, or a string expression
 *   files        only plain .txt files, the extension is added automatically
 *                wa NAME il FILE kal        read a file as a string (list of byte codes)
 *                wa NAME mokil FILE kal     read a file as a list of lines (list of strings)
 *                jich FILE tzibil TEXT kal      write one line (overwrites the file)
 *                jich FILE moktzibil TEXT kal   append one line
 *                TEXT works like the body of tzib: literal words, tzibil wojol ... for text
 *                that contains keywords, or an expression whose value is a string
 *   programs     wa NAME meyahil FILE kal   reads a .txt file as code into a code variable;
 *                the word NAME on its own then runs it (in the current scope)
 *   mut          executes everything collected so far; '#' starts a comment
 *
 * Numbers are exact rationals with arbitrary-size integers (base 1e9 limbs).
 * Memory model: every Val owns its data unless flagged "borrowed"
 * (own == 0); borrowed values point into variable storage and must be
 * copied (v_own) before anything is stored.  Errors use longjmp and may
 * leak the memory that was in flight; the interpreter state stays valid.
 */
#define _POSIX_C_SOURCE 200809L
#include <ctype.h>
#include <math.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>

typedef unsigned __int128 u128;

#define MAX_STELLEN 10        /* digits after the decimal point when printing */
#define MAX_EXP 10000         /* largest allowed integer exponent for ajaw */
#define MAX_CALLS 50000       /* default limit for nested function and code-variable calls */
#define MAX_LOOP 10000000L    /* iteration limit for one ichnal loop */

/* ------------------------------------------------------------------ errors */

static jmp_buf err_jmp;
static char err_msg[512];

__attribute__((noreturn, format(printf, 1, 2)))
static void fail(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(err_msg, sizeof err_msg, fmt, ap);
    va_end(ap);
    longjmp(err_jmp, 1);
}

__attribute__((noinline)) static void *xmalloc(size_t n)
{
    void *p = malloc(n ? n : 1);
    if (!p) { fputs("out of memory\n", stderr); exit(2); }
    return p;
}

__attribute__((noinline)) static void *xrealloc(void *q, size_t n)
{
    void *p = realloc(q, n ? n : 1);
    if (!p) { fputs("out of memory\n", stderr); exit(2); }
    return p;
}

__attribute__((noinline)) static void *xcalloc(size_t c, size_t n)
{
    void *p = calloc(c ? c : 1, n ? n : 1);
    if (!p) { fputs("out of memory\n", stderr); exit(2); }
    return p;
}

/* ----------------------------------------------------------- string builder */

typedef struct { char *s; size_t n, cap; } Sb;

static void sb_init(Sb *b)
{
    b->cap = 64;
    b->n = 0;
    b->s = xmalloc(b->cap);
    b->s[0] = 0;
}

static void sb_putn(Sb *b, const char *s, size_t len)
{
    if (b->n + len + 1 > b->cap) {
        while (b->n + len + 1 > b->cap) b->cap *= 2;
        b->s = xrealloc(b->s, b->cap);
    }
    memcpy(b->s + b->n, s, len);
    b->n += len;
    b->s[b->n] = 0;
}

static void sb_puts(Sb *b, const char *s) { sb_putn(b, s, strlen(s)); }
static void sb_putc(Sb *b, char c) { sb_putn(b, &c, 1); }
static void sb_free(Sb *b) { free(b->s); b->s = NULL; b->n = b->cap = 0; }

/* ------------------------------------------------------------------ bignum */
/* Magnitude only, base 1e9, d[0] is the least significant limb.
 * Zero is n == 0 (d may be NULL). */

#define BASE 1000000000u

typedef struct { int n; uint32_t *d; } Big;

static Big big_new(int n)
{
    Big b;
    b.n = n;
    b.d = n ? xcalloc((size_t)n, sizeof(uint32_t)) : NULL;
    return b;
}

static Big big_zero(void) { Big b = {0, NULL}; return b; }

static void big_free(Big *b) { free(b->d); b->d = NULL; b->n = 0; }

/* drop leading zero limbs; a zero value releases its buffer */
static void big_trim(Big *b)
{
    while (b->n > 0 && b->d[b->n - 1] == 0) b->n--;
    if (b->n == 0) { free(b->d); b->d = NULL; }
}

static Big big_from_u64(uint64_t x)
{
    uint32_t tmp[3];
    int n = 0;
    while (x) { tmp[n++] = (uint32_t)(x % BASE); x /= BASE; }
    Big b = big_new(n);
    if (n) memcpy(b.d, tmp, (size_t)n * sizeof(uint32_t));
    return b;
}

static Big big_copy(const Big *a)
{
    Big b = big_new(a->n);
    if (a->n) memcpy(b.d, a->d, (size_t)a->n * sizeof(uint32_t));
    return b;
}

static int big_cmp(const Big *a, const Big *b)
{
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    for (int i = a->n - 1; i >= 0; i--)
        if (a->d[i] != b->d[i]) return a->d[i] < b->d[i] ? -1 : 1;
    return 0;
}

static int big_is_one(const Big *a) { return a->n == 1 && a->d[0] == 1; }

static Big big_add(const Big *a, const Big *b)
{
    int n = (a->n > b->n ? a->n : b->n) + 1;
    Big r = big_new(n);
    uint64_t c = 0;
    for (int i = 0; i < n; i++) {
        uint64_t s = c + (i < a->n ? a->d[i] : 0) + (i < b->n ? b->d[i] : 0);
        r.d[i] = (uint32_t)(s % BASE);
        c = s / BASE;
    }
    big_trim(&r);
    return r;
}

/* requires a >= b */
static Big big_sub(const Big *a, const Big *b)
{
    Big r = big_new(a->n);
    int64_t borrow = 0;
    for (int i = 0; i < a->n; i++) {
        int64_t s = (int64_t)a->d[i] - borrow - (i < b->n ? (int64_t)b->d[i] : 0);
        if (s < 0) { s += BASE; borrow = 1; } else borrow = 0;
        r.d[i] = (uint32_t)s;
    }
    big_trim(&r);
    return r;
}

static Big big_mul(const Big *a, const Big *b)
{
    if (a->n == 0 || b->n == 0) return big_zero();
    Big r = big_new(a->n + b->n);
    for (int i = 0; i < a->n; i++) {
        uint64_t carry = 0;
        for (int j = 0; j < b->n; j++) {
            uint64_t cur = r.d[i + j] + (uint64_t)a->d[i] * b->d[j] + carry;
            r.d[i + j] = (uint32_t)(cur % BASE);
            carry = cur / BASE;
        }
        int k = i + b->n;
        while (carry) {
            uint64_t cur = r.d[k] + carry;
            r.d[k] = (uint32_t)(cur % BASE);
            carry = cur / BASE;
            k++;
        }
    }
    big_trim(&r);
    return r;
}

/* m must be < 2^32 */
static Big big_mul_small(const Big *a, uint32_t m)
{
    Big r = big_new(a->n + 2);
    uint64_t carry = 0;
    for (int i = 0; i < a->n; i++) {
        uint64_t cur = (uint64_t)a->d[i] * m + carry;
        r.d[i] = (uint32_t)(cur % BASE);
        carry = cur / BASE;
    }
    r.d[a->n] = (uint32_t)(carry % BASE);
    r.d[a->n + 1] = (uint32_t)(carry / BASE);
    big_trim(&r);
    return r;
}

/* divide by a single limb-sized number (0 < m < 2^32), returns the remainder */
static uint32_t big_divmod_small(const Big *a, uint32_t m, Big *q)
{
    *q = big_new(a->n);
    uint64_t rem = 0;
    for (int i = a->n - 1; i >= 0; i--) {
        uint64_t cur = rem * BASE + a->d[i];
        q->d[i] = (uint32_t)(cur / m);
        rem = cur % m;
    }
    big_trim(q);
    return (uint32_t)rem;
}

/* schoolbook long division; the quotient limb is estimated from the top two
 * limbs of the divisor and then corrected (off by at most a few) */
static void big_divmod(const Big *a, const Big *b, Big *q, Big *r)
{
    if (b->n == 0) fail("Division by zero");
    if (big_cmp(a, b) < 0) { *q = big_zero(); *r = big_copy(a); return; }
    if (b->n == 1) {
        uint32_t rem = big_divmod_small(a, b->d[0], q);
        *r = big_from_u64(rem);
        return;
    }
    Big quo = big_new(a->n);
    Big rem = big_zero();
    int bn = b->n;
    u128 bt = (u128)b->d[bn - 1] * BASE + b->d[bn - 2];
    for (int i = a->n - 1; i >= 0; i--) {
        /* rem = rem * BASE + a[i] */
        rem.d = xrealloc(rem.d, ((size_t)rem.n + 1) * sizeof(uint32_t));
        if (rem.n) memmove(rem.d + 1, rem.d, (size_t)rem.n * sizeof(uint32_t));
        rem.d[0] = a->d[i];
        rem.n++;
        big_trim(&rem);
        if (big_cmp(&rem, b) < 0) { quo.d[i] = 0; continue; }

        /* here bn <= rem.n <= bn + 1 */
        u128 rt;
        if (rem.n == bn)
            rt = (u128)rem.d[bn - 1] * BASE + rem.d[bn - 2];
        else
            rt = ((u128)rem.d[bn] * BASE + rem.d[bn - 1]) * BASE + rem.d[bn - 2];
        uint64_t qd = (uint64_t)(rt / bt);
        if (qd >= BASE) qd = BASE - 1;

        Big prod = big_mul_small(b, (uint32_t)qd);
        while (big_cmp(&prod, &rem) > 0) {         /* estimate too large */
            qd--;
            Big t = big_sub(&prod, b);
            big_free(&prod);
            prod = t;
        }
        Big diff = big_sub(&rem, &prod);
        big_free(&prod);
        big_free(&rem);
        while (big_cmp(&diff, b) >= 0) {           /* estimate too small */
            qd++;
            Big t = big_sub(&diff, b);
            big_free(&diff);
            diff = t;
        }
        rem = diff;
        quo.d[i] = (uint32_t)qd;
    }
    big_trim(&quo);
    *q = quo;
    *r = rem;
}

static uint64_t big_to_u64_small(const Big *a)       /* requires n <= 2 */
{
    uint64_t v = 0;
    for (int i = a->n - 1; i >= 0; i--) v = v * BASE + a->d[i];
    return v;
}

static Big big_gcd(const Big *a, const Big *b)
{
    if (a->n <= 2 && b->n <= 2) {                    /* fast path: fits in 64 bits */
        uint64_t x = big_to_u64_small(a), y = big_to_u64_small(b);
        while (y) { uint64_t t = x % y; x = y; y = t; }
        return big_from_u64(x);
    }
    Big x = big_copy(a), y = big_copy(b);
    while (y.n) {
        Big q, r;
        big_divmod(&x, &y, &q, &r);
        big_free(&q);
        big_free(&x);
        x = y;
        y = r;
    }
    return x;
}

/* returns a malloc'ed decimal string */
static char *big_to_dec(const Big *a)
{
    if (a->n == 0) { char *z = xmalloc(2); z[0] = '0'; z[1] = 0; return z; }
    char *s = xmalloc((size_t)a->n * 9 + 1);
    int pos = sprintf(s, "%u", a->d[a->n - 1]);
    for (int i = a->n - 2; i >= 0; i--) pos += sprintf(s + pos, "%09u", a->d[i]);
    return s;
}

static Big big_from_dec(const char *s, size_t len)
{
    while (len > 1 && *s == '0') { s++; len--; }
    if (len == 1 && *s == '0') return big_zero();
    int n = (int)((len + 8) / 9);
    Big b = big_new(n);
    size_t end = len;
    for (int i = 0; i < n; i++) {
        size_t start = end >= 9 ? end - 9 : 0;
        uint32_t v = 0;
        for (size_t k = start; k < end; k++) v = v * 10 + (uint32_t)(s[k] - '0');
        b.d[i] = v;
        end = start;
    }
    big_trim(&b);
    return b;
}

static Big big_pow10(int k)
{
    Sb s;
    sb_init(&s);
    sb_putc(&s, '1');
    for (int i = 0; i < k; i++) sb_putc(&s, '0');
    Big b = big_from_dec(s.s, s.n);
    sb_free(&s);
    return b;
}

/* ---------------------------------------------------------------- rationals */
/* value = (neg ? -1 : 1) * num / den,  den > 0,  gcd(num, den) = 1,
 * zero is stored with neg = 0 and den = 1 */

typedef struct { int neg; Big num, den; } Rat;

static void rat_free(Rat *r) { big_free(&r->num); big_free(&r->den); }

static Rat rat_copy(const Rat *r)
{
    Rat c = { r->neg, big_copy(&r->num), big_copy(&r->den) };
    return c;
}

static int rat_is_int(const Rat *r) { return big_is_one(&r->den); }
static int rat_is_zero(const Rat *r) { return r->num.n == 0; }

/* reduce to lowest terms and fix the sign of zero */
static void rat_norm(Rat *r)
{
    if (r->num.n == 0) {
        r->neg = 0;
        big_free(&r->den);
        r->den = big_from_u64(1);
        return;
    }
    if (big_is_one(&r->den)) return;
    Big g = big_gcd(&r->num, &r->den);
    if (!big_is_one(&g)) {
        Big q, rem;
        big_divmod(&r->num, &g, &q, &rem);
        big_free(&rem);
        big_free(&r->num);
        r->num = q;
        big_divmod(&r->den, &g, &q, &rem);
        big_free(&rem);
        big_free(&r->den);
        r->den = q;
    }
    big_free(&g);
}

/* takes ownership of num and den */
static Rat rat_make(int neg, Big num, Big den)
{
    Rat r = { neg, num, den };
    rat_norm(&r);
    return r;
}

static Rat rat_from_i64(long long v)
{
    int neg = v < 0;
    uint64_t m = neg ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
    Rat r = { neg && m != 0, big_from_u64(m), big_from_u64(1) };
    return r;
}

/* signed addition of magnitudes */
static Big sadd(int na, const Big *a, int nb, const Big *b, int *nout)
{
    if (na == nb) { *nout = na; return big_add(a, b); }
    int c = big_cmp(a, b);
    if (c == 0) { *nout = 0; return big_zero(); }
    if (c > 0) { *nout = na; return big_sub(a, b); }
    *nout = nb;
    return big_sub(b, a);
}

static Rat rat_add(const Rat *a, const Rat *b)
{
    int neg;
    if (rat_is_int(a) && rat_is_int(b)) {            /* fast path: no gcd needed */
        Big n = sadd(a->neg, &a->num, b->neg, &b->num, &neg);
        Rat r = { neg, n, big_from_u64(1) };
        return r;
    }
    Big x = big_mul(&a->num, &b->den);
    Big y = big_mul(&b->num, &a->den);
    Big n = sadd(a->neg, &x, b->neg, &y, &neg);
    big_free(&x);
    big_free(&y);
    return rat_make(neg, n, big_mul(&a->den, &b->den));
}

static Rat rat_sub(const Rat *a, const Rat *b)
{
    Rat nb = *b;                                     /* shallow copy, not freed */
    nb.neg = b->num.n ? !b->neg : 0;
    return rat_add(a, &nb);
}

static Rat rat_mul(const Rat *a, const Rat *b)
{
    Big n = big_mul(&a->num, &b->num);
    int neg = n.n ? (a->neg ^ b->neg) : 0;
    if (rat_is_int(a) && rat_is_int(b)) {
        Rat r = { neg, n, big_from_u64(1) };
        return r;
    }
    return rat_make(neg, n, big_mul(&a->den, &b->den));
}

/* b must be non-zero */
static Rat rat_div(const Rat *a, const Rat *b)
{
    Big n = big_mul(&a->num, &b->den);
    Big d = big_mul(&a->den, &b->num);
    return rat_make(n.n ? (a->neg ^ b->neg) : 0, n, d);
}

static int rat_sign(const Rat *a) { return a->num.n == 0 ? 0 : (a->neg ? -1 : 1); }

static int rat_cmp(const Rat *a, const Rat *b)
{
    int sa = rat_sign(a), sb = rat_sign(b);
    if (sa != sb) return sa < sb ? -1 : 1;
    if (sa == 0) return 0;
    int c;
    if (rat_is_int(a) && rat_is_int(b)) {
        c = big_cmp(&a->num, &b->num);
    } else {
        Big x = big_mul(&a->num, &b->den);
        Big y = big_mul(&b->num, &a->den);
        c = big_cmp(&x, &y);
        big_free(&x);
        big_free(&y);
    }
    return sa < 0 ? -c : c;
}

/* extract a small integer; returns 0 when the value is not an integer or too big */
static int rat_to_long(const Rat *r, long *out)
{
    if (!rat_is_int(r) || r->num.n > 2) return 0;
    long v = (long)big_to_u64_small(&r->num);
    *out = r->neg ? -v : v;
    return 1;
}

/* approximate log2 of a positive Big (only used to pick a scaling factor) */
static double big_log2(const Big *a)
{
    double top = a->d[a->n - 1];
    if (a->n > 1) top += a->d[a->n - 2] / 1e9;
    if (a->n > 2) top += a->d[a->n - 3] / 1e18;
    return log2(top) + (a->n - 1) * log2(1e9);
}

/* a * 2^k for k >= 0 */
static Big big_shl_bits(const Big *a, long k)
{
    Big r = big_copy(a);
    while (k > 0) {
        int s = k > 29 ? 29 : (int)k;
        Big t = big_mul_small(&r, 1u << s);
        big_free(&r);
        r = t;
        k -= s;
    }
    return r;
}

/* Correctly rounded (nearest, ties to even) conversion of num/den to double:
 * scale so that the integer quotient has about 66 bits, keep a sticky bit for
 * the remainder, then round that quotient to 53 bits by hand. */
static double rat_to_double(const Rat *r)
{
    if (r->num.n == 0) return 0.0;
    long e0 = (long)floor(big_log2(&r->num) - big_log2(&r->den));
    long k = 66 - e0;
    Big n = k >= 0 ? big_shl_bits(&r->num, k) : big_copy(&r->num);
    Big d = k >= 0 ? big_copy(&r->den) : big_shl_bits(&r->den, -k);
    Big q, rem;
    big_divmod(&n, &d, &q, &rem);
    int sticky = rem.n != 0;
    u128 Q = 0;
    for (int i = q.n - 1; i >= 0; i--) Q = Q * BASE + q.d[i];
    big_free(&n); big_free(&d); big_free(&q); big_free(&rem);

    int L = 0;
    while (L < 128 && (Q >> L) != 0) L++;
    int shift = L - 53;                                 /* L is about 66, so shift > 0 */
    u128 mant = Q >> shift;
    u128 low = Q & (((u128)1 << shift) - 1);
    u128 half = (u128)1 << (shift - 1);
    if (low > half || (low == half && (sticky || (mant & 1)))) mant++;
    double res = ldexp((double)(uint64_t)mant, (int)(shift - k));
    return r->neg ? -res : res;
}

/* exact rational from a double, using the shortest decimal that round-trips */
static Rat rat_from_double(double d)
{
    char buf[64];
    for (int p = 1; p <= 17; p++) {
        snprintf(buf, sizeof buf, "%.*g", p, d);
        if (strtod(buf, NULL) == d) break;
    }
    const char *s = buf;
    int neg = 0;
    if (*s == '-') { neg = 1; s++; }
    Sb digs;
    sb_init(&digs);
    int frac = 0, seen_dot = 0;
    for (; *s && *s != 'e' && *s != 'E'; s++) {
        if (*s == '.') { seen_dot = 1; continue; }
        sb_putc(&digs, *s);
        if (seen_dot) frac++;
    }
    int e10 = 0;
    if (*s == 'e' || *s == 'E') e10 = atoi(s + 1);
    e10 -= frac;
    Big num = big_from_dec(digs.s, digs.n);
    sb_free(&digs);
    Big den = big_from_u64(1);
    if (e10 > 0) {
        Big p = big_pow10(e10), t = big_mul(&num, &p);
        big_free(&p);
        big_free(&num);
        num = t;
    } else if (e10 < 0) {
        big_free(&den);
        den = big_pow10(-e10);
    }
    return rat_make(neg && num.n != 0, num, den);
}

/* b ^ e for a non-negative integer exponent (square and multiply) */
static Rat rat_pow_nonneg(const Rat *b, long n)
{
    Rat result = rat_from_i64(1);
    Rat base = rat_copy(b);
    while (n) {
        if (n & 1) {
            Rat t = rat_mul(&result, &base);
            rat_free(&result);
            result = t;
        }
        n >>= 1;
        if (n) {
            Rat t = rat_mul(&base, &base);
            rat_free(&base);
            base = t;
        }
    }
    rat_free(&base);
    return result;
}

static Rat rat_pow(const Rat *b, const Rat *e)
{
    long n;
    if (rat_is_int(e)) {
        if (!rat_to_long(e, &n) || labs(n) > MAX_EXP) fail("Exponent too large");
        if (rat_is_zero(b) && n < 0) fail("Division by zero");
        Rat p = rat_pow_nonneg(b, n < 0 ? -n : n);
        if (n < 0) {                                  /* invert */
            Big t = p.num;
            p.num = p.den;
            p.den = t;
        }
        return p;
    }
    double bd = rat_to_double(b), ed = rat_to_double(e);
    if (isinf(bd) || isinf(ed)) fail("Power cannot be computed");
    double r = pow(bd, ed);
    if (isnan(r) || isinf(r)) fail("Power cannot be computed");
    return rat_from_double(r);
}

/* floor of a rational, as an integer rational */
static Rat rat_floor(const Rat *x)
{
    Big q, r;
    big_divmod(&x->num, &x->den, &q, &r);
    int neg = x->neg && x->num.n != 0;
    if (neg && r.n != 0) {                           /* round toward minus infinity */
        Big one = big_from_u64(1);
        Big t = big_add(&q, &one);
        big_free(&one);
        big_free(&q);
        q = t;
    }
    big_free(&r);
    Rat res = { neg && q.n != 0, q, big_from_u64(1) };
    return res;
}

/* ------------------------------------------------------------------ values */

enum { V_NUM, V_BOOL, V_LIST, V_VOID };   /* V_VOID: a call that returned nothing */

typedef struct List List;
typedef struct Val {
    int t;
    int own;                    /* 0 = borrowed from a variable or list */
    union { Rat r; int b; List *l; } u;
} Val;
struct List { int n, cap; Val *v; };

static void list_free(List *l);
static List *list_copy(const List *l);

static List *list_new(void) { return xcalloc(1, sizeof(List)); }

static void list_push(List *l, Val v)                /* v must be owned */
{
    if (l->n == l->cap) {
        l->cap = l->cap ? l->cap * 2 : 4;
        l->v = xrealloc(l->v, (size_t)l->cap * sizeof(Val));
    }
    l->v[l->n++] = v;
}

static Val v_num(Rat r) { Val v; v.t = V_NUM; v.own = 1; v.u.r = r; return v; }
static Val v_bool(int b) { Val v; v.t = V_BOOL; v.own = 1; v.u.b = b; return v; }
static Val v_list(List *l) { Val v; v.t = V_LIST; v.own = 1; v.u.l = l; return v; }

static void v_free(Val *v)
{
    if (!v->own) return;
    if (v->t == V_NUM) rat_free(&v->u.r);
    else if (v->t == V_LIST) list_free(v->u.l);
}

/* returns an owned value; deep-copies when v is borrowed */
static Val v_own(Val v)
{
    if (v.own) return v;
    Val r;
    r.t = v.t;
    r.own = 1;
    switch (v.t) {
    case V_NUM:  r.u.r = rat_copy(&v.u.r); break;
    case V_BOOL: r.u.b = v.u.b; break;
    case V_VOID: break;
    default:     r.u.l = list_copy(v.u.l); break;
    }
    return r;
}

static List *list_copy(const List *l)
{
    List *c = list_new();
    for (int i = 0; i < l->n; i++) {
        Val e = l->v[i];
        e.own = 0;
        list_push(c, v_own(e));
    }
    return c;
}

static void list_free(List *l)
{
    for (int i = 0; i < l->n; i++) v_free(&l->v[i]);
    free(l->v);
    free(l);
}

static int v_equal(const Val *a, const Val *b)        /* structural equality */
{
    if (a->t != b->t || a->t == V_VOID) return 0;
    if (a->t == V_NUM) return rat_cmp(&a->u.r, &b->u.r) == 0;
    if (a->t == V_BOOL) return a->u.b == b->u.b;
    if (a->u.l->n != b->u.l->n) return 0;
    for (int i = 0; i < a->u.l->n; i++)
        if (!v_equal(&a->u.l->v[i], &b->u.l->v[i])) return 0;
    return 1;
}

/* ------------------------------------------------- printing in Maya notation */

static const char *WORDS[] = {"mih", "jun", "ka", "ux", "cha", "ho",
                              "wak", "huk", "waxak", "balun", "la"};

typedef struct { int k; Sb s; } Term;
typedef struct { Term *a; int n, cap; } Terms;

static void maya_uint(unsigned long k, Sb *out);

static Term *terms_add(Terms *T, int k)
{
    if (T->n == T->cap) {
        T->cap = T->cap ? T->cap * 2 : 8;
        T->a = xrealloc(T->a, (size_t)T->cap * sizeof(Term));
    }
    Term *t = &T->a[T->n++];
    t->k = k;
    sb_init(&t->s);
    return t;
}

static void terms_free(Terms *T)
{
    for (int i = 0; i < T->n; i++) sb_free(&T->a[i].s);
    free(T->a);
    T->a = NULL;
    T->n = T->cap = 0;
}

/* digit d (1..9) at position 10^k, bigger factor first */
static void term_text(int d, int k, Sb *s)
{
    if (k == 0) { sb_puts(s, WORDS[d]); return; }
    if (k == 1) {
        sb_puts(s, "la");
        if (d != 1) { sb_puts(s, " on "); sb_puts(s, WORDS[d]); }
        return;
    }
    sb_puts(s, "la ajaw ");
    if (k <= 10) {
        sb_puts(s, WORDS[k]);
    } else {                                        /* compound exponent: parentheses */
        sb_puts(s, "pakal ");
        maya_uint((unsigned long)k, s);
        sb_puts(s, " kal");
    }
    if (d != 1) { sb_puts(s, " on "); sb_puts(s, WORDS[d]); }
}

/* one term per non-zero digit of the decimal string ds, highest first */
static void terms_from_digits(const char *ds, Terms *T)
{
    size_t len = strlen(ds);
    for (size_t i = 0; i < len; i++) {
        int d = ds[i] - '0';
        if (!d) continue;
        int k = (int)(len - 1 - i);
        term_text(d, k, &terms_add(T, k)->s);
    }
}

static void terms_join(const Terms *T, Sb *out)
{
    for (int i = 0; i < T->n; i++) {
        if (i) sb_puts(out, " tzak ");
        sb_puts(out, T->a[i].s.s);
    }
}

static void maya_uint(unsigned long k, Sb *out)
{
    char buf[32];
    snprintf(buf, sizeof buf, "%lu", k);
    Terms T = {0};
    terms_from_digits(buf, &T);
    if (T.n == 0) sb_puts(out, "mih");
    else terms_join(&T, out);
    terms_free(&T);
}

/* print x rounded to MAX_STELLEN decimals; negative numbers become
 * "mih cham ...", multi-term ones in parentheses */
static void maya_rat(const Rat *x, Sb *out)
{
    /* n = floor(|x| * 10^MAX_STELLEN + 1/2) = floor((2*num*10^k + den) / (2*den)) */
    Big p10 = big_from_u64(10000000000ULL);
    Big t1 = big_mul(&x->num, &p10);
    Big t2 = big_mul_small(&t1, 2);
    Big t3 = big_add(&t2, &x->den);
    Big d2 = big_mul_small(&x->den, 2);
    Big n, r;
    big_divmod(&t3, &d2, &n, &r);
    big_free(&p10); big_free(&t1); big_free(&t2); big_free(&t3);
    big_free(&d2); big_free(&r);

    int neg = x->neg && n.n != 0;
    Big q1, ganz;
    uint32_t r1 = big_divmod_small(&n, 1000000000u, &q1);
    uint32_t r2 = big_divmod_small(&q1, 10, &ganz);
    uint64_t rest = (uint64_t)r2 * 1000000000ull + r1;
    big_free(&n);
    big_free(&q1);

    char frac[32];
    snprintf(frac, sizeof frac, "%010llu", (unsigned long long)rest);
    size_t flen = MAX_STELLEN;
    while (flen > 0 && frac[flen - 1] == '0') flen--;

    char *ds = big_to_dec(&ganz);
    big_free(&ganz);
    Terms T = {0};
    terms_from_digits(ds, &T);
    free(ds);

    if (flen) {
        if (T.n == 0 || T.a[T.n - 1].k != 0) {
            Term *t = terms_add(&T, 0);
            sb_puts(&t->s, "mih");
        }
        Sb *last = &T.a[T.n - 1].s;
        sb_puts(last, " uchab");
        for (size_t i = 0; i < flen; i++) {
            sb_putc(last, ' ');
            sb_puts(last, WORDS[frac[i] - '0']);
        }
    }
    if (T.n == 0) {
        sb_puts(out, "mih");
    } else {
        if (neg) sb_puts(out, T.n > 1 ? "mih cham pakal " : "mih cham ");
        terms_join(&T, out);
        if (neg && T.n > 1) sb_puts(out, " kal");
    }
    terms_free(&T);
}

static void print_val(const Val *v, Sb *out)
{
    switch (v->t) {
    case V_NUM:  maya_rat(&v->u.r, out); break;
    case V_BOOL: sb_puts(out, v->u.b ? "utzil" : "machaj"); break;
    case V_VOID: fail("The function returned no value");
    default:
        if (v->u.l->n == 0) { sb_puts(out, "uhaj kal"); break; }
        sb_puts(out, "uhaj ");
        for (int i = 0; i < v->u.l->n; i++) {
            if (i) sb_puts(out, " mok ");
            print_val(&v->u.l->v[i], out);
        }
        sb_puts(out, " kal");
    }
}

/* ------------------------------------------------------ strings and tokens */

enum {
    K_NAME = 0, K_NUM, K_TZAK, K_CHAM, K_ON, K_JATZ, K_UCHAB, K_AJAW,
    K_PAKAL, K_KAL, K_TZIB, K_MUT, K_WA, K_KABA, K_WOJOL, K_JOLOM, K_KABIS,
    K_UHAJ, K_MOK, K_NUP, K_MAB, K_EK, K_XOK, K_TAN, K_ICHNAL,
    K_BAHIS, K_LAKAM, K_KUKUL, K_MACHAJ, K_UTZIL,
    K_KOH, K_TUPAJ, K_UT, K_TA, K_KIM, K_CHOKTE,
    K_IL, K_MOKIL, K_JICH, K_TZIBIL, K_MOKTZIBIL, K_MEYAHIL, K_TI, K_NAH, K_KAS, K_WAY, K_JEL
};

typedef struct { const char *s; int kw; int num; } Tok;   /* s is interned */

static const struct { const char *s; int kw; int num; } KW[] = {
    {"mih", K_NUM, 0}, {"jun", K_NUM, 1}, {"ka", K_NUM, 2}, {"ux", K_NUM, 3},
    {"cha", K_NUM, 4}, {"ho", K_NUM, 5}, {"wak", K_NUM, 6}, {"huk", K_NUM, 7},
    {"waxak", K_NUM, 8}, {"balun", K_NUM, 9}, {"la", K_NUM, 10},
    {"tzak", K_TZAK, 0}, {"cham", K_CHAM, 0}, {"on", K_ON, 0}, {"jatz", K_JATZ, 0},
    {"uchab", K_UCHAB, 0}, {"ajaw", K_AJAW, 0}, {"pakal", K_PAKAL, 0}, {"kal", K_KAL, 0},
    {"tzib", K_TZIB, 0}, {"mut", K_MUT, 0}, {"wa", K_WA, 0}, {"kaba", K_KABA, 0},
    {"wojol", K_WOJOL, 0}, {"jolom", K_JOLOM, 0}, {"kabis", K_KABIS, 0},
    {"uhaj", K_UHAJ, 0}, {"mok", K_MOK, 0}, {"nup", K_NUP, 0}, {"mab", K_MAB, 0},
    {"ek", K_EK, 0}, {"xok", K_XOK, 0}, {"tan", K_TAN, 0}, {"ichnal", K_ICHNAL, 0},
    {"bahis", K_BAHIS, 0}, {"lakam", K_LAKAM, 0}, {"kukul", K_KUKUL, 0},
    {"machaj", K_MACHAJ, 0}, {"utzil", K_UTZIL, 0},
    {"koh", K_KOH, 0}, {"tupaj", K_TUPAJ, 0}, {"ut", K_UT, 0}, {"ta", K_TA, 0},
    {"kim", K_KIM, 0}, {"chokte", K_CHOKTE, 0},
    {"il", K_IL, 0}, {"mokil", K_MOKIL, 0}, {"jich", K_JICH, 0}, {"tzibil", K_TZIBIL, 0},
    {"moktzibil", K_MOKTZIBIL, 0}, {"meyahil", K_MEYAHIL, 0}, {"ti", K_TI, 0}, {"nah", K_NAH, 0},
    {"kas", K_KAS, 0}, {"way", K_WAY, 0}, {"jel", K_JEL, 0},
};

/* words that may appear in a calculation (everything else is a name or a command) */
static int is_calc_word(int kw)
{
    switch (kw) {
    case K_NUM: case K_TZAK: case K_CHAM: case K_ON: case K_JATZ: case K_UCHAB:
    case K_AJAW: case K_PAKAL: case K_KAL: case K_BAHIS: case K_LAKAM: case K_KUKUL:
    case K_MACHAJ: case K_UHAJ: case K_MOK: case K_NUP: case K_MAB:
    case K_KOH: case K_TUPAJ: case K_UT: case K_NAH:
    case K_KAS: case K_WAY: case K_JEL:
        return 1;
    default:
        return 0;
    }
}

/* words that start a statement or belong to one */
static int is_code_word(int kw)
{
    return kw == K_TZIB || kw == K_MUT || kw == K_WA || kw == K_JOLOM ||
           kw == K_XOK || kw == K_ICHNAL || kw == K_EK || kw == K_KIM || kw == K_JICH || kw == K_TI;
}

/* words that open a bracket which is closed by kal */
static int is_opener(int kw)
{
    return kw == K_PAKAL || kw == K_TZIB || kw == K_WA || kw == K_JOLOM ||
           kw == K_XOK || kw == K_ICHNAL || kw == K_EK || kw == K_KIM || kw == K_JICH || kw == K_TI || kw == K_KAS || kw == K_UHAJ;
}

/* string interning: equal words share one pointer, so names compare by pointer */
static const char **itab;
static size_t icap, icnt;

static uint64_t hash_str(const char *s)
{
    uint64_t h = 1469598103934665603ULL;
    for (; *s; s++) h = (h ^ (unsigned char)*s) * 1099511628211ULL;
    return h;
}

static const char *intern(const char *s)
{
    if (icnt * 2 >= icap) {                          /* grow and rehash */
        size_t ncap = icap ? icap * 2 : 256;
        const char **nt = xcalloc(ncap, sizeof(char *));
        for (size_t i = 0; i < icap; i++) {
            if (!itab[i]) continue;
            size_t j = hash_str(itab[i]) & (ncap - 1);
            while (nt[j]) j = (j + 1) & (ncap - 1);
            nt[j] = itab[i];
        }
        free(itab);
        itab = nt;
        icap = ncap;
    }
    size_t j = hash_str(s) & (icap - 1);
    while (itab[j]) {
        if (strcmp(itab[j], s) == 0) return itab[j];
        j = (j + 1) & (icap - 1);
    }
    char *copy = strdup(s);
    if (!copy) { fputs("out of memory\n", stderr); exit(2); }
    itab[j] = copy;
    icnt++;
    return copy;
}

typedef struct { Tok *a; int n, cap; } TokVec;

static void tv_push(TokVec *v, Tok t)
{
    if (v->n == v->cap) {
        v->cap = v->cap ? v->cap * 2 : 64;
        v->a = xrealloc(v->a, (size_t)v->cap * sizeof(Tok));
    }
    v->a[v->n++] = t;
}

static Tok classify(const char *word)
{
    Tok t = { intern(word), K_NAME, 0 };
    for (size_t i = 0; i < sizeof KW / sizeof KW[0]; i++)
        if (strcmp(word, KW[i].s) == 0) { t.kw = KW[i].kw; t.num = KW[i].num; break; }
    return t;
}

/* split text into words; '#' starts a comment that runs to the end of the line */
static void tokenize(const char *text, TokVec *out)
{
    const char *p = text;
    while (*p) {
        if (isspace((unsigned char)*p)) { p++; continue; }
        if (*p == '#') { while (*p && *p != '\n') p++; continue; }
        const char *start = p;
        while (*p && !isspace((unsigned char)*p) && *p != '#') p++;
        size_t len = (size_t)(p - start);
        char *w = xmalloc(len + 1);
        memcpy(w, start, len);
        w[len] = 0;
        tv_push(out, classify(w));
        free(w);
    }
}

/* --------------------------------------------------------------- variables */

typedef struct {
    const char *name;           /* interned */
    int kind;                   /* 0 = empty, 1 = value, 2 = code, 3 = function */
    Val val;                    /* kind 1 */
    Tok *code;                  /* kinds 2 and 3: the body tokens */
    int ncode;
    const char **params;        /* kind 3: parameter names */
    int nparams;
} Var;

typedef struct { Var **tab; size_t cap, cnt; } Scope;

static Scope global_scope;
static Scope *cur_scope = &global_scope;   /* innermost active scope (function frame or global) */

/* Code arrays of redefined variables may still be executing, so they are only
 * released at the top level (after a whole chunk has run). */
static void **garbage;
static size_t ngarbage, capgarbage;

static void defer_free(void *p)
{
    if (ngarbage == capgarbage) {
        capgarbage = capgarbage ? capgarbage * 2 : 64;
        garbage = xrealloc(garbage, capgarbage * sizeof(void *));
    }
    garbage[ngarbage++] = p;
}

static void collect_garbage(void)
{
    for (size_t i = 0; i < ngarbage; i++) free(garbage[i]);
    ngarbage = 0;
}

static size_t hash_ptr(const void *p)
{
    uint64_t h = (uint64_t)(uintptr_t)p;
    h ^= h >> 33;
    h *= 0xff51afd7ed558ccdULL;
    h ^= h >> 33;
    return (size_t)h;
}

static Var *scope_raw(Scope *s, const char *name)         /* entry even if empty */
{
    if (!s->cap) return NULL;
    size_t j = hash_ptr(name) & (s->cap - 1);
    while (s->tab[j]) {
        if (s->tab[j]->name == name) return s->tab[j];
        j = (j + 1) & (s->cap - 1);
    }
    return NULL;
}

static Var *scope_find(Scope *s, const char *name)        /* only defined variables */
{
    Var *v = scope_raw(s, name);
    return v && v->kind ? v : NULL;
}

static Var *scope_slot(Scope *s, const char *name)        /* find or create */
{
    Var *v = scope_raw(s, name);
    if (v) return v;
    if (s->cnt * 2 >= s->cap) {
        size_t ncap = s->cap ? s->cap * 2 : 16;
        Var **nt = xcalloc(ncap, sizeof(Var *));
        for (size_t i = 0; i < s->cap; i++) {
            if (!s->tab[i]) continue;
            size_t j = hash_ptr(s->tab[i]->name) & (ncap - 1);
            while (nt[j]) j = (j + 1) & (ncap - 1);
            nt[j] = s->tab[i];
        }
        free(s->tab);
        s->tab = nt;
        s->cap = ncap;
    }
    v = xcalloc(1, sizeof(Var));
    v->name = name;
    size_t j = hash_ptr(name) & (s->cap - 1);
    while (s->tab[j]) j = (j + 1) & (s->cap - 1);
    s->tab[j] = v;
    s->cnt++;
    return v;
}

/* Variable lookup: the current function frame first, then the global scope. */
static Var *var_find(const char *name)
{
    Var *v = scope_find(cur_scope, name);
    if (!v && cur_scope != &global_scope) v = scope_find(&global_scope, name);
    return v;
}

static void var_clear(Var *x)
{
    if (x->kind == 1) v_free(&x->val);
    if (x->code) defer_free(x->code);
    if (x->params) defer_free((void *)x->params);
    x->kind = 0;
    x->code = NULL;
    x->ncode = 0;
    x->params = NULL;
    x->nparams = 0;
}

static void scope_free(Scope *s)
{
    for (size_t i = 0; i < s->cap; i++) {
        if (!s->tab[i]) continue;
        var_clear(s->tab[i]);
        free(s->tab[i]);
    }
    free(s->tab);
    s->tab = NULL;
    s->cap = s->cnt = 0;
}

/* Assignments always go to the current scope.  An owned v is moved into the
 * variable, a borrowed v is copied first (so v may point into the old value). */
static void var_set_value(const char *name, Val v)
{
    Val o = v_own(v);
    Var *x = scope_slot(cur_scope, name);
    var_clear(x);
    x->kind = 1;
    x->val = o;
}

static Tok *copy_toks(const Tok *t, int n)
{
    Tok *c = xmalloc((size_t)(n ? n : 1) * sizeof(Tok));
    if (n) memcpy(c, t, (size_t)n * sizeof(Tok));
    return c;
}

static void var_set_code(const char *name, const Tok *t, int n)
{
    Var *x = scope_slot(cur_scope, name);
    var_clear(x);
    x->kind = 2;
    x->code = copy_toks(t, n);
    x->ncode = n;
}

static void var_set_function(const char *name, const char **params, int np, const Tok *t, int n)
{
    Var *x = scope_slot(cur_scope, name);
    var_clear(x);
    x->kind = 3;
    x->code = copy_toks(t, n);
    x->ncode = n;
    x->params = xmalloc((size_t)(np ? np : 1) * sizeof(char *));
    if (np) memcpy(x->params, params, (size_t)np * sizeof(char *));
    x->nparams = np;
}

/* -------------------------------------------------------------- evaluation */
/* Recursive descent that evaluates while parsing:
 *   comparison > sum (tzak cham nup) > product (on jatz koh tupaj) > power (ajaw,
 *   right associative) > atom (postfix mab, ut, nah, jel, kas ... way ... kal) > basis (number with uchab,
 *   name, name pakal args kal, pakal, uhaj) */

typedef struct {
    const Tok *t;
    int n, i;
    int calls;                  /* the slice contains a function call (NAME pakal) */
} P;

static void execute(const Tok *t, int n, Val *last, int *has);
static Val call_function(const char *name, const Var *fn, Val *args, int nargs);

static int pk(const P *p, int k)                       /* kind of the token k ahead, -1 at end */
{
    int j = p->i + k;
    return j < p->n ? p->t[j].kw : -1;
}

static const Tok *pnext(P *p)
{
    if (p->i >= p->n) fail("Expression ends unexpectedly");
    return &p->t[p->i++];
}

static int scan_calls(const Tok *t, int n)
{
    for (int i = 0; i + 1 < n; i++)
        if (t[i].kw == K_NAME && t[i + 1].kw == K_PAKAL) return 1;
    return 0;
}

/* True if a function call (NAME pakal) appears in the tokens from p->i up to the kal that closes
 * the group we are in, or to the end of the slice. */
static int calls_ahead(const P *p)
{
    int depth = 0;
    for (int i = p->i; i < p->n; i++) {
        int kw = p->t[i].kw;
        if (kw == K_WOJOL) break;
        if (is_opener(kw)) depth++;
        else if (kw == K_KAL && --depth < 0) break;
        if (kw == K_NAME && i + 1 < p->n && p->t[i + 1].kw == K_PAKAL) return 1;
    }
    return 0;
}

/* True if the basis that starts at p->i (a name, a call, a group or a list literal) contains a call. */
static int basis_calls_ahead(const P *p)
{
    int k0 = pk(p, 0);
    if (k0 == K_NAME) return pk(p, 1) == K_PAKAL;
    if (k0 != K_PAKAL && k0 != K_UHAJ) return 0;
    int depth = 0;
    for (int i = p->i; i < p->n; i++) {
        int kw = p->t[i].kw;
        if (kw == K_WOJOL) break;
        if (is_opener(kw)) depth++;
        else if (kw == K_KAL) depth--;
        if (kw == K_NAME && i + 1 < p->n && p->t[i + 1].kw == K_PAKAL) return 1;
        if (depth == 0) break;
    }
    return 0;
}

/* A call may modify variables that a borrowed value points into, so values that
 * are still needed afterwards are copied first, but only when a call is possible. */
static Val hold(const P *p, Val v)
{
    return p->calls ? v_own(v) : v;
}

static Val need_value(Val v)
{
    if (v.t == V_VOID) fail("The function returned no value");
    return v;
}

static void need_num(const Val *v)
{
    if (v->t == V_VOID) fail("The function returned no value");
    if (v->t == V_BOOL) fail("Cannot do arithmetic with utzil/machaj");
    if (v->t == V_LIST) fail("Lists only work with nup, mab and ut");
}

static Val v_arith(int kw, Val a, Val b)               /* consumes a and b */
{
    if (kw == K_NUP) {
        if (a.t != V_LIST || b.t != V_LIST) fail("nup joins two lists");
        List *l = list_new();
        for (int s = 0; s < 2; s++) {
            const List *src = s ? b.u.l : a.u.l;
            for (int i = 0; i < src->n; i++) {
                Val e = src->v[i];
                e.own = 0;
                list_push(l, v_own(e));
            }
        }
        v_free(&a);
        v_free(&b);
        return v_list(l);
    }
    need_num(&a);
    need_num(&b);
    Rat r;
    switch (kw) {
    case K_TZAK: r = rat_add(&a.u.r, &b.u.r); break;
    case K_CHAM: r = rat_sub(&a.u.r, &b.u.r); break;
    case K_ON:   r = rat_mul(&a.u.r, &b.u.r); break;
    case K_JATZ:
        if (rat_is_zero(&b.u.r)) fail("Division by zero");
        r = rat_div(&a.u.r, &b.u.r);
        break;
    case K_KOH: case K_TUPAJ: {                        /* floor division and remainder */
        if (rat_is_zero(&b.u.r)) fail("Division by zero");
        Rat d = rat_div(&a.u.r, &b.u.r);
        Rat q = rat_floor(&d);
        rat_free(&d);
        if (kw == K_KOH) {
            r = q;
        } else {
            Rat bq = rat_mul(&b.u.r, &q);
            r = rat_sub(&a.u.r, &bq);
            rat_free(&bq);
            rat_free(&q);
        }
        break;
    }
    default:     r = rat_pow(&a.u.r, &b.u.r); break;   /* K_AJAW */
    }
    v_free(&a);
    v_free(&b);
    return v_num(r);
}

static Val v_compare(int kw, int neg, Val a, Val b)    /* consumes a and b */
{
    if (a.t == V_VOID || b.t == V_VOID) fail("The function returned no value");
    int res;
    if (kw == K_BAHIS) {
        if (a.t == V_LIST || b.t == V_LIST) {
            res = v_equal(&a, &b);
        } else {
            need_num(&a);
            need_num(&b);
            res = rat_cmp(&a.u.r, &b.u.r) == 0;
        }
    } else {
        need_num(&a);
        need_num(&b);
        int c = rat_cmp(&a.u.r, &b.u.r);
        res = kw == K_LAKAM ? c > 0 : c < 0;
    }
    v_free(&a);
    v_free(&b);
    return v_bool(neg ? !res : res);
}

/* validate an index for list l and return it as a C integer */
static long list_index(const List *l, const Val *i)
{
    if (i->t != V_NUM || !rat_is_int(&i->u.r)) fail("The index must be an integer");
    long n;
    if (!rat_to_long(&i->u.r, &n) || n < 0 || n >= l->n) {
        Sb s;
        sb_init(&s);
        maya_rat(&i->u.r, &s);
        sb_puts(&s, " is out of range (list length ");
        maya_uint((unsigned long)l->n, &s);
        sb_putc(&s, ')');
        fail("Index %s", s.s);
    }
    return n;
}

static Val v_index(Val a, Val i)                       /* L mab I; consumes a and i */
{
    if (a.t != V_LIST) fail("mab only works on lists");
    long n = list_index(a.u.l, &i);
    Val e = a.u.l->v[n];
    e.own = 0;                                          /* borrowed element */
    if (a.own) {                                        /* the list dies: copy the element out */
        Val o = v_own(e);
        v_free(&a);
        v_free(&i);
        return o;
    }
    v_free(&i);
    return e;
}

/* L ut X: index of the first element equal to X, or -1 if there is none */
static Val v_find(Val a, Val x)                        /* consumes a and x */
{
    if (a.t != V_LIST) fail("ut only works on lists");
    if (x.t == V_VOID) fail("The function returned no value");
    long at = -1;
    for (int k = 0; k < a.u.l->n; k++)
        if (v_equal(&a.u.l->v[k], &x)) { at = k; break; }
    v_free(&a);
    v_free(&x);
    return v_num(rat_from_i64(at));
}

/* L nah: the length of a list or string, as a number (a postfix word without operand) */
static Val v_length(Val a)                             /* consumes a */
{
    if (a.t != V_LIST) fail("nah only works on lists and strings");
    long n = a.u.l->n;
    v_free(&a);
    return v_num(rat_from_i64(n));
}

static List *bytes_to_list(const char *buf, size_t n);
static void string_from_val(const Val *v, Sb *out);
static Val eval_slice(const Tok *t, int n);

/* L kas I way J kal: the elements from index I up to (not including) J, as a new list.
 * Strict: 0 <= I <= J <= length, otherwise it is an error (like mab). */
static Val v_slice(Val l, Val a, Val b)                /* consumes l, a and b */
{
    if (l.t != V_LIST) fail("kas only works on lists and strings");
    long i, j;
    if (a.t != V_NUM || b.t != V_NUM || !rat_is_int(&a.u.r) || !rat_is_int(&b.u.r))
        fail("The slice bounds must be integers");
    if (!rat_to_long(&a.u.r, &i) || !rat_to_long(&b.u.r, &j) || i < 0 || j < i || j > l.u.l->n) {
        Sb sa, sb2, sl;
        sb_init(&sa);
        sb_init(&sb2);
        sb_init(&sl);
        maya_rat(&a.u.r, &sa);
        maya_rat(&b.u.r, &sb2);
        maya_uint((unsigned long)l.u.l->n, &sl);
        fail("Slice bounds %s way %s are out of range (list length %s)", sa.s, sb2.s, sl.s);
    }
    List *r = list_new();
    for (long k = i; k < j; k++) {
        Val e = l.u.l->v[k];
        e.own = 0;
        list_push(r, v_own(e));
    }
    v_free(&l);
    v_free(&a);
    v_free(&b);
    return v_list(r);
}

static int is_number_word(int kw)                      /* words allowed in a number text */
{
    return kw == K_NUM || kw == K_TZAK || kw == K_CHAM || kw == K_ON || kw == K_JATZ ||
           kw == K_KOH || kw == K_TUPAJ || kw == K_AJAW || kw == K_UCHAB || kw == K_PAKAL ||
           kw == K_KAL;
}

/* X jel: a number becomes its text in Maya notation (exactly what tzib prints); a string
 * holding a number in Maya notation becomes that number.  The text may only use number
 * words and the operators for numbers, so it is evaluated like any other calculation. */
static Val v_change(Val a)                             /* consumes a */
{
    if (a.t == V_NUM) {
        Sb s;
        sb_init(&s);
        maya_rat(&a.u.r, &s);
        List *l = bytes_to_list(s.s, s.n);
        sb_free(&s);
        v_free(&a);
        return v_list(l);
    }
    if (a.t != V_LIST) fail("jel needs a number or a string");
    Sb s;
    sb_init(&s);
    string_from_val(&a, &s);
    for (size_t i = 0; i < s.n; i++)
        if (s.s[i] == 0) fail("jel: the text contains a NUL byte");
    TokVec tv = {0};
    tokenize(s.s, &tv);
    if (tv.n == 0) fail("jel: the text is empty, a number in Maya notation is expected");
    for (int i = 0; i < tv.n; i++)
        if (!is_number_word(tv.a[i].kw))
            fail("jel: \"%s\" is not part of a number in Maya notation", tv.a[i].s);
    Val v = eval_slice(tv.a, tv.n);
    free(tv.a);
    sb_free(&s);
    v_free(&a);
    return v;
}

static Val eval_compare(P *p);

/* arguments of a call: ARG mok ARG ... kal (the opening pakal is already consumed) */
static int parse_args(P *p, Val **out)
{
    int n = 0, cap = 4;
    Val *a = xmalloc((size_t)cap * sizeof(Val));
    if (pk(p, 0) == K_KAL) { p->i++; *out = a; return 0; }
    for (;;) {
        Val v = need_value(eval_compare(p));
        if (n == cap) { cap *= 2; a = xrealloc(a, (size_t)cap * sizeof(Val)); }
        a[n++] = v_own(v);
        const Tok *t2 = pnext(p);
        if (t2->kw == K_KAL) break;
        if (t2->kw != K_MOK) fail("In a call, mok separates the arguments; found: \"%s\"", t2->s);
    }
    *out = a;
    return n;
}

static Val eval_basis(P *p)
{
    const Tok *tk = pnext(p);
    switch (tk->kw) {
    case K_NUM: {
        Rat v = rat_from_i64(tk->num);
        if (pk(p, 0) == K_UCHAB) {                      /* decimal digits follow */
            p->i++;
            Sb digs;
            sb_init(&digs);
            while (pk(p, 0) == K_NUM && p->t[p->i].num <= 9) {
                sb_putc(&digs, (char)('0' + p->t[p->i].num));
                p->i++;
            }
            if (digs.n == 0) fail("uchab must be followed by digit words (mih to balun)");
            Rat f = rat_make(0, big_from_dec(digs.s, digs.n), big_pow10((int)digs.n));
            Rat sum = rat_add(&v, &f);
            rat_free(&v);
            rat_free(&f);
            sb_free(&digs);
            v = sum;
        }
        return v_num(v);
    }
    case K_PAKAL: {
        Val v = eval_compare(p);
        if (pk(p, 0) != K_KAL) fail("pakal is missing its matching kal");
        p->i++;
        return v;
    }
    case K_UHAJ: {
        List *l = list_new();
        if (pk(p, 0) == K_KAL) { p->i++; return v_list(l); }
        for (;;) {
            Val e = need_value(eval_compare(p));
            list_push(l, v_own(e));
            const Tok *t2 = pnext(p);
            if (t2->kw == K_KAL) return v_list(l);
            if (t2->kw != K_MOK)
                fail("In a uhaj list, mok separates the elements; found: \"%s\"", t2->s);
        }
    }
    case K_NAME: {
        Var *x = var_find(tk->s);
        if (pk(p, 0) == K_PAKAL) {                      /* call: NAME pakal ARGS kal */
            p->i++;
            if (!x || x->kind != 3) fail("\"%s\" is not a function", tk->s);
            Var fn = *x;                                /* the arguments may redefine the function */
            Val *args;
            int na = parse_args(p, &args);
            Val r = call_function(tk->s, &fn, args, na);
            free(args);
            return r;
        }
        if (!x) fail("\"%s\" has no value", tk->s);
        if (x->kind == 2)
            fail("\"%s\" contains statements and cannot be used in a calculation", tk->s);
        if (x->kind == 3) fail("\"%s\" is a function; call it with pakal ... kal", tk->s);
        Val v = x->val;
        v.own = 0;                                      /* borrowed: no copy for plain reads */
        return v;
    }
    default:
        fail("Unexpected: \"%s\" (expected: number word, name, uhaj or pakal)", tk->s);
    }
}

static Val eval_atom(P *p)
{
    Val v = eval_basis(p);
    while (pk(p, 0) == K_MAB || pk(p, 0) == K_UT || pk(p, 0) == K_NAH ||
           pk(p, 0) == K_JEL || pk(p, 0) == K_KAS) {    /* Matrix mab mih mab mih */
        int op = p->t[p->i++].kw;
        if (op == K_NAH || op == K_JEL) {               /* no operand: L nah, X jel */
            v = op == K_NAH ? v_length(v) : v_change(v);
            continue;
        }
        if (op == K_KAS) {                              /* L kas I way J kal */
            if (calls_ahead(p)) v = v_own(v);           /* a call in the bounds may change the list */
            Val a = hold(p, need_value(eval_compare(p)));
            if (pk(p, 0) != K_WAY) fail("Correct form: L kas I way J kal");
            p->i++;
            Val b = need_value(eval_compare(p));
            if (pk(p, 0) != K_KAL) fail("kas is missing its matching kal");
            p->i++;
            v = v_slice(v, a, b);
            continue;
        }
        if (basis_calls_ahead(p)) v = v_own(v);
        Val i = eval_basis(p);
        v = op == K_MAB ? v_index(v, i) : v_find(v, i);
    }
    return v;
}

static Val eval_power(P *p)
{
    Val b = eval_atom(p);
    if (pk(p, 0) == K_AJAW) {
        p->i++;
        b = hold(p, b);
        Val e = eval_power(p);                          /* right associative */
        return v_arith(K_AJAW, b, e);
    }
    return b;
}

static Val eval_product(P *p)
{
    Val v = eval_power(p);
    while (pk(p, 0) == K_ON || pk(p, 0) == K_JATZ || pk(p, 0) == K_KOH || pk(p, 0) == K_TUPAJ) {
        int op = p->t[p->i++].kw;
        v = hold(p, v);
        Val r = eval_power(p);
        v = v_arith(op, v, r);
    }
    return v;
}

static Val eval_sum(P *p)
{
    Val v = eval_product(p);
    while (pk(p, 0) == K_TZAK || pk(p, 0) == K_CHAM || pk(p, 0) == K_NUP) {
        int op = p->t[p->i++].kw;
        v = hold(p, v);
        Val r = eval_product(p);
        v = v_arith(op, v, r);
    }
    return v;
}

static int is_comparator(int kw) { return kw == K_BAHIS || kw == K_LAKAM || kw == K_KUKUL; }

static Val eval_compare(P *p)
{
    Val l = eval_sum(p);
    int neg = 0;
    if (pk(p, 0) == K_MACHAJ && is_comparator(pk(p, 1))) { neg = 1; p->i++; }
    if (is_comparator(pk(p, 0))) {
        int op = p->t[p->i++].kw;
        l = hold(p, l);
        Val r = eval_sum(p);
        return v_compare(op, neg, l, r);
    }
    return l;
}

/* evaluate a complete token slice as one expression */
static Val eval_slice(const Tok *t, int n)
{
    if (n == 0) fail("Empty expression");
    P p = { t, n, 0, scan_calls(t, n) };
    Val v = eval_compare(&p);
    if (p.i < n) fail("Unexpected: \"%s\"", t[p.i].s);
    return v;
}

/* ---------------------------------------------------------------- statements */

static int call_depth;
static long max_calls = MAX_CALLS;      /* lowered at startup if the C stack is small */

/* Index just behind the kal that closes the opener at position i.  The literal
 * text after wojol runs up to the next kal, whatever words it contains. */
static int block_end(const Tok *t, int n, int i)
{
    int depth = 1, j = i + 1;
    while (j < n && depth > 0) {
        int kw = t[j].kw;
        if (kw == K_WOJOL) {
            while (j + 1 < n && t[j + 1].kw != K_KAL) j++;
        } else if (is_opener(kw)) {
            depth++;
        } else if (kw == K_KAL) {
            depth--;
        }
        j++;
    }
    if (depth) fail("A kal is missing");
    return j;
}

/* first token of kind kw at bracket depth 0, searching from position `from`; -1 if none */
static int find_top(const Tok *t, int n, int from, int kw)
{
    int depth = 0;
    for (int k = from; k < n; k++) {
        int w = t[k].kw;
        if (w == K_WOJOL) {
            while (k + 1 < n && t[k + 1].kw != K_KAL) k++;
        } else if (is_opener(w)) {
            depth++;
        } else if (w == K_KAL) {
            depth--;
        } else if (w == kw && depth == 0) {
            return k;
        }
    }
    return -1;
}

/* index of the first top-level kabis (the split between head and body) */
static int split_kabis(const Tok *t, int n)
{
    int k = find_top(t, n, 0, K_KABIS);
    if (k < 0) fail("A kabis is missing");
    return k;
}

static void print_line(const char *s)
{
    printf(">>> %s\n", s);
}

static void do_write(const Tok *t, int n)               /* body of tzib ... kal */
{
    Sb out;
    sb_init(&out);
    if (n > 0 && t[0].kw == K_WOJOL) {                  /* literal text */
        for (int i = 1; i < n; i++) {
            if (i > 1) sb_putc(&out, ' ');
            sb_puts(&out, t[i].s);
        }
    } else {
        int calc = 0;
        for (int i = 0; i < n && !calc; i++)
            if (is_calc_word(t[i].kw) || (t[i].kw == K_NAME && var_find(t[i].s))) calc = 1;
        if (calc) {
            Val v = eval_slice(t, n);
            print_val(&v, &out);
            v_free(&v);
        } else {                                        /* only unknown words: print as text */
            for (int i = 0; i < n; i++) {
                if (i) sb_putc(&out, ' ');
                sb_puts(&out, t[i].s);
            }
        }
    }
    print_line(out.s);
    sb_free(&out);
}

static void check_name(const Tok *tk)
{
    if (tk->kw != K_NAME) fail("\"%s\" is a keyword, not a variable name", tk->s);
}

/* parse "N1 mok N2 mok ..." into out[]; returns the count */
static int parse_names(const Tok *t, int n, const char **out, int allow_empty)
{
    if (n == 0) {
        if (allow_empty) return 0;
        fail("A name is missing");
    }
    int cnt = 0, i = 0;
    for (;;) {
        check_name(&t[i]);
        out[cnt++] = t[i].s;
        i++;
        if (i >= n) return cnt;
        if (t[i].kw != K_MOK) fail("Names are separated by mok; found: \"%s\"", t[i].s);
        i++;
        if (i >= n) fail("A name is missing after mok");
    }
}

/* Resolve NAME (ta INDEX)* to the storage of the addressed value.  All index
 * expressions are evaluated first, so a call inside an index cannot invalidate
 * the pointer that is returned. */
static Val *place_ref(const Tok *t, int n)
{
    if (n < 1 || t[0].kw != K_NAME) fail("A variable name is expected here");
    P p = { t, n, 1, scan_calls(t, n) };
    Val *idx = xmalloc(((size_t)n + 1) * sizeof(Val));
    int ni = 0;
    while (p.i < n) {
        if (t[p.i].kw != K_TA) fail("Unexpected: \"%s\" (expected: ta)", t[p.i].s);
        p.i++;
        idx[ni++] = v_own(need_value(eval_basis(&p)));
    }
    Var *x = var_find(t[0].s);
    if (!x || x->kind != 1) fail("\"%s\" has no value", t[0].s);
    Val *slot = &x->val;
    for (int q = 0; q < ni; q++) {
        if (slot->t != V_LIST) fail("ta only works on lists");
        slot = &slot->u.l->v[list_index(slot->u.l, &idx[q])];
        v_free(&idx[q]);
    }
    free(idx);
    return slot;
}

/* ------------------------------------------------------------- files, exec */
/* Only plain .txt files.  The file name is a single plain word; ".txt" is added. */

static char *file_path(const Tok *tk)
{
    if (tk->kw != K_NAME)
        fail("A file name must be a plain word, not the keyword \"%s\"", tk->s);
    size_t len = strlen(tk->s);
    char *p = xmalloc(len + 5);
    memcpy(p, tk->s, len);
    memcpy(p + len, ".txt", 5);
    return p;
}

static char *slurp(const char *path, size_t *len)       /* whole file, binary safe */
{
    FILE *f = fopen(path, "rb");
    if (!f) fail("Cannot open file \"%s\"", path);
    size_t cap = 4096, n = 0, r;
    char *buf = xmalloc(cap);
    while ((r = fread(buf + n, 1, cap - n, f)) > 0) {
        n += r;
        if (n == cap) { cap *= 2; buf = xrealloc(buf, cap); }
    }
    fclose(f);
    *len = n;
    return buf;
}

static List *bytes_to_list(const char *buf, size_t n)   /* a string is a list of byte codes */
{
    List *l = list_new();
    for (size_t i = 0; i < n; i++) list_push(l, v_num(rat_from_i64((unsigned char)buf[i])));
    return l;
}

/* lines without their terminators ("\n" or "\r\n"); a final newline does not start a new line */
static List *lines_to_list(const char *buf, size_t n)
{
    List *l = list_new();
    size_t start = 0;
    for (size_t i = 0; i <= n; i++) {
        if (i < n && buf[i] != '\n') continue;
        if (i == n && start == n) break;                /* nothing after the last newline */
        size_t end = i;
        if (end > start && buf[end - 1] == '\r') end--;
        list_push(l, v_list(bytes_to_list(buf + start, end - start)));
        start = i + 1;
    }
    return l;
}

/* a string value (list of integers 0..255) as bytes */
static void string_from_val(const Val *v, Sb *out)
{
    if (v->t != V_LIST) fail("A string (a list of byte codes 0 to 255) is expected here");
    for (int i = 0; i < v->u.l->n; i++) {
        const Val *e = &v->u.l->v[i];
        long c;
        if (e->t != V_NUM || !rat_to_long(&e->u.r, &c) || c < 0 || c > 255)
            fail("A string (a list of byte codes 0 to 255) is expected here");
        sb_putc(out, (char)c);
    }
}

/* The text for jich: the words literally if the body starts with wojol or contains
 * no calculation word and no variable (like tzib); otherwise the value of the
 * expression, which must be a string. */
static void text_of_body(const Tok *t, int n, Sb *out)
{
    if (n > 0 && t[0].kw == K_WOJOL) {
        for (int i = 1; i < n; i++) {
            if (i > 1) sb_putc(out, ' ');
            sb_puts(out, t[i].s);
        }
        return;
    }
    int calc = 0;
    for (int i = 0; i < n && !calc; i++)
        if (is_calc_word(t[i].kw) || (t[i].kw == K_NAME && var_find(t[i].s))) calc = 1;
    if (calc) {
        Val v = eval_slice(t, n);
        string_from_val(&v, out);
        v_free(&v);
    } else {
        for (int i = 0; i < n; i++) {
            if (i) sb_putc(out, ' ');
            sb_puts(out, t[i].s);
        }
    }
}

/* One line per call: the text plus a newline unless it is empty (for a write) or already
 * ends with one.  An append never glues onto a last line that has no newline. */
static void write_text(const char *path, int append, const Sb *text)
{
    int ends_nl = text->n > 0 && text->s[text->n - 1] == '\n';
    int need_sep = 0;
    if (append) {
        FILE *r = fopen(path, "rb");
        if (r) {
            if (fseek(r, -1, SEEK_END) == 0) {
                int c = fgetc(r);
                need_sep = c != EOF && c != '\n';
            }
            fclose(r);
        }
    }
    FILE *f = fopen(path, append ? "ab" : "wb");
    if (!f) fail("Cannot open file \"%s\" for writing", path);
    if (need_sep) fputc('\n', f);
    if (text->n) fwrite(text->s, 1, text->n, f);
    if (!ends_nl && (append || text->n > 0)) fputc('\n', f);
    if (fclose(f) != 0) fail("Cannot write file \"%s\"", path);
}

static void do_jich(const Tok *t, int n)                /* jich FILE tzibil|moktzibil TEXT kal */
{
    if (n < 2 || (t[1].kw != K_TZIBIL && t[1].kw != K_MOKTZIBIL))
        fail("Correct form: jich FILE tzibil TEXT kal  or  jich FILE moktzibil TEXT kal");
    char *path = file_path(&t[0]);
    Sb text;
    sb_init(&text);
    text_of_body(t + 2, n - 2, &text);                  /* may call functions: before touching the file */
    write_text(path, t[1].kw == K_MOKTZIBIL, &text);
    free(path);
    sb_free(&text);
}

/* ti TEXT kal: print one line of text to the console, without the ">>> " prefix of tzib.
 * TEXT works like the text of jich ... tzibil: literal words, wojol ... for words that are
 * keywords, or an expression whose value is a string.  A newline is added unless the text
 * already ends with one (so an empty text prints an empty line). */
static void do_say(const Tok *t, int n)
{
    Sb text;
    sb_init(&text);
    text_of_body(t, n, &text);
    if (text.n) fwrite(text.s, 1, text.n, stdout);
    if (text.n == 0 || text.s[text.n - 1] != '\n') putchar('\n');
    sb_free(&text);
}

/* A program text must be balanced: every opener has its kal (the text after wojol is skipped). */
static void check_balanced(const Tok *t, int n)
{
    int depth = 0;
    for (int i = 0; i < n; i++) {
        int kw = t[i].kw;
        if (kw == K_WOJOL) {
            while (i + 1 < n && t[i + 1].kw != K_KAL) i++;
        } else if (is_opener(kw)) {
            depth++;
        } else if (kw == K_KAL && --depth < 0) {
            fail("kal without an opening word in the program text");
        }
    }
    if (depth) fail("A kal is missing in the program text");
}

/*  wa NAME kaba VALUE kal
 *  wa NAME ta I ta J kaba VALUE kal            set one element
 *  wa A mok B kaba X mok Y kal                 parallel assignment (all values first)
 *  wa NAME wojol TEXT kal                      string: a list of byte codes
 *  wa F chokte P1 mok P2 kaba BODY kal         function (several names: one body each) */
static void do_define(const Tok *t, int n)
{
    int k = 0;                                          /* the head ends at kaba or wojol */
    while (k < n && t[k].kw != K_KABA && t[k].kw != K_WOJOL && t[k].kw != K_IL && t[k].kw != K_MOKIL &&
           t[k].kw != K_MEYAHIL) k++;
    if (k == n) fail("Correct form: wa NAME kaba ... kal");
    const Tok *body = t + k + 1;
    int bn = n - k - 1;

    if (t[k].kw == K_IL || t[k].kw == K_MOKIL) {        /* read a file */
        if (k != 1 || bn != 1) fail("Correct form: wa NAME il FILE kal  or  wa NAME mokil FILE kal");
        check_name(&t[0]);
        char *path = file_path(&body[0]);
        size_t len;
        char *buf = slurp(path, &len);
        free(path);
        Val v = v_list(t[k].kw == K_IL ? bytes_to_list(buf, len) : lines_to_list(buf, len));
        free(buf);
        var_set_value(t[0].s, v);
        return;
    }

    if (t[k].kw == K_MEYAHIL) {                         /* read a file as code; NAME alone runs it */
        if (k != 1 || bn != 1) fail("Correct form: wa NAME meyahil FILE kal");
        check_name(&t[0]);
        char *path = file_path(&body[0]);
        size_t len;
        char *buf = slurp(path, &len);
        free(path);
        for (size_t i = 0; i < len; i++)
            if (buf[i] == 0) fail("The program file contains a NUL byte");
        buf = xrealloc(buf, len + 1);
        buf[len] = 0;
        TokVec tv = {0};
        tokenize(buf, &tv);
        free(buf);
        check_balanced(tv.a, tv.n);
        var_set_code(t[0].s, tv.a, tv.n);
        free(tv.a);
        return;
    }

    if (t[k].kw == K_WOJOL) {
        if (k != 1) fail("Correct form: wa NAME wojol TEXT kal");
        check_name(&t[0]);
        Sb s;
        sb_init(&s);
        for (int i = 0; i < bn; i++) {
            if (i) sb_putc(&s, ' ');
            sb_puts(&s, body[i].s);
        }
        List *l = list_new();
        for (size_t i = 0; i < s.n; i++)
            list_push(l, v_num(rat_from_i64((unsigned char)s.s[i])));
        sb_free(&s);
        var_set_value(t[0].s, v_list(l));
        return;
    }

    if (k == 1 && t[0].kw == K_NAME && find_top(body, bn, 0, K_MOK) < 0) {
        /* fast path for the common case "wa NAME kaba VALUE kal": no temporary arrays */
        for (int j = 0; j < bn; j++)
            if (is_code_word(body[j].kw)) { var_set_code(t[0].s, body, bn); return; }
        var_set_value(t[0].s, need_value(eval_slice(body, bn)));
        return;
    }

    if (k > 1 && t[1].kw == K_TA) {                     /* element assignment */
        Val nv = v_own(need_value(eval_slice(body, bn)));
        Val *slot = place_ref(t, k);
        v_free(slot);
        *slot = nv;
        return;
    }

    int ch = find_top(t, k, 0, K_CHOKTE);
    int hn = ch >= 0 ? ch : k;
    const char **names = xmalloc(((size_t)hn + 1) * sizeof(char *));
    int nn = parse_names(t, hn, names, 0);
    const char **params = NULL;
    int np = 0;
    if (ch >= 0) {
        params = xmalloc(((size_t)(k - ch) + 1) * sizeof(char *));
        np = parse_names(t + ch + 1, k - ch - 1, params, 1);
    }

    int *starts = xmalloc(((size_t)bn + 2) * sizeof(int));
    int *ends = xmalloc(((size_t)bn + 2) * sizeof(int));
    int parts = 0, start = 0;
    for (;;) {                                          /* split the body at top-level mok */
        int m = find_top(body, bn, start, K_MOK);
        starts[parts] = start;
        ends[parts] = m < 0 ? bn : m;
        parts++;
        if (m < 0) break;
        start = m + 1;
    }
    if (parts != nn) {
        Sb a, b;
        sb_init(&a);
        sb_init(&b);
        maya_uint((unsigned long)nn, &a);
        maya_uint((unsigned long)parts, &b);
        fail("%s names but %s values", a.s, b.s);
    }

    if (ch >= 0) {
        for (int i = 0; i < nn; i++)
            var_set_function(names[i], params, np, body + starts[i], ends[i] - starts[i]);
    } else {
        Val *vals = xmalloc((size_t)nn * sizeof(Val));
        int *is_code = xcalloc((size_t)nn, sizeof(int));
        for (int i = 0; i < nn; i++) {                  /* first evaluate everything ... */
            const Tok *pt = body + starts[i];
            int pl = ends[i] - starts[i];
            for (int j = 0; j < pl; j++)
                if (is_code_word(pt[j].kw)) { is_code[i] = 1; break; }
            if (!is_code[i]) vals[i] = v_own(need_value(eval_slice(pt, pl)));
        }
        for (int i = 0; i < nn; i++) {                  /* ... then assign */
            if (is_code[i]) var_set_code(names[i], body + starts[i], ends[i] - starts[i]);
            else var_set_value(names[i], vals[i]);
        }
        free(vals);
        free(is_code);
    }
    free(names);
    free(params);
    free(starts);
    free(ends);
}

static int check_condition(const Tok *t, int n)
{
    Val v = eval_slice(t, n);
    if (v.t != V_BOOL)
        fail("The condition must be utzil or machaj (compare with bahis, lakam, kukul)");
    return v.u.b;
}

static void do_if(const Tok *t, int n)                  /* jolom COND kabis ... kal */
{
    int k = split_kabis(t, n);
    if (check_condition(t, k)) execute(t + k + 1, n - k - 1, NULL, NULL);
}

static void do_foreach(const Tok *t, int n)             /* xok NAME tan LIST kabis ... kal */
{
    int k = split_kabis(t, n);
    if (k < 3 || t[1].kw != K_TAN) fail("Correct form: xok NAME tan LIST kabis ... kal");
    check_name(&t[0]);
    const char *name = t[0].s;
    Val lv = need_value(eval_slice(t + 2, k - 2));
    if (lv.t != V_LIST) fail("xok needs a list (uhaj ... kal)");
    Val own = v_own(lv);                                /* iterate over a snapshot */
    for (int i = 0; i < own.u.l->n; i++) {
        Val e = own.u.l->v[i];
        e.own = 0;
        var_set_value(name, e);
        execute(t + k + 1, n - k - 1, NULL, NULL);
    }
    v_free(&own);
}

static void do_while(const Tok *t, int n)               /* ichnal COND kabis ... kal */
{
    int k = split_kabis(t, n);
    long count = 0;
    while (check_condition(t, k)) {
        if (++count > MAX_LOOP) fail("Loop runs too long (aborted)");
        execute(t + k + 1, n - k - 1, NULL, NULL);
    }
}

static void do_append(const Tok *t, int n)              /* ek PLACE kabis VALUE kal */
{
    int k = split_kabis(t, n);
    Val nv = v_own(need_value(eval_slice(t + k + 1, n - k - 1)));
    Val *slot = place_ref(t, k);
    if (slot->t != V_LIST) fail("ek needs a list");
    list_push(slot->u.l, nv);
}

static void do_delete(const Tok *t, int n)              /* kim PLACE kabis INDEX kal */
{
    int k = split_kabis(t, n);
    Val iv = v_own(need_value(eval_slice(t + k + 1, n - k - 1)));
    Val *slot = place_ref(t, k);
    if (slot->t != V_LIST) fail("kim needs a list");
    List *l = slot->u.l;
    long at = list_index(l, &iv);
    v_free(&iv);
    v_free(&l->v[at]);
    memmove(&l->v[at], &l->v[at + 1], (size_t)(l->n - at - 1) * sizeof(Val));
    l->n--;
}

/* Run a function body in a fresh scope.  The result is the value of the body's
 * last statement if that is an expression, otherwise V_VOID. */
static Val call_function(const char *name, const Var *fn, Val *args, int nargs)
{
    if (nargs != fn->nparams) fail("Wrong number of arguments for \"%s\"", name);
    if (call_depth >= max_calls) fail("Call depth limit reached (recursion too deep)");
    Scope s = {0};
    for (int i = 0; i < nargs; i++) {
        Var *v = scope_slot(&s, fn->params[i]);
        var_clear(v);
        v->kind = 1;
        v->val = args[i];                               /* moved into the new scope */
    }
    Scope *saved = cur_scope;
    cur_scope = &s;
    call_depth++;
    Val result;
    result.t = V_VOID;
    result.own = 1;
    int has = 0;
    execute(fn->code, fn->ncode, &result, &has);
    call_depth--;
    cur_scope = saved;
    scope_free(&s);
    if (!has) { result.t = V_VOID; result.own = 1; }
    return result;
}

/* an expression statement or a lone code variable */
static void do_statement(const Tok *t, int n, Val *last, int *has)
{
    if (n == 1 && t[0].kw == K_NAME) {
        Var *x = var_find(t[0].s);
        if (x && x->kind == 2) {                        /* a lone code variable runs its body */
            if (call_depth >= max_calls) fail("Circular definition at \"%s\"", t[0].s);
            call_depth++;
            execute(x->code, x->ncode, NULL, NULL);
            call_depth--;
            return;
        }
    }
    Val v = eval_slice(t, n);
    if (last) { *last = v_own(v); *has = 1; }           /* value of the last statement */
    else v_free(&v);
}

static void execute(const Tok *t, int n, Val *last, int *has)
{
    int i = 0;
    while (i < n) {
        int kw = t[i].kw;
        if (kw == K_MUT) { i++; continue; }             /* separator inside a block */
        if (is_code_word(kw)) {
            int j = block_end(t, n, i);
            const Tok *body = t + i + 1;
            int bn = j - i - 2;
            switch (kw) {
            case K_TZIB:   do_write(body, bn); break;
            case K_WA:     do_define(body, bn); break;
            case K_JOLOM:  do_if(body, bn); break;
            case K_XOK:    do_foreach(body, bn); break;
            case K_ICHNAL: do_while(body, bn); break;
            case K_EK:     do_append(body, bn); break;
            case K_JICH:   do_jich(body, bn); break;
            case K_TI:     do_say(body, bn); break;
            default:       do_delete(body, bn); break;  /* K_KIM */
            }
            i = j;
        } else {                                        /* expression statement */
            int j = i;
            while (j < n && !is_code_word(t[j].kw)) j++;
            do_statement(t + i, j - i, j == n ? last : NULL, has);
            i = j;
        }
    }
}

/* ------------------------------------------------------- input and the REPL */

static TokVec pending;        /* tokens collected since the last mut */
static int depth;             /* open brackets in `pending` */
static int text_mode;         /* inside the literal text after wojol */

static void reset_input(void)
{
    pending.n = 0;
    depth = 0;
    text_mode = 0;
    call_depth = 0;
    cur_scope = &global_scope;
}

/* collect tokens; a mut at bracket depth 0 executes everything collected */
static void feed(const TokVec *tv)
{
    for (int i = 0; i < tv->n; i++) {
        Tok t = tv->a[i];
        if (text_mode) {                                /* literal text: only kal ends it */
            if (t.kw != K_KAL) { tv_push(&pending, t); continue; }
            text_mode = 0;
        } else if (t.kw == K_WOJOL) {
            text_mode = 1;
            tv_push(&pending, t);
            continue;
        }
        if (t.kw == K_MUT && depth == 0) {
            int n = pending.n;
            pending.n = 0;
            execute(pending.a, n, NULL, NULL);
            collect_garbage();
            continue;
        }
        if (is_opener(t.kw)) {
            depth++;
        } else if (t.kw == K_KAL) {
            if (--depth < 0) {
                reset_input();
                fail("kal without an opening word (pakal, tzib, wa, jolom, xok, ichnal, ek, kim, uhaj)");
            }
        }
        tv_push(&pending, t);
    }
}

__attribute__((noinline)) static char *read_file(const char *path)
{
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    size_t cap = 1 << 16, n = 0;
    char *buf = xmalloc(cap);
    size_t r;
    while ((r = fread(buf + n, 1, cap - n - 1, f)) > 0) {
        n += r;
        if (cap - n < 2) { cap *= 2; buf = xrealloc(buf, cap); }
    }
    fclose(f);
    buf[n] = 0;
    return buf;
}

static void report_error(void)
{
    fflush(stdout);
    fprintf(stderr, "Error: %s\n", err_msg);
}

static int real_main(int argc, char **argv)
{
    if (argc > 1 && strcmp(argv[1], "--keywords") == 0) {   /* the keyword table, one word per line */
        for (size_t k = 0; k < sizeof KW / sizeof KW[0]; k++) puts(KW[k].s);
        return 0;
    }
    if (argc > 2 && strcmp(argv[1], "--tokens") == 0) {     /* test helper: "INDEX WORD" per token */
        char *src = read_file(argv[2]);
        if (!src) { fprintf(stderr, "Cannot read %s\n", argv[2]); return 1; }
        TokVec tv = {0};
        tokenize(src, &tv);
        for (int i = 0; i < tv.n; i++) {
            long idx = -1;                                  /* position in the keyword table, -1 for names */
            for (size_t k = 0; k < sizeof KW / sizeof KW[0]; k++)
                if (strcmp(tv.a[i].s, KW[k].s) == 0) { idx = (long)k; break; }
            printf("%ld %s\n", idx, tv.a[i].s);
        }
        free(tv.a);
        free(src);
        return 0;
    }
    if (argc > 1) {                                     /* file mode */
        char *src = read_file(argv[1]);
        if (!src) { fprintf(stderr, "Cannot read %s\n", argv[1]); return 1; }
        if (setjmp(err_jmp)) { report_error(); return 1; }
        TokVec tv = {0};
        tokenize(src, &tv);
        feed(&tv);
        free(tv.a);
        free(src);
        fflush(stdout);
        if (pending.n > 0)
            fputs("Note: a mut (or a kal) is missing at the end; the rest was not executed.\n",
                  stderr);
        return 0;
    }

    int tty = isatty(0);                                /* REPL */
    if (tty) puts("Itzamna (C interpreter) - mut executes, Ctrl+D exits");
    static char *line;
    static size_t cap;
    for (;;) {
        if (setjmp(err_jmp)) { report_error(); reset_input(); }
        if (tty) { fputs(pending.n ? "...       " : "itzamna> ", stdout); fflush(stdout); }
        if (getline(&line, &cap, stdin) < 0) break;
        TokVec tv = {0};
        tokenize(line, &tv);
        feed(&tv);
        free(tv.a);
        fflush(stdout);
    }
    if (tty) putchar('\n');
    return 0;
}

/* Deep recursion in Itzamna programs needs a deep C stack.  Instead of running on a
 * second thread (which slows malloc down for the whole process) the stack limit is
 * raised and the program re-executes itself once, so the main thread gets the big stack.
 * If that is impossible, the call limit is lowered to what the current stack can take. */
#define STACK_WANTED ((rlim_t)1 << 30)
#define STACK_PER_CALL 4096                             /* conservative C stack use of one Itzamna call */

int main(int argc, char **argv)
{
    struct rlimit rl;
    if (getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY) {
        if (rl.rlim_cur < STACK_WANTED && !getenv("ITZAMNA_STACK_SET")) {
            rlim_t target = (rl.rlim_max == RLIM_INFINITY || rl.rlim_max >= STACK_WANTED)
                            ? STACK_WANTED : rl.rlim_max;
            if (target > rl.rlim_cur) {
                struct rlimit nl = { target, rl.rlim_max };
                if (setrlimit(RLIMIT_STACK, &nl) == 0) {
                    setenv("ITZAMNA_STACK_SET", "1", 1);
                    execv("/proc/self/exe", argv);      /* the new limit applies to the new image */
                }
            }
        }
        if (getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY) {
            long fit = (long)(rl.rlim_cur / STACK_PER_CALL);
            if (fit < max_calls) max_calls = fit;
        }
    }
    return real_main(argc, argv);
}
