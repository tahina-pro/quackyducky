/* Correctness tests for the duplicate-key check prototypes:
 *  - SipHash test vector;
 *  - hand-written cases;
 *  - differential random testing against the verified EverCBOR nondet
 *    validator (bounded and unbounded), on equivalence-heavy inputs (small
 *    value domain, non-minimal integer encodings, shuffled map entries,
 *    planted re-encoded duplicate keys);
 *  - DUP_FLAG_ROOT_ONLY against an oracle built from the verified validator;
 *  - scratch exactly sized (heap-allocated so that ASan catches overruns),
 *    one byte short -> DUP_SCRATCH_TOO_SMALL;
 *  - no allocation during a check (malloc & co. are wrapped at link time).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include "dupcheck.h"
#include "dupcheck_internal.h"
#include "verified_wrap.h"
#include "gen.h"

/* ---- allocation trap ---- */
static int forbid_alloc = 0;
void *__real_malloc(size_t); void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t); void __real_free(void *);
static void trap(const char *f) {
  fprintf(stderr, "FAIL: %s called during a duplicate check\n", f);
  abort();
}
void *__wrap_malloc(size_t n) { if (forbid_alloc) trap("malloc"); return __real_malloc(n); }
void *__wrap_calloc(size_t a, size_t n) { if (forbid_alloc) trap("calloc"); return __real_calloc(a, n); }
void *__wrap_realloc(void *p, size_t n) { if (forbid_alloc) trap("realloc"); return __real_realloc(p, n); }
void __wrap_free(void *p) { if (forbid_alloc) trap("free"); __real_free(p); }

static const uint8_t hkey[16] = { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
                                  14, 15, 16 };
static unsigned failures = 0;
#define CHECK(c, ...) do { if (!(c)) { failures++; \
  fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); \
  fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); } } while (0)

enum { V_SORT, V_HASH_CANON, V_HASH_NAIVE, V_HASH0_CANON, V_HASH0_NAIVE,
       NVARIANTS };
static const char *vname[] = { "sort", "hash-canon", "hash-naive",
                               "hash0-canon", "hash0-naive" };

static dup_result run(int v, const uint8_t *b, size_t len, size_t D, size_t N,
                      unsigned flags) {
  size_t sz = v == V_SORT ? dupcheck_sort_scratch_size(D, N)
            : dupcheck_hash_scratch_size(D, N,
                (v == V_HASH_NAIVE || v == V_HASH0_NAIVE)
                  ? DUP_CONFIRM_NAIVE : DUP_CONFIRM_CANON);
  void *s = malloc(sz ? sz : 1);
  dup_result r;
  dupcheck_hash_mask = (v == V_HASH0_CANON || v == V_HASH0_NAIVE) ? 0 : ~0ULL;
  forbid_alloc = 1;
  switch (v) {
  case V_SORT: r = dupcheck_sort(b, len, D, N, flags, s, sz); break;
  case V_HASH_CANON: case V_HASH0_CANON:
    r = dupcheck_hash(b, len, D, N, flags, DUP_CONFIRM_CANON, hkey, s, sz);
    break;
  default:
    r = dupcheck_hash(b, len, D, N, flags, DUP_CONFIRM_NAIVE, hkey, s, sz);
  }
  forbid_alloc = 0;
  dupcheck_hash_mask = ~0ULL;
  if (sz > 0) {
    dup_result r2;
    forbid_alloc = 1;
    if (v == V_SORT) r2 = dupcheck_sort(b, len, D, N, flags, s, sz - 1);
    else r2 = dupcheck_hash(b, len, D, N, flags, DUP_CONFIRM_NAIVE, hkey, s,
                            dupcheck_hash_scratch_size(D, N, DUP_CONFIRM_NAIVE) - 1);
    forbid_alloc = 0;
    CHECK(r2 == DUP_SCRATCH_TOO_SMALL, "scratch - 1 accepted (%s)", vname[v]);
  }
  free(s);
  return r;
}

/* All variants agree; returns their common result. */
static dup_result run_all(const uint8_t *b, size_t len, size_t D, size_t N,
                          unsigned flags) {
  dup_result r0 = run(V_SORT, b, len, D, N, flags);
  for (int v = 1; v < NVARIANTS; v++) {
    dup_result r = run(v, b, len, D, N, flags);
    CHECK(r == r0, "%s=%d but sort=%d (D=%zu N=%zu len=%zu)", vname[v], r, r0,
          D, N, len);
  }
  return r0;
}

/* ---- SipHash ---- */
static void test_siphash(void) {
  uint8_t k[16], m[64];
  for (int i = 0; i < 16; i++) k[i] = (uint8_t)i;
  for (int i = 0; i < 64; i++) m[i] = (uint8_t)i;
  sip_state s;
  sip_init(&s, k); sip_update(&s, m, 15, 2);
  CHECK(sip_final(&s, 2, 4) == 0xa129ca6149be45e5ULL, "siphash-2-4 vector");
  /* streaming == one-shot */
  for (size_t n = 0; n < 64; n++)
    for (size_t cut = 0; cut <= n; cut++) {
      sip_state a, b2;
      sip_init(&a, k); sip_update(&a, m, n, 1);
      sip_init(&b2, k); sip_update(&b2, m, cut, 1);
      sip_update(&b2, m + cut, n - cut, 1);
      CHECK(sip_final(&a, 1, 3) == sip_final(&b2, 1, 3), "siphash streaming");
    }
}

/* ---- hand-written cases ---- */
static void test_cases(void) {
  uint8_t b[256]; size_t o;
  struct { const char *name; dup_result expect; size_t D, N; } t;
#define CASE(nm, exp, d, n) t.name = nm; t.expect = exp; t.D = d; t.N = n; \
  CHECK(verified_wf(b, o) == o, "%s: not WF", t.name);                    \
  { dup_result r = run_all(b, o, t.D, t.N, 0);                           \
    CHECK(r == t.expect, "%s: got %d", t.name, r);                       \
    size_t vb = verified_bounded(t.D, t.N, b, o);                         \
    CHECK((vb == o) == (r == DUP_OK), "%s: verified=%zu", t.name, vb); }

  /* {1: 0, 1(non-minimal): 0} */
  o = emit_head(b, 0, 5, 2); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  o = emit_head_w(b, o, 0, 1, 8); o = emit_head(b, o, 0, 0);
  CASE("int-noncanon-dup", DUP_DUPLICATE, 1, 2);
  /* {0: 0, -1: 0} : major 0 and 1 with same argument are distinct */
  o = emit_head(b, 0, 5, 2); o = emit_head(b, o, 0, 0); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 1, 0); o = emit_head(b, o, 0, 0);
  CASE("int-sign-distinct", DUP_OK, 1, 2);
  /* {{1:2, 3:4}: 0, {3:4, 1:2}: 0} */
  o = emit_head(b, 0, 5, 2);
  o = emit_head(b, o, 5, 2); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 2);
  o = emit_head(b, o, 0, 3); o = emit_head(b, o, 0, 4); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 5, 2); o = emit_head(b, o, 0, 3); o = emit_head(b, o, 0, 4);
  o = emit_head(b, o, 0, 1); o = emit_head_w(b, o, 0, 2, 2); o = emit_head(b, o, 0, 0);
  CASE("map-key-permuted-dup", DUP_DUPLICATE, 2, 2);
  CASE("map-key-depth-bound", DUP_BOUND_EXCEEDED, 1, 2);
  CASE("map-key-length-bound", DUP_BOUND_EXCEEDED, 2, 1);
  /* {{1:2}: 0, {1:3}: 0} */
  o = emit_head(b, 0, 5, 2);
  o = emit_head(b, o, 5, 1); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 2);
  o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 5, 1); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 3);
  o = emit_head(b, o, 0, 0);
  CASE("map-key-distinct-values", DUP_OK, 2, 2);
  /* {{}: 0, {}: 1} */
  o = emit_head(b, 0, 5, 2); o = emit_head(b, o, 5, 0); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 5, 0); o = emit_head(b, o, 0, 1);
  CASE("empty-map-key-dup", DUP_DUPLICATE, 2, 2);
  /* [ {1:0, 1:0} ] : duplicate in a map below an array */
  o = emit_head(b, 0, 4, 1); o = emit_head(b, o, 5, 2);
  o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  CASE("dup-under-array", DUP_DUPLICATE, 1, 2);
  /* {0: {1:0, 1:0}} : duplicate in a map value */
  o = emit_head(b, 0, 5, 1); o = emit_head(b, o, 0, 0); o = emit_head(b, o, 5, 2);
  o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  CASE("dup-in-value", DUP_DUPLICATE, 2, 2);
  /* ... but not when only the root map is checked */
  CHECK(run(V_SORT, b, o, 2, 2, DUP_FLAG_ROOT_ONLY) == DUP_OK, "root-only value");
  CHECK(run(V_HASH_CANON, b, o, 2, 2, DUP_FLAG_ROOT_ONLY) == DUP_OK, "root-only value");
  /* {[{1:0,2:0}, h'61']: 0, [{2:0,1:0}, h'61']: 1} */
  o = emit_head(b, 0, 5, 2);
  for (int i = 0; i < 2; i++) {
    o = emit_head(b, o, 4, 2); o = emit_head(b, o, 5, 2);
    o = emit_head(b, o, 0, (uint64_t)(1 + i)); o = emit_head(b, o, 0, 0);
    o = emit_head(b, o, 0, (uint64_t)(2 - i)); o = emit_head(b, o, 0, 0);
    o = emit_bytes(b, o, (const uint8_t *)"a", 1); o = emit_head(b, o, 0, (uint64_t)i);
  }
  CASE("array-of-map-key-dup", DUP_DUPLICATE, 2, 2);
  /* tagged: {6(1): 0, 6(1 non-minimal): 0} */
  o = emit_head(b, 0, 5, 2); o = emit_head(b, o, 6, 6); o = emit_head(b, o, 0, 1);
  o = emit_head(b, o, 0, 0); o = emit_head_w(b, o, 6, 6, 4);
  o = emit_head_w(b, o, 0, 1, 2); o = emit_head(b, o, 0, 0);
  CASE("tag-noncanon-dup", DUP_DUPLICATE, 1, 2);
  /* D = 0, scalar ok, map rejected */
  o = emit_head(b, 0, 0, 5);
  CASE("scalar-D0", DUP_OK, 0, 0);
  o = emit_head(b, 0, 5, 0);
  CASE("map-D0", DUP_BOUND_EXCEEDED, 0, 0);
#undef CASE
}

/* ---- random equivalence-heavy generator ---- */
typedef struct node {
  uint8_t maj;
  uint64_t v;          /* value / length / tag / map entries */
  struct node **c;     /* children (maps: k0, v0, k1, v1, ...) */
  uint8_t s[3];
} node;

#define ARENA 200000
static node arena[ARENA];
static node *ptrs[4 * ARENA];
static size_t na, np;

static node *gen_node(int depth) {
  if (na >= ARENA || np + 16 >= 4 * ARENA) depth = 0;
  node *x = &arena[na++];
  unsigned r = (unsigned)rng_below(depth > 0 ? 12 : 5);
  switch (r) {
  case 0: x->maj = 0; x->v = rng_below(8) == 0 ? (1ULL << 40) : rng_below(3); break;
  case 1: x->maj = 1; x->v = rng_below(2); break;
  case 2: case 3:
    x->maj = (uint8_t)r; x->v = rng_below(3);
    for (unsigned i = 0; i < x->v; i++) x->s[i] = (uint8_t)('a' + rng_below(2));
    break;
  case 4: x->maj = 7; x->v = 20 + rng_below(2); break;
  case 5: case 6: {
    x->maj = 4; x->v = rng_below(4);
    x->c = &ptrs[np]; np += x->v;
    for (unsigned i = 0; i < x->v; i++) x->c[i] = gen_node(depth - 1);
    break;
  }
  case 7: case 8: case 9: case 10: {
    x->maj = 5; x->v = rng_below(5);
    x->c = &ptrs[np]; np += 2 * x->v;
    for (unsigned i = 0; i < x->v; i++) {
      x->c[2 * i] = gen_node(depth - 1);
      x->c[2 * i + 1] = gen_node(depth - 1);
    }
    /* plant an equivalent duplicate key (re-encoded at serialization) */
    if (x->v >= 2 && rng_below(3) == 0) {
      unsigned i = (unsigned)rng_below(x->v), j = (unsigned)rng_below(x->v);
      if (i != j) x->c[2 * j] = x->c[2 * i];
    }
    break;
  }
  default:
    x->maj = 6; x->v = rng_below(2);
    x->c = &ptrs[np]; np += 1;
    x->c[0] = gen_node(depth - 1);
  }
  return x;
}

static size_t ser(const node *x, uint8_t *b, size_t o) {
  o = emit_head_w(b, o, x->maj, x->v, rand_width(x->v));
  switch (x->maj) {
  case 2: case 3: memcpy(b + o, x->s, x->v); o += x->v; break;
  case 4: for (uint64_t i = 0; i < x->v; i++) o = ser(x->c[i], b, o); break;
  case 6: o = ser(x->c[0], b, o); break;
  case 5: {
    unsigned perm[8];
    for (unsigned i = 0; i < x->v; i++) perm[i] = i;
    for (unsigned i = (unsigned)x->v; i > 1; i--) {
      unsigned j = (unsigned)rng_below(i), t = perm[i - 1];
      perm[i - 1] = perm[j]; perm[j] = t;
    }
    for (unsigned i = 0; i < x->v; i++) {
      o = ser(x->c[2 * perm[i]], b, o);
      o = ser(x->c[2 * perm[i] + 1], b, o);
    }
    break;
  }
  default: break;
  }
  return o;
}

/* ROOT_ONLY oracle: the root map's keys are valid and pairwise not
 * equivalent; equivalence of two valid keys k1, k2 is decided by the
 * verified validator on {k1: 0, k2: 0}. */
static int root_only_oracle(const uint8_t *b, size_t len) {
  (void)len;
  uint8_t maj; uint64_t n;
  uint32_t o = rd_head(b, 0, &maj, &n);
  if (maj != MT_MAP) return 1;
  uint32_t ks[8], ke[8];
  for (uint64_t i = 0; i < n; i++) {
    ks[i] = o; ke[i] = skip_item(b, o); o = skip_item(b, ke[i]);
    if (verified_unbounded(b + ks[i], ke[i] - ks[i]) != ke[i] - ks[i]) return 0;
  }
  static uint8_t m[1 << 16];
  for (uint64_t i = 0; i < n; i++)
    for (uint64_t j = i + 1; j < n; j++) {
      size_t l = emit_head(m, 0, 5, 2);
      memcpy(m + l, b + ks[i], ke[i] - ks[i]); l += ke[i] - ks[i];
      l = emit_head(m, l, 0, 0);
      memcpy(m + l, b + ks[j], ke[j] - ks[j]); l += ke[j] - ks[j];
      l = emit_head(m, l, 0, 0);
      if (verified_unbounded(m, l) != l) return 0;
    }
  return 1;
}

static void test_random(unsigned iters) {
  static uint8_t b[1 << 16];
  unsigned stats[5] = { 0 }, nontrivial_root = 0;
  size_t total_len = 0, max_len = 0;
  for (unsigned it = 0; it < iters; it++) {
    na = np = 0;
    node *x = gen_node(1 + (int)rng_below(5));
    size_t len = ser(x, b, 0);
    if (len > sizeof(b) / 2) continue;
    CHECK(verified_wf(b, len) == len, "random input not WF");
    total_len += len; if (len > max_len) max_len = len;
    /* bounded, small random bounds */
    size_t D = rng_below(5), N = rng_below(6);
    dup_result r = run_all(b, len, D, N, 0);
    size_t vb = verified_bounded(D, N, b, len);
    CHECK((vb == len) == (r == DUP_OK),
          "bounded mismatch: ours=%d verified=%zu D=%zu N=%zu it=%u", r, vb,
          D, N, it);
    stats[r]++;
    /* effectively unbounded */
    r = run_all(b, len, 64, 64, 0);
    size_t vu = verified_unbounded(b, len);
    CHECK(r != DUP_BOUND_EXCEEDED, "unexpected bound");
    CHECK((vu == len) == (r == DUP_OK), "unbounded mismatch: ours=%d verified=%zu it=%u",
          r, vu, it);
    stats[3 + (r == DUP_OK)]++;
    /* root only */
    r = run_all(b, len, 64, 64, DUP_FLAG_ROOT_ONLY);
    int ro = root_only_oracle(b, len);
    CHECK(ro == (r == DUP_OK), "root-only mismatch: ours=%d oracle=%d it=%u", r, ro, it);
    if (b[0] >> 5 == MT_MAP && ro != (vu == len)) nontrivial_root++;
  }
  printf("random: avg len %zu, max len %zu\n", total_len / iters, max_len);
  printf("random: %u iterations; bounded: ok=%u dup=%u bound=%u; "
         "unbounded: dup=%u ok=%u; root-only differs from full: %u\n",
         iters, stats[0], stats[1], stats[2], stats[3], stats[4],
         nontrivial_root);
}

int main(int argc, char **argv) {
  unsigned iters = argc > 1 ? (unsigned)atoi(argv[1]) : 100000;
  test_siphash();
  test_cases();
  test_random(iters);
  if (failures) { printf("%u FAILURES\n", failures); return 1; }
  printf("all tests passed\n");
  return 0;
}
