/* Benchmarks for the duplicate-key check prototypes. Prints CSV:
 *   family,param,bytes,D,N,variant,ns,result,cmp_calls,map_cmps,hash_calls,probes,scratch
 * Variants:
 *   wf           verified validate_raw_data_item (well-formedness only)
 *   verified-b   verified cbor_nondet_validate_bounded(D, N)
 *   verified-u   verified unbounded nondet validator
 *   sort         dupcheck_sort
 *   hash-canon   dupcheck_hash, canonical confirmation
 *   hash-naive   dupcheck_hash, naive confirmation
 *   hash0-canon  dupcheck_hash with all hashes forced to 0 (worst case)
 * Times are per call (median of 5 batches of >= 20 ms; a single call if it takes > 0.1 s). A variant whose
 * single call exceeds CAP_NS (0.5 s) is not run on larger parameters of the family.
 */
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include "dupcheck.h"
#include "verified_wrap.h"
#include "gen.h"

#define CAP_NS 5e8
#define BUF_SIZE (64u << 20)
static uint8_t *buf;
static const uint8_t hkey[16] = { 0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a, 0x69,
                                  0x78, 0x87, 0x96, 0xa5, 0xb4, 0xc3, 0xd2,
                                  0xe1, 0xf0 };

static double now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

enum { WF, VB, VU, SORT, HCANON, HNAIVE, H0CANON, NV };
static const char *vname[NV] = { "wf", "verified-b", "verified-u", "sort",
                                 "hash-canon", "hash-naive", "hash0-canon" };

static size_t scratch_size(int v, size_t D, size_t N) {
  switch (v) {
  case SORT: return dupcheck_sort_scratch_size(D, N);
  case HCANON: case H0CANON: return dupcheck_hash_scratch_size(D, N, DUP_CONFIRM_CANON);
  case HNAIVE: return dupcheck_hash_scratch_size(D, N, DUP_CONFIRM_NAIVE);
  default: return 0;
  }
}

/* returns 0 = accept, else the dup_result / 1 for verified rejections */
static int call(int v, size_t len, size_t D, size_t N, void *s, size_t sz) {
  switch (v) {
  case WF: return verified_wf(buf, len) == len ? 0 : 1;
  case VB: return verified_bounded(D, N, buf, len) == len ? 0 : 1;
  case VU: return verified_unbounded(buf, len) == len ? 0 : 1;
  case SORT: return dupcheck_sort(buf, len, D, N, 0, s, sz);
  case HCANON: return dupcheck_hash(buf, len, D, N, 0, DUP_CONFIRM_CANON, hkey, s, sz);
  case H0CANON: {
    dupcheck_hash_mask = 0;
    int r = dupcheck_hash(buf, len, D, N, 0, DUP_CONFIRM_CANON, hkey, s, sz);
    dupcheck_hash_mask = ~0ULL;
    return r;
  }
  default: return dupcheck_hash(buf, len, D, N, 0, DUP_CONFIRM_NAIVE, hkey, s, sz);
  }
}

static int cmpd(const void *a, const void *b) {
  double x = *(const double *)a, y = *(const double *)b;
  return x < y ? -1 : x > y;
}

static bool capped[NV];

static void measure(const char *fam, double param, size_t len, size_t D,
                    size_t N, unsigned variants) {
  if (verified_wf(buf, len) != len) {
    fprintf(stderr, "%s %g: input not well-formed\n", fam, param);
    exit(1);
  }
  for (int v = 0; v < NV; v++) {
    if (!(variants & (1u << v)) || capped[v]) continue;
    size_t sz = scratch_size(v, D, N);
    void *s = malloc(sz ? sz : 1);
    dup_stats = (dup_stats_t){ 0 };
    double t0 = now_ns();
    int r = call(v, len, D, N, s, sz);
    double one = now_ns() - t0;
    dup_stats_t st = dup_stats;
    double med = one;
    if (one > CAP_NS) capped[v] = true;
    if (one < 1e8) {
      unsigned iters = one > 0 ? (unsigned)(2e7 / (one + 1)) + 1 : 1000;
      double res[5];
      for (int k = 0; k < 5; k++) {
        t0 = now_ns();
        for (unsigned i = 0; i < iters; i++) (void)call(v, len, D, N, s, sz);
        res[k] = (now_ns() - t0) / iters;
      }
      qsort(res, 5, sizeof(double), cmpd);
      med = res[2];
    }
    printf("%s,%g,%zu,%zu,%zu,%s,%.0f,%d,%llu,%llu,%llu,%llu,%zu\n", fam, param,
           len, D, N, vname[v], med, r, (unsigned long long)st.cmp_calls,
           (unsigned long long)st.map_cmps, (unsigned long long)st.hash_calls,
           (unsigned long long)st.probes, sz);
    fflush(stdout);
    free(s);
  }
}
static void start_family(void) { for (int v = 0; v < NV; v++) capped[v] = false; }

#define ALL ((1u << NV) - 1)
#define NO_H0 (ALL & ~(1u << H0CANON))
#define NO_VU (ALL & ~(1u << VU))

static void shuffle(uint64_t *a, size_t n) {
  for (size_t i = n; i > 1; i--) {
    size_t j = rng_below(i);
    uint64_t t = a[i - 1]; a[i - 1] = a[j]; a[j] = t;
  }
}
static uint64_t *perm_buf;
static uint64_t *perm(size_t n) {
  for (size_t i = 0; i < n; i++) perm_buf[i] = i;
  shuffle(perm_buf, n);
  return perm_buf;
}

/* ---------------- families ---------------- */

/* A1: map of n distinct integer keys (shuffled, minimal), values 0. */
static size_t gen_wide_int(size_t n, unsigned w) {
  uint64_t *p = perm(n);
  size_t o = emit_head(buf, 0, 5, n);
  for (size_t i = 0; i < n; i++) {
    o = emit_head_w(buf, o, 0, p[i], w);
    o = emit_head(buf, o, 0, 0);
  }
  return o;
}

/* A2: n byte-string keys of length L sharing a common prefix; they only
 * differ in their last 4 bytes. */
static size_t gen_wide_prefix(size_t n, size_t L) {
  uint64_t *p = perm(n);
  size_t o = emit_head(buf, 0, 5, n);
  for (size_t i = 0; i < n; i++) {
    o = emit_head(buf, o, 2, L);
    memset(buf + o, 'x', L - 4);
    for (int k = 0; k < 4; k++) buf[o + L - 4 + k] = (uint8_t)(p[i] >> (24 - 8 * k));
    o += L;
    o = emit_head(buf, o, 0, 0);
  }
  return o;
}

/* A4: array of m maps {1: -7, 4: h'kid...', 3: "application/cbor",
 * 33: [h'cert', h'cert'], -1: 1, -2: h'x'*32, -3: h'y'*32, 5: h'nonce'}
 * (COSE-like headers/keys), entries in a fixed non-sorted order. */
static size_t gen_cose_like(size_t m) {
  static const uint8_t cert[64] = { 0 };
  size_t o = emit_head(buf, 0, 4, m);
  for (size_t i = 0; i < m; i++) {
    o = emit_head(buf, o, 5, 8);
    o = emit_head(buf, o, 0, 1); o = emit_head(buf, o, 1, 6);
    o = emit_head(buf, o, 0, 4); o = emit_bytes(buf, o, (const uint8_t *)"kid-0001", 8);
    o = emit_head(buf, o, 0, 3);
    o = emit_head(buf, o, 3, 16); memcpy(buf + o, "application/cbor", 16); o += 16;
    o = emit_head(buf, o, 0, 33); o = emit_head(buf, o, 4, 2);
    o = emit_bytes(buf, o, cert, 64); o = emit_bytes(buf, o, cert, 64);
    o = emit_head(buf, o, 1, 0); o = emit_head(buf, o, 0, 1);
    o = emit_head(buf, o, 1, 1); o = emit_bytes(buf, o, cert, 32);
    o = emit_head(buf, o, 1, 2); o = emit_bytes(buf, o, cert, 32);
    o = emit_head(buf, o, 0, 5); o = emit_bytes(buf, o, cert, 12);
  }
  return o;
}

/* A5: {0: {0: ... {0: 0}}}, d nested maps in values. */
static size_t gen_map_chain(size_t d) {
  size_t o = 0;
  for (size_t i = 0; i < d; i++) {
    o = emit_head(buf, o, 5, 1);
    o = emit_head(buf, o, 0, 0);
  }
  return emit_head(buf, o, 0, 0);
}

/* B1: {K_d: 0, K_d: 0}, K_0 = 0, K_d = {K_{d-1}: 0, -1: 0} (map depth d+1;
 * exponential for the verified unbounded validator). */
static size_t gen_dupkey_key(size_t o, size_t d) {
  if (d == 0) return emit_head(buf, o, 0, 0);
  o = emit_head(buf, o, 5, 2);
  o = gen_dupkey_key(o, d - 1);
  o = emit_head(buf, o, 0, 0);
  o = emit_head(buf, o, 1, 0);
  return emit_head(buf, o, 0, 0);
}
static size_t gen_map_dupkey(size_t d) {
  size_t o = emit_head(buf, 0, 5, 2);
  for (int i = 0; i < 2; i++) { o = gen_dupkey_key(o, d); o = emit_head(buf, o, 0, 0); }
  return o;
}

/* B2: map with n keys, each a map of m integer entries {j: 0} (j < m-1)
 * plus {m-1: i}, entries shuffled independently in each key: keys only
 * differ in the value of their largest entry, so every comparison has to
 * sort both maps. If dup, the last key is a re-shuffled copy of the first. */
static size_t gen_resort(size_t n, size_t m, bool dup) {
  uint64_t *p = malloc(n * sizeof(uint64_t));
  for (size_t i = 0; i < n; i++) p[i] = i;
  shuffle(p, n);
  size_t o = emit_head(buf, 0, 5, n);
  for (size_t i = 0; i < n; i++) {
    uint64_t id = (dup && i == n - 1) ? p[0] : p[i];
    o = emit_head(buf, o, 5, m);
    uint64_t *q = perm(m);
    for (size_t j = 0; j < m; j++) {
      o = emit_head(buf, o, 0, q[j]);
      o = emit_head(buf, o, 0, q[j] == m - 1 ? id : 0);
    }
    o = emit_head(buf, o, 0, 0);
  }
  free(p);
  return o;
}

/* B3: nested re-sorting. item(0, x) = x; item(t, x) = map whose keys are
 * item(t-1, j) for j < m-1 and item(t-1, BIG + x), all values 0, entries
 * shuffled. Two item(t, ·) only differ in their largest key, and so on
 * recursively: with O(D) memory, comparing them re-sorts every nested map,
 * so the sort variant costs ~(2 m log m + m)^t per comparison while the
 * input size is ~m^t. Root: map with n keys item(t, i). Map depth t + 1. */
static size_t gen_item(size_t o, size_t t, size_t m, uint64_t x) {
  if (t == 0) return emit_head(buf, o, 0, x);
  o = emit_head(buf, o, 5, m);
  uint64_t q[16];
  for (size_t j = 0; j < m; j++) q[j] = j;
  for (size_t j = m; j > 1; j--) {
    size_t k = rng_below(j); uint64_t tt = q[j - 1]; q[j - 1] = q[k]; q[k] = tt;
  }
  for (size_t j = 0; j < m; j++) {
    o = gen_item(o, t - 1, m, q[j] == m - 1 ? 1000 + x : q[j]);
    o = emit_head(buf, o, 0, 0);
  }
  return o;
}
static size_t gen_nested_resort(size_t t, size_t m, size_t n) {
  size_t o = emit_head(buf, 0, 5, n);
  for (size_t i = 0; i < n; i++) {
    o = gen_item(o, t, m, i);
    o = emit_head(buf, o, 0, 0);
  }
  return o;
}

/* B6: map with n keys, each an array of k maps of m shuffled integer
 * entries; keys only differ in the last map. A single key holds k maps:
 * their sorted forms cannot all be cached in O(D N) memory. */
static size_t gen_array_of_maps_key(size_t n, size_t k, size_t m) {
  size_t o = emit_head(buf, 0, 5, n);
  for (size_t i = 0; i < n; i++) {
    o = emit_head(buf, o, 4, k);
    for (size_t a = 0; a < k; a++) {
      o = emit_head(buf, o, 5, m);
      uint64_t *q = perm(m);
      for (size_t j = 0; j < m; j++) {
        o = emit_head(buf, o, 0, q[j]);
        o = emit_head(buf, o, 0, (a == k - 1 && q[j] == m - 1) ? i : 0);
      }
    }
    o = emit_head(buf, o, 0, 0);
  }
  return o;
}

int main(int argc, char **argv) {
  bool quick = argc > 1 && !strcmp(argv[1], "quick");
  buf = malloc(BUF_SIZE);
  perm_buf = malloc(sizeof(uint64_t) * (1u << 22));
  printf("family,param,bytes,D,N,variant,ns,result,cmp_calls,map_cmps,"
         "hash_calls,probes,scratch\n");
  size_t maxn = quick ? (1u << 12) : (1u << 20);

  start_family();
  for (size_t n = 16; n <= maxn; n *= 4) {
    size_t len = gen_wide_int(n, 0);
    measure("A1_wide_int", (double)n, len, 1, n, ALL);
  }
  start_family();
  for (size_t n = 16; n <= maxn; n *= 4) {
    size_t len = gen_wide_int(n, 8);
    measure("A3_wide_int_8byte", (double)n, len, 1, n, NO_H0);
  }
  start_family();
  for (size_t n = 16; n <= maxn / 16; n *= 4) {
    size_t len = gen_wide_prefix(n, 256);
    measure("A2_wide_prefix_L256", (double)n, len, 1, n, ALL);
  }
  start_family();
  for (size_t m = 16; m <= maxn / 4; m *= 4) {
    size_t len = gen_cose_like(m);
    measure("A4_cose_like_array", (double)m, len, 2, 8, NO_H0);
  }
  start_family();
  for (size_t d = 16; d <= (quick ? 1024u : 16384u); d *= 4) {
    size_t len = gen_map_chain(d);
    measure("A5_map_chain", (double)d, len, d, 1, NO_H0);
  }
  start_family();
  for (size_t d = 2; d <= (quick ? 16u : 64u); d += 2) {
    size_t len = gen_map_dupkey(d);
    measure("B1_map_dupkey", (double)d, len, d + 1, 2, NO_H0);
  }
  start_family();
  for (size_t n = 16; n <= maxn / 64; n *= 4) {
    size_t len = gen_resort(n, 32, false);
    measure("B2_resort_n_m32", (double)n, len, 2, n > 32 ? n : 32, NO_H0);
  }
  start_family();
  for (size_t m = 4; m <= maxn / 64; m *= 4) {
    size_t len = gen_resort(64, m, false);
    measure("B2_resort_m_n64", (double)m, len, 2, m > 64 ? m : 64, NO_H0);
  }
  start_family();
  for (size_t n = 16; n <= maxn / 64; n *= 4) {
    size_t len = gen_resort(n, 32, true);
    measure("B4_resort_dup_n_m32", (double)n, len, 2, n > 32 ? n : 32, NO_H0);
  }
  start_family();
  for (size_t t = 1; t <= (quick ? 5u : 9u); t++) {
    size_t len = gen_nested_resort(t, 4, 8);
    measure("B3_nested_resort_m4_n8", (double)t, len, t + 1, 8, NO_H0);
  }
  start_family();
  for (size_t k = 1; k <= (quick ? 64u : 4096u); k *= 4) {
    size_t len = gen_array_of_maps_key(64, k, 16);
    measure("B6_array_of_maps_key_n64_m16", (double)k, len, 2, 64, NO_H0);
  }
  /* hash collision worst case: everything collides */
  start_family();
  for (size_t n = 16; n <= (quick ? 1024u : 16384u); n *= 2) {
    size_t len = gen_wide_int(n, 0);
    measure("A6_wide_int_allcollide", (double)n, len, 1, n,
            (1u << H0CANON) | (1u << SORT) | (1u << HCANON));
  }
  start_family();
  for (size_t n = 16; n <= (quick ? 256u : 2048u); n *= 2) {
    size_t len = gen_resort(n, 32, false);
    measure("B5_resort_allcollide_m32", (double)n, len, 2, n > 32 ? n : 32,
            (1u << H0CANON) | (1u << SORT) | (1u << HCANON));
  }
  return 0;
}
