/* Collision attacks on dupcheck_hash by an attacker who KNOWS the SipHash
 * key (e.g. a fixed, leaked or caller-misused key). Each crafted input is
 * then checked with the known key and with a fresh secret key.
 *
 *   bucket  t: 2^t integer keys whose hashes share the low log2(cap) bits,
 *              i.e. all land in the same open-addressing bucket. Costs
 *              ~2^t * cap SipHash evaluations to craft.
 *   mapsum t: 2^t distinct maps (2t entries each) used as keys, all with the
 *              same full 64-bit hash. A map is hashed through the sum of its
 *              entry hashes mod 2^64, so one 4-sum collision
 *                E(a,x) + E(b,y) = E(a,x') + E(b,y')
 *              per pair of keys (a, b), found by a Wagner-style merge on
 *              2^L-element lists (~2^(L+1) hashes, L = 22), gives two
 *              interchangeable halves; t independent such collisions give
 *              2^t maps with equal sums (Joux-style multicollision).
 */
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "dupcheck.h"
#include "dupcheck_internal.h"
#include "verified_wrap.h"
#include "gen.h"

static const uint8_t known[16] = { 0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a, 0x69,
                                   0x78, 0x87, 0x96, 0xa5, 0xb4, 0xc3, 0xd2,
                                   0xe1, 0xf0 };
static uint8_t secret[16];

static double now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

/* Must match dupcheck_hash.c (feed_head, entry_hash). */
static uint64_t h_uint(uint64_t v) {
  uint8_t t[9];
  t[0] = MT_UINT;
  for (int i = 0; i < 8; i++) t[1 + i] = (uint8_t)(v >> (8 * i));
  sip_state s;
  sip_init(&s, known);
  sip_update(&s, t, 9, 1);
  return sip_final(&s, 1, 3);
}
static uint64_t h_entry(uint64_t hk, uint64_t hv) {
  uint8_t t[16];
  for (int j = 0; j < 8; j++) {
    t[j] = (uint8_t)(hk >> (8 * j));
    t[8 + j] = (uint8_t)(hv >> (8 * j));
  }
  sip_state s;
  sip_init(&s, known);
  sip_update(&s, t, 16, 1);
  return sip_final(&s, 1, 3);
}

typedef struct { uint64_t v; uint32_t x, y; } ent;
static int cmp_low;
static uint64_t low_mask;
static int cmp_ent(const void *p, const void *q) {
  uint64_t a = ((const ent *)p)->v, b = ((const ent *)q)->v;
  if (cmp_low) { a &= low_mask; b &= low_mask; }
  return a < b ? -1 : a > b;
}

/* Finds (x,y) != (x',y') with E(a,x)+E(b,y) = E(a,x')+E(b,y') mod 2^64. */
#define L 22
static int four_sum1(uint64_t a, uint64_t b, uint32_t base, uint32_t out[4]) {
  size_t n = (size_t)1 << L;
  ent *A = malloc(n * sizeof(ent)), *B = malloc(n * sizeof(ent));
  ent *P = malloc(4 * n * sizeof(ent));
  uint64_t ha = h_uint(a), hb = h_uint(b);
  for (uint32_t i = 0; i < n; i++) {
    A[i] = (ent){ h_entry(ha, h_uint(base + i)), base + i, 0 };
    B[i] = (ent){ h_entry(hb, h_uint(base + i)), 0, base + i };
  }
  low_mask = n - 1; cmp_low = 1;
  qsort(B, n, sizeof(ent), cmp_ent);
  size_t np = 0;
  for (size_t i = 0; i < n && np < 4 * n; i++) {
    uint64_t want = (0 - A[i].v) & low_mask;
    size_t lo = 0, hi = n;                 /* first B with low >= want */
    while (lo < hi) {
      size_t m = (lo + hi) / 2;
      if ((B[m].v & low_mask) < want) lo = m + 1; else hi = m;
    }
    for (; lo < n && (B[lo].v & low_mask) == want && np < 4 * n; lo++)
      P[np++] = (ent){ A[i].v + B[lo].v, A[i].x, B[lo].y };
  }
  cmp_low = 0;
  qsort(P, np, sizeof(ent), cmp_ent);
  for (size_t i = 1; i < np; i++)
    if (P[i].v == P[i - 1].v) {
      out[0] = P[i - 1].x; out[1] = P[i - 1].y;
      out[2] = P[i].x;     out[3] = P[i].y;
      free(A); free(B); free(P);
      return 1;
    }
  free(A); free(B); free(P);
  return 0;
}

/* Each attempt finds ~2 collisions on average; retry with fresh values. */
static void four_sum(uint64_t a, uint64_t b, uint32_t out[4]) {
  for (uint32_t base = 0; !four_sum1(a, b, base, out); base += 1u << L)
    fprintf(stderr, "no 4-sum collision for (%llu,%llu), retrying\n",
            (unsigned long long)a, (unsigned long long)b);
}

static uint8_t *buf;
static void *scr;

static void run(const char *atk, int t, size_t len, size_t D, size_t N) {
  if (verified_wf(buf, len) != len) { fprintf(stderr, "not WF\n"); exit(1); }
  struct { const char *name; int v; } vs[] = {
    { "wf", 0 }, { "sort", 1 }, { "hash-canon/known-key", 2 },
    { "hash-canon/secret-key", 3 }, { "hash-naive/known-key", 4 } };
  for (size_t k = 0; k < sizeof vs / sizeof vs[0]; k++) {
    if (vs[k].v == 4 && D > 1 && t > 10) continue;  /* too slow */
    size_t sz = 0;
    int r = 0;
    double best = 1e30;
    for (int rep = 0; rep < 3; rep++) {
      memset(&dup_stats, 0, sizeof dup_stats);
      double t0 = now_ns();
      switch (vs[k].v) {
      case 0: r = verified_wf(buf, len) == len ? 0 : 1; break;
      case 1: sz = dupcheck_sort_scratch_size(D, N);
              r = dupcheck_sort(buf, len, D, N, 0, scr, sz); break;
      case 2: case 3: sz = dupcheck_hash_scratch_size(D, N, DUP_CONFIRM_CANON);
              r = dupcheck_hash(buf, len, D, N, 0, DUP_CONFIRM_CANON,
                                vs[k].v == 2 ? known : secret, scr, sz); break;
      default: sz = dupcheck_hash_scratch_size(D, N, DUP_CONFIRM_NAIVE);
              r = dupcheck_hash(buf, len, D, N, 0, DUP_CONFIRM_NAIVE, known,
                                scr, sz); break;
      }
      double dt = now_ns() - t0;
      if (dt < best) best = dt;
      if (dt > 2e9) break;
    }
    printf("%s,%d,%zu,%s,%.0f,%d,%llu,%llu,%llu\n", atk, t, len, vs[k].name,
           best, r, (unsigned long long)(dup_stats.cmp_calls + dup_stats.eq_calls),
           (unsigned long long)dup_stats.map_cmps,
           (unsigned long long)dup_stats.probes);
    fflush(stdout);
  }
}

static void bucket(int t) {
  size_t n = (size_t)1 << t, cap = 2 * n, o = 0;   /* table_cap(n) */
  double t0 = now_ns();
  o = emit_head(buf, o, MT_MAP, n);
  uint64_t k = 0;
  for (size_t i = 0; i < n; i++) {
    while (h_uint(k) & (cap - 1)) k++;
    o = emit_head(buf, o, MT_UINT, k++);
    o = emit_head(buf, o, MT_UINT, 0);
  }
  fprintf(stderr, "bucket t=%d: crafted in %.1f s\n", t, (now_ns() - t0) / 1e9);
  run("bucket", t, o, 1, n);
}

static uint32_t (*coll)[4];
static void mapsum(int t) {
  size_t n = (size_t)1 << t, o = 0;
  o = emit_head(buf, o, MT_MAP, n);
  for (size_t s = 0; s < n; s++) {
    o = emit_head(buf, o, MT_MAP, 2 * (uint64_t)t);
    for (int i = 0; i < t; i++) {
      int c = (s >> i) & 1;
      o = emit_head(buf, o, MT_UINT, 2 * (uint64_t)i);
      o = emit_head(buf, o, MT_UINT, coll[i][2 * c]);
      o = emit_head(buf, o, MT_UINT, 2 * (uint64_t)i + 1);
      o = emit_head(buf, o, MT_UINT, coll[i][2 * c + 1]);
    }
    o = emit_head(buf, o, MT_UINT, 0);
  }
  size_t N = n > 2 * (size_t)t ? n : 2 * (size_t)t;
  run("mapsum", t, o, 2, N);
}

int main(int argc, char **argv) {
  int tmax_b = argc > 1 ? atoi(argv[1]) : 14;
  int tmax_m = argc > 2 ? atoi(argv[2]) : 12;
  buf = malloc(64u << 20);
  scr = malloc(256u << 20);
  srand((unsigned)time(NULL));
  for (int i = 0; i < 16; i++) secret[i] = (uint8_t)rand();
  printf("attack,t,bytes,variant,ns,result,cmp_calls,map_cmps,probes\n");
  for (int t = 8; t <= tmax_b; t += 2) bucket(t);
  coll = malloc((size_t)tmax_m * sizeof *coll);
  double t0 = now_ns();
  for (int i = 0; i < tmax_m; i++) {
    four_sum(2 * (uint64_t)i, 2 * (uint64_t)i + 1, coll[i]);
    fprintf(stderr, "4-sum %d: (%u,%u) ~ (%u,%u), %.1f s total\n", i,
            coll[i][0], coll[i][1], coll[i][2], coll[i][3],
            (now_ns() - t0) / 1e9);
  }
  for (int t = 8; t <= tmax_m; t += 2) mapsum(t);
  return 0;
}
