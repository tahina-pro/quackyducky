/* Internal shared definitions: raw CBOR reader, item skipping, canonical
 * comparator, merge sort, map walker. Inputs are assumed well-formed. */
#ifndef DUPCHECK_INTERNAL_H
#define DUPCHECK_INTERNAL_H

#include <stdbool.h>
#include <string.h>
#include "dupcheck.h"

enum { MT_UINT = 0, MT_NEGINT = 1, MT_BYTES = 2, MT_TEXT = 3,
       MT_ARRAY = 4, MT_MAP = 5, MT_TAG = 6, MT_SIMPLE = 7 };

/* Read the head at offset o; return the offset just after it. */
static inline uint32_t rd_head(const uint8_t *b, uint32_t o,
                               uint8_t *maj, uint64_t *val) {
  uint8_t ib = b[o++];
  uint8_t ai = ib & 31;
  *maj = ib >> 5;
  if (ai < 24) { *val = ai; return o; }
  uint64_t v = 0;
  unsigned n = 1u << (ai - 24); /* 24..27 -> 1,2,4,8 (well-formed input) */
  for (unsigned i = 0; i < n; i++) v = (v << 8) | b[o + i];
  *val = v;
  return o + n;
}

/* Offset just after the item starting at o. Iterative. */
static inline uint32_t skip_item(const uint8_t *b, uint32_t o) {
  uint64_t pending = 1;
  while (pending > 0) {
    uint8_t maj; uint64_t v;
    pending--;
    o = rd_head(b, o, &maj, &v);
    switch (maj) {
    case MT_BYTES: case MT_TEXT: o += (uint32_t)v; break;
    case MT_ARRAY: pending += v; break;
    case MT_MAP: pending += 2 * v; break;
    case MT_TAG: pending += 1; break;
    default: break;
    }
  }
  return o;
}

/* Canonical comparator context. Level l (0 <= l < nlevels) owns three
 * arrays of N key offsets: ex (entries of the left map), ey (right map) and
 * aux (merge sort buffer). A comparison of two keys of a map starts at level
 * 0; a map nested at level l uses level l's arrays and compares its own
 * keys/values at level l + 1. */
typedef struct {
  const uint8_t *buf;
  uint32_t *lv;          /* nlevels * 3 * N */
  uint32_t N;
  uint32_t nlevels;
  bool overflow;         /* defensive: nesting deeper than nlevels */
} canon_ctx;

/* < 0, 0, > 0. On equal items, *xend and *yend are set to the item ends. */
int canon_cmp(canon_ctx *c, uint32_t x, uint32_t y, uint32_t level,
              uint32_t *xend, uint32_t *yend);

/* Naive structural equivalence (no scratch). */
bool naive_eq(const uint8_t *b, uint32_t x, uint32_t y,
              uint32_t *xend, uint32_t *yend);

/* Sort a[0..n) of item offsets with canon_cmp at `level`. Returns false iff
 * two equal items were found (duplicate). aux has room for n offsets. */
bool canon_sort(canon_ctx *c, uint32_t *a, uint32_t *aux, uint32_t n,
                uint32_t level);

/* Map walker: calls on_map(env, keys, n) when the map closes (post-order,
 * so all maps nested in its keys have already been checked), for every map
 * to be checked. Keys are given as offsets. */
typedef dup_result (*on_map_fn)(void *env, uint32_t *keys, uint32_t n);

typedef struct {
  uint64_t rem;    /* direct children (keys + values) not yet started */
  uint64_t sub;    /* pending items of the current direct child */
  uint32_t n;      /* number of entries (maps) */
  uint32_t nkeys;
  uint8_t is_map, check, in_key, cur_is_key;
} walk_frame;

/* frames: D + 1 frames; keys: D * N offsets. */
dup_result walk_maps(const uint8_t *buf, uint32_t len, uint32_t D,
                     uint32_t N, unsigned flags, walk_frame *frames,
                     uint32_t *keys, on_map_fn on_map, void *env);

/* Scratch layout helpers. */
static inline size_t align8(size_t x) { return (x + 7) & ~(size_t)7; }
/* a * b with saturation at SIZE_MAX */
static inline size_t mul_sat(size_t a, size_t b) {
  if (a != 0 && b > SIZE_MAX / a) return SIZE_MAX;
  return a * b;
}
static inline size_t add_sat(size_t a, size_t b) {
  return (a > SIZE_MAX - b) ? SIZE_MAX : a + b;
}
size_t walk_scratch_size(size_t D, size_t N);
size_t canon_scratch_size(size_t D, size_t N);

/* SipHash-c-d, streaming. */
typedef struct {
  uint64_t v0, v1, v2, v3;
  uint64_t m;        /* pending bytes, little-endian */
  unsigned mlen;     /* number of pending bytes (0..7) */
  uint64_t total;
} sip_state;
void sip_init(sip_state *s, const uint8_t key[16]);
void sip_update(sip_state *s, const uint8_t *p, size_t n, int c);
uint64_t sip_final(sip_state *s, int c, int d);

#endif
