/* Shared parts of the duplicate-key checks: canonical comparator, naive
 * equivalence, merge sort and the bounded map walker. */
#include "dupcheck_internal.h"

dup_stats_t dup_stats;

static int map_cmp(canon_ctx *c, uint32_t x, uint32_t y, uint32_t n,
                   uint32_t level, uint32_t *xe, uint32_t *ye);

int canon_cmp(canon_ctx *c, uint32_t x, uint32_t y, uint32_t level,
              uint32_t *xend, uint32_t *yend) {
  const uint8_t *b = c->buf;
  uint64_t pending = 1;
  while (pending > 0) {
    uint8_t mx, my; uint64_t vx, vy;
    pending--;
    x = rd_head(b, x, &mx, &vx);
    y = rd_head(b, y, &my, &vy);
    /* Order: major type, then argument (integer value, string length, array
     * length, map length, tag, simple value), then contents. */
    if (mx != my) return mx < my ? -1 : 1;
    if (vx != vy) return vx < vy ? -1 : 1;
    switch (mx) {
    case MT_BYTES: case MT_TEXT: {
      int r = memcmp(b + x, b + y, (size_t)vx);
      if (r) return r;
      x += (uint32_t)vx; y += (uint32_t)vy;
      break;
    }
    case MT_ARRAY: pending += vx; break;
    case MT_TAG: pending += 1; break;
    case MT_MAP:
      if (vx > 0) {
        int r = map_cmp(c, x, y, (uint32_t)vx, level, &x, &y);
        if (r) return r;
      }
      break;
    default: break;
    }
  }
  *xend = x; *yend = y;
  return 0;
}

/* Two valid maps with n entries each: sort both entry lists by key, then
 * compare (key, value) pairs lexicographically. Valid maps have pairwise
 * non-equivalent keys, so equal sorted lists <=> raw_equiv. */
static int map_cmp(canon_ctx *c, uint32_t x, uint32_t y, uint32_t n,
                   uint32_t level, uint32_t *xe, uint32_t *ye) {
  const uint8_t *b = c->buf;
  dup_stats.map_cmps++;
  if (level >= c->nlevels || n > c->N) { c->overflow = true; return 1; }
  uint32_t *ex = c->lv + (size_t)level * 3 * c->N;
  uint32_t *ey = ex + c->N;
  uint32_t *aux = ey + c->N;
  for (uint32_t i = 0; i < n; i++) {
    ex[i] = x; x = skip_item(b, skip_item(b, x));
    ey[i] = y; y = skip_item(b, skip_item(b, y));
  }
  *xe = x; *ye = y;
  /* Keys of valid maps are distinct: the return values can be ignored. */
  (void)canon_sort(c, ex, aux, n, level + 1);
  (void)canon_sort(c, ey, aux, n, level + 1);
  for (uint32_t i = 0; i < n; i++) {
    uint32_t vx, vy, e1, e2;
    int r = canon_cmp(c, ex[i], ey[i], level + 1, &vx, &vy);
    if (r) return r;
    r = canon_cmp(c, vx, vy, level + 1, &e1, &e2);
    if (r) return r;
  }
  return 0;
}

bool naive_eq(const uint8_t *b, uint32_t x, uint32_t y,
              uint32_t *xend, uint32_t *yend) {
  uint64_t pending = 1;
  while (pending > 0) {
    uint8_t mx, my; uint64_t vx, vy;
    pending--;
    x = rd_head(b, x, &mx, &vx);
    y = rd_head(b, y, &my, &vy);
    if (mx != my || vx != vy) return false;
    switch (mx) {
    case MT_BYTES: case MT_TEXT:
      if (memcmp(b + x, b + y, (size_t)vx)) return false;
      x += (uint32_t)vx; y += (uint32_t)vy;
      break;
    case MT_ARRAY: pending += vx; break;
    case MT_TAG: pending += 1; break;
    case MT_MAP: {
      /* Spec-like: every entry of x has an equivalent entry in y. Since both
       * maps are valid and have the same length, this is a bijection. */
      uint32_t y0 = y, kx = x;
      for (uint64_t i = 0; i < vx; i++) {
        uint32_t vxo = skip_item(b, kx);
        uint32_t ky = y0;
        bool found = false;
        for (uint64_t j = 0; j < vy; j++) {
          uint32_t vyo, e1, e2;
          if (naive_eq(b, kx, ky, &e1, &vyo)) {
            if (!naive_eq(b, vxo, vyo, &e1, &e2)) return false;
            found = true;
            break;
          }
          ky = skip_item(b, skip_item(b, ky));
        }
        if (!found) return false;
        kx = skip_item(b, vxo);
      }
      x = kx;
      for (uint64_t j = 0; j < vy; j++) y = skip_item(b, skip_item(b, y));
      break;
    }
    default: break;
    }
  }
  *xend = x; *yend = y;
  return true;
}

static inline int cmp_items(canon_ctx *c, uint32_t x, uint32_t y,
                            uint32_t level) {
  uint32_t e1, e2;
  if (level == 0) dup_stats.cmp_calls++;
  return canon_cmp(c, x, y, level, &e1, &e2);
}

#define RUN 8

/* Bottom-up merge sort with insertion-sorted runs. Any comparison returning
 * 0 aborts with false. This is complete: both insertion sort and merging
 * compare an element with its equivalent neighbour before placing it. */
bool canon_sort(canon_ctx *c, uint32_t *a, uint32_t *aux, uint32_t n,
                uint32_t level) {
  if (n < 2) return true;
  for (uint32_t s = 0; s < n; s += RUN) {
    uint32_t e = (s + RUN < n) ? s + RUN : n;
    for (uint32_t i = s + 1; i < e; i++) {
      uint32_t t = a[i], j = i;
      while (j > s) {
        int r = cmp_items(c, a[j - 1], t, level);
        if (r == 0) return false;
        if (r < 0) break;
        a[j] = a[j - 1];
        j--;
      }
      a[j] = t;
    }
  }
  uint32_t *src = a, *dst = aux;
  for (uint32_t w = RUN; w < n; w *= 2) {
    for (uint32_t lo = 0; lo < n; lo += 2 * w) {
      uint32_t mid = (lo + w < n) ? lo + w : n;
      uint32_t hi = (lo + 2 * w < n) ? lo + 2 * w : n;
      uint32_t i = lo, j = mid, k = lo;
      while (i < mid && j < hi) {
        int r = cmp_items(c, src[i], src[j], level);
        if (r == 0) return false;
        dst[k++] = (r < 0) ? src[i++] : src[j++];
      }
      while (i < mid) dst[k++] = src[i++];
      while (j < hi) dst[k++] = src[j++];
    }
    uint32_t *t = src; src = dst; dst = t;
  }
  if (src != a) memcpy(a, src, (size_t)n * sizeof(uint32_t));
  return true;
}

dup_result walk_maps(const uint8_t *buf, uint32_t len, uint32_t D,
                     uint32_t N, unsigned flags, walk_frame *frames,
                     uint32_t *keys, on_map_fn on_map, void *env) {
  (void)len;
  uint32_t o = 0, top = 0;
  frames[0] = (walk_frame){ .rem = 1 };
  for (;;) {
    walk_frame *f = &frames[top];
    if (f->sub == 0) {
      if (f->rem == 0) {
        if (top == 0) return DUP_OK;
        if (f->check) {
          dup_result r = on_map(env, keys + (size_t)(top - 1) * N, f->nkeys);
          if (r != DUP_OK) return r;
        }
        top--;
        continue;
      }
      if (f->is_map) {
        f->cur_is_key = ((2 * (uint64_t)f->n - f->rem) % 2) == 0;
        if (f->cur_is_key && f->check)
          keys[(size_t)(top - 1) * N + f->nkeys++] = o;
      }
      f->rem--;
      f->sub = 1;
      continue;
    }
    uint32_t h = o;
    uint8_t maj; uint64_t v;
    o = rd_head(buf, o, &maj, &v);
    f->sub--;
    switch (maj) {
    case MT_BYTES: case MT_TEXT: o += (uint32_t)v; break;
    case MT_ARRAY: f->sub += v; break;
    case MT_TAG: f->sub += 1; break;
    case MT_MAP: {
      if (top + 1 > D || v > N) return DUP_BOUND_EXCEEDED;
      walk_frame *g = &frames[top + 1];
      bool in_key = f->in_key || (f->is_map && f->check && f->cur_is_key);
      *g = (walk_frame){ .rem = 2 * v, .n = (uint32_t)v, .is_map = 1,
                         .in_key = in_key,
                         .check = !(flags & DUP_FLAG_ROOT_ONLY) || h == 0 ||
                                  in_key };
      top++;
      break;
    }
    default: break;
    }
  }
}

size_t walk_scratch_size(size_t D, size_t N) {
  return add_sat(align8(mul_sat(add_sat(D, 1), sizeof(walk_frame))),
                 align8(mul_sat(mul_sat(D, N), sizeof(uint32_t))));
}

size_t canon_scratch_size(size_t D, size_t N) {
  size_t levels = D > 0 ? D - 1 : 0;
  return align8(mul_sat(mul_sat(levels, 3), mul_sat(N, sizeof(uint32_t))));
}
