/* Hash-based duplicate-key check. */
#include "dupcheck_internal.h"

#define SIP_C 1
#define SIP_D 3

uint64_t dupcheck_hash_mask = ~(uint64_t)0;

typedef struct { uint64_t h; uint32_t off1; uint32_t pad; } slot;

static size_t table_cap(size_t N) {
  size_t cap = 2;
  while (cap < 2 * N) {
    if (cap > SIZE_MAX / 2) return SIZE_MAX;
    cap *= 2;
  }
  return cap;
}

/* Walker frame, extended with a SipHash stream for the current direct child
 * and the order-independent accumulator of the map's entry hashes. */
typedef struct {
  uint64_t rem, sub;
  uint32_t n, nkeys;
  uint8_t is_map, check, in_key, cur_is_key, hcur, in_child;
  sip_state s;     /* hash of the current direct child (if hcur) */
  uint64_t hk;     /* hash of the key of the current entry */
  uint64_t acc;    /* sum of H(H(k), H(v)) over finished entries */
} hframe;

/* Scratch layout:
 *   frames         (D + 1) * sizeof(hframe)
 *   key offsets    D * N * 4
 *   key hashes     D * N * 8
 *   table          cap(N) * 16, cap(N) = smallest power of 2 >= 2N
 *   comparator     (D - 1) * 3 * N * 4   (DUP_CONFIRM_CANON only)
 */
size_t dupcheck_hash_scratch_size(size_t D, size_t N, dup_confirm confirm) {
  size_t s = align8(mul_sat(add_sat(D, 1), sizeof(hframe)));
  s = add_sat(s, align8(mul_sat(mul_sat(D, N), sizeof(uint32_t))));
  s = add_sat(s, mul_sat(mul_sat(D, N), sizeof(uint64_t)));
  s = add_sat(s, mul_sat(table_cap(N), sizeof(slot)));
  if (confirm == DUP_CONFIRM_CANON) s = add_sat(s, canon_scratch_size(D, N));
  return s;
}

typedef struct {
  const uint8_t *buf;
  slot *table;
  dup_confirm confirm;
  canon_ctx c;
} hash_env;

static void feed_head(sip_state *s, uint8_t maj, uint64_t v) {
  uint8_t t[9];
  t[0] = maj;
  for (int i = 0; i < 8; i++) t[1 + i] = (uint8_t)(v >> (8 * i));
  sip_update(s, t, 9, SIP_C);
}

static uint64_t entry_hash(const uint8_t key[16], uint64_t hk, uint64_t hv) {
  uint8_t t[16];
  for (int j = 0; j < 8; j++) {
    t[j] = (uint8_t)(hk >> (8 * j));
    t[8 + j] = (uint8_t)(hv >> (8 * j));
  }
  sip_state es;
  sip_init(&es, key);
  sip_update(&es, t, 16, SIP_C);
  return sip_final(&es, SIP_C, SIP_D);
}

static bool confirm_eq(hash_env *e, uint32_t x, uint32_t y) {
  uint32_t e1, e2;
  if (e->confirm == DUP_CONFIRM_NAIVE) {
    dup_stats.eq_calls++;
    return naive_eq(e->buf, x, y, &e1, &e2);
  }
  dup_stats.cmp_calls++;
  return canon_cmp(&e->c, x, y, 0, &e1, &e2) == 0;
}

static dup_result dedup(hash_env *e, const uint32_t *keys,
                        const uint64_t *hs, uint32_t n) {
  if (n < 2) return DUP_OK;
  size_t cap = table_cap(n), m = cap - 1;
  memset(e->table, 0, cap * sizeof(slot));
  for (uint32_t i = 0; i < n; i++) {
    uint64_t h = hs[i] & dupcheck_hash_mask;
    size_t j = (size_t)h & m;
    while (e->table[j].off1 != 0) {
      dup_stats.probes++;
      if (e->table[j].h == h && confirm_eq(e, e->table[j].off1 - 1, keys[i]))
        return DUP_DUPLICATE;
      j = (j + 1) & m;
    }
    e->table[j].h = h;
    e->table[j].off1 = keys[i] + 1;
  }
  return DUP_OK;
}

/* Like walk_maps (canon.c), but every key is hashed while it is walked:
 * each open map holds one SipHash stream for its current direct child, so
 * the whole input is hashed once, with O(D) hash states. The hash of an
 * item is invariant under raw_equiv on valid items: integers are hashed by
 * (major type, value) whatever their encoding width; a map is hashed as
 * (MAP, n, sum of H(H(k), H(v)) over its entries), independently of the
 * order of its entries. */
static dup_result walk_hash(hash_env *e, uint32_t D, uint32_t N,
                            unsigned flags, const uint8_t key[16],
                            hframe *fr, uint32_t *keys, uint64_t *khash) {
  const uint8_t *b = e->buf;
  uint32_t o = 0, top = 0;
  memset(&fr[0], 0, sizeof(hframe));
  fr[0].rem = 1;
  for (;;) {
    hframe *f = &fr[top];
    if (f->sub == 0) {
      if (f->in_child) {          /* direct child finished */
        f->in_child = 0;
        if (f->hcur) {
          uint64_t h = sip_final(&f->s, SIP_C, SIP_D);
          if (f->cur_is_key) {
            f->hk = h;
            if (f->check) {
              khash[(size_t)(top - 1) * N + f->nkeys - 1] = h;
              dup_stats.hash_calls++;
            }
          } else
            f->acc += entry_hash(key, f->hk, h);
        }
      }
      if (f->rem == 0) {
        if (top == 0) return DUP_OK;
        if (f->check) {
          dup_result r = dedup(e, keys + (size_t)(top - 1) * N,
                               khash + (size_t)(top - 1) * N, f->nkeys);
          if (r != DUP_OK) return r;
        }
        hframe *p = &fr[top - 1];
        if (p->hcur) {
          feed_head(&p->s, MT_MAP, f->n);
          feed_head(&p->s, 0xff, f->acc);
        }
        top--;
        continue;
      }
      if (f->is_map) {
        f->cur_is_key = ((2 * (uint64_t)f->n - f->rem) % 2) == 0;
        if (f->cur_is_key && f->check)
          keys[(size_t)(top - 1) * N + f->nkeys++] = o;
        /* the key of a checked map, or anything inside such a key */
        f->hcur = (f->cur_is_key && f->check) || f->in_key;
        if (f->hcur) sip_init(&f->s, key);
      }
      f->rem--;
      f->sub = 1;
      f->in_child = 1;
      continue;
    }
    uint32_t h = o;
    uint8_t maj; uint64_t v;
    o = rd_head(b, o, &maj, &v);
    f->sub--;
    switch (maj) {
    case MT_BYTES: case MT_TEXT:
      if (f->hcur) {
        feed_head(&f->s, maj, v);
        sip_update(&f->s, b + o, (size_t)v, SIP_C);
      }
      o += (uint32_t)v;
      break;
    case MT_ARRAY: if (f->hcur) feed_head(&f->s, maj, v); f->sub += v; break;
    case MT_TAG: if (f->hcur) feed_head(&f->s, maj, v); f->sub += 1; break;
    case MT_MAP: {
      if (top + 1 > D || v > N) return DUP_BOUND_EXCEEDED;
      hframe *g = &fr[top + 1];
      bool in_key = f->hcur;
      g->rem = 2 * v; g->sub = 0; g->n = (uint32_t)v; g->nkeys = 0;
      g->is_map = 1; g->in_key = in_key; g->in_child = 0; g->hcur = 0;
      g->check = !(flags & DUP_FLAG_ROOT_ONLY) || h == 0 || in_key;
      g->acc = 0;
      top++;
      break;
    }
    default: if (f->hcur) feed_head(&f->s, maj, v); break;
    }
  }
}

dup_result dupcheck_hash(const uint8_t *buf, size_t len, size_t D, size_t N,
                         unsigned flags, dup_confirm confirm,
                         const uint8_t key[16],
                         void *scratch, size_t scratch_size) {
  if (len >= UINT32_MAX - 1 || N >= UINT32_MAX / 2 || D >= UINT32_MAX)
    return DUP_INPUT_TOO_LARGE;
  if (scratch_size < dupcheck_hash_scratch_size(D, N, confirm))
    return DUP_SCRATCH_TOO_SMALL;
  uint8_t *p = scratch;
  hframe *frames = (hframe *)p;
  p += align8((D + 1) * sizeof(hframe));
  uint32_t *keys = (uint32_t *)p;
  p += align8(D * N * sizeof(uint32_t));
  uint64_t *khash = (uint64_t *)p;
  p += D * N * sizeof(uint64_t);
  hash_env e = { .buf = buf, .table = (slot *)p, .confirm = confirm };
  p += table_cap(N) * sizeof(slot);
  e.c = (canon_ctx){ .buf = buf, .lv = (uint32_t *)p, .N = (uint32_t)N,
                     .nlevels = (confirm == DUP_CONFIRM_CANON && D > 0)
                                    ? (uint32_t)D - 1 : 0 };
  dup_result r = walk_hash(&e, (uint32_t)D, (uint32_t)N, flags, key, frames,
                           keys, khash);
  if (e.c.overflow) return DUP_BOUND_EXCEEDED; /* unreachable on WF input */
  return r;
}
