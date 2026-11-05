/* Sort-based duplicate-key check. */
#include "dupcheck_internal.h"

/* Scratch layout:
 *   walker frames  (D + 1) * sizeof(walk_frame)
 *   walker keys    D * N * 4        (key offsets of each open map)
 *   sort aux       N * 4            (merge buffer for the map being closed)
 *   comparator     (D - 1) * 3 * N * 4
 */
size_t dupcheck_sort_scratch_size(size_t D, size_t N) {
  return add_sat(add_sat(walk_scratch_size(D, N),
                         align8(mul_sat(N, sizeof(uint32_t)))),
                 canon_scratch_size(D, N));
}

typedef struct {
  canon_ctx c;
  uint32_t *aux;
} sort_env;

static dup_result sort_on_map(void *env, uint32_t *keys, uint32_t n) {
  sort_env *e = env;
  if (!canon_sort(&e->c, keys, e->aux, n, 0)) return DUP_DUPLICATE;
  return DUP_OK;
}

dup_result dupcheck_sort(const uint8_t *buf, size_t len, size_t D, size_t N,
                         unsigned flags, void *scratch, size_t scratch_size) {
  if (len >= UINT32_MAX || N >= UINT32_MAX / 2 || D >= UINT32_MAX)
    return DUP_INPUT_TOO_LARGE;
  if (scratch_size < dupcheck_sort_scratch_size(D, N))
    return DUP_SCRATCH_TOO_SMALL;
  uint8_t *p = scratch;
  walk_frame *frames = (walk_frame *)p;
  p += align8((D + 1) * sizeof(walk_frame));
  uint32_t *keys = (uint32_t *)p;
  p += align8(D * N * sizeof(uint32_t));
  sort_env e;
  e.aux = (uint32_t *)p;
  p += align8(N * sizeof(uint32_t));
  e.c = (canon_ctx){ .buf = buf, .lv = (uint32_t *)p, .N = (uint32_t)N,
                     .nlevels = D > 0 ? (uint32_t)D - 1 : 0 };
  dup_result r = walk_maps(buf, (uint32_t)len, (uint32_t)D, (uint32_t)N,
                           flags, frames, keys, sort_on_map, &e);
  if (e.c.overflow) return DUP_BOUND_EXCEEDED; /* unreachable on WF input */
  return r;
}
