/* Unverified prototypes of map-key duplicate checks for non-deterministic
 * CBOR (EverCBOR nondet), meant to evaluate the practicality of a "weak"
 * nondet API that only checks well-formedness (validate_raw_data_item) and
 * leaves duplicate-key checking to a separate, bounded operation.
 *
 * Precondition of every check: buf[0..len) is exactly one data item accepted
 * by the verified validate_raw_data_item (well-formed raw CBOR: no floats, no
 * indefinite lengths, valid simple values and UTF-8).
 *
 * Semantics (matches CBOR.Spec.Raw.Nondet / Valid): the item is accepted iff
 *   - map_depth(item) <= D and every map has at most N entries
 *     (CBOR.Spec.Raw.Base.map_depth: a map counts 1, arrays/tags count 0);
 *   - no map has two keys that are equivalent (raw_equiv: integers compared
 *     by value regardless of encoding width, maps compared as sets of
 *     entries regardless of order and encoding).
 *
 * None of these functions allocates: all the memory they use is either the
 * caller-provided scratch buffer, whose size only depends on (D, N), or the
 * C stack, whose depth is O(D) (recursion only happens on maps nested inside
 * map keys, at most D - 1 levels).
 */
#ifndef DUPCHECK_H
#define DUPCHECK_H

#include <stddef.h>
#include <stdint.h>

typedef enum {
  DUP_OK = 0,
  DUP_DUPLICATE = 1,          /* some map has two equivalent keys */
  DUP_BOUND_EXCEEDED = 2,     /* map depth > D or some map length > N */
  DUP_SCRATCH_TOO_SMALL = 3,
  DUP_INPUT_TOO_LARGE = 4     /* offsets are 32-bit: len must be < 2^32 */
} dup_result;

/* Only check the keys of the root map (and, as required for the
 * equivalence of keys to be meaningful, every map nested inside those keys).
 * Maps nested in values of the root map are still walked (bounds are still
 * enforced) but their keys are not checked. */
#define DUP_FLAG_ROOT_ONLY 1u

/* Scratch buffers must be 8-byte aligned. */

/* Sort-based check: every map's keys are sorted with a bottom-up merge sort
 * under a canonical total order whose equality is raw_equiv on valid items.
 * Deterministic worst case, no secret. Maps nested in keys are re-sorted
 * each time they are compared (no input-dependent memory to cache them). */
size_t dupcheck_sort_scratch_size(size_t D, size_t N);
dup_result dupcheck_sort(const uint8_t *buf, size_t len, size_t D, size_t N,
                         unsigned flags, void *scratch, size_t scratch_size);

/* Hash-based check: every key is hashed with keyed SipHash-1-3 over a
 * canonical token stream (maps hashed as an order-independent sum of entry
 * hashes, so equivalent keys have equal hashes) and inserted into an
 * open-addressing table; hash hits are confirmed by an exact comparison:
 *   DUP_CONFIRM_CANON: canonical comparison (same as the sort variant;
 *                      needs the comparator scratch);
 *   DUP_CONFIRM_NAIVE: spec-like quadratic set inclusion on maps (no
 *                      scratch, but O(2^D)-style worst case on hash hits).
 * Expected time is linear for a secret, uniformly random key. */
typedef enum { DUP_CONFIRM_CANON = 0, DUP_CONFIRM_NAIVE = 1 } dup_confirm;
size_t dupcheck_hash_scratch_size(size_t D, size_t N, dup_confirm confirm);
dup_result dupcheck_hash(const uint8_t *buf, size_t len, size_t D, size_t N,
                         unsigned flags, dup_confirm confirm,
                         const uint8_t key[16],
                         void *scratch, size_t scratch_size);

/* Testing/benchmarking only: hashes are AND-ed with this mask before use
 * (default all ones). Setting it to 0 makes every pair of keys collide and
 * exhibits the confirmation worst case. */
extern uint64_t dupcheck_hash_mask;

/* Operation counters (not thread-safe; for benchmarks). */
typedef struct {
  uint64_t cmp_calls;      /* top-level key comparisons (canonical) */
  uint64_t eq_calls;       /* top-level key comparisons (naive) */
  uint64_t map_cmps;       /* nested map comparisons (each re-collects/sorts) */
  uint64_t hash_calls;     /* top-level key hashes */
  uint64_t probes;         /* hash table probes */
} dup_stats_t;
extern dup_stats_t dup_stats;

#endif
