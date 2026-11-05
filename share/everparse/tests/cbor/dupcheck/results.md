# Duplicate map key checks for nondet CBOR: unverified prototypes and benchmarks

## Context

PR #345 bounds the map depth `D` and map length `N` of the verified nondet
validator, but its duplicate-key check remains quadratic in `N` and, for
maps nested in map keys, exponential in `D` (`O(2^D * K^2)`). This directory
evaluates, *before* committing to verification, two alternative duplicate
checks meant for a "weak" nondet API: the parser only checks
well-formedness (`validate_raw_data_item`), and a separate operation checks
map keys under caller-chosen bounds `D` and `N`.

Both prototypes are unverified C (C11, `-Wall -Wextra -Wvla -Werror`). They:

- take a buffer already accepted by the verified `validate_raw_data_item`;
- accept iff `map_depth <= D`, every map has `<= N` entries, and no map
  has two `raw_equiv` keys (same semantics as `cbor_nondet_validate_bounded`);
- never allocate: the only memory is a caller-provided scratch buffer whose
  size depends only on `(D, N)` (`dupcheck_*_scratch_size`), plus `O(D)`
  C stack (recursion only on maps nested inside map keys);
- optionally (`DUP_FLAG_ROOT_ONLY`) only check the root map's keys (plus,
  necessarily, every map nested inside those keys), as in the "weak API"
  proposal.

## What is implemented

| File | Content |
|---|---|
| `dupcheck.h` | public API, result codes, flags |
| `dupcheck_internal.h` | head reader, iterative `skip_item`, shared types |
| `canon.c` | canonical comparator, naive equivalence, merge sort, bounded map walker |
| `dupcheck_sort.c` | sort-based check |
| `dupcheck_hash.c` | hash-based check (streaming hashing walker, open addressing) |
| `siphash.c` | streaming SipHash-c-d (1-3 used), checked against the 2-4 test vector |
| `verified_wrap.c` | includes the verified `CBORNondet.c` to expose `validate_raw_data_item`, `cbor_nondet_validate_bounded` and the unbounded validator (oracle and baseline) |
| `test_dupcheck.c`, `gen.h` | correctness tests |
| `bench_dupcheck.c`, `fit.py` | benchmarks and summary |
| `bench.csv`, `bench_fit.md` | raw and summarized benchmark results of the run below |

**Walker** (both variants). Iterative post-order walk with one frame per
open *map* (at most `D`, arrays and tags are handled with counters, so their
nesting is unbounded and costs no memory). Each frame stores the offsets of
its keys (`N` per frame). When a map closes, all maps inside its keys have
already been checked, so its keys are valid and can be compared with a
comparator that is only correct on valid items.

**Canonical comparator** (`canon_cmp`). A total order on valid items whose
equality is `raw_equiv`: major type, then argument (integer value whatever its
encoding width, string/array/map length, tag, simple value), then contents.
Arrays and tags are compared in lock-step without recursion. Two maps are
compared by collecting the entries of both into the level's scratch, merge
sorting both by key, then comparing keys and values pairwise; this recurses
(at most `D - 1` levels, one scratch level of `3N` offsets each).

**Sort variant.** At map close, bottom-up merge sort (insertion-sorted runs of
8) of the key offsets under `canon_cmp`; any comparison returning 0 is a
duplicate (complete: insertion and merging always compare an element with an
equivalent neighbour).

**Hash variant.** Keys are hashed *while being walked*: each open map frame
holds one SipHash-1-3 stream for its current direct child (so `O(D)` hash
states, and each byte is hashed once). The hash is invariant under
`raw_equiv` on valid items: integers are hashed as `(major, value)`, maps as
`(MAP, n, Σ H(H(k), H(v)) mod 2^64)`, independent of entry order. At map close
the key hashes go into an open-addressing table (power of two `>= 2n` slots,
prefix cleared in `O(n)`); hash hits are confirmed by `canon_cmp`
(`DUP_CONFIRM_CANON`) or by a spec-like quadratic set inclusion that needs no
scratch (`DUP_CONFIRM_NAIVE`). The 128-bit SipHash key must be secret and
random; correctness never depends on it, only performance does.
`dupcheck_hash_mask` (testing only) masks hashes to exhibit the all-collide
worst case (`hash0-canon` below); `attack_hash.c` shows it is reachable
with a known key.

### Scratch and stack

Exact formulas (`walk_frame` is 32 B, the hash frame is 104 B):

- sort: `32(D+1) + 4DN + 4N + 12(D-1)N` bytes;
- hash: `104(D+1) + 12DN + 16·pow2ceil(2N) [+ 12(D-1)N with CONFIRM_CANON]`.

| D | N | sort | hash-canon | hash-naive |
|---|---|---|---|---|
| 1 | 64 | 576 B | 3.0 KB | 3.0 KB |
| 1 | 1024 | 8.1 KB | 44 KB | 44 KB |
| 1 | 65536 | 512 KB | 2.8 MB | 2.8 MB |
| 2 | 1024 | 24 KB | 68 KB | 56 KB |
| 4 | 1024 | 56 KB | 117 KB | 81 KB |
| 16 | 64 | 16 KB | 27 KB | 16 KB |
| 16 | 1024 | 249 KB | 406 KB | 226 KB |
| 16 | 65536 | 15.5 MB | 25.3 MB | 14.0 MB |

The hash table dominates for small `D` (it could be halved with 8-byte
slots: 32-bit hash fragment + 32-bit offset). C stack (`gcc -O2
-fstack-usage`): about 350 B per level of maps nested in keys for the
canonical comparator (`canon_cmp` 192 B + `canon_sort` 160 B), 160 B per level
for `naive_eq`; the walkers themselves are not recursive (`dupcheck_hash`
352 B total).

## Correctness evidence (`make test`, `make test-asan`)

- SipHash-2-4 reference vector; streaming split invariance.
- 15 hand-written cases (non-minimal integers and tags, `0` vs `-1`, permuted
  map keys, maps in arrays in keys, duplicates under arrays and in values,
  `D = 0`, depth and length bounds, root-only).
- Differential random testing, 10^6 inputs (avg 52 B, up to 3.5 KB, maps
  nested up to 5 deep, inside keys too) from an equivalence-heavy generator
  (values in tiny domains, random non-minimal widths, shuffled map entries,
  planted re-encoded duplicate keys). For every input, all five variants
  (sort, hash-canon, hash-naive, and both with all hashes forced to 0) must
  return the same result, which must agree with:
  - the verified `cbor_nondet_validate_bounded(D, N)` for random small
    `D in [0,4]`, `N in [0,5]` (accept/reject: 708164 / 291836);
  - the verified unbounded validator with `D = N = 64` (183177 duplicates);
  - for `DUP_FLAG_ROOT_ONLY`, an oracle built from the verified validator
    (each root key valid; `{k_i: 0, k_j: 0}` valid for every pair).
- Every check runs on a heap scratch of the exact advertised size (so that
  AddressSanitizer catches overruns); one byte less must give
  `DUP_SCRATCH_TOO_SMALL`.
- `malloc/calloc/realloc/free` are wrapped at link time and abort if called
  during a check.
- All of the above also pass under `-fsanitize=address,undefined`
  (2·10^5 iterations).
- Mutation sanity: making the sort compare unsorted maps, or making the map
  hash order-dependent, is caught (hundreds of failures in 2·10^4 iterations).

(libFuzzer was not used: clang is not installed on the benchmark machine.)

## Benchmarks (`make bench`)

Machine: AMD EPYC 7V13, gcc 13.3.0, `-O2`, single thread. Time per call,
median of 5 batches of at least 20 ms (single call above 0.1 s); a variant is
dropped for larger parameters after a call exceeds 0.5 s ("capped"). Times
are for the check alone; the weak API pays `wf` + check. `verified-b` /
`verified-u` are the verified bounded (with the same `D`, `N`) and unbounded
nondet validators, which include well-formedness. Full tables:
`bench_fit.md`; raw data with operation counters: `bench.csv`.

Families (all inputs well-formed; only B1 and B4 contain duplicates):

- A1/A3: one map with `n` distinct integer keys (minimal / 8-byte encodings).
- A2: `n` 256-byte string keys sharing a 252-byte prefix.
- A4: array of `m` COSE-like 8-entry header maps (realistic).
- A5: chain of `d` maps nested in values.
- A6/B5: A1/B2 with all hashes forced equal (hash worst case).
- B1: `{K_d: 0, K_d: 0}`, `K_d = {K_{d-1}: 0, -1: 0}` (exponential for the
  verified validator).
- B2/B4: `n` keys that are 32-entry maps, shuffled, differing only in their
  largest entry (each comparison must re-sort both maps); B4 adds a
  re-shuffled copy of the first key.
- B3: keys that are maps whose keys are maps ... `t` levels, 4 entries per
  map, near-identical at every level (nested re-sorting).
- B6: 64 keys, each an array of `k` 16-entry maps differing only in the last
  map (many maps per key: their sorted forms cannot be cached in `O(D·N)`).

### Headline numbers

| Input | bytes | wf | verified-b | sort | hash-canon | hash0-canon |
|---|---|---|---|---|---|---|
| A1 n = 16384 | 65 KB | 0.31 ms | 4.88 s | 2.5 ms | 0.57 ms | 1.28 s |
| A1 n = 1048576 | 6.2 MB | 21.8 ms | (capped) | 297 ms | 45 ms | (capped) |
| A2 n = 65536 | 17 MB | 1.4 ms | (capped) | 27 ms | 8.8 ms | (capped) |
| A4 m = 262144 | 66 MB | 61 ms | 459 ms | 37 ms | 65 ms | - |
| A5 d = 16384 | 33 KB | 0.32 ms | 3.04 s | 0.26 ms | 0.54 ms | - |
| B1 d = 20 | 165 B | 1.6 us | 726 ms | 5.0 us | 11 us | - |
| B2 n = 16384 | 1.3 MB | 11 ms | (capped) | 695 ms | 43 ms | - |
| B3 t = 6 | 104 KB | 0.95 ms | 4.45 s | 1.08 s | 3.6 ms | - |
| B3 t = 9 | 6.6 MB | 56 ms | (capped) | (capped) | 242 ms | - |
| B6 k = 4096 | 8.7 MB | 86 ms | (capped) | 1.01 s | 339 ms | - |

### Empirical growth (least-squares slope of log time vs log bytes)

| Family | verified-b | sort | hash-canon | hash0-canon |
|---|---|---|---|---|
| A1 wide int keys | 1.80 | 1.10 | 0.96 | 1.89 |
| A2 long common prefix | 2.01 | 1.25 | 1.00 | 1.90 |
| A4 COSE-like | 1.00 | 1.00 | 1.00 | - |
| A5 map chain in values | 1.96 | 1.06 | 1.02 | - |
| B2 re-sort, n grows | 2.01 | 1.20 | 1.01 | - |
| B2 re-sort, m grows | 1.68 | 1.16 | 0.92 | - |
| B5 re-sort, all collide | - | 1.25 | 1.01 | 1.98 |
| B6 many maps per key | 1.28 | 1.03 | 1.01 | - |
| B3 nested re-sort | x11.9 / level | **x14.4 / level** | x4.10 / level | - |
| B1 dup chain | x2.03 / level | x1.08 / level | x1.07 / level | - |

(B1 and B3 are parameterized by depth; the per-level time ratio is shown,
input size grows x1.05 and x4.02 per level respectively.)

## Findings

1. **Both prototypes remove the pathological cases of the verified
   validator on flat and value-nested maps.** On a 16384-key map the
   verified bounded validator takes 4.9 s, the sort check 2.5 ms and the hash
   check 0.57 ms; on a 16384-deep chain of maps in values (A5), 3 s vs
   0.26 / 0.54 ms; on B1 (exponential for the verified validator) both are
   essentially linear in the input.

2. **The hash variant is linear on every family**, including nested maps in
   keys (B3: time grows x4.1 per level, exactly as the input does). It costs
   1-2x `wf` on integer keys and realistic maps (A1, A4), up to 4-6x `wf`
   when keys are long byte strings or nested maps (A2, B3), because `wf`
   skips byte-string contents while the hash must read them. Weak parse +
   hash check stays faster than the verified validator even on benign inputs
   (A4: 61 + 65 ms vs 459 ms for 66 MB).

3. **The sort variant is `O(K log n)` when keys contain no maps** (slopes
   1.1-1.25; 5-20x `wf` on wide maps), deterministic and needs 2-6x less scratch. **But
   with maps in keys and no input-dependent memory it must re-sort nested maps
   at every comparison**: B2 is 16x slower than hash, and on B3 the cost grows
   x14.4 per level of nesting while the input grows x4: exponential in `D`,
   as predicted (1.08 s on a 104 KB input with `D = 7`). This is inherent to
   the `O(D·N)` memory budget, not an implementation artefact.

4. **The hash variant's worst case is quadratic** (`hash0-canon`: slope ~1.9,
   1.28 s for 16384 keys, the same order as the verified validator), reached
   only if an attacker can produce collisions, i.e. only if the SipHash key
   leaks or is not random. Canonical confirmation keeps that worst case
   free of the `2^D` factor; naive confirmation is equally fast on real hits
   (it only runs on true duplicates or 2^-64 accidents) and saves
   `12(D-1)N` bytes of scratch, but would be `2^D`-style under forced
   collisions.

5. Comparing maps nested in keys re-scans them (`skip_item`) at each level, so
   the confirmation/comparison of one key costs `O(D·|key|)` (visible as the
   slightly super-linear growth of B1, which compares two `d`-deep keys).

## Collision attacks with a known key (`make attack`)

`dupcheck_hash_mask = 0` (the `hash0-*` rows above) is a simulation: it
models an attacker who makes every key collide. `attack_hash.c` checks
whether a real attacker can do this when they **know the SipHash key**
(fixed, leaked, or a caller passing a constant). It crafts real inputs
against the real hash code and checks each input with that key and with a
fresh random key. Results are in `attack.csv` (single core, best of 3).

1. **Bucket flooding** (`bucket`, maps of `2^t` integer keys). The table
   index is only the low `log2(cap) = t+1` bits of the hash, so keys whose
   hashes share those bits are found by brute force in about `2^t · cap`
   SipHash calls (`t = 16`: about 2^33 calls, under 3 minutes). Every insertion
   then probes the whole cluster: `n^2/2` probes, but no confirmations,
   because the full 64-bit hashes differ.

   | t | keys | wf | sort | hash, known key | hash, secret key | probes known / secret |
   |---|---|---|---|---|---|---|
   | 12 | 4096 | 0.08 ms | 0.26 ms | 7.6 ms | 0.13 ms | 8.4M / 1.9k |
   | 14 | 16384 | 0.33 ms | 1.2 ms | 110 ms | 0.60 ms | 134M / 8.2k |
   | 16 | 65536 | 1.3 ms | 5.3 ms | **1.83 s** | 2.5 ms | 2.1G / 32k |

2. **Full 64-bit multicollisions through the additive map hash** (`mapsum`).
   A map key is hashed through `Σ E(k, v) mod 2^64`. With a known key, a
   4-sum `E(a,x) + E(b,y) = E(a,x') + E(b,y')` with `(x,y) != (x',y')` costs
   two lists of 2^22 entry hashes plus a merge on the low 22 bits and a
   birthday match on the high 42 bits (Wagner's generalized birthday,
   about 4 s per 4-sum). `t` independent 4-sums on disjoint key pairs give
   `2^t` distinct maps with `2t` entries each and identical sums, hence
   identical key hashes (a Joux-style multicollision). The crafting cost is
   linear in `t` and `2^t` keys collide, so this is *exactly* the `hash0`
   regime: `n^2/2` confirmations, each a full map comparison.

   | t | colliding keys | bytes | wf | sort | hash, known key | hash, secret key | hash-naive, known key |
   |---|---|---|---|---|---|---|---|
   | 8 | 256 | 25 KB | 0.08 ms | 0.97 ms | 16 ms | 0.34 ms | 4.5 ms |
   | 10 | 1024 | 125 KB | 0.39 ms | 8.1 ms | 436 ms | 1.5 ms | 69 ms |
   | 12 | 4096 | 602 KB | 1.9 ms | 48 ms | **8.08 s** | 7.6 ms | (skipped) |

   Crafting `t = 12` took 50 s on one core, and every further doubling of
   the key count costs about 4 s more. All variants accept every input (the
   keys are pairwise distinct), so the attack is pure CPU exhaustion: 600 KB
   take 8 s, 1000x the secret-key time and 170x the sort variant.

**Conclusions.**

- With a **secret, uniformly random key** neither attack applies. The
  attacker never sees hash values, and SipHash is a PRF. Any fixed pair of
  distinct keys then collides on 64 bits with probability about 2^-64, and
  the probe counts above (about 0.5 per key) match the analysis. The only
  remaining routes are key recovery or timing side channels across many
  queries with the same key, and no practical such attack on SipHash is known.
- With a **known key**, both attacks are cheap. Flooding a 64K-key map to
  ~1.8 s needs only brute force; the additive map hash allows arbitrarily
  large full multicollisions at negligible cost. The mask is therefore not
  artificial: it is what a known-key attacker obtains.
- The key is a security parameter. The API must not let a constant key look
  acceptable: draw it from the OS RNG, or make the library own it.

**Hardening that removes the key from the worst case** (not implemented):

1. Replace the open-addressing table by a sort of the `(hash, offset)` pairs
   on the 64-bit hash (radix sort: `O(n)` time and `16n` bytes, no more scratch
   than the table). This removes bucket flooding by construction: only full
   64-bit equalities remain.
2. Inside each run of equal hashes, sort with `canon_sort` instead of
   confirming pairwise. The worst case of the hash variant is then the
   sort variant's worst case, whether or not the key is known (8.08 s ->
   about 48 ms on `mapsum` 12), and the expected case stays linear.
3. Optionally, make full collisions expensive even with a known key by
   hashing a map from its *sorted* entry hashes instead of their sum
   (`8N` more bytes per nested level). Collisions then need generic 64-bit
   SipHash collisions (2^32 work per pair, much more for k-way), instead
   of a 4-sum.

With (1) and (2), the hash variant is never asymptotically worse than the
sort variant and is linear in expectation with a secret key. The proof
obligations are unchanged: the sort on hashes needs no correctness argument
beyond permutation, and the run sort reuses the comparator.

## Recommendation for verification

- **Default: hash-based check with canonical confirmation.** Linear expected
  time on every family, `O(D)` hash states, scratch `O(D·N)`. Its functional
  correctness does not depend on hash quality: the proof obligations are
  (a) the hash is invariant under `raw_equiv` on valid items (needs a
  commutativity lemma for the map entry sum; SipHash itself can be an
  uninterpreted function), and (b) the canonical comparator decides
  `raw_equiv` on valid items (shared with the sort variant). The API must take
  the secret key from the caller (or a platform RNG). With a leaked key the
  current version is quadratic in practice (see the attacks section), so the
  hardening (1)+(2) above should be part of the verified design.
- **Deterministic alternative: the sort-based check**, recommended when map
  keys cannot contain maps (e.g. CDDL-constrained protocols such as COSE/CWT
  with integer/text keys): `O(K log n)` worst case, no secret, smallest
  scratch, and the comparator + merge sort can reuse the existing
  `raw_equiv_sorted_optimal` theory. When keys may contain maps, it should
  be offered only with a small `D` (its worst case is roughly
  `(2 m log m + m)^(D-1)` per comparison).
- Both share the bounded walker and the canonical comparator, which should be
  verified first.

## Limitations

Unverified prototypes; offsets are 32-bit (inputs `< 4 GiB`); the comparator
recursion is bounded by `D` but not removed; one machine, one compiler.

## Reproducing

```
make test        # correctness (1e5 random iterations by default)
make test-asan   # same under ASan/UBSan
make bench       # ~2.5 min: bench.csv and bench_fit.md
make attack      # ~5 min: known-key collision attacks -> attack.csv
```

`./out/bench_dupcheck.exe quick` runs reduced sizes (~40 s).
