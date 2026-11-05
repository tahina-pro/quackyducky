/* Streaming SipHash-c-d (Aumasson & Bernstein), written from the
 * specification. Little-endian message words, as in the reference. */
#include "dupcheck_internal.h"

#define ROTL(x, b) (uint64_t)(((x) << (b)) | ((x) >> (64 - (b))))

static inline void sipround(sip_state *s) {
  s->v0 += s->v1; s->v1 = ROTL(s->v1, 13); s->v1 ^= s->v0;
  s->v0 = ROTL(s->v0, 32);
  s->v2 += s->v3; s->v3 = ROTL(s->v3, 16); s->v3 ^= s->v2;
  s->v0 += s->v3; s->v3 = ROTL(s->v3, 21); s->v3 ^= s->v0;
  s->v2 += s->v1; s->v1 = ROTL(s->v1, 17); s->v1 ^= s->v2;
  s->v2 = ROTL(s->v2, 32);
}

static inline uint64_t load64le(const uint8_t *p) {
  return (uint64_t)p[0] | (uint64_t)p[1] << 8 | (uint64_t)p[2] << 16 |
         (uint64_t)p[3] << 24 | (uint64_t)p[4] << 32 | (uint64_t)p[5] << 40 |
         (uint64_t)p[6] << 48 | (uint64_t)p[7] << 56;
}

static inline void compress(sip_state *s, uint64_t m, int c) {
  s->v3 ^= m;
  for (int i = 0; i < c; i++) sipround(s);
  s->v0 ^= m;
}

void sip_init(sip_state *s, const uint8_t key[16]) {
  uint64_t k0 = load64le(key), k1 = load64le(key + 8);
  s->v0 = k0 ^ 0x736f6d6570736575ULL;
  s->v1 = k1 ^ 0x646f72616e646f6dULL;
  s->v2 = k0 ^ 0x6c7967656e657261ULL;
  s->v3 = k1 ^ 0x7465646279746573ULL;
  s->m = 0; s->mlen = 0; s->total = 0;
}

void sip_update(sip_state *s, const uint8_t *p, size_t n, int c) {
  s->total += n;
  while (n > 0 && s->mlen != 0) {
    s->m |= (uint64_t)*p++ << (8 * s->mlen);
    n--;
    if (++s->mlen == 8) { compress(s, s->m, c); s->m = 0; s->mlen = 0; }
  }
  while (n >= 8) { compress(s, load64le(p), c); p += 8; n -= 8; }
  while (n > 0) { s->m |= (uint64_t)*p++ << (8 * s->mlen++); n--; }
}

uint64_t sip_final(sip_state *s, int c, int d) {
  uint64_t b = s->m | ((s->total & 0xff) << 56);
  compress(s, b, c);
  s->v2 ^= 0xff;
  for (int i = 0; i < d; i++) sipround(s);
  return s->v0 ^ s->v1 ^ s->v2 ^ s->v3;
}
