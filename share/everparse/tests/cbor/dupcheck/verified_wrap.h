#ifndef VERIFIED_WRAP_H
#define VERIFIED_WRAP_H
#include <stddef.h>
#include <stdint.h>
/* Each returns the size of the accepted prefix, or 0 on rejection. */
size_t verified_wf(const uint8_t *b, size_t len);          /* well-formed */
size_t verified_bounded(size_t D, size_t N, const uint8_t *b, size_t len);
size_t verified_unbounded(const uint8_t *b, size_t len);
#endif
