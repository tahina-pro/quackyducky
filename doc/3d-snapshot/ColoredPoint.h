

#ifndef __ColoredPoint_H
#define __ColoredPoint_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




uint64_t
ColoredPointValidateColoredPoint1(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
);

uint64_t
ColoredPointValidateColoredPoint2(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
);

#if defined(__cplusplus)
}
#endif

#define __ColoredPoint_H_DEFINED
#endif
