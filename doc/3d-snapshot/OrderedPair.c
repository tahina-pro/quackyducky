

#include "OrderedPair.h"

/*
Auto-generated field identifier for error reporting
*/
#define ORDEREDPAIR__ORDEREDPAIR__LESSER ((uint64_t)33U)

/*
Auto-generated field identifier for error reporting
*/
#define ORDEREDPAIR__ORDEREDPAIR__GREATER ((uint64_t)34U)

static inline uint64_t ValidateOrderedPairLesser(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _orderedPair_lesser
        of type OrderedPair._orderedPair
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field lesser */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, ORDEREDPAIR__ORDEREDPAIR__LESSER);
}

static inline uint64_t ValidateOrderedPairGreater(uint32_t Lesser, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _orderedPair_greater
        of type OrderedPair._orderedPair
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field greater */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition0 = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition0);
  uint64_t resultAfterOrderedPairGreater;
  if (hasBytes)
  {
    resultAfterOrderedPairGreater = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterOrderedPairGreater = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t result;
  if (EverParseIsError(resultAfterOrderedPairGreater))
  {
    result = resultAfterOrderedPairGreater;
  }
  else
  {
    /* reading field value */
    uint32_t position = *Input.pos;
    uint32_t result0 = Load32Le(Input.buf + position);
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)4U;
    uint32_t orderedPairGreater = result0;
    /* start: checking constraint */
    BOOLEAN orderedPairGreaterConstraintIsOk = Lesser <= orderedPairGreater;
    /* end: checking constraint */
    result =
      EverParseCheckConstraintOk(orderedPairGreaterConstraintIsOk,
        resultAfterOrderedPairGreater);
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, ORDEREDPAIR__ORDEREDPAIR__GREATER);
}

uint64_t OrderedPairValidateOrderedPair(EverParseInputBuffer Input)
{
  /* Field _orderedPair_lesser */
  uint64_t resultAfterlesser = ValidateOrderedPairLesser(Input);
  if (EverParseIsError(resultAfterlesser))
  {
    return resultAfterlesser;
  }
  uint32_t position = *Input.pos;
  uint32_t result = Load32Le(Input.buf + position);
  uint32_t currentPosition = *Input.pos;
  *Input.pos = currentPosition + (uint32_t)4U;
  uint32_t lesser = result;
  /* Field _orderedPair_greater */
  return ValidateOrderedPairGreater(lesser, Input);
}

