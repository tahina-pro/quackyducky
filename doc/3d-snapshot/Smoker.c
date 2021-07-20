

#include "Smoker.h"

/*
Auto-generated field identifier for error reporting
*/
#define SMOKER__SMOKER__AGE ((uint64_t)37U)

/*
Auto-generated field identifier for error reporting
*/
#define SMOKER__SMOKER__CIGARETTESCONSUMED ((uint64_t)38U)

static inline uint64_t ValidateSmokerCigarettesConsumed(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _smoker_cigarettesConsumed
        of type Smoker._smoker
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field cigarettesConsumed */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)1U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, SMOKER__SMOKER__CIGARETTESCONSUMED);
}

uint64_t SmokerValidateSmoker(EverParseInputBuffer Input)
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  uint32_t startPosition2 = *Input.pos;
  uint64_t startPosition3 = (uint64_t)startPosition2;
  /* Validating field age */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition0 = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition0);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t
  resultAfterage = EverParseMaybeSetErrorCode(result, startPosition3, SMOKER__SMOKER__AGE);
  if (EverParseIsError(resultAfterage))
  {
    return resultAfterage;
  }
  uint32_t position = *Input.pos;
  uint32_t result0 = Load32Le(Input.buf + position);
  uint32_t currentPosition1 = *Input.pos;
  *Input.pos = currentPosition1 + (uint32_t)4U;
  uint32_t age = result0;
  BOOLEAN ageConstraintIsOk = age >= (uint32_t)(uint8_t)21U;
  uint64_t
  resultAfterage1 =
    EverParseCheckConstraintOkWithFieldId(ageConstraintIsOk,
      startPosition1,
      resultAfterage,
      SMOKER__SMOKER__AGE);
  if (EverParseIsError(resultAfterage1))
  {
    return resultAfterage1;
  }
  /* Field _smoker_cigarettesConsumed */
  uint64_t res = ValidateSmokerCigarettesConsumed(Input);
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

