#include "TestWrapper.h"
#include <stdio.h>
#include <stdlib.h>

// This function is declared in the generated TestWrapper.c, but not
// defined. It is the callback function called if the validator for
// Test.T fails.
void TestEverParseError(char *StructName, char *FieldName, char *Reason) {
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

// defining iterator operations declared in Test.3d
#define CHECK_OUT(p) \
  if (p == NULL) \
    return; \
  if (p->countRemaining == 0) \
    return;

void SetCurrentf1 (OUT* p, uint32_t f1) {
  CHECK_OUT(p);
  p->current->f1 = f1;
}

void SetCurrentf2 (OUT* p, uint32_t f2) {
  CHECK_OUT(p);
  p->current->f2 = f2;
}

void Advance (OUT* p) {
  CHECK_OUT(p);
  p->current++;
  p->countRemaining--;
}

#define testSize 18

int main(void) {
  uint8_t *test = calloc(testSize, sizeof(uint8_t));
  OUT_PAIR array[testSize]; // output only, no need to initialize
  OUT out = {
    .current = array,
    .countRemaining = testSize
  };
  if (test != NULL) {
    if (TestCheckContainer(&out, test, testSize)) {
      printf("Validation succeeded\n");
    }
  }
  free(test);
  return 0;
}
