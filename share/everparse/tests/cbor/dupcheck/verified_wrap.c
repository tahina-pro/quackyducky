/* Thin wrappers around the verified EverCBOR nondet C code, used as the
 * well-formedness precondition, as the correctness oracle and as the
 * performance baseline. CBORNondet.c is included (rather than linked) to
 * access the static validate_raw_data_item. */
#include "CBORNondet.c"
#include "verified_wrap.h"

static CBOR_Pulse_Raw_Slice_byte_slice mk(const uint8_t *b, size_t len) {
  return Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t((uint8_t *)b, len);
}

size_t verified_wf(const uint8_t *b, size_t len) {
  size_t off = 0;
  if (CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item(mk(b, len), &off))
    return off;
  return 0;
}

size_t verified_bounded(size_t D, size_t N, const uint8_t *b, size_t len) {
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded(D, N, mk(b, len));
}

size_t verified_unbounded(const uint8_t *b, size_t len) {
  FStar_Pervasives_Native_option__size_t none = {
    .tag = FStar_Pervasives_Native_None };
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_validate(none, false, mk(b, len));
}
