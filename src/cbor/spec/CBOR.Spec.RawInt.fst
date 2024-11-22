module CBOR.Spec.RawInt
include CBOR.Spec.Constants

module U8 = FStar.UInt8
module U64 = FStar.UInt64

type integer_size = (n: U8.t { U8.v n <= 4 })

open FStar.Mul

let raw_uint64_size_prop (size: integer_size) (value: U64.t) : Tot prop =
  if U8.v size = 0
  then U64.v value <= U8.v max_simple_value_additional_info
  else U64.v value < pow2 (8 * pow2 (U8.v size - 1))

type raw_uint64 = {
  size: integer_size;
  value: (value: U64.t { raw_uint64_size_prop size value })
}
