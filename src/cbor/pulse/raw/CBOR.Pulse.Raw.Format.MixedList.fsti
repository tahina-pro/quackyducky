module CBOR.Pulse.Raw.Format.MixedList

module SZ = FStar.SizeT

val cbor_raw_mixed_list ([@@@strictly_positive] t: Type0) : Type0

val cbor_raw_mixed_list_length (#t: Type0) (ml: cbor_raw_mixed_list t) : Tot SZ.t

val cbor_raw_mixed_iterator ([@@@strictly_positive] t: Type0) : Type0
