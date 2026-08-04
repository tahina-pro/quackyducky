module CBOR.Pulse.Raw.Format.MixedList

module SZ = FStar.SizeT
module U64 = FStar.UInt64

val cbor_raw_mixed_list ([@@@strictly_positive] t: Type0) : Type0

val cbor_raw_mixed_list_length (#t: Type0) (ml: cbor_raw_mixed_list t) : Tot U64.t

val cbor_raw_mixed_iterator ([@@@strictly_positive] t: Type0) : Type0

(* A dummy (empty) mixed-list value, used to initialize the scratch-cell
   references the array-builder / map-insert APIs require, without heap
   allocation. *)
inline_for_extraction
val cbor_raw_mixed_list_dummy (#t: Type0) (_: unit) : cbor_raw_mixed_list t
