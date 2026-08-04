module CBOR.Pulse.Raw.Format.MixedList
open Pulse.Lib.Pervasives

module IT = LowParse.PulseParse.Iterator.Type
module IO = LowParse.PulseParse.Iterator.IntOps
module U64 = FStar.UInt64

let cbor_raw_mixed_list t = IT.mixed_list U64.t t

let cbor_raw_mixed_list_length ml = IT.mixed_list_length IO.u64_ops ml

(* The mixed-list iterator is the lowparse `iterator` together with a ghost
   permission field.  The permission field lets the Layer-2 operations
   (Format.Serialized) normalize the effective permission to `1.0R` at the
   outer level after operations (notably `truncate`) that change the
   underlying permission, mirroring the record-with-perm design of the
   serialized iterator. *)
noeq
type mixed_iterator ([@@@strictly_positive] t: Type0) = {
  mi_iterator: IT.iterator U64.t t;
  mi_perm: perm;
}

let cbor_raw_mixed_iterator t = mixed_iterator t

let cbor_raw_mixed_list_dummy #t () = IT.Base IT.Empty
