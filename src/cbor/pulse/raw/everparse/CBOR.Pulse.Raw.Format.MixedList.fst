module CBOR.Pulse.Raw.Format.MixedList
open Pulse.Lib.Pervasives

let cbor_raw_mixed_list t = LowParse.PulseParse.Iterator.Type.mixed_list t

let cbor_raw_mixed_list_length ml = LowParse.PulseParse.Iterator.Type.mixed_list_length ml

(* The mixed-list iterator is the lowparse `iterator` together with a ghost
   permission field.  The permission field lets the Layer-2 operations
   (Format.Serialized) normalize the effective permission to `1.0R` at the
   outer level after operations (notably `truncate`) that change the
   underlying permission, mirroring the record-with-perm design of the
   serialized iterator. *)
noeq
type mixed_iterator ([@@@strictly_positive] t: Type0) = {
  mi_iterator: LowParse.PulseParse.Iterator.Type.iterator t;
  mi_perm: perm;
}

let cbor_raw_mixed_iterator t = mixed_iterator t
