module CBOR.Pulse.Raw.Format.Serialized.C
open CBOR.Pulse.Raw.Format.Match.C
open CBOR.Pulse.Raw.Iterator.C
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64

val cbor_serialized_array_iterator_match
  (p: perm)
  (i: cbor_raw_serialized_iterator)
  (a: list raw_data_item)
: slprop

val cbor_serialized_array_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
: stt cbor_raw_serialized_iterator
    (cbor_match_serialized_array c pm r)
    (fun res -> exists* p .
      cbor_serialized_array_iterator_match p res (Array?.v r) **
      trade
        (cbor_serialized_array_iterator_match p res (Array?.v r))
        (cbor_match_serialized_array c pm r)
    )

val cbor_serialized_map_iterator_match
  (p: perm)
  (i: cbor_raw_serialized_iterator)
  (a: list (raw_data_item & raw_data_item))
: slprop

val cbor_serialized_map_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
: stt cbor_raw_serialized_iterator
    (cbor_match_serialized_map c pm r)
    (fun res -> exists* p .
      cbor_serialized_map_iterator_match p res (Map?.v r) **
      trade
        (cbor_serialized_map_iterator_match p res (Map?.v r))
        (cbor_match_serialized_map c pm r)
    )
