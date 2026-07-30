module CBOR.Pulse.Raw.Format.Serialized
open CBOR.Pulse.Raw.Iterator.Base
include CBOR.Pulse.Raw.Match
open CBOR.Pulse.Raw.Iterator
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module ML = CBOR.Pulse.Raw.Format.MixedList

val cbor_match_serialized_tagged_get_payload
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Tagged? r })
: stt cbor_raw
  (cbor_match_serialized_tagged c pm r)
  (fun res ->
    cbor_match 1.0R res (Tagged?.v r) **
    trade
      (cbor_match 1.0R res (Tagged?.v r))
      (cbor_match_serialized_tagged c pm r) **
    pure (~ (CBOR_Case_Array? res \/ CBOR_Case_Map? res \/ CBOR_Case_Tagged? res \/ CBOR_Case_Array_Gen? res \/ CBOR_Case_Map_Gen? res))
  )

val cbor_serialized_array_item
  (c: cbor_serialized)
  (i: U64.t)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
: stt cbor_raw
    (cbor_match_serialized_array c pm r **
      pure (U64.v i < List.Tot.length (Array?.v r))
    )
    (fun res -> exists* y .
      cbor_match 1.0R res y **
      trade
        (cbor_match 1.0R res y)
        (cbor_match_serialized_array c pm r) **
      pure (
        U64.v i < List.Tot.length (Array?.v r) /\
        List.Tot.index (Array?.v r) (U64.v i) == y
      )
    )

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

val cbor_serialized_array_iterator_is_empty : cbor_raw_serialized_iterator_is_empty_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_length : cbor_raw_serialized_iterator_length_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_next (_: unit) : cbor_raw_serialized_iterator_next_t cbor_match cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_next_with_depth (n: Ghost.erased nat) : cbor_raw_serialized_iterator_next_t (cbor_match_with_depth n) cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_truncate : cbor_raw_serialized_iterator_truncate_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_share : cbor_raw_serialized_iterator_share_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_gather : cbor_raw_serialized_iterator_gather_t cbor_serialized_array_iterator_match

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

val cbor_serialized_map_iterator_is_empty : cbor_raw_serialized_iterator_is_empty_t cbor_serialized_map_iterator_match

val cbor_serialized_map_iterator_next (_: unit) : cbor_raw_serialized_iterator_next_t cbor_match_map_entry cbor_serialized_map_iterator_match

val cbor_serialized_map_iterator_next_with_depth (n: Ghost.erased nat) : cbor_raw_serialized_iterator_next_t (cbor_match_map_entry_with_depth n) cbor_serialized_map_iterator_match

val cbor_serialized_map_iterator_share : cbor_raw_serialized_iterator_share_t cbor_serialized_map_iterator_match

val cbor_serialized_map_iterator_gather : cbor_raw_serialized_iterator_gather_t cbor_serialized_map_iterator_match

////////////////////////////////////////////////////////////////////////////////
// Mixed-list ("_Gen") iterators, built on the lowparse mixed-list iterator API.
// These mirror the serialized iterators above, and are used by Read.fst to
// dispatch the CBOR_Case_Array_Gen / CBOR_Case_Map_Gen cases.
////////////////////////////////////////////////////////////////////////////////

// ===== ARRAY (non-depth) =====

val cbor_mixed_array_iterator_match
  (p: perm)
  (i: ML.cbor_raw_mixed_iterator cbor_raw)
  (a: list raw_data_item)
: slprop

val cbor_mixed_array_iterator_init
  (c: cbor_mixed_list_array)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
: stt (ML.cbor_raw_mixed_iterator cbor_raw)
    (cbor_match_mixed_list_array pm c r cbor_match)
    (fun res -> exists* p .
      cbor_mixed_array_iterator_match p res (Array?.v r) **
      trade
        (cbor_mixed_array_iterator_match p res (Array?.v r))
        (cbor_match_mixed_list_array pm c r cbor_match)
    )

val cbor_mixed_array_iterator_is_empty : cbor_raw_mixed_iterator_is_empty_t cbor_mixed_array_iterator_match

val cbor_mixed_array_iterator_length : cbor_raw_mixed_iterator_length_t cbor_mixed_array_iterator_match

val cbor_mixed_array_iterator_next (_: unit) : cbor_raw_mixed_iterator_next_t cbor_match cbor_mixed_array_iterator_match

val cbor_mixed_array_iterator_truncate : cbor_raw_mixed_iterator_truncate_t cbor_mixed_array_iterator_match

val cbor_mixed_array_iterator_share : cbor_raw_mixed_iterator_share_t cbor_mixed_array_iterator_match

val cbor_mixed_array_iterator_gather : cbor_raw_mixed_iterator_gather_t cbor_mixed_array_iterator_match

val cbor_mixed_array_item
  (c: cbor_mixed_list_array)
  (i: U64.t)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
: stt cbor_raw
    (cbor_match_mixed_list_array pm c r cbor_match **
      pure (U64.v i < List.Tot.length (Array?.v r))
    )
    (fun res -> exists* p' y .
      cbor_match p' res y **
      trade
        (cbor_match p' res y)
        (cbor_match_mixed_list_array pm c r cbor_match) **
      pure (
        U64.v i < List.Tot.length (Array?.v r) /\
        List.Tot.index (Array?.v r) (U64.v i) == y
      )
    )

// ===== MAP (non-depth) =====

val cbor_mixed_map_iterator_match
  (p: perm)
  (i: ML.cbor_raw_mixed_iterator cbor_map_entry)
  (a: list (raw_data_item & raw_data_item))
: slprop

val cbor_mixed_map_iterator_init
  (c: cbor_mixed_list_map)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
: stt (ML.cbor_raw_mixed_iterator cbor_map_entry)
    (cbor_match_mixed_list_map pm c r cbor_match)
    (fun res -> exists* p .
      cbor_mixed_map_iterator_match p res (Map?.v r) **
      trade
        (cbor_mixed_map_iterator_match p res (Map?.v r))
        (cbor_match_mixed_list_map pm c r cbor_match)
    )

val cbor_mixed_map_iterator_is_empty : cbor_raw_mixed_iterator_is_empty_t cbor_mixed_map_iterator_match

val cbor_mixed_map_iterator_next (_: unit) : cbor_raw_mixed_iterator_next_t cbor_match_map_entry cbor_mixed_map_iterator_match

val cbor_mixed_map_iterator_share : cbor_raw_mixed_iterator_share_t cbor_mixed_map_iterator_match

val cbor_mixed_map_iterator_gather : cbor_raw_mixed_iterator_gather_t cbor_mixed_map_iterator_match

////////////////////////////////////////////////////////////////////////////////
// Depth-aware mixed-list ("_Gen") iterators. The element predicate is
// [cbor_match_with_depth d] (array) or [cbor_match_map_entry_with_depth d]
// (map), so that the depth-aware readers in Read.fst can dispatch the
// CBOR_Case_Array_Gen / CBOR_Case_Map_Gen cases.
////////////////////////////////////////////////////////////////////////////////

// ===== ARRAY (depth) =====

val cbor_mixed_array_iterator_match_with_depth
  (d: Ghost.erased nat)
  (p: perm)
  (i: ML.cbor_raw_mixed_iterator cbor_raw)
  (a: list raw_data_item)
: slprop

val cbor_mixed_array_iterator_init_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_mixed_list_array)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
: stt (ML.cbor_raw_mixed_iterator cbor_raw)
    (cbor_match_with_depth depth pm (CBOR_Case_Array_Gen c) r)
    (fun res -> exists* p .
      cbor_mixed_array_iterator_match_with_depth (nat_pred depth) p res (Array?.v r) **
      trade
        (cbor_mixed_array_iterator_match_with_depth (nat_pred depth) p res (Array?.v r))
        (cbor_match_with_depth depth pm (CBOR_Case_Array_Gen c) r)
    )

val cbor_mixed_array_iterator_is_empty_with_depth (d: Ghost.erased nat) : cbor_raw_mixed_iterator_is_empty_t (cbor_mixed_array_iterator_match_with_depth d)

val cbor_mixed_array_iterator_next_with_depth (d: Ghost.erased nat) : cbor_raw_mixed_iterator_next_t (cbor_match_with_depth d) (cbor_mixed_array_iterator_match_with_depth d)

// ===== MAP (depth) =====

val cbor_mixed_map_iterator_match_with_depth
  (d: Ghost.erased nat)
  (p: perm)
  (i: ML.cbor_raw_mixed_iterator cbor_map_entry)
  (a: list (raw_data_item & raw_data_item))
: slprop

val cbor_mixed_map_iterator_init_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_mixed_list_map)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
: stt (ML.cbor_raw_mixed_iterator cbor_map_entry)
    (cbor_match_with_depth depth pm (CBOR_Case_Map_Gen c) r)
    (fun res -> exists* p .
      cbor_mixed_map_iterator_match_with_depth (nat_pred depth) p res (Map?.v r) **
      trade
        (cbor_mixed_map_iterator_match_with_depth (nat_pred depth) p res (Map?.v r))
        (cbor_match_with_depth depth pm (CBOR_Case_Map_Gen c) r)
    )

val cbor_mixed_map_iterator_is_empty_with_depth (d: Ghost.erased nat) : cbor_raw_mixed_iterator_is_empty_t (cbor_mixed_map_iterator_match_with_depth d)

val cbor_mixed_map_iterator_next_with_depth (d: Ghost.erased nat) : cbor_raw_mixed_iterator_next_t (cbor_match_map_entry_with_depth d) (cbor_mixed_map_iterator_match_with_depth d)

