module CBOR.Pulse.Raw.Format.Match
include CBOR.Pulse.Raw.Type
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade

val cbor_match_serialized_payload_array
  (c: slice U8.t)
  (p: perm)
  (r: list raw_data_item)
: Tot slprop

val cbor_match_serialized_payload_map
  (c: slice U8.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
: Tot slprop

val cbor_match_serialized_payload_tagged
  (c: slice U8.t)
  (p: perm)
  (r: raw_data_item)
: Tot slprop

val cbor_match_serialized_payload_array_share
  (c: slice U8.t)
  (p: perm)
  (r: list raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_array c p r)
    (fun _ ->
      cbor_match_serialized_payload_array c (p /. 2.0R) r **
      cbor_match_serialized_payload_array c (p /. 2.0R) r
    )

val cbor_match_serialized_payload_array_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: list raw_data_item)
  (p2: perm)
  (r2: list raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_array c p1 r1 **
      cbor_match_serialized_payload_array c p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_array c (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_map_share
  (c: slice U8.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_map c p r)
    (fun _ ->
      cbor_match_serialized_payload_map c (p /. 2.0R) r **
      cbor_match_serialized_payload_map c (p /. 2.0R) r
    )

val cbor_match_serialized_payload_map_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: list (raw_data_item & raw_data_item))
  (p2: perm)
  (r2: list (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_map c p1 r1 **
      cbor_match_serialized_payload_map c p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_map c (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_tagged_share
  (c: slice U8.t)
  (p: perm)
  (r: raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_tagged c p r)
    (fun _ ->
      cbor_match_serialized_payload_tagged c (p /. 2.0R) r **
      cbor_match_serialized_payload_tagged c (p /. 2.0R) r
    )

val cbor_match_serialized_payload_tagged_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_tagged c p1 r1 **
      cbor_match_serialized_payload_tagged c p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_tagged c (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_array_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list raw_data_item))
  (c': slice U8.t)
: stt unit
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_array c p r **
      pure (len c == len c')
    )
    (fun _ ->
      cbor_match_serialized_payload_array c p r **
      cbor_match_serialized_payload_array c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_array c' 1.0R r)
        (exists* v' . pts_to c' v')
    )

val cbor_match_serialized_payload_map_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list (raw_data_item & raw_data_item)))
  (c': slice U8.t)
: stt unit
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_map c p r **
      pure (len c == len c')
    )
    (fun _ ->
      cbor_match_serialized_payload_map c p r **
      cbor_match_serialized_payload_map c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_map c' 1.0R r)
        (exists* v' . pts_to c' v')
    )

val cbor_match_serialized_payload_tagged_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased raw_data_item)
  (c': slice U8.t)
: stt unit
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_tagged c p r **
      pure (len c == len c')
    )
    (fun _ ->
      cbor_match_serialized_payload_tagged c p r **
      cbor_match_serialized_payload_tagged c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_tagged c' 1.0R r)
        (exists* v' . pts_to c' v')
    )

val cbor_match_mixed_list_array
  (p: perm)
  (c: cbor_mixed_list_array)
  (r: raw_data_item { Array? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
: Tot slprop

val cbor_match_mixed_list_map
  (p: perm)
  (c: cbor_mixed_list_map)
  (r: raw_data_item { Map? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
: Tot slprop

(* ==== Phase B: abstract mixed-list operations for the _Gen cases ==== *)

module U64 = FStar.UInt64

val cbor_match_mixed_list_array_length
  (p: perm)
  (c: cbor_mixed_list_array)
  (r: raw_data_item { Array? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
: stt_ghost unit emp_inames
    (cbor_match_mixed_list_array p c r cbor_match)
    (fun _ -> cbor_match_mixed_list_array p c r cbor_match ** pure (
      c.cbor_array_gen_length_size == (Array?.len r).size /\
      U64.v (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length c.cbor_array_gen_ptr) == U64.v (Array?.len r).value
    ))

val cbor_match_mixed_list_map_length
  (p: perm)
  (c: cbor_mixed_list_map)
  (r: raw_data_item { Map? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
: stt_ghost unit emp_inames
    (cbor_match_mixed_list_map p c r cbor_match)
    (fun _ -> cbor_match_mixed_list_map p c r cbor_match ** pure (
      c.cbor_map_gen_length_size == (Map?.len r).size /\
      U64.v (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length c.cbor_map_gen_ptr) == U64.v (Map?.len r).value
    ))

val cbor_match_mixed_list_array_weaken
  (p: perm)
  (c: cbor_mixed_list_array)
  (r: raw_data_item { Array? r })
  (cm1 cm2: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (prf: (
    (p': perm) ->
    (c': cbor_raw) ->
    (v': raw_data_item { List.Tot.memP v' (Array?.v r) /\ v' << r }) ->
    stt_ghost unit emp_inames (cm1 p' c' v') (fun _ -> cm2 p' c' v')
  ))
: stt_ghost unit emp_inames
    (cbor_match_mixed_list_array p c r cm1)
    (fun _ -> cbor_match_mixed_list_array p c r cm2)

val cbor_match_mixed_list_map_weaken
  (p: perm)
  (c: cbor_mixed_list_map)
  (r: raw_data_item { Map? r })
  (cm1 cm2: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (prf: (
    (p': perm) ->
    (x: cbor_map_entry) ->
    (pair: (raw_data_item & raw_data_item) { List.Tot.memP pair (Map?.v r) /\ fst pair << r /\ snd pair << r }) ->
    stt_ghost unit emp_inames
      (cm1 p' x.cbor_map_entry_key (fst pair) ** cm1 p' x.cbor_map_entry_value (snd pair))
      (fun _ -> cm2 p' x.cbor_map_entry_key (fst pair) ** cm2 p' x.cbor_map_entry_value (snd pair))
  ))
: stt_ghost unit emp_inames
    (cbor_match_mixed_list_map p c r cm1)
    (fun _ -> cbor_match_mixed_list_map p c r cm2)

val cbor_match_mixed_list_array_perm_eq
  (p1 p2: perm)
  (c1 c2: cbor_mixed_list_array)
  (r: raw_data_item { Array? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
: Lemma
  (requires (p1 *. c1.cbor_array_gen_perm == p2 *. c2.cbor_array_gen_perm /\
             c1.cbor_array_gen_length_size == c2.cbor_array_gen_length_size /\
             c1.cbor_array_gen_ptr == c2.cbor_array_gen_ptr))
  (ensures cbor_match_mixed_list_array p1 c1 r cbor_match == cbor_match_mixed_list_array p2 c2 r cbor_match)

val cbor_match_mixed_list_map_perm_eq
  (p1 p2: perm)
  (c1 c2: cbor_mixed_list_map)
  (r: raw_data_item { Map? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
: Lemma
  (requires (p1 *. c1.cbor_map_gen_perm == p2 *. c2.cbor_map_gen_perm /\
             c1.cbor_map_gen_length_size == c2.cbor_map_gen_length_size /\
             c1.cbor_map_gen_ptr == c2.cbor_map_gen_ptr))
  (ensures cbor_match_mixed_list_map p1 c1 r cbor_match == cbor_match_mixed_list_map p2 c2 r cbor_match)

val cbor_match_mixed_list_array_share
  (p: perm)
  (c: cbor_mixed_list_array)
  (r: raw_data_item { Array? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (cbor_match_share: (
    (p': perm) ->
    (c': cbor_raw) ->
    (v': raw_data_item { v' << r }) ->
    stt_ghost unit emp_inames (cbor_match p' c' v') (fun _ -> cbor_match (p' /. 2.0R) c' v' ** cbor_match (p' /. 2.0R) c' v')
  ))
: stt_ghost unit emp_inames
    (cbor_match_mixed_list_array p c r cbor_match)
    (fun _ -> cbor_match_mixed_list_array (p /. 2.0R) c r cbor_match ** cbor_match_mixed_list_array (p /. 2.0R) c r cbor_match)

val cbor_match_mixed_list_map_share
  (p: perm)
  (c: cbor_mixed_list_map)
  (r: raw_data_item { Map? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (cbor_match_share: (
    (p': perm) ->
    (c': cbor_raw) ->
    (v': raw_data_item { v' << r }) ->
    stt_ghost unit emp_inames (cbor_match p' c' v') (fun _ -> cbor_match (p' /. 2.0R) c' v' ** cbor_match (p' /. 2.0R) c' v')
  ))
: stt_ghost unit emp_inames
    (cbor_match_mixed_list_map p c r cbor_match)
    (fun _ -> cbor_match_mixed_list_map (p /. 2.0R) c r cbor_match ** cbor_match_mixed_list_map (p /. 2.0R) c r cbor_match)

val cbor_match_mixed_list_array_gather
  (p1 p2: perm)
  (c: cbor_mixed_list_array)
  (r1: raw_data_item { Array? r1 })
  (r2: raw_data_item { Array? r2 })
  (cbor_match: perm -> cbor_raw -> raw_data_item -> slprop)
  (cbor_match_gather: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (v1': raw_data_item { v1' << r1 }) ->
    (p2': perm) ->
    (v2': raw_data_item) ->
    stt_ghost unit emp_inames (cbor_match p1' c' v1' ** cbor_match p2' c' v2') (fun _ -> cbor_match (p1' +. p2') c' v1' ** pure (v1' == v2'))
  ))
: stt_ghost unit emp_inames
    (cbor_match_mixed_list_array p1 c r1 cbor_match ** cbor_match_mixed_list_array p2 c r2 cbor_match)
    (fun _ -> cbor_match_mixed_list_array (p1 +. p2) c r1 cbor_match ** pure (r1 == r2))

val cbor_match_mixed_list_map_gather
  (p1 p2: perm)
  (c: cbor_mixed_list_map)
  (r1: raw_data_item { Map? r1 })
  (r2: raw_data_item { Map? r2 })
  (cbor_match: perm -> cbor_raw -> raw_data_item -> slprop)
  (cbor_match_gather: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (v1': raw_data_item { v1' << r1 }) ->
    (p2': perm) ->
    (v2': raw_data_item) ->
    stt_ghost unit emp_inames (cbor_match p1' c' v1' ** cbor_match p2' c' v2') (fun _ -> cbor_match (p1' +. p2') c' v1' ** pure (v1' == v2'))
  ))
: stt_ghost unit emp_inames
    (cbor_match_mixed_list_map p1 c r1 cbor_match ** cbor_match_mixed_list_map p2 c r2 cbor_match)
    (fun _ -> cbor_match_mixed_list_map (p1 +. p2) c r1 cbor_match ** pure (r1 == r2))
