module CBOR.Pulse.Raw.Format.Match.C
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade
module A = Pulse.Lib.ArrayPtr

noeq
type cbor_serialized = {
  cbor_serialized_header: raw_uint64;
  cbor_serialized_ptr: A.ptr U8.t;
  cbor_serialized_len: SZ.t;
  cbor_serialized_perm: perm;
}

val cbor_match_serialized_payload_array
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: list raw_data_item)
: Tot slprop

val cbor_match_serialized_payload_map
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
: Tot slprop

val cbor_match_serialized_payload_tagged
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: raw_data_item)
: Tot slprop

val cbor_match_serialized_payload_array_share
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: list raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_array a len p r)
    (fun _ ->
      cbor_match_serialized_payload_array a len (p /. 2.0R) r **
      cbor_match_serialized_payload_array a len (p /. 2.0R) r
    )

val cbor_match_serialized_payload_array_gather
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p1: perm)
  (r1: list raw_data_item)
  (p2: perm)
  (r2: list raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_array a len p1 r1 **
      cbor_match_serialized_payload_array a len p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_array a len (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_map_share
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_map a len p r)
    (fun _ ->
      cbor_match_serialized_payload_map a len (p /. 2.0R) r **
      cbor_match_serialized_payload_map a len (p /. 2.0R) r
    )

val cbor_match_serialized_payload_map_gather
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p1: perm)
  (r1: list (raw_data_item & raw_data_item))
  (p2: perm)
  (r2: list (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_map a len p1 r1 **
      cbor_match_serialized_payload_map a len p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_map a len (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_tagged_share
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_tagged a len p r)
    (fun _ ->
      cbor_match_serialized_payload_tagged a len (p /. 2.0R) r **
      cbor_match_serialized_payload_tagged a len (p /. 2.0R) r
    )

val cbor_match_serialized_payload_tagged_gather
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p1: perm)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_tagged a len p1 r1 **
      cbor_match_serialized_payload_tagged a len p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_tagged a len (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_array_copy
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: Ghost.erased (list raw_data_item))
  (a': A.ptr U8.t)
: stt unit
    (exists* v' . pts_to a' v' **
      cbor_match_serialized_payload_array a len p r **
      pure (Seq.length v' == SZ.v len)
    )
    (fun _ ->
      cbor_match_serialized_payload_array a len p r **
      cbor_match_serialized_payload_array a' len 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_array a' len 1.0R r)
        (exists* v' . pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )

val cbor_match_serialized_payload_map_copy
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: Ghost.erased (list (raw_data_item & raw_data_item)))
  (a': A.ptr U8.t)
: stt unit
    (exists* v' . pts_to a' v' **
      cbor_match_serialized_payload_map a len p r **
      pure (Seq.length v' == SZ.v len)
    )
    (fun _ ->
      cbor_match_serialized_payload_map a len p r **
      cbor_match_serialized_payload_map a' len 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_map a' len 1.0R r)
        (exists* v' . pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )

val cbor_match_serialized_payload_tagged_copy
  (a: A.ptr U8.t)
  (len: SZ.t)
  (p: perm)
  (r: Ghost.erased raw_data_item)
  (a': A.ptr U8.t)
: stt unit
    (exists* v' . pts_to a' v' **
      cbor_match_serialized_payload_tagged a len p r **
      pure (Seq.length v' == SZ.v len)
    )
    (fun _ ->
      cbor_match_serialized_payload_tagged a len p r **
      cbor_match_serialized_payload_tagged a' len 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_tagged a' len 1.0R r)
        (exists* v' . pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )
