module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux4
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux3

module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

let map_of_list_sub
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m: Map.t key (list value))
  (k: key)
  (v: value)
  (lv': list value)
: Pure (Map.t key (list value))
  (requires (
    Map.get m k == Some (v :: lv')
  ))
  (ensures fun m' ->
    (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m') /\
    m == map_of_list_cons key_eq k v m'
  )
=
  let f (kv: (key & list value)) : bool =
    not (key_eq k (fst kv))
  in
  let m' : Map.t key (list value) = match lv' with
  | [] -> Map.filter f m
  | _ -> EqTest.map_set #key #(list value) m k (key_eq k) lv'
  in
  assert (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m');
  assert (Map.equal m (map_of_list_cons key_eq k v m'));
  m'


val impl_serialize_map_group_valid_map_zero_or_more_snoc_overflow_gen
  (maxl: cbor -> option nat)
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\
    (m2 =!= Map.empty _ _) /\
    cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1 >= pow2 64
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2 len == false
  ))

let impl_serialize_map_group_insert_prf_gen_post
  (p: bare_cbor_map_parser)
  (pe: bare_cbor_parser)
  (w: Seq.seq U8.t)
  (l: cbor_map)
  (sz0: nat)
  (k: cbor)
  (sz1: nat)
  (v: cbor)
  (sz2: nat)
: Tot prop
=
    SZ.fits (sz0 + sz1 + sz2) /\
    sz0 + sz1 + sz2 <= Seq.length w /\
    cbor_serialize_map_insert_pre p pe l (SZ.uint_to_t sz0) k (SZ.uint_to_t (sz0 + sz1)) v (Seq.slice w 0 (sz0 + sz1 + sz2))

val impl_serialize_map_group_insert_prf_gen
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (pe: bare_cbor_parser)
  (w_inv: Seq.seq U8.t)
  (l: cbor_map)
  (sz0: nat)
  (k: cbor)
  (z2l: Seq.seq U8.t)
  (v: cbor)
  (w2: Seq.seq U8.t)
  (sz2: nat)
: Lemma
  (requires (
    let sz1 = Seq.length z2l in
    sz0 <= Seq.length w_inv /\
    p (cbor_map_length l) w_inv == Some (l, sz0) /\
    sz1 > 0 /\
    pe z2l == Some (k, sz1) /\
    sz2 > 0 /\
    sz2 <= Seq.length w2 /\
    pe (Seq.slice w2 0 sz2) == Some (v, sz2) /\
    SZ.fits (sz0 + sz1 + sz2)
  ))
  (ensures (
    let sz1 = Seq.length z2l in
    let z1l = Seq.slice w_inv 0 sz0 in
    let w = Seq.append z1l (Seq.append z2l w2) in
    impl_serialize_map_group_insert_prf_gen_post p pe w l sz0 k sz1 v sz2
  ))
