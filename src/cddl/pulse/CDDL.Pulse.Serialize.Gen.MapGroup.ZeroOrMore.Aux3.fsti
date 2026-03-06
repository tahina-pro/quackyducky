module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux3
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2

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

val impl_serialize_map_group_valid_map_zero_or_more_snoc_gen
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
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
      impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp (map_of_list_cons key_eq k v m2) len <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v))) /\
      FStar.UInt.fits (cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1) 64 /\
      (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
      (sp.mg_serializable (map_of_list_snoc key_eq m1 k v) ==>
        impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v))) sp m2 len
      )
    )) /\ (
      (
        sp1.serializable k /\
        sp2.serializable v /\
        (~ (except (sp1.serializer k, sp2.serializer v))) /\
        (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
      ) ==> (
      sp.mg_serializable (map_of_list_snoc key_eq m1 k v) /\
      cbor_map_disjoint l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) /\
      cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)) /\
      cbor_map_length (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_length (sp.mg_serializer m1) + 1
  ))))
