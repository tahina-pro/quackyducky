module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux6
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux5

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

module SM = Pulse.Lib.SeqMatch

val impl_serialize_map_zero_or_more_valid_false_sz1_gen
  (pe: cbor_parser)
  (minl: cbor_min_length pe)
  (maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
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
  (ke: key)
  (va: value)
  (m2: Map.t key (list value))
  (v0: Map.t key (list value))
  (len: nat)
  (count: U64.t)
  (size0: SZ.t)
  (w w1: Seq.seq U8.t)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
    let l' = cbor_map_union l (sp.mg_serializer m1) in
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty (map_of_list_cons key_eq ke va m2) /\
    impl_serialize_map_group_pre p count size0 l' w /\
    Seq.length w == len /\
    Seq.length w1 == len - SZ.v size0 /\
    impl_serialize_map_group_valid maxl l sp v0 len ==
      impl_serialize_map_group_valid maxl l' sp (map_of_list_cons key_eq ke va m2) len /\
    // pa1 returned 0: key serialization failed
    not (sp1.serializable ke && Some? (maxl (sp1.serializer ke)) && Some?.v (maxl (sp1.serializer ke)) <= Seq.length w1)
  )))
  (ensures (
    impl_serialize_map_group_valid maxl l (mg_zero_or_more_match_item sp1 sp2 except) v0 len == false
  ))
