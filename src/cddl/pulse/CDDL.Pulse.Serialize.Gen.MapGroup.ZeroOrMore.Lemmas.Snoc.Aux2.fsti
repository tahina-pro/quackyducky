module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas.Snoc.Aux2
open CDDL.Pulse.Serialize.Gen.MapGroup.Base
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

val impl_serialize_map_group_valid_map_zero_or_more_snoc_length1
  (#key #value: Type) (#tkey: typ) (sp1: spec tkey key true) (key_eq: EqTest.eq_test key)
  (#tvalue: typ) (#inj: bool) (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map) (m1: Map.t key (list value)) (k: key) (v: value) (m2: Map.t key (list value))
  (sq: squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m1' = map_of_list_snoc key_eq m1 k v in
    let m2' = map_of_list_cons key_eq k v m2 in
    sp.mg_serializable m1 /\ cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\ sp1.serializable k /\ sp2.serializable v /\
    (~ (except (sp1.serializer k, sp2.serializer v))) /\ sp.mg_serializable m2 /\
    (~ (Map.defined k m2)) /\
    (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
    sp.mg_serializable m2' /\
    cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2') /\
    sp.mg_serializable m1' /\
    cbor_map_disjoint l (sp.mg_serializer m1') /\
    cbor_map_length (sp.mg_serializer m1') == cbor_map_length (sp.mg_serializer m1) + 1
  ))
: Tot (squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m1' = map_of_list_snoc key_eq m1 k v in    
    let m2' = map_of_list_cons key_eq k v m2 in
    sp.mg_serializable m1' /\ sp.mg_serializable m2' /\
    cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') == cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) + cbor_map_length (sp.mg_serializer m2)
  ))
