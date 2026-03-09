module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas.Snoc.Aux2
open CDDL.Pulse.Serialize.Gen.MapGroup.Base
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

#push-options "--z3rlimit 128 --fuel 2 --ifuel 1 --split_queries always --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_length1
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
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let m1' = map_of_list_snoc key_eq m1 k v in
  let m2' = map_of_list_cons key_eq k v m2 in
  // Conjunct 1: serializable m1' — directly from enriched precondition
  let _p1 : squash (sp.mg_serializable m1') = () in
  // Conjunct 2: serializable m2' — directly from enriched precondition
  let _p2 : squash (sp.mg_serializable m2') = () in
  // Intermediate: length m2' == 1 + length m2
  let _q1 : squash (cbor_map_length (sp.mg_serializer m2') == 1 + cbor_map_length (sp.mg_serializer m2)) =
    let mkv = EqTest.map_singleton k (key_eq k) [v] in
    map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
    map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
    assert (sp.mg_serializable mkv);
    assert (sp.mg_serializer mkv == cbor_map_singleton (sp1.serializer k) (sp2.serializer v));
    map_of_list_serializable_disjoint sp1 sp2 except mkv m2;
    assert (cbor_map_disjoint (sp.mg_serializer mkv) (sp.mg_serializer m2));
    map_of_list_is_append_cons key_eq k v m2;
    map_of_list_is_append_serializable_intro sp1 sp2 except mkv m2 m2';
    assert (sp.mg_serializer m2' == cbor_map_union (sp.mg_serializer mkv) (sp.mg_serializer m2));
    cbor_map_length_disjoint_union (sp.mg_serializer mkv) (sp.mg_serializer m2);
    cbor_map_length_singleton (sp1.serializer k) (sp2.serializer v)
  in
  // Intermediate: length (union l m1') == length (union l m1) + 1
  let _q2 : squash (cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) == cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + 1) =
    cbor_map_length_disjoint_union l (sp.mg_serializer m1');
    cbor_map_length_disjoint_union l (sp.mg_serializer m1)
  in
  // Chain via calc: from _q1 (b==1+d) and _q2 (c==a+1), prove a+b==c+d
  let _ = calc (==) {
    cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2');
    (==) { () }
    cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + (1 + cbor_map_length (sp.mg_serializer m2));
    (==) { () }
    (cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + 1) + cbor_map_length (sp.mg_serializer m2);
    (==) { () }
    cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) + cbor_map_length (sp.mg_serializer m2);
  } in
  ()

#pop-options
