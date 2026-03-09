module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas.Snoc.Aux
open CDDL.Pulse.Serialize.Gen.MapGroup.Base
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas.Snoc.Aux3
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1 --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native --split_queries always"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc'
  (#key #value: Type) (#tkey: typ) (sp1: spec tkey key true) (key_eq: EqTest.eq_test key)
  (#tvalue: typ) (#inj: bool) (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (maxl: cbor -> option nat)
  (l: cbor_map) (m1: Map.t key (list value)) (k: key) (v: value) (m2: Map.t key (list value)) (len: nat)
  (sq: squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ cbor_map_disjoint l (sp.mg_serializer m1) /\ map_of_list_maps_to_nonempty m2
  ))
: Tot (squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
      impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp (map_of_list_cons key_eq k v m2) len <==> (
      sp1.serializable k /\ sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v))) /\
      FStar.UInt.fits (cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1) 64 /\
      Some? (cbor_map_max_length maxl (cbor_map_union l (sp.mg_serializer m1))) /\
      Some? (maxl (sp1.serializer k)) /\ Some? (maxl (sp2.serializer v)) /\
      Some?.v (cbor_map_max_length maxl (cbor_map_union l (sp.mg_serializer m1))) + Some?.v (maxl (sp1.serializer k)) + Some?.v (maxl (sp2.serializer v)) <= len /\
      (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
      (sp.mg_serializable (map_of_list_snoc key_eq m1 k v) ==>
        impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v))) sp m2 len
      )
    ))
  ))
= let m2' = map_of_list_cons key_eq k v m2 in
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  map_of_list_maps_to_nonempty_cons key_eq k v m2 ();
  map_of_list_is_append_cons key_eq k v m2;
  map_of_list_is_append_serializable_elim sp1 sp2 except mkv m2 m2';
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  impl_serialize_map_group_valid_map_zero_or_more_snoc_aux sp1 key_eq sp2 except l m1 k v m2 len;
  if sp1.serializable k && sp2.serializable v && (not (except (sp1.serializer k, sp2.serializer v)))
  then begin
    if sp.mg_serializable m2
    then begin
      if Map.defined k m2
      then begin
        if cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))
        then ()
        else begin
          let m1' = map_of_list_snoc key_eq m1 k v in
          map_of_list_is_append_snoc key_eq m1 k v;
          assert (cbor_map_defined (sp1.serializer k) (sp.mg_serializer m2));
          assert (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1')));
          let _b0 = cbor_map_disjoint_tot (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2) in
          assert (_b0 == false);
          assert (sp.mg_serializable m1');
          ()
        end
      end
      else begin
        map_of_list_serializable_disjoint sp1 sp2 except mkv m2;
        map_of_list_is_append_serializable_intro sp1 sp2 except mkv m2 m2';
        impl_serialize_map_group_valid_map_zero_or_more_snoc_inner sp1 key_eq sp2 except maxl l m1 k v m2 len ()
      end
    end
    else begin
      let _v = impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len in
      if cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))
      then ()
      else begin
        let m1' = map_of_list_snoc key_eq m1 k v in
        let _v2 = impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1')) sp m2 len in
        ()
      end
    end
  end
  else begin
    let _v = impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len in
    ()
  end

#pop-options
