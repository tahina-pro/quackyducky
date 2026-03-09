module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas.Snoc
open CDDL.Pulse.Serialize.Gen.MapGroup.Base
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas.Snoc.Aux
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1"

let impl_serialize_map_group_valid_map_zero_or_more_snoc
  (#key #value: Type) (#tkey: typ) (sp1: spec tkey key true) (key_eq: EqTest.eq_test key)
  (#tvalue: typ) (#inj: bool) (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (maxl: cbor -> option nat)
  (l: cbor_map) (m1: Map.t key (list value)) (k: key) (v: value) (m2: Map.t key (list value)) (len: nat)
= impl_serialize_map_group_valid_map_zero_or_more_snoc_aux sp1 key_eq sp2 except l m1 k v m2 len;
  impl_serialize_map_group_valid_map_zero_or_more_snoc' sp1 key_eq sp2 except maxl l m1 k v m2 len ()

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_overflow
  (#key #value: Type) (#tkey: typ) (sp1: spec tkey key true) (key_eq: EqTest.eq_test key)
  (#tvalue: typ) (#inj: bool) (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (maxl: cbor -> option nat)
  (l: cbor_map) (m1: Map.t key (list value)) (m2: Map.t key (list value)) (len: nat)
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let prf (k: key)
  : Lemma (requires (Map.defined k m2))
    (ensures (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2 len)))
  = let Some lv = Map.get m2 k in
    let v :: lv' = lv in
    let m2' = map_of_list_sub key_eq m2 k v lv' in
    map_of_list_is_append_cons key_eq k v m2';
    impl_serialize_map_group_valid_map_zero_or_more_snoc sp1 key_eq sp2 except maxl l m1 k v m2' len
  in
  Classical.forall_intro (Classical.move_requires prf);
  assert (~ (Map.equal m2 (Map.empty _ _)))

#pop-options
