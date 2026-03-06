module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2

#push-options "--z3rlimit 1024 --split_queries always"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_length1_gen
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
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m2' = map_of_list_cons key_eq k v m2 in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\
    sp1.serializable k /\
    sp2.serializable v /\
    (~ (except (sp1.serializer k, sp2.serializer v))) /\
    sp.mg_serializable m2 /\
    (~ (Map.defined k m2)) /\
    (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
    sp.mg_serializable m2' /\
    cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m1' = map_of_list_snoc key_eq m1 k v in
    let m2' = map_of_list_cons key_eq k v m2 in
    sp.mg_serializable m1' /\
    sp.mg_serializable m2' /\
    cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') == cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) + cbor_map_length (sp.mg_serializer m2) /\
    cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2') == cbor_map_union (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2)
  ))
=
  impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1_gen sp1 key_eq sp2 except l m1 k v m2 ();
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  let m2' = map_of_list_cons key_eq k v m2 in
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_cons key_eq k v m2;
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  // establish mkv serializable
  let _sq_mkv_ser : squash (sp.mg_serializable mkv /\ sp.mg_serializer mkv == cbor_map_singleton (sp1.serializer k) (sp2.serializer v))
  = () in
  // establish m1 disjoint mkv
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  let _sq_m1_mkv_disj : squash (cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer mkv))
  = () in
  // establish m1' = union m1 mkv and m1' serializable
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  let _sq_m1'_props : squash (sp.mg_serializable m1' /\ sp.mg_serializer m1' == cbor_map_union (sp.mg_serializer m1) (sp.mg_serializer mkv))
  = () in
  // establish l disjoint m1'
  cbor_map_disjoint_union_r l (sp.mg_serializer m1) (sp.mg_serializer mkv);
  let _sq_l_m1'_disj : squash (cbor_map_disjoint l (sp.mg_serializer m1'))
  = () in
  // establish mkv disjoint m2
  map_of_list_serializable_disjoint sp1 sp2 except mkv m2;
  let _sq_mkv_m2_disj : squash (cbor_map_disjoint (sp.mg_serializer mkv) (sp.mg_serializer m2))
  = () in
  // establish m2' = union mkv m2
  map_of_list_is_append_serializable_intro sp1 sp2 except mkv m2 m2';
  let _sq_m2'_props : squash (sp.mg_serializable m2' /\ sp.mg_serializer m2' == cbor_map_union (sp.mg_serializer mkv) (sp.mg_serializer m2))
  = () in
  // length calculations: use move_requires to avoid needing explicit disjoint proofs at each call site
  Classical.move_requires (cbor_map_length_disjoint_union l) (sp.mg_serializer m1);
  Classical.move_requires (cbor_map_length_disjoint_union l) (sp.mg_serializer m1');
  Classical.move_requires (cbor_map_length_disjoint_union (sp.mg_serializer m1)) (sp.mg_serializer mkv);
  Classical.move_requires (cbor_map_length_disjoint_union (sp.mg_serializer mkv)) (sp.mg_serializer m2);
  Classical.move_requires (cbor_map_length_disjoint_union (cbor_map_union l (sp.mg_serializer m1))) (sp.mg_serializer m2');
  Classical.move_requires (cbor_map_length_disjoint_union (cbor_map_union l (sp.mg_serializer m1'))) (sp.mg_serializer m2);
  let ll = cbor_map_length l in
  let lm1 = cbor_map_length (sp.mg_serializer m1) in
  let lm2 = cbor_map_length (sp.mg_serializer m2) in
  impl_serialize_map_group_valid_map_zero_or_more_snoc_length ll lm1 1 lm2;
  // Union equality:
  // union (union l (s m1)) (s m2') = union (union l (s m1)) (union (s mkv) (s m2))
  //  = union l (union (s m1) (union (s mkv) (s m2)))     [by assoc]
  //  = union l (union (union (s m1) (s mkv)) (s m2))     [by assoc]
  //  = union l (union (s m1') (s m2))                    [by m1' def]
  //  = union (union l (s m1')) (s m2)                    [by assoc]
  cbor_map_union_assoc (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer mkv) (sp.mg_serializer m2);
  cbor_map_union_assoc l (sp.mg_serializer m1) (cbor_map_union (sp.mg_serializer mkv) (sp.mg_serializer m2));
  cbor_map_union_assoc l (sp.mg_serializer m1) (sp.mg_serializer mkv);
  cbor_map_union_assoc l (cbor_map_union (sp.mg_serializer m1) (sp.mg_serializer mkv)) (sp.mg_serializer m2);
  cbor_map_union_assoc l (sp.mg_serializer m1') (sp.mg_serializer m2);
  ()

#pop-options
