module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux4

#push-options "--z3rlimit 64"

#restart-solver

let impl_serialize_map_group_valid_map_zero_or_more_snoc_overflow_gen
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
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let prf
    (k: key)
  : Lemma
    (requires (Map.defined k m2))
    (ensures (
      impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2 len == false
    ))
  = assert (Some? (Map.get m2 k));
    let Some lv = Map.get m2 k in
    assert (Cons? lv);
    let v :: lv' = lv in
    let m2' = map_of_list_sub key_eq m2 k v lv' in
    map_of_list_is_append_cons key_eq k v m2';
    impl_serialize_map_group_valid_map_zero_or_more_snoc_gen maxl sp1 key_eq sp2 except l m1 k v m2' len;
    ()
  in
  Classical.forall_intro (Classical.move_requires prf);
  assert (~ (Map.equal m2 (Map.empty _ _)));
  ()

#restart-solver

let impl_serialize_map_group_insert_prf_gen
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
= let sz1 = Seq.length z2l in
  let z1l = Seq.slice w_inv 0 sz0 in
  let w = Seq.append z1l (Seq.append z2l w2) in
  let w' = Seq.slice w 0 (sz0 + sz1 + sz2) in
  // Establish Seq.slice w' 0 sz0 == z1l
  Seq.append_slices z1l (Seq.append z2l w2);
  Seq.slice_slice w 0 (sz0 + sz1 + sz2) 0 sz0;
  assert (Seq.slice w' 0 sz0 == z1l);
  // p count z1l == Some (l, sz0) via prefix prop from p count w_inv
  assert (Seq.equal (Seq.slice z1l 0 sz0) z1l);
  assert (Seq.slice w_inv 0 sz0 == z1l);
  // w'[sz0..sz0+sz1] == z2l
  Seq.lemma_split w sz0;
  Seq.slice_slice w sz0 (Seq.length w) 0 sz1;
  Seq.append_slices z2l w2;
  assert (Seq.slice w' sz0 (sz0 + sz1) == z2l);
  // w'[(sz0+sz1)..] == Seq.slice w2 0 sz2
  Seq.slice_slice w sz0 (Seq.length w) sz1 (sz1 + sz2);
  Seq.slice_slice w 0 (sz0 + sz1 + sz2) (sz0 + sz1) (sz0 + sz1 + sz2);
  assert (Seq.slice w' (sz0 + sz1) (Seq.length w') == Seq.slice w2 0 sz2);
  ()

#pop-options
