module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux3

#push-options "--z3rlimit 256 --z3cliopt 'smt.qi.eager_threshold=100' --split_queries always"

#restart-solver

let impl_serialize_map_group_valid_map_zero_or_more_snoc_gen
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
= impl_serialize_map_group_valid_map_zero_or_more_snoc_aux_gen maxl sp1 key_eq sp2 except l m1 k v m2 len;
  let m2' = map_of_list_cons key_eq k v m2 in
  map_of_list_is_append_cons key_eq k v m2;
  let sq1 : squash (map_of_list_maps_to_nonempty m2) = assert (map_of_list_maps_to_nonempty m2) in
  let sq2 : squash (map_of_list_maps_to_nonempty m2') = map_of_list_maps_to_nonempty_cons key_eq k v m2 sq1 in
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_serializable_elim' sp1 sp2 except mkv m2 m2' () () sq2;
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  if
    sp1.serializable k &&
    sp2.serializable v &&
    (not (except (sp1.serializer k, sp2.serializer v)))
  then begin
    if sp.mg_serializable m2
    then begin
      map_of_list_serializable_disjoint sp1 sp2 except mkv m2;
      if Map.defined k m2
      then ()
      else begin
        map_of_list_is_append_cons key_eq k v m2;
        map_of_list_is_append_serializable_intro sp1 sp2 except mkv m2 m2';
        if cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))
        then begin
          assert (~ (cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')));
          assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))
        end
        else begin
          assert (cbor_map_disjoint l (sp.mg_serializer m1'));
          assert (cbor_map_disjoint l (sp.mg_serializer m2') <==> cbor_map_disjoint l (sp.mg_serializer m2));
          assert (cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2') <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2));
          map_of_list_is_append_snoc key_eq m1 k v;
          impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1_gen sp1 key_eq sp2 except l m1 k v m2 ();
          assert (cbor_map_disjoint (sp.mg_serializer m1') (sp.mg_serializer m2) <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2));
          assert (cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2') <==> cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2));
          if cbor_map_disjoint_tot (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')
          then begin
            cbor_map_length_disjoint_union l (sp.mg_serializer m1');
            impl_serialize_map_group_valid_map_zero_or_more_snoc_length1_gen sp1 key_eq sp2 except l m1 k v m2;
            assert (cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') == cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) + cbor_map_length (sp.mg_serializer m2));
            assert (cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') >= cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + 1);
            // The key insight for Gen: union l' s(m2') == union l'' s(m2)
            // so cbor_map_max_length maxl of both sides is the same
            assert (cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2') == cbor_map_union (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2));
            ()
          end
          else begin
            assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len));
            assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1')) sp m2 len))
          end
        end
      end
    end
    else begin
      assert (forall l' . ~ (impl_serialize_map_group_valid maxl l' sp m2 len));
      assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))
    end
  end
  else assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))

#pop-options
