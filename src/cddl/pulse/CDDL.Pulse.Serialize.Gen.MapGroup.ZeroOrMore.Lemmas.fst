module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas
open CDDL.Pulse.Serialize.Gen.MapGroup.Base
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Cbor = CBOR.Spec.API.Format
module Iterator = CDDL.Pulse.Iterator.Base

#push-options "--z3rlimit 32 --split_queries always --fuel 2 --ifuel 1"

#restart-solver
let map_of_list_serializable_disjoint
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2) ==>
    (Map.disjoint m1 m2 <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2))
  ))
= ()

#restart-solver
let map_of_list_is_append_serializable_intro_serializable
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (map_of_list_is_append m1 m2 m))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2 /\ Map.disjoint m1 m2) ==>
      sp.mg_serializable m
  ))
= ()

#restart-solver
let map_of_list_is_append_serializable_intro
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (map_of_list_is_append m1 m2 m))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2 /\ (Map.disjoint m1 m2 \/ cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2))) ==>
    (Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2) /\
      sp.mg_serializable m /\
      sp.mg_serializer m == (sp.mg_serializer m1 `cbor_map_union` sp.mg_serializer m2)
    )
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro_serializable sp1 sp2 except m1 m2 m;
  map_of_list_serializable_disjoint sp1 sp2 except m1 m2;
  if sp.mg_serializable m1 && sp.mg_serializable m2 && cbor_map_disjoint_tot (sp.mg_serializer m1) (sp.mg_serializer m2)
  then begin
    assert (
      forall kv . (map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m kv <==> (map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m1 kv \/ map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m2 kv)
    ));
    cbor_map_mem_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2);
    cbor_map_mem_ext (sp.mg_serializer m) (sp.mg_serializer m1 `cbor_map_union` sp.mg_serializer m2)
  end

#push-options "--z3rlimit 128 --fuel 2 --ifuel 1 --split_queries no"
#restart-solver
let map_of_list_is_append_serializable_elim
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m /\
    map_of_list_maps_to_nonempty m1 /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let aux (k: key) : Lemma
    (requires (Map.defined k m1 /\ Map.defined k m2))
    (ensures (~ (sp.mg_serializable m)))
  = let Some l1 = Map.get m1 k in
    let Some l2 = Map.get m2 k in
    List.Tot.append_length l1 l2;
    assert (List.Tot.length (List.Tot.append l1 l2) >= 2);
    assert (Map.get m k == Some (List.Tot.append l1 l2));
    assert (Map.mem (k, List.Tot.append l1 l2) m);
    assert (~ (map_entry_serializable sp1 sp2 except (k, List.Tot.append l1 l2)))
  in
  Classical.forall_intro (Classical.move_requires aux);
  map_of_list_serializable_disjoint sp1 sp2 except m1 m2
#pop-options

#restart-solver
let map_of_list_is_append_serializable_singleton
  (#key #value: Type) (#tkey: typ) (sp1: spec tkey key true)
  (#tvalue: typ) (#inj: bool) (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (k: key) (k_eq: EqTest.eq_test_for k) (v: value)
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m = EqTest.map_singleton k k_eq [v] in
    (sp.mg_serializable m <==> (sp1.serializable k /\ sp2.serializable v /\ (~ (except (sp1.serializer k, sp2.serializer v))))) /\
    (sp.mg_serializable m ==> (sp.mg_serializer m == cbor_map_singleton (sp1.serializer k) (sp2.serializer v)))))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let m = EqTest.map_singleton k k_eq [v] in
  assert (forall kv . Map.mem kv m <==> (fst kv == k /\ snd kv == [v]));
  assert (sp.mg_serializable m <==> (forall kv . Map.mem kv m ==> map_entry_serializable sp1 sp2 except kv));
  assert (sp.mg_serializable m <==> map_entry_serializable sp1 sp2 except (k, [v]));
  if sp.mg_serializable m
  then begin
    cbor_map_mem_ext (sp.mg_serializer m) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v))
  end

#pop-options

#push-options "--fuel 2 --ifuel 1"

let map_of_list_maps_to_nonempty_singleton
  (#key: Type) (#value: Type) (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: list value) (sq: squash (Cons? v))
: Lemma (map_of_list_maps_to_nonempty (Map.singleton k k_eq v))
= ()

let map_of_list_maps_to_nonempty_cons
  (#key: Type) (#value: Type) (k_eq: EqTest.eq_test key)
  (k: key) (v: value) (m: Map.t key (list value))
  (sq: squash (map_of_list_maps_to_nonempty m))
: Lemma (map_of_list_maps_to_nonempty (map_of_list_cons k_eq k v m))
= ()

let map_of_list_is_append_snoc
  (#key #value: Type) (key_eq: EqTest.eq_test key) (m1: Map.t key (list value)) (k: key) (v: value)
: Lemma (map_of_list_is_append m1 (Map.singleton k (key_eq k) [v]) (map_of_list_snoc key_eq m1 k v))
= ()

let map_of_list_is_append_cons
  (#key #value: Type) (key_eq: EqTest.eq_test key) (k: key) (v: value) (m1: Map.t key (list value))
: Lemma (map_of_list_is_append (Map.singleton k (key_eq k) [v]) m1 (map_of_list_cons key_eq k v m1))
= ()

#pop-options

#push-options "--fuel 2 --ifuel 1"

let map_of_list_sub
  (#key #value: Type) (key_eq: EqTest.eq_test key) (m: Map.t key (list value)) (k: key) (v: value) (lv': list value)
: Pure (Map.t key (list value))
  (requires (Map.get m k == Some (v :: lv')))
  (ensures fun m' ->
    (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m') /\
    m == map_of_list_cons key_eq k v m'
  )
= let f (kv: (key & list value)) : bool = not (key_eq k (fst kv)) in
  let m' : Map.t key (list value) = match lv' with
  | [] -> Map.filter f m
  | _ -> EqTest.map_set #key #(list value) m k (key_eq k) lv'
  in
  assert (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m');
  assert (Map.equal m (map_of_list_cons key_eq k v m'));
  m'

#pop-options

(* ===== Snoc aux lemma ===== *)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 1"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_aux
  (#key #value: Type) (#tkey: typ) (sp1: spec tkey key true) (key_eq: EqTest.eq_test key)
  (#tvalue: typ) (#inj: bool) (sp2: spec tvalue value inj)
  (except: map_constraint { map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map) (m1: Map.t key (list value)) (k: key) (v: value) (m2: Map.t key (list value)) (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ cbor_map_disjoint l (sp.mg_serializer m1) /\ map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
      (sp1.serializable k /\ sp2.serializable v /\
        (~ (except (sp1.serializer k, sp2.serializer v))) /\
        (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
      ) ==> (
      sp.mg_serializable (map_of_list_snoc key_eq m1 k v) /\
      cbor_map_disjoint l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) /\
      cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)) /\
      cbor_map_length (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_length (sp.mg_serializer m1) + 1
  ))))
= 
  let m2' = map_of_list_cons key_eq k v m2 in
  map_of_list_maps_to_nonempty_cons key_eq k v m2 ();
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_cons key_eq k v m2;
  map_of_list_is_append_serializable_elim sp1 sp2 except mkv m2 m2';
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  if sp1.serializable k && sp2.serializable v &&
     (not (except (sp1.serializer k, sp2.serializer v))) &&
     (not (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
  then begin
      assert (sp.mg_serializable m1');
      assert (cbor_map_disjoint l (sp.mg_serializer mkv));
      assert (cbor_map_disjoint l (sp.mg_serializer m1'));
      assert (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)));
      assert (cbor_map_length (sp.mg_serializer mkv) == 1);
      assert (cbor_map_length (sp.mg_serializer m1') == cbor_map_length (sp.mg_serializer m1) + 1)
  end

#pop-options
(* ===== Iterator invariant: defined in .fsti ===== *)

(* ===== Iterator gen type: defined in .fsti ===== *)

(* ===== slice_split_post: defined in .fsti ===== *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

let impl_serialize_map_group_insert_prf
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (pe: cbor_parser)
  (w: Seq.seq U8.t)
  (l: cbor_map)
  (sz0: nat)
  (k: cbor)
  (sz1: nat { sz0 + sz1 <= Seq.length w })
  (v: cbor)
  (sz2: nat)
  (w2: Seq.seq U8.t { Seq.length w2 <= Seq.length w - sz0 - sz1 })
: Lemma
  (requires (
    p (cbor_map_length l) w == Some (l, sz0) /\
    pe (Seq.slice (Seq.slice w sz0 (Seq.length w)) 0 sz1) == Some (k, sz1) /\
    sz2 <= Seq.length w2 /\
    Seq.slice w2 0 sz2 `Seq.equal` (Seq.slice (Seq.slice (Seq.slice w (sz0 + sz1) (Seq.length w)) 0 (Seq.length w2)) 0 sz2) /\
    pe (Seq.slice w2 0 sz2) == Some (v, sz2) /\
    SZ.fits (sz0 + sz1 + sz2)
  ))
  (ensures (
    SZ.fits (sz0 + sz1 + sz2) /\
    sz0 + sz1 + sz2 <= Seq.length w /\
    cbor_serialize_map_insert_pre p pe l (SZ.uint_to_t sz0) k (SZ.uint_to_t (sz0 + sz1)) v (Seq.slice w 0 (sz0 + sz1 + sz2))
  ))
= let w' = Seq.slice w 0 (sz0 + sz1 + sz2) in
  let size0 = SZ.uint_to_t sz0 in
  let size1 = SZ.uint_to_t (sz0 + sz1) in
  let size2 = SZ.uint_to_t (sz0 + sz1 + sz2) in
  Seq.lemma_eq_elim (Seq.slice w' 0 (SZ.v size0)) (Seq.slice w 0 sz0);
  cbor_parse_map_prefix_slice p (cbor_map_length l) w l sz0;
  Seq.lemma_eq_elim (Seq.slice w' (SZ.v size0) (SZ.v size1)) (Seq.slice (Seq.slice w sz0 (Seq.length w)) 0 sz1);
  Seq.lemma_eq_elim (Seq.slice w' (SZ.v size1) (SZ.v size2)) (Seq.slice w2 0 sz2);
  ()

#pop-options

(* slice_split_post is defined in .fsti *)

(* seq_slice_append_pat has SMTPat — keep in .fst only, NOT exposed in .fsti *)
#push-options "--fuel 2 --ifuel 1"

let seq_slice_append_pat
  (#t: Type) (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
  [SMTPat (Seq.append s1 s2)]
= ()

#pop-options
