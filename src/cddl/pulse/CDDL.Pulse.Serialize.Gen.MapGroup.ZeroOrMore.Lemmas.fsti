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

val map_of_list_serializable_disjoint
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

val map_of_list_is_append_serializable_intro
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

val map_of_list_is_append_serializable_elim
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

val map_of_list_is_append_serializable_singleton
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

val map_of_list_maps_to_nonempty_singleton
  (#key: Type) (#value: Type) (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: list value) (sq: squash (Cons? v))
: Lemma (map_of_list_maps_to_nonempty (Map.singleton k k_eq v))

val map_of_list_maps_to_nonempty_cons
  (#key: Type) (#value: Type) (k_eq: EqTest.eq_test key)
  (k: key) (v: value) (m: Map.t key (list value))
  (sq: squash (map_of_list_maps_to_nonempty m))
: Lemma (map_of_list_maps_to_nonempty (map_of_list_cons k_eq k v m))

val map_of_list_is_append_snoc
  (#key #value: Type) (key_eq: EqTest.eq_test key) (m1: Map.t key (list value)) (k: key) (v: value)
: Lemma (map_of_list_is_append m1 (Map.singleton k (key_eq k) [v]) (map_of_list_snoc key_eq m1 k v))

val map_of_list_is_append_cons
  (#key #value: Type) (key_eq: EqTest.eq_test key) (k: key) (v: value) (m1: Map.t key (list value))
: Lemma (map_of_list_is_append (Map.singleton k (key_eq k) [v]) m1 (map_of_list_cons key_eq k v m1))

val map_of_list_sub
  (#key #value: Type) (key_eq: EqTest.eq_test key) (m: Map.t key (list value)) (k: key) (v: value) (lv': list value)
: Pure (Map.t key (list value))
  (requires (Map.get m k == Some (v :: lv')))
  (ensures fun m' ->
    (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m') /\
    m == map_of_list_cons key_eq k v m'
  )

val impl_serialize_map_group_valid_map_zero_or_more_snoc_aux
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

(* Definitions that must be in the interface *)

let impl_serialize_map_zero_or_more_iterator_inv
    (#key: typ) (#tkey: Type0) (sp1: (spec key tkey true))
    (#value: typ) (#tvalue: Type0) (#inj: bool) (sp2: (spec value tvalue inj))
    (except: map_constraint { map_constraint_value_injective key sp2.parser except })
    (p: bare_cbor_map_parser)
    (maxl: cbor -> option nat)
    (v0: Map.t tkey (list tvalue)) (l: cbor_map)
    (res: bool) (w: Seq.seq U8.t) (m1 m2 m2': Map.t tkey (list tvalue))
    (count: U64.t) (size: SZ.t)
: Tot prop
= let sp = (mg_zero_or_more_match_item sp1 sp2 except) in
    map_of_list_is_append m1 m2' v0 /\
    map_of_list_maps_to_nonempty m1 /\
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    (res == true ==> (
      m2' == m2 /\
      impl_serialize_map_group_pre p count size (cbor_map_union l (sp.mg_serializer m1)) w
    )) /\
    impl_serialize_map_group_valid maxl l sp v0 (Seq.length w) == (res && impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' (Seq.length w))

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator_gen_t
    (#pe: cbor_parser)
    (#minl: cbor_min_length pe)
    (#maxl: cbor_max_length pe)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    ([@@@erasable]r1: rel ikey tkey)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    ([@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    ([@@@erasable] except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (#ivalue: Type0)
    ([@@@erasable]r2: rel ivalue tvalue)
    (#p: cbor_map_parser minl maxl)
    (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec ikey) -> [@@@erasable] Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
= impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (r (Iterator.mk_spec r1) (Iterator.mk_spec r2))

val impl_serialize_map_group_insert_prf
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

let slice_split_post
  (#t: Type) (i: SZ.t) (v v1 v2: Seq.seq t)
: Tot prop
= SZ.v i <= Seq.length v /\
  v1 == Seq.slice v 0 (SZ.v i) /\
  v2 == Seq.slice v (SZ.v i) (Seq.length v) /\
  Seq.length v1 == SZ.v i /\
  Seq.length v2 == Seq.length v - SZ.v i /\
  v == Seq.append v1 v2
