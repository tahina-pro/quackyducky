module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux1
include CDDL.Pulse.Serialize.Gen.MapGroup.Base
include Pulse.Lib.Pervasives
include CBOR.Spec.API.Type
include CBOR.Pulse.API.Base

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

include CDDL.Pulse.Serialize.Gen.MapGroup.Aux
include CDDL.Pulse.Serialize.Gen.MapGroup.Choice

let impl_serialize_map_zero_or_more_insert_pre_helper
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (pe: cbor_parser)
  (l: cbor_map)
  (key: cbor)
  (value: cbor)
  (wl: Seq.seq U8.t)
  (w0_slice w1_slice w2_slice: Seq.seq U8.t)
  (size0: SZ.t) (size1 size2: SZ.t)
: Lemma
  (requires (
    SZ.v size0 <= SZ.v size1 /\
    SZ.v size1 <= SZ.v size2 /\
    SZ.v size2 == Seq.length wl /\
    p (cbor_map_length l) w0_slice == Some (l, SZ.v size0) /\
    Seq.slice wl 0 (SZ.v size0) == w0_slice /\
    pe w1_slice == Some (key, SZ.v size1 - SZ.v size0) /\
    Seq.slice wl (SZ.v size0) (SZ.v size1) == w1_slice /\
    pe w2_slice == Some (value, SZ.v size2 - SZ.v size1) /\
    Seq.slice wl (SZ.v size1) (Seq.length wl) == w2_slice
  ))
  (ensures (
    cbor_serialize_map_insert_pre p pe l size0 key size1 value wl
  ))
= ()

(* Helper that works with the buffer shapes after split/join in the iterator *)
let impl_serialize_map_zero_or_more_insert_pre_helper2
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (pe: cbor_parser)
  (l: cbor_map)
  (key: cbor)
  (value: cbor)
  (w_orig: Seq.seq U8.t)
  (w1_after_key: Seq.seq U8.t)
  (z2l: Seq.seq U8.t)
  (w2: Seq.seq U8.t)
  (count: U64.t)
  (size0: SZ.t) (sz1 sz2: SZ.t)
: Lemma
  (requires (
    SZ.v sz1 > 0 /\
    SZ.v sz2 > 0 /\
    SZ.v size0 <= Seq.length w_orig /\
    SZ.fits (SZ.v size0 + SZ.v sz1) /\
    SZ.fits (SZ.v size0 + SZ.v sz1 + SZ.v sz2) /\
    SZ.v size0 + SZ.v sz1 + SZ.v sz2 <= Seq.length w_orig /\
    p (U64.v count) w_orig == Some (l, SZ.v size0) /\
    Seq.length w1_after_key == Seq.length w_orig - SZ.v size0 /\
    z2l == Seq.slice w1_after_key 0 (SZ.v sz1) /\
    pe (Seq.slice w1_after_key 0 (SZ.v sz1)) == Some (key, SZ.v sz1) /\
    SZ.v sz2 <= Seq.length w2 /\
    Seq.length w2 == Seq.length w1_after_key - SZ.v sz1 /\
    pe (Seq.slice w2 0 (SZ.v sz2)) == Some (value, SZ.v sz2)
  ))
  (ensures (
    let size1 = SZ.uint_to_t (SZ.v size0 + SZ.v sz1) in
    let size2 = SZ.uint_to_t (SZ.v size0 + SZ.v sz1 + SZ.v sz2) in
    let wl = Seq.slice (Seq.append (Seq.slice w_orig 0 (SZ.v size0)) (Seq.append z2l w2)) 0 (SZ.v size2) in
    cbor_serialize_map_insert_pre p pe l size0 key size1 value wl
  ))
= let size1_n = SZ.v size0 + SZ.v sz1 in
  let size2_n = size1_n + SZ.v sz2 in
  let w_joined = Seq.append (Seq.slice w_orig 0 (SZ.v size0)) (Seq.append z2l w2) in
  let wl = Seq.slice w_joined 0 size2_n in
  let w0s = Seq.slice w_orig 0 (SZ.v size0) in
  Seq.lemma_eq_elim (Seq.slice wl 0 (SZ.v size0)) w0s;
  // p returns cbor_map_length m == n, so cbor_map_length l == U64.v count
  cbor_parse_map_prefix_slice p (U64.v count) w_orig l (SZ.v size0);
  assert (p (U64.v count) w0s == Some (l, SZ.v size0));
  assert (cbor_map_length l == U64.v count);
  Seq.lemma_eq_elim (Seq.slice wl (SZ.v size0) size1_n) z2l;
  Seq.lemma_eq_elim (Seq.slice wl size1_n (Seq.length wl)) (Seq.slice w2 0 (SZ.v sz2))

(* impl_serialize_map_zero_or_more *)

let impl_serialize_map_zero_or_more_iterator_inv_gen
    (p: bare_cbor_map_parser) (minl: cbor -> nat) (maxl: cbor -> option nat)
    (#key: typ) (#tkey: Type0)
    (sp1: spec key tkey true)
    (#value: typ) (#tvalue: Type0) (#inj: bool)
    (sp2: spec value tvalue inj)
    (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (v0: Map.t tkey (list tvalue))
  (l: cbor_map)
  (res: bool)
  (w: Seq.seq U8.t)
  (m1 m2 m2': Map.t tkey (list tvalue))
  (count: U64.t)
  (size: SZ.t)
: Tot prop
=
  let sp = (mg_zero_or_more_match_item sp1 sp2 except) in
      map_of_list_is_append m1 m2' v0 /\
      map_of_list_maps_to_nonempty m1 /\
      sp.mg_serializable m1 /\
      cbor_map_disjoint l (sp.mg_serializer m1) /\
      (res == true ==> (
        m2' == m2 /\
        impl_serialize_map_group_pre p count size (cbor_map_union l (sp.mg_serializer m1)) w
      )) /\
      impl_serialize_map_group_valid maxl l sp v0 (Seq.length w) == (if res then impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' (Seq.length w) else false)

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
let map_of_list_serializable_disjoint
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
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
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m
  ))
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
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m
  ))
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
    let prf_m (kv: (cbor & cbor)) : Lemma (cbor_map_mem kv (sp.mg_serializer m) <==> map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m kv)
    = map_group_zero_or_more_match_item_serializer'_mem sp1 sp2 except m kv
    in
    let prf_m1 (kv: (cbor & cbor)) : Lemma (cbor_map_mem kv (sp.mg_serializer m1) <==> map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m1 kv)
    = map_group_zero_or_more_match_item_serializer'_mem sp1 sp2 except m1 kv
    in
    let prf_m2 (kv: (cbor & cbor)) : Lemma (cbor_map_mem kv (sp.mg_serializer m2) <==> map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m2 kv)
    = map_group_zero_or_more_match_item_serializer'_mem sp1 sp2 except m2 kv
    in
    Classical.forall_intro prf_m;
    Classical.forall_intro prf_m1;
    Classical.forall_intro prf_m2;
    assert (
      forall kv . (map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m kv <==> (map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m1 kv \/ map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m2 kv)
    ));
    cbor_map_mem_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2);
    cbor_map_mem_ext (sp.mg_serializer m) (sp.mg_serializer m1 `cbor_map_union` sp.mg_serializer m2)
  end

#pop-options

let map_of_list_is_append_snoc
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
: Lemma
  (map_of_list_is_append
    m1
    (Map.singleton k (key_eq k) [v])
    (map_of_list_snoc key_eq m1 k v)
  )
= ()

let map_of_list_is_append_cons
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m1: Map.t key (list value))
: Lemma
  (map_of_list_is_append
    (Map.singleton k (key_eq k) [v])
    m1
    (map_of_list_cons key_eq k v m1)
  )
= ()

#push-options "--z3rlimit 64 --split_queries always"

#restart-solver
let map_of_list_is_append_serializable_elim
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
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
    (sp.mg_serializable m
    ) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  if sp.mg_serializable m
  then begin
    assert (
      sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2
    );
    map_of_list_serializable_disjoint sp1 sp2 except m1 m2
  end

let map_of_list_is_append_serializable_elim'
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
  (sq: squash (map_of_list_is_append m1 m2 m))
  (sq1: squash (map_of_list_maps_to_nonempty m1))
  (sq2: squash (map_of_list_maps_to_nonempty m2))
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m
    ) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))
= map_of_list_is_append_serializable_elim sp1 sp2 except m1 m2 m

#pop-options

#push-options "--z3rlimit 64"

#restart-solver
let map_of_list_is_append_serializable_singleton
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (k: key)
  (k_eq: EqTest.eq_test_for k)
  (v: value)
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m = EqTest.map_singleton k k_eq [v] in
    (sp.mg_serializable m <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v)))
    )) /\
    (sp.mg_serializable m ==> (
    sp.mg_serializer m == cbor_map_singleton (sp1.serializer k) (sp2.serializer v)
  ))))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let m = EqTest.map_singleton k k_eq [v] in
  assert (forall kv . Map.mem kv m <==> (fst kv == k /\ snd kv == [v]));
  assert (sp.mg_serializable m <==> (forall kv . Map.mem kv m ==> map_entry_serializable sp1 sp2 except kv));
  assert (sp.mg_serializable m <==> map_entry_serializable sp1 sp2 except (k, [v]));
  if sp.mg_serializable m
  then begin
    let prf (kv: (cbor & cbor)) : Lemma (cbor_map_mem kv (sp.mg_serializer m) <==> map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m kv)
    = map_group_zero_or_more_match_item_serializer'_mem sp1 sp2 except m kv
    in
    Classical.forall_intro prf;
    cbor_map_mem_ext
      (sp.mg_serializer m)
      (cbor_map_singleton (sp1.serializer k) (sp2.serializer v))
  end

#pop-options

let map_of_list_maps_to_nonempty_singleton
  (#key: Type)
  (#value: Type)
  (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: list value)
  (sq: squash (Cons? v))
: Lemma
  (map_of_list_maps_to_nonempty (Map.singleton k k_eq v))
= ()

let map_of_list_maps_to_nonempty_cons
  (#key: Type)
  (#value: Type)
  (k_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m: Map.t key (list value))
  (sq: squash (map_of_list_maps_to_nonempty m))
: Lemma
  (map_of_list_maps_to_nonempty (map_of_list_cons k_eq k v m))
= ()

let impl_serialize_map_group_valid_map_zero_or_more_snoc_length
  (ll lm1 lkv lm2: nat)
: Lemma
  ((ll + lm1) + (lkv + lm2) == (ll + (lm1 + lkv)) + lm2)
= ()

#push-options "--z3rlimit 32 --print_implicits"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_aux_gen
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
=
  let m2' = map_of_list_cons key_eq k v m2 in
  map_of_list_maps_to_nonempty_cons key_eq k v m2 ();
  assert (map_of_list_maps_to_nonempty m2');
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_serializable_elim sp1 sp2 except mkv m2 m2';
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  if
        sp1.serializable k &&
        sp2.serializable v &&
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

#push-options "--z3rlimit 256 --split_queries always"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1_gen
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
  (sq: squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    sp1.serializable k /\
    sp2.serializable v /\
    (~ (except (sp1.serializer k, sp2.serializer v))) /\
    sp.mg_serializable m2 /\
    (~ (Map.defined k m2)) /\
    (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
  ))
: Tot (squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m1' = map_of_list_snoc key_eq m1 k v in
    sp.mg_serializable m1' /\
    cbor_map_disjoint (sp.mg_serializer m1') (sp.mg_serializer m2) <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
  ))
=
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  map_of_list_serializable_disjoint sp1 sp2 except m1 m2;
  map_of_list_serializable_disjoint sp1 sp2 except m1' m2;
  ()

#pop-options
