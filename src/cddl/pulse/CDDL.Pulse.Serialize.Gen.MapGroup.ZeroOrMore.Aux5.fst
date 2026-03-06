module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux5
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux4
#lang-pulse

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

module SM = Pulse.Lib.SeqMatch

let seq_slice_append_pat (#t: Type) (s1 s2: Seq.seq t)
: Lemma
  (ensures Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
  [SMTPat (Seq.append s1 s2)]
= Seq.lemma_split (Seq.append s1 s2) (Seq.length s1);
  Seq.append_slices s1 s2

let slice_split_post
  (#t: Type)
  (i: SZ.t)
  (v v1 v2: Seq.seq t)
: Tot prop
= SZ.v i <= Seq.length v /\
  v1 == Seq.slice v 0 (SZ.v i) /\
  v2 == Seq.slice v (SZ.v i) (Seq.length v) /\
  Seq.length v1 == SZ.v i /\
  Seq.length v2 == Seq.length v - SZ.v i /\
  v == Seq.append v1 v2

inline_for_extraction noextract [@@noextract_to "krml"]
fn slice_split (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t) (#v: Ghost.erased (Seq.seq t))
    requires pts_to s #p v ** pure (
      SZ.v i <= Seq.length v
    )
    returns res: (S.slice t & S.slice t)
    ensures (let (s1, s2) = res in exists* v1 v2 .
      pts_to s1 #p v1 **
      pts_to s2 #p v2 **
      S.is_split s s1 s2 **
      pure (slice_split_post i v v1 v2)
    )
{
  Seq.lemma_split v (SZ.v i);
  let (s1, s2) = S.split s i;
  (s1, s2)
}

(* Gen iterator type alias *)

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator_gen_t
    (p: bare_cbor_map_parser) (minl: cbor -> nat) (maxl: cbor -> option nat)
    (#key: Ghost.erased typ) (#tkey: Type0)
    (sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0) (r1: rel ikey tkey)
    (#value: Ghost.erased typ) (#tvalue: Type0) (#inj: Ghost.erased bool)
    (sp2: Ghost.erased (spec value tvalue inj))
    (except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (#ivalue: Type0) (r2: rel ivalue tvalue)
    (iterator: (Ghost.erased (Iterator.type_spec ikey) -> Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
= impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_
    (mg_zero_or_more_match_item sp1 sp2 except) #_ (r (Iterator.mk_spec r1) (Iterator.mk_spec r2))

(* Gen iterator core loop function *)

(* Helper: when except holds, valid l sp v0 len == false *)
let impl_serialize_map_zero_or_more_valid_false_except_gen
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
  (ke: key)
  (va: value)
  (m2 v0: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\
    sp1.serializable ke /\
    sp2.serializable va /\
    except (sp1.serializer ke, sp2.serializer va) /\
    impl_serialize_map_group_valid maxl l sp v0 len ==
      impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp (map_of_list_cons key_eq ke va m2) len
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    impl_serialize_map_group_valid maxl l sp v0 len == false
  ))
= impl_serialize_map_group_valid_map_zero_or_more_snoc_gen maxl sp1 key_eq sp2 except l m1 ke va m2 len

let map_of_list_maps_to_nonempty_snoc
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m: Map.t key (list value))
  (k: key)
  (v: value)
: Lemma
  (requires map_of_list_maps_to_nonempty m)
  (ensures map_of_list_maps_to_nonempty (map_of_list_snoc key_eq m k v))
= let m' = map_of_list_snoc key_eq m k v in
  let aux (k': key) : Lemma (map_of_list_maps_to_nonempty_at m' k') =
    if key_eq k k' then
      match Map.get m k with
      | None -> ()
      | Some l -> List.Tot.append_length l [v]
    else ()
  in
  Classical.forall_intro aux

// Helper: explicitly apply cbor_parse_prefix_prop to go from pe (slice x 0 n) to pe x
#push-options "--z3rlimit 32"
let cbor_parse_prefix_apply
  (pe: cbor_parser)
  (x: Seq.seq U8.t)
  (n: nat)
: Lemma
  (requires (
    n <= Seq.length x /\
    Some? (pe (Seq.slice x 0 n))
  ))
  (ensures (
    pe x == pe (Seq.slice x 0 n)
  ))
= let y = Seq.slice x 0 n in
  let sn = Some?.v (pe y) in
  assert (0 < snd sn /\ snd sn <= Seq.length y);
  assert (snd sn <= n);
  assert (Seq.length x >= snd sn);
  assert (Seq.equal (Seq.slice y 0 (snd sn)) (Seq.slice x 0 (snd sn)));
  assert (cbor_parse_prefix_prop' pe y x)
#pop-options
