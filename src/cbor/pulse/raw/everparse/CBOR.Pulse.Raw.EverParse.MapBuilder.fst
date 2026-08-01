module CBOR.Pulse.Raw.EverParse.MapBuilder
#lang-pulse
friend CBOR.Pulse.Raw.Format.Match
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Optimal
open CBOR.Pulse.Raw.Match
open LowParse.Spec.Combinators
open LowParse.Spec.VCList

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module PB = LowParse.PulseParse.Base
module LPB = LowParse.Pulse.Base
module ML = CBOR.Pulse.Raw.Format.MixedList
module Util = CBOR.Pulse.Raw.Util
module S = Pulse.Lib.Slice
module PM = Pulse.Lib.SeqMatch

(* ================================================================ *)
(* minimal_len_size_prop                                            *)
(* ================================================================ *)

let minimal_len_size_prop (len: U64.t)
  : Lemma (raw_uint64_size_prop (minimal_len_size len) len)
= ()

(* The map-entry-list parser [parse_nlist n (nondep_then parse parse)] is    *)
(* strong for any [n]: needed to weaken a serialized payload to a            *)
(* [pts_to_parsed_strong_prefix].                                            *)
let map_payload_kind_strong (n: nat)
: Lemma
    ((parse_nlist_kind n
        (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)).parser_kind_subkind
      == Some ParserStrong)
= parse_nlist_kind_subkind n
    (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind);
  assert_norm
    ((and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind).parser_kind_subkind
      == Some ParserStrong)

let perm_one_r (q: perm) : Lemma (q *. 1.0R == q) = ()

let perm_one_l (q: perm) : Lemma (1.0R *. q == q) = ()

(* Local elimination of a serialized map into its raw serialized      *)
(* payload (a [pts_to_serialized] over the map-entry-list serializer), *)
(* with a trade back.  Mirrors [Format.Serialized.cbor_match_serialized_map_elim]. *)
ghost
fn map_serialized_elim
  (v: cbor_serialized) (pm: perm) (r: raw_data_item { Map? r })
requires
  cbor_match_serialized_map v pm r
ensures exists* pm'.
  LPB.pts_to_serialized
    (serialize_nlist (U64.v (Map?.len r).value)
       (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item))
    (to_slice v.cbor_serialized_payload) #pm' (Map?.v r) **
  Trade.trade
    (LPB.pts_to_serialized
      (serialize_nlist (U64.v (Map?.len r).value)
         (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item))
      (to_slice v.cbor_serialized_payload) #pm' (Map?.v r))
    (cbor_match_serialized_map v pm r) **
  pure (v.cbor_serialized_header == Map?.len r)
{
  unfold (cbor_match_serialized_map v pm r);
  unfold (cbor_match_serialized_payload_map (to_slice v.cbor_serialized_payload)
            (pm `Util.perm_mul` v.cbor_serialized_perm) (Map?.v r));
  with pm'. assert (LPB.pts_to_serialized
    (serialize_nlist (U64.v (Map?.len r).value)
       (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item))
    (to_slice v.cbor_serialized_payload) #pm' (Map?.v r));
  Trade.intro_trade
    (LPB.pts_to_serialized
      (serialize_nlist (U64.v (Map?.len r).value)
         (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item))
      (to_slice v.cbor_serialized_payload) #pm' (Map?.v r))
    (cbor_match_serialized_map v pm r)
    emp
    fn _ {
      fold (cbor_match_serialized_payload_map (to_slice v.cbor_serialized_payload)
              (pm `Util.perm_mul` v.cbor_serialized_perm) (Map?.v r));
      fold (cbor_match_serialized_map v pm r);
    };
}

(* ================================================================ *)
(* cbor_mk_map_full                                                 *)
(*                                                                  *)
(* Mirrors [ArrayBuilder.cbor_array_finalize], but consumes the raw *)
(* [mixed_list_match] directly (no owned wrapper) and produces a    *)
(* [CBOR_Case_Map_Gen] node.                                        *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
fn cbor_mk_map_full
  (pm: perm)
  (ml: IT.mixed_list cbor_map_entry)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.mixed_list_match cbor_match_map_entry
    (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l) **
  pure (FStar.UInt.fits (SZ.v (IT.mixed_list_length ml)) 64)
returns y: cbor_raw
ensures
  cbor_map_finalized pm ml y (Ghost.reveal l) **
  pure (CBOR_Case_Map_Gen? y)
{
  I.mixed_list_match_length cbor_match_map_entry
    (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l);
  FStar.Math.Lemmas.small_mod (SZ.v (IT.mixed_list_length ml)) (pow2 64);
  let len64 = SZ.sizet_to_uint64 (IT.mixed_list_length ml);
  minimal_len_size_prop len64;
  let len : raw_uint64 = mk_raw_uint64 len64;
  let ct : cbor_mixed_list_map = {
    cbor_map_gen_length_size = minimal_len_size len64;
    cbor_map_gen_ptr = ml;
    cbor_map_gen_perm = pm;
  };
  let xh0 : Ghost.erased (r: raw_data_item { Map? r }) =
    Ghost.hide (Map len (Ghost.reveal l));
  let y : cbor_raw = CBOR_Case_Map_Gen ct;
  perm_one_l pm;
  rewrite (I.mixed_list_match cbor_match_map_entry
             (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l))
    as (I.mixed_list_match cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item)
          (1.0R *. ct.cbor_map_gen_perm) ct.cbor_map_gen_ptr
          (Map?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (c: cbor_map_entry) (pm0: perm)
    (yv: (raw_data_item & raw_data_item) { List.Tot.memP yv (Map?.v (Ghost.reveal xh0)) })
    requires cbor_match_map_entry pm0 c yv
    ensures cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 c yv
  {
    map_elem_precedes (Ghost.reveal xh0) yv;
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) cbor_match pm0 c yv;
    rewrite (cbor_match_map_entry pm0 c yv)
      as (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 c yv);
  };
  I.mixed_list_match_weaken
    cbor_match_map_entry (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match)
    (nondep_then parse_raw_data_item parse_raw_data_item)
    (1.0R *. ct.cbor_map_gen_perm) ct.cbor_map_gen_ptr
    (Map?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_map 1.0R ct (Ghost.reveal xh0) cbor_match);
  cbor_match_eq_map_gen 1.0R ct (Ghost.reveal xh0);
  Trade.rewrite_with_trade
    (cbor_match_mixed_list_map 1.0R ct (Ghost.reveal xh0) cbor_match)
    (cbor_match 1.0R y (Ghost.reveal xh0));
  Trade.intro_trade
    (cbor_match_mixed_list_map 1.0R ct (Ghost.reveal xh0) cbor_match)
    (I.mixed_list_match cbor_match_map_entry
       (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l))
    emp
    fn _ {
      unfold (cbor_match_mixed_list_map 1.0R ct (Ghost.reveal xh0) cbor_match);
      ghost
      fn prf_fwd (c: cbor_map_entry) (pm0: perm)
        (yv: (raw_data_item & raw_data_item) { List.Tot.memP yv (Map?.v (Ghost.reveal xh0)) })
        requires cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 c yv
        ensures cbor_match_map_entry pm0 c yv
      {
        map_elem_precedes (Ghost.reveal xh0) yv;
        cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) cbor_match pm0 c yv;
        rewrite (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 c yv)
          as (cbor_match_map_entry pm0 c yv);
      };
      I.mixed_list_match_weaken
        (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match) cbor_match_map_entry
        (nondep_then parse_raw_data_item parse_raw_data_item)
        (1.0R *. ct.cbor_map_gen_perm) ct.cbor_map_gen_ptr
        (Map?.v (Ghost.reveal xh0)) prf_fwd;
      perm_one_l pm;
      rewrite (I.mixed_list_match cbor_match_map_entry
                 (nondep_then parse_raw_data_item parse_raw_data_item)
                 (1.0R *. ct.cbor_map_gen_perm) ct.cbor_map_gen_ptr
                 (Map?.v (Ghost.reveal xh0)))
        as (I.mixed_list_match cbor_match_map_entry
              (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l));
    };
  Trade.trans
    (cbor_match 1.0R y (Ghost.reveal xh0))
    (cbor_match_mixed_list_map 1.0R ct (Ghost.reveal xh0) cbor_match)
    (I.mixed_list_match cbor_match_map_entry
       (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l));
  rewrite (cbor_match 1.0R y (Ghost.reveal xh0))
    as (cbor_match 1.0R y (Map len (Ghost.reveal l)));
  rewrite (Trade.trade (cbor_match 1.0R y (Ghost.reveal xh0))
             (I.mixed_list_match cbor_match_map_entry
                (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l)))
    as (Trade.trade (cbor_match 1.0R y (Map len (Ghost.reveal l)))
          (I.mixed_list_match cbor_match_map_entry
             (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l)));
  fold (cbor_map_finalized pm ml y (Ghost.reveal l));
  y
}
#pop-options

(* ================================================================ *)
(* ================================================================ *)
(* cbor_map_borrow_entries_serialized                              *)
(*                                                                  *)
(* Serialized-map arm of the borrow: turn the serialized payload    *)
(* into a [Base (Serialized ...)] mixed_list node, with a trade      *)
(* back.  The [Serialized] node carries no per-element vmatch (the   *)
(* entries live only as bytes), so the result holds for any entry    *)
(* vmatch, in particular [cbor_match_map_entry].                     *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
fn cbor_map_borrow_entries_serialized
  (pm: perm) (v: cbor_serialized)
  (#xh: Ghost.erased (r: raw_data_item { Map? r }))
requires
  cbor_match pm (CBOR_Case_Serialized_Map v) (Ghost.reveal xh) ** pure (SZ.fits_u64)
returns ml: IT.mixed_list cbor_map_entry
ensures exists* (pm': perm).
  I.mixed_list_match cbor_match_map_entry
    (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml
    (Map?.v (Ghost.reveal xh)) **
  Trade.trade
    (I.mixed_list_match cbor_match_map_entry
      (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml
      (Map?.v (Ghost.reveal xh)))
    (cbor_match pm (CBOR_Case_Serialized_Map v) (Ghost.reveal xh))
{
  Trade.rewrite_with_trade
    (cbor_match pm (CBOR_Case_Serialized_Map v) (Ghost.reveal xh))
    (cbor_match_serialized_map v pm (Ghost.reveal xh));
  map_serialized_elim v pm (Ghost.reveal xh);
  with pm_s. _;
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Serialized_Map v) (Ghost.reveal xh));
  (* now: pts_to_serialized (serialize_nlist N sndt) (to_slice payload) #pm_s (Map?.v xh)
          ** Trade.trade (pts_to_serialized ..) (cbor_match ..)
          ** pure (v.cbor_serialized_header == Map?.len xh) *)
  PB.pts_to_serialized_parsed (to_slice v.cbor_serialized_payload);
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Serialized_Map v) (Ghost.reveal xh));
  map_payload_kind_strong (U64.v (Map?.len (Ghost.reveal xh)).value);
  PB.pts_to_parsed_weaken_strong_prefix
    (parse_nlist (U64.v (Map?.len (Ghost.reveal xh)).value)
       (nondep_then parse_raw_data_item parse_raw_data_item))
    (to_slice v.cbor_serialized_payload);
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Serialized_Map v) (Ghost.reveal xh));
  (* now: pts_to_parsed_strong_prefix (parse_nlist N ndt) (to_slice payload) #(pm_s /. 2) (Map?.v xh)
          ** Trade.trade (strong_prefix ..) (cbor_match ..) [Tsp] *)
  let count = SZ.uint64_to_sizet v.cbor_serialized_header.value;
  perm_one_r (pm_s /. 2.0R);
  rewrite (PB.pts_to_parsed_strong_prefix
             (parse_nlist (U64.v (Map?.len (Ghost.reveal xh)).value)
                (nondep_then parse_raw_data_item parse_raw_data_item))
             (to_slice v.cbor_serialized_payload) #(pm_s /. 2.0R) (Map?.v (Ghost.reveal xh)))
    as (PB.pts_to_parsed_strong_prefix
          (parse_nlist (0 + SZ.v count)
             (nondep_then parse_raw_data_item parse_raw_data_item))
          (to_slice v.cbor_serialized_payload) #((pm_s /. 2.0R) *. 1.0R) (Map?.v (Ghost.reveal xh)));
  fold (I.base_mixed_list_match_n cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item) 0 (SZ.v count) (pm_s /. 2.0R)
          (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload))
          (Map?.v (Ghost.reveal xh)));
  fold (I.mixed_list_match_n cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item) 0 (SZ.v count) (pm_s /. 2.0R)
          (IT.Base #cbor_map_entry
             (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload)))
          (Map?.v (Ghost.reveal xh)));
  fold (I.mixed_list_match cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item) (pm_s /. 2.0R)
          (IT.Base #cbor_map_entry
             (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload)))
          (Map?.v (Ghost.reveal xh)));
  let ml : IT.mixed_list cbor_map_entry =
    IT.Base #cbor_map_entry
      (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload));
  rewrite (I.mixed_list_match cbor_match_map_entry
             (nondep_then parse_raw_data_item parse_raw_data_item) (pm_s /. 2.0R)
             (IT.Base #cbor_map_entry
                (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload)))
             (Map?.v (Ghost.reveal xh)))
    as (I.mixed_list_match cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item) (pm_s /. 2.0R) ml
          (Map?.v (Ghost.reveal xh)));
  Trade.intro_trade
    (I.mixed_list_match cbor_match_map_entry
       (nondep_then parse_raw_data_item parse_raw_data_item) (pm_s /. 2.0R) ml
       (Map?.v (Ghost.reveal xh)))
    (PB.pts_to_parsed_strong_prefix
       (parse_nlist (U64.v (Map?.len (Ghost.reveal xh)).value)
          (nondep_then parse_raw_data_item parse_raw_data_item))
       (to_slice v.cbor_serialized_payload) #(pm_s /. 2.0R) (Map?.v (Ghost.reveal xh)))
    (pure (U64.v (Map?.len (Ghost.reveal xh)).value == 0 + SZ.v count))
    fn _ {
      rewrite (I.mixed_list_match cbor_match_map_entry
                 (nondep_then parse_raw_data_item parse_raw_data_item) (pm_s /. 2.0R) ml
                 (Map?.v (Ghost.reveal xh)))
        as (I.mixed_list_match cbor_match_map_entry
              (nondep_then parse_raw_data_item parse_raw_data_item) (pm_s /. 2.0R)
              (IT.Base #cbor_map_entry
                 (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload)))
              (Map?.v (Ghost.reveal xh)));
      unfold (I.mixed_list_match cbor_match_map_entry
                (nondep_then parse_raw_data_item parse_raw_data_item) (pm_s /. 2.0R)
                (IT.Base #cbor_map_entry
                   (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload)))
                (Map?.v (Ghost.reveal xh)));
      unfold (I.mixed_list_match_n cbor_match_map_entry
                (nondep_then parse_raw_data_item parse_raw_data_item) 0 (SZ.v count) (pm_s /. 2.0R)
                (IT.Base #cbor_map_entry
                   (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload)))
                (Map?.v (Ghost.reveal xh)));
      unfold (I.base_mixed_list_match_n cbor_match_map_entry
                (nondep_then parse_raw_data_item parse_raw_data_item) 0 (SZ.v count) (pm_s /. 2.0R)
                (IT.Serialized #cbor_map_entry 1.0R count (to_slice v.cbor_serialized_payload))
                (Map?.v (Ghost.reveal xh)));
      with l_all. _;
      perm_one_r (pm_s /. 2.0R);
      rewrite (PB.pts_to_parsed_strong_prefix
                 (parse_nlist (0 + SZ.v count)
                    (nondep_then parse_raw_data_item parse_raw_data_item))
                 (to_slice v.cbor_serialized_payload) #((pm_s /. 2.0R) *. 1.0R) l_all)
        as (PB.pts_to_parsed_strong_prefix
              (parse_nlist (U64.v (Map?.len (Ghost.reveal xh)).value)
                 (nondep_then parse_raw_data_item parse_raw_data_item))
              (to_slice v.cbor_serialized_payload) #(pm_s /. 2.0R) (Map?.v (Ghost.reveal xh)));
    };
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Serialized_Map v) (Ghost.reveal xh));
  ml
}
#pop-options

(* ================================================================ *)
(* cbor_map_borrow_entries_inline                                   *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
fn cbor_map_borrow_entries_inline
  (pm: perm) (v: cbor_map)
  (#xh: Ghost.erased (r: raw_data_item { Map? r }))
requires
  cbor_match pm (CBOR_Case_Map v) (Ghost.reveal xh)
returns ml: IT.mixed_list cbor_map_entry
ensures exists* (pm': perm).
  I.mixed_list_match cbor_match_map_entry
    (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml
    (Map?.v (Ghost.reveal xh)) **
  Trade.trade
    (I.mixed_list_match cbor_match_map_entry
      (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml
      (Map?.v (Ghost.reveal xh)))
    (cbor_match pm (CBOR_Case_Map v) (Ghost.reveal xh))
{
  cbor_match_eq_map0 pm v (Ghost.reveal xh);
  Trade.rewrite_with_trade
    (cbor_match pm (CBOR_Case_Map v) (Ghost.reveal xh))
    (cbor_match_map0 v pm (Ghost.reveal xh) cbor_match);
  unfold (cbor_match_map0 v pm (Ghost.reveal xh) cbor_match);
  with w. _;
  S.pts_to_len v.cbor_map_ptr;
  (* weaken the item matcher from bounded [entry0] to plain [entry] *)
  ghost
  fn weaken_fwd (c: cbor_map_entry)
    (yv: (yv: (raw_data_item & raw_data_item) { yv << Map?.v (Ghost.reveal xh) }))
    requires cbor_match_map_entry0 (Ghost.reveal xh)
               (cbor_match (pm `Util.perm_mul` v.cbor_map_payload_perm)) c yv
    ensures cbor_match_map_entry (pm *. v.cbor_map_payload_perm) c yv
  {
    rewrite (cbor_match_map_entry0 (Ghost.reveal xh)
               (cbor_match (pm `Util.perm_mul` v.cbor_map_payload_perm)) c yv)
      as (cbor_match_map_entry (pm *. v.cbor_map_payload_perm) c yv);
  };
  PM.seq_list_match_weaken
    w (Map?.v (Ghost.reveal xh))
    (cbor_match_map_entry0 (Ghost.reveal xh)
       (cbor_match (pm `Util.perm_mul` v.cbor_map_payload_perm)))
    (cbor_match_map_entry (pm *. v.cbor_map_payload_perm))
    weaken_fwd;
  rewrite (S.pts_to v.cbor_map_ptr #(pm `Util.perm_mul` v.cbor_map_array_perm) w)
    as (S.pts_to v.cbor_map_ptr #(pm *. v.cbor_map_array_perm) w);
  assert (pure (w `Seq.equal`
    Seq.slice w 0 (0 + SZ.v (S.len v.cbor_map_ptr))));
  fold (I.base_mixed_list_match_n cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item)
          0 (SZ.v (S.len v.cbor_map_ptr)) pm
          (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr)
          (Map?.v (Ghost.reveal xh)));
  fold (I.mixed_list_match_n cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item)
          0 (SZ.v (S.len v.cbor_map_ptr)) pm
          (IT.Base #cbor_map_entry
             (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr))
          (Map?.v (Ghost.reveal xh)));
  fold (I.mixed_list_match cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item) pm
          (IT.Base #cbor_map_entry
             (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr))
          (Map?.v (Ghost.reveal xh)));
  let ml : IT.mixed_list cbor_map_entry =
    IT.Base #cbor_map_entry
      (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr);
  rewrite (I.mixed_list_match cbor_match_map_entry
             (nondep_then parse_raw_data_item parse_raw_data_item) pm
             (IT.Base #cbor_map_entry
                (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr))
             (Map?.v (Ghost.reveal xh)))
    as (I.mixed_list_match cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item) pm ml
          (Map?.v (Ghost.reveal xh)));
  Trade.intro_trade
    (I.mixed_list_match cbor_match_map_entry
       (nondep_then parse_raw_data_item parse_raw_data_item) pm ml
       (Map?.v (Ghost.reveal xh)))
    (cbor_match_map0 v pm (Ghost.reveal xh) cbor_match)
    (pure (v.cbor_map_length_size == (Map?.len (Ghost.reveal xh)).size /\
           SZ.v (S.len v.cbor_map_ptr) == U64.v (Map?.len (Ghost.reveal xh)).value))
    fn _ {
      rewrite (I.mixed_list_match cbor_match_map_entry
                 (nondep_then parse_raw_data_item parse_raw_data_item) pm ml
                 (Map?.v (Ghost.reveal xh)))
        as (I.mixed_list_match cbor_match_map_entry
              (nondep_then parse_raw_data_item parse_raw_data_item) pm
              (IT.Base #cbor_map_entry
                 (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr))
              (Map?.v (Ghost.reveal xh)));
      unfold (I.mixed_list_match cbor_match_map_entry
                (nondep_then parse_raw_data_item parse_raw_data_item) pm
                (IT.Base #cbor_map_entry
                   (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr))
                (Map?.v (Ghost.reveal xh)));
      unfold (I.mixed_list_match_n cbor_match_map_entry
                (nondep_then parse_raw_data_item parse_raw_data_item)
                0 (SZ.v (S.len v.cbor_map_ptr)) pm
                (IT.Base #cbor_map_entry
                   (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr))
                (Map?.v (Ghost.reveal xh)));
      unfold (I.base_mixed_list_match_n cbor_match_map_entry
                (nondep_then parse_raw_data_item parse_raw_data_item)
                0 (SZ.v (S.len v.cbor_map_ptr)) pm
                (IT.Slice #cbor_map_entry v.cbor_map_array_perm v.cbor_map_payload_perm v.cbor_map_ptr)
                (Map?.v (Ghost.reveal xh)));
      with l' l1. _;
      S.pts_to_len v.cbor_map_ptr;
      assert (pure (l1 `Seq.equal` l'));
      ghost
      fn weaken_bwd (c: cbor_map_entry)
        (yv: (yv: (raw_data_item & raw_data_item) { yv << Map?.v (Ghost.reveal xh) }))
        requires cbor_match_map_entry (pm *. v.cbor_map_payload_perm) c yv
        ensures cbor_match_map_entry0 (Ghost.reveal xh)
                  (cbor_match (pm `Util.perm_mul` v.cbor_map_payload_perm)) c yv
      {
        rewrite (cbor_match_map_entry (pm *. v.cbor_map_payload_perm) c yv)
          as (cbor_match_map_entry0 (Ghost.reveal xh)
                (cbor_match (pm `Util.perm_mul` v.cbor_map_payload_perm)) c yv);
      };
      PM.seq_list_match_weaken
        l1 (Map?.v (Ghost.reveal xh))
        (cbor_match_map_entry (pm *. v.cbor_map_payload_perm))
        (cbor_match_map_entry0 (Ghost.reveal xh)
           (cbor_match (pm `Util.perm_mul` v.cbor_map_payload_perm)))
        weaken_bwd;
      rewrite (S.pts_to v.cbor_map_ptr #(pm *. v.cbor_map_array_perm) l')
        as (S.pts_to v.cbor_map_ptr #(pm `Util.perm_mul` v.cbor_map_array_perm) l');
      rewrite (PM.seq_list_match l1 (Map?.v (Ghost.reveal xh))
                 (cbor_match_map_entry0 (Ghost.reveal xh)
                    (cbor_match (pm `Util.perm_mul` v.cbor_map_payload_perm))))
        as (PM.seq_list_match l' (Map?.v (Ghost.reveal xh))
              (cbor_match_map_entry0 (Ghost.reveal xh)
                 (cbor_match (pm `Util.perm_mul` v.cbor_map_payload_perm))));
      fold (cbor_match_map0 v pm (Ghost.reveal xh) cbor_match);
    };
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Map v) (Ghost.reveal xh));
  ml
}
#pop-options

(* ================================================================ *)
(* cbor_map_borrow_entries                                          *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
fn cbor_map_borrow_entries
  (pm: perm) (x: cbor_raw)
  (#xh: Ghost.erased (r: raw_data_item { Map? r }))
requires
  cbor_match pm x (Ghost.reveal xh) ** pure (SZ.fits_u64)
returns ml: IT.mixed_list cbor_map_entry
ensures exists* (pm': perm).
  I.mixed_list_match cbor_match_map_entry
    (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml
    (Map?.v (Ghost.reveal xh)) **
  Trade.trade
    (I.mixed_list_match cbor_match_map_entry
      (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml
      (Map?.v (Ghost.reveal xh)))
    (cbor_match pm x (Ghost.reveal xh))
{
  cbor_match_cases x;
  match x {
    norewrite
    CBOR_Case_Map v -> {
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match pm (CBOR_Case_Map v) (Ghost.reveal xh));
      let ml = cbor_map_borrow_entries_inline pm v #xh;
      Trade.trans _ _ (cbor_match pm x (Ghost.reveal xh));
      ml
    }
    norewrite
    CBOR_Case_Serialized_Map v -> {
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match pm (CBOR_Case_Serialized_Map v) (Ghost.reveal xh));
      let ml = cbor_map_borrow_entries_serialized pm v #xh;
      Trade.trans _ _ (cbor_match pm x (Ghost.reveal xh));
      ml
    }
    norewrite
    CBOR_Case_Map_Gen v -> {
      cbor_match_eq_map_gen pm v (Ghost.reveal xh);
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match_mixed_list_map pm v (Ghost.reveal xh) cbor_match);
      unfold (cbor_match_mixed_list_map pm v (Ghost.reveal xh) cbor_match);
      (* context now:
           mixed_list_match (cbor_match_map_entry_bounded xh cbor_match) (nondep..)
             (pm *. v.cbor_map_gen_perm) v.cbor_map_gen_ptr (Map?.v xh)
           ** pure (v.cbor_map_gen_length_size == (Map?.len xh).size)
           ** Trade.trade (cbor_match_mixed_list_map ..) (cbor_match pm x xh) *)
      ghost
      fn prf_fwd (c: cbor_map_entry) (pm0: perm)
        (yv: (raw_data_item & raw_data_item) { List.Tot.memP yv (Map?.v (Ghost.reveal xh)) })
        requires cbor_match_map_entry_bounded (Ghost.reveal xh) cbor_match pm0 c yv
        ensures cbor_match_map_entry pm0 c yv
      {
        map_elem_precedes (Ghost.reveal xh) yv;
        cbor_match_map_entry_bounded_eq (Ghost.reveal xh) cbor_match pm0 c yv;
        rewrite (cbor_match_map_entry_bounded (Ghost.reveal xh) cbor_match pm0 c yv)
          as (cbor_match_map_entry pm0 c yv);
      };
      I.mixed_list_match_weaken
        (cbor_match_map_entry_bounded (Ghost.reveal xh) cbor_match) cbor_match_map_entry
        (nondep_then parse_raw_data_item parse_raw_data_item)
        (pm *. v.cbor_map_gen_perm) v.cbor_map_gen_ptr
        (Map?.v (Ghost.reveal xh)) prf_fwd;
      let ml = v.cbor_map_gen_ptr;
      rewrite (I.mixed_list_match cbor_match_map_entry
                 (nondep_then parse_raw_data_item parse_raw_data_item)
                 (pm *. v.cbor_map_gen_perm) v.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh)))
        as (I.mixed_list_match cbor_match_map_entry
              (nondep_then parse_raw_data_item parse_raw_data_item)
              (pm *. v.cbor_map_gen_perm) ml (Map?.v (Ghost.reveal xh)));
      (* rebuild the trade: mixed_list_match -> cbor_match_mixed_list_map, then compose *)
      Trade.intro_trade
        (I.mixed_list_match cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item)
          (pm *. v.cbor_map_gen_perm) ml (Map?.v (Ghost.reveal xh)))
        (cbor_match_mixed_list_map pm v (Ghost.reveal xh) cbor_match)
        (pure (v.cbor_map_gen_length_size == (Map?.len (Ghost.reveal xh)).size))
        fn _ {
          rewrite (I.mixed_list_match cbor_match_map_entry
                     (nondep_then parse_raw_data_item parse_raw_data_item)
                     (pm *. v.cbor_map_gen_perm) ml (Map?.v (Ghost.reveal xh)))
            as (I.mixed_list_match cbor_match_map_entry
                  (nondep_then parse_raw_data_item parse_raw_data_item)
                  (pm *. v.cbor_map_gen_perm) v.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh)));
          ghost
          fn prf_bwd (c: cbor_map_entry) (pm0: perm)
            (yv: (raw_data_item & raw_data_item) { List.Tot.memP yv (Map?.v (Ghost.reveal xh)) })
            requires cbor_match_map_entry pm0 c yv
            ensures cbor_match_map_entry_bounded (Ghost.reveal xh) cbor_match pm0 c yv
          {
            map_elem_precedes (Ghost.reveal xh) yv;
            cbor_match_map_entry_bounded_eq (Ghost.reveal xh) cbor_match pm0 c yv;
            rewrite (cbor_match_map_entry pm0 c yv)
              as (cbor_match_map_entry_bounded (Ghost.reveal xh) cbor_match pm0 c yv);
          };
          I.mixed_list_match_weaken
            cbor_match_map_entry (cbor_match_map_entry_bounded (Ghost.reveal xh) cbor_match)
            (nondep_then parse_raw_data_item parse_raw_data_item)
            (pm *. v.cbor_map_gen_perm) v.cbor_map_gen_ptr
            (Map?.v (Ghost.reveal xh)) prf_bwd;
          fold (cbor_match_mixed_list_map pm v (Ghost.reveal xh) cbor_match);
        };
      Trade.trans
        (I.mixed_list_match cbor_match_map_entry
          (nondep_then parse_raw_data_item parse_raw_data_item)
          (pm *. v.cbor_map_gen_perm) ml (Map?.v (Ghost.reveal xh)))
        (cbor_match_mixed_list_map pm v (Ghost.reveal xh) cbor_match)
        (cbor_match pm x (Ghost.reveal xh));
      ml
    }
  }
}
#pop-options
