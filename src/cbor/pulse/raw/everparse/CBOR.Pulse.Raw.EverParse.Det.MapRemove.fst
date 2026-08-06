module CBOR.Pulse.Raw.EverParse.Det.MapRemove
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.Type
open CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.Combinators
open FStar.Real

module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module MB = CBOR.Pulse.Raw.EverParse.MapBuilder
module Fmt = CBOR.Pulse.Raw.EverParse.Format
module For = CBOR.Spec.Raw.Format
module Valid = CBOR.Spec.Raw.Valid
module MapLexInsert = CBOR.Spec.Raw.MapLexInsert
module SpecMap = CBOR.Spec.Raw.Map
module Optimal = CBOR.Spec.Raw.Optimal
module IO = LowParse.PulseParse.Iterator.IntOps
module Sort = CBOR.Spec.Raw.Sort
module U = CBOR.Spec.Util
module MR = CBOR.Pulse.Raw.EverParse.MapRemove

(* Total accessor for the entry list of a (map) [raw_data_item]; avoids the
   partial projector [Map?.v] in postconditions where [Map? _] is not in scope. *)
let map_payload (x: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match x with
  | Map _ v -> v
  | _ -> []

(* ================================================================ *)
(* Deterministic map remove-by-key (Phase 2-A, raw det wrapper).    *)
(*                                                                  *)
(* [cbor_raw_det_map_remove x key ...] borrows the entries of the   *)
(* deterministic (key-sorted, minimal-length) CBOR map [x], runs    *)
(* the verified structural splice engine                            *)
(* [MapRemove.cbor_raw_map_remove_entry], and ALWAYS returns a      *)
(* CBOR map: the filtered map when the key was present, or [x]      *)
(* itself (unchanged) when the key was absent.  Dual of             *)
(* [Det.MapInsert.cbor_raw_det_map_entry_insert].                   *)
(* ================================================================ *)

(* [MapLexInsert.order0] is definitionally the deterministic key order;   *)
(* this bridges its strict-order facts (via [For.lemma_compare_prop]).    *)
let order0_eq ()
: Lemma (MapLexInsert.order0 == For.deterministically_encoded_cbor_map_key_order)
= assert_norm (MapLexInsert.order0 == For.deterministically_encoded_cbor_map_key_order)

(* From key-sortedness (strict key order) the map keys have no repeats. *)
let map_sorted_no_repeats (l: list (raw_data_item & raw_data_item))
: Lemma
    (requires (L.sorted (Valid.map_entry_order MapLexInsert.order0 _) l == true))
    (ensures (L.no_repeats_p (L.map fst l)))
= order0_eq ();
  let _ = For.lemma_compare_prop in
  assert (Sort.compare_prop MapLexInsert.order0 For.cbor_compare);
  SpecMap.list_sorted_map_entry_order_no_repeats MapLexInsert.order0 l

(* Filtering-out a key preserves key-sortedness. *)
let map_sorted_filter (vk: raw_data_item) (l: list (raw_data_item & raw_data_item))
: Lemma
    (requires (L.sorted (Valid.map_entry_order MapLexInsert.order0 _) l == true))
    (ensures (L.sorted (Valid.map_entry_order MapLexInsert.order0 _) (MR.filtered_out vk l) == true))
= order0_eq ();
  let _ = For.lemma_compare_prop in
  assert (Sort.compare_prop MapLexInsert.order0 For.cbor_compare);
  U.list_sorted_filter (Valid.map_entry_order MapLexInsert.order0 _)
    (fun e -> not (MR.key_eq (fst e) vk)) l

(* When the key is absent the filter is the identity (structural). *)
let filtered_out_absent (vk: raw_data_item) (l: list (raw_data_item & raw_data_item))
: Lemma
    (requires (~ (L.memP vk (L.map fst l))))
    (ensures (MR.filtered_out vk l == l))
= MR.filter_all_neq l vk

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

fn cbor_raw_det_map_remove
  (x: cbor_raw)
  (key: cbor_raw)
  (r1 r2 r3 r4: R.ref (IT.mixed_list U64.t cbor_map_entry))
  (#pm: perm) (#xh: Ghost.erased raw_data_item)
  (#pk: perm) (#vk: Ghost.erased raw_data_item)
requires
  cbor_match pm x xh **
  cbor_match pk key vk **
  (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4) **
  pure (Map? (Ghost.reveal xh) /\
        L.sorted (Valid.map_entry_order MapLexInsert.order0 _) (Map?.v (Ghost.reveal xh)) == true)
returns res: cbor_raw
ensures exists* (xh_result: raw_data_item).
  cbor_match 1.0R res xh_result **
  cbor_match pk key vk **
  Trade.trade
    (cbor_match 1.0R res xh_result)
    (cbor_match pm x xh **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
  pure (Map? xh_result /\
        map_payload xh_result == MR.filtered_out (Ghost.reveal vk) (map_payload (Ghost.reveal xh)) /\
        (Map?.len xh_result <: raw_uint64) ==
          Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (map_payload xh_result))) /\
        FStar.UInt.fits (L.length (map_payload xh_result)) U64.n /\
        L.sorted (Valid.map_entry_order MapLexInsert.order0 _) (map_payload xh_result) == true)
{
  let xhm : Ghost.erased (r: raw_data_item { Map? r }) = Ghost.hide (Ghost.reveal xh);
  rewrite (cbor_match pm x (Ghost.reveal xh)) as (cbor_match pm x (Ghost.reveal xhm));
  let ml0 = MB.cbor_map_borrow_entries pm x #xhm;
  with pm0. assert (
    I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)) **
    Trade.trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
      (cbor_match pm x (Ghost.reveal xhm))
  );
  map_sorted_no_repeats (Map?.v (Ghost.reveal xhm));
  let res = MR.cbor_raw_map_remove_entry key ml0 r1 r2 r3 r4 #pm0 #(Map?.v (Ghost.reveal xhm)) #pk #vk;
  match res {
    Some ml' -> {
      with pm'. assert (
        I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
          (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))) **
        Trade.trade
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
             (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)) **
           (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
      );
      map_sorted_filter (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm));
      let m = MB.cbor_mk_map_full pm' ml' #(MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)));
      unfold (MB.cbor_map_finalized pm' ml' m (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))));
      with len. assert (
        cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))) **
        Trade.trade
          (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
             (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
      );
      // Compose: m_match ==> ml'_match ==> (ml0_match ** refs) ==> (cbor_match pm x xhm ** refs).
      Trade.trans
        (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
           (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4));
      Trade.trans_concl_l
        (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
        (cbor_match pm x (Ghost.reveal xhm))
        (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4);
      rewrite (Trade.trade
        (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (cbor_match pm x (Ghost.reveal xhm) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)))
        as (Trade.trade
        (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xh)))))
        (cbor_match pm x (Ghost.reveal xh) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)));
      rewrite (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        as (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xh)))));
      m
    }
    None -> {
      with dummy. assert (pure (~ (L.memP (Ghost.reveal vk) (L.map fst (Map?.v (Ghost.reveal xhm))))));
      filtered_out_absent (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm));
      // [filtered_out vk (Map?.v xhm) == Map?.v xhm]: relabel the borrowed entries
      // (and the borrow-trade hypothesis) to the [filtered_out] form so the build
      // below mirrors the Some branch and gives [cbor_match 1.0R] uniformly.
      rewrite (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
        as (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))));
      rewrite (Trade.trade
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
          (cbor_match pm x (Ghost.reveal xhm)))
        as (Trade.trade
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
          (cbor_match pm x (Ghost.reveal xhm)));
      let m = MB.cbor_mk_map_full pm0 ml0 #(MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)));
      unfold (MB.cbor_map_finalized pm0 ml0 m (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))));
      with len. assert (
        cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))) **
        Trade.trade
          (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
      );
      // m_match ==> ml0_match(filtered) ==> cbor_match pm x xhm, then adjoin refs.
      Trade.trans
        (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
        (cbor_match pm x (Ghost.reveal xhm));
      Trade.weak_concl_r
        (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (cbor_match pm x (Ghost.reveal xhm))
        (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4);
      rewrite (Trade.trade
        (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (cbor_match pm x (Ghost.reveal xhm) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)))
        as (Trade.trade
        (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xh)))))
        (cbor_match pm x (Ghost.reveal xh) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)));
      rewrite (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        as (cbor_match 1.0R m (Map len (MR.filtered_out (Ghost.reveal vk) (Map?.v (Ghost.reveal xh)))));
      m
    }
  }
}

#pop-options
