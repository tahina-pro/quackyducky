module CBOR.Pulse.Raw.EverParse.Nondet.MapRemove
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.Type
open CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.Combinators
open FStar.Real

module SZ = FStar.SizeT
module I16 = FStar.Int16
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module IM = CBOR.Pulse.Raw.EverParse.Iterator.Mixed
module Append = LowParse.PulseParse.Iterator.Append
module PB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module LPB = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module Cmp = CBOR.Pulse.Raw.Compare
module Perm = CBOR.Pulse.Raw.Match.Perm
module SB = CBOR.Pulse.Raw.EverParse.Serialized.Base
module Fmt = CBOR.Pulse.Raw.EverParse.Format
module For = CBOR.Spec.Raw.Format
module IO = LowParse.PulseParse.Iterator.IntOps
module V = CBOR.Spec.Raw.Valid
module U = CBOR.Spec.Util
module NondetCompare = CBOR.Pulse.Raw.Nondet.Compare
module MR = CBOR.Pulse.Raw.EverParse.MapRemove
module MB = CBOR.Pulse.Raw.EverParse.MapBuilder

(* Bridge the lowparse dictionary views [IO.u64_ops.v]/[IO.u64_ops.fits] to
   the concrete [U64.v]/[< pow2 64]. *)
let u64_ops_v_eq (x: U64.t)
  : Lemma (IO.u64_ops.v x == U64.v x)
    [SMTPat (IO.u64_ops.v x)]
= ()

let u64_ops_fits_eq (n: nat)
  : Lemma (IO.u64_ops.fits n == (n < pow2 64 <: prop))
    [SMTPat (IO.u64_ops.fits n)]
= ()

(* Key equality used for NONDET map-entry removal: two keys are "equal" iff
   they are [raw_equiv] (semantically equal, i.e. same [mk_cbor] abstract
   value).  This is the SOUND notion for non-canonical (nondet) encodings,
   where a valid map may hold a NON-OPTIMAL key that is [raw_equiv] to -- but
   structurally different from -- the query key; the deterministic engine's
   structural [cbor_compare = 0] equality would MISS such a key.  We reuse the
   deterministic engine's GENERIC list-narrow lemmas (module [MR]); only the
   comparator-dependent filter lemmas below are re-proved for [raw_equiv]. *)
let key_equiv (k1 k2: raw_data_item) : bool = V.raw_equiv k1 k2

(* Spec-level result of removing (the [raw_equiv]-class of) key [vk]: the
   entries whose key is NOT [raw_equiv] to [vk]. *)
let filtered_out_equiv (vk: raw_data_item) (m: list (raw_data_item & raw_data_item))
: list (raw_data_item & raw_data_item)
= L.filter (fun e -> not (key_equiv (fst e) vk)) m

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* If no key of [m] is [raw_equiv] to [vk], filtering keeps every entry. *)
let rec filter_all_neq_equiv (m: list (raw_data_item & raw_data_item)) (vk: raw_data_item)
: Lemma (requires (forall k. L.memP k (L.map fst m) ==> V.raw_equiv k vk == false))
        (ensures (L.filter (fun e -> not (key_equiv (fst e) vk)) m == m))
        (decreases m)
= match m with
  | [] -> ()
  | hd :: tl -> filter_all_neq_equiv tl vk

#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Core setoid removal: filtering out the [raw_equiv]-class of [vk] from a
   no-setoid-repeats key list removes exactly the (unique) matching middle
   entry, leaving the structural splice [prefix ++ suffix]. *)
let filter_removes_unique_key_equiv
  (l prefix suffix: list (raw_data_item & raw_data_item))
  (matched: (raw_data_item & raw_data_item))
  (vk: raw_data_item)
: Lemma
  (requires (l == L.append prefix (matched :: suffix) /\ V.raw_equiv (fst matched) vk == true /\
             U.list_no_setoid_repeats V.raw_equiv (L.map fst l)))
  (ensures (L.filter (fun e -> not (key_equiv (fst e) vk)) l == L.append prefix suffix))
= let km = fst matched in
  let p : (raw_data_item & raw_data_item -> bool) = (fun e -> not (key_equiv (fst e) vk)) in
  L.map_append fst prefix (matched :: suffix);
  introduce forall ki. L.memP ki (L.map fst prefix) ==> V.raw_equiv ki vk == false
  with begin
    introduce _ ==> _
    with _. begin
      U.list_no_setoid_repeats_append_elim_memP V.raw_equiv (L.map fst prefix) (km :: L.map fst suffix) () ki km;
      V.raw_equiv_sym km vk;
      if V.raw_equiv ki vk then V.raw_equiv_trans ki vk km
    end
  end;
  L.append_assoc (L.map fst prefix) [km] (L.map fst suffix);
  introduce forall kj. L.memP kj (L.map fst suffix) ==> V.raw_equiv kj vk == false
  with begin
    introduce _ ==> _
    with _. begin
      U.list_no_setoid_repeats_append_elim_memP V.raw_equiv (L.append (L.map fst prefix) [km]) (L.map fst suffix) () km kj;
      L.append_memP (L.map fst prefix) [km] km;
      V.raw_equiv_sym kj vk;
      if V.raw_equiv kj vk then V.raw_equiv_trans km vk kj
    end
  end;
  MR.filter_append p prefix (matched :: suffix);
  filter_all_neq_equiv prefix vk;
  filter_all_neq_equiv suffix vk

#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Bridge (split form): narrow-splice == setoid-filter, and key is present. *)
let map_remove_correct_equiv
  (l prefix suffix: list (raw_data_item & raw_data_item))
  (matched: (raw_data_item & raw_data_item))
  (vk: raw_data_item)
: Lemma
  (requires (l == L.append prefix (matched :: suffix) /\ V.raw_equiv (fst matched) vk == true /\
             U.list_no_setoid_repeats V.raw_equiv (L.map fst l)))
  (ensures (
    let k = L.length prefix in
    k < L.length l /\
    I.list_narrow l 0 k == prefix /\
    I.list_narrow l (k + 1) (L.length l - k - 1) == suffix /\
    L.append (I.list_narrow l 0 k) (I.list_narrow l (k + 1) (L.length l - k - 1))
      == filtered_out_equiv vk l /\
    L.existsb (V.raw_equiv vk) (L.map fst l)))
= MR.list_narrow_split3 prefix matched suffix;
  filter_removes_unique_key_equiv l prefix suffix matched vk;
  L.map_append fst prefix (matched :: suffix);
  L.append_length prefix (matched :: suffix);
  L.append_memP (L.map fst prefix) (fst matched :: L.map fst suffix) (fst matched);
  V.raw_equiv_sym (fst matched) vk;
  U.list_existsb_intro (V.raw_equiv vk) (L.map fst l) (fst matched)

#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Bridge (position form): the single lemma the Pulse [Some] branch calls. *)
let map_remove_correct_at_equiv
  (l: list (raw_data_item & raw_data_item)) (k: nat) (vk: raw_data_item)
: Lemma
  (requires (k < L.length l /\ V.raw_equiv (fst (L.index l k)) vk == true /\
             U.list_no_setoid_repeats V.raw_equiv (L.map fst l)))
  (ensures (
    L.append (I.list_narrow l 0 k) (I.list_narrow l (k + 1) (L.length l - k - 1))
      == filtered_out_equiv vk l /\
    L.existsb (V.raw_equiv vk) (L.map fst l) /\
    L.length (I.list_narrow l 0 k) == k))
= let prefix = I.list_narrow l 0 k in
  let suffix = I.list_narrow l (k + 1) (L.length l - k - 1) in
  let matched = L.index l k in
  MR.list_decompose_at l k;
  I.list_narrow_length l 0 k;
  map_remove_correct_equiv l prefix suffix matched vk

#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Absent case (None branch): if no key is [raw_equiv] to [vk], the
   setoid-filter is the identity. *)
let filter_all_neq_equiv_absent (m: list (raw_data_item & raw_data_item)) (vk: raw_data_item)
: Lemma (requires (~ (L.existsb (V.raw_equiv vk) (L.map fst m))))
        (ensures (filtered_out_equiv vk m == m))
= introduce forall k. L.memP k (L.map fst m) ==> V.raw_equiv k vk == false
  with begin
    introduce _ ==> _
    with _. begin
      if V.raw_equiv k vk
      then begin V.raw_equiv_sym k vk; U.list_existsb_intro (V.raw_equiv vk) (L.map fst m) k end
    end
  end;
  filter_all_neq_equiv m vk

#pop-options

(* ================================================================ *)
(* Pulse infrastructure (share / gather / reader for map entries),  *)
(* rebuilt locally (the internal versions are not exported).        *)
(* ================================================================ *)

ghost
fn cbor_match_map_entry_share
  (x1: cbor_map_entry)
  (#p: perm)
  (#x2: (raw_data_item & raw_data_item))
requires cbor_match_map_entry p x1 x2
ensures cbor_match_map_entry (p /. 2.0R) x1 x2 ** cbor_match_map_entry (p /. 2.0R) x1 x2
{
  unfold (cbor_match_map_entry p x1 x2);
  Perm.cbor_raw_share p x1.cbor_map_entry_key (fst x2);
  Perm.cbor_raw_share p x1.cbor_map_entry_value (snd x2);
  fold (cbor_match_map_entry (p /. 2.0R) x1 x2);
  fold (cbor_match_map_entry (p /. 2.0R) x1 x2);
}

ghost
fn cbor_match_map_entry_gather
  (x1: cbor_map_entry)
  (#p: perm)
  (#x2: (raw_data_item & raw_data_item))
  (#p': perm)
  (#x2': (raw_data_item & raw_data_item))
requires cbor_match_map_entry p x1 x2 ** cbor_match_map_entry p' x1 x2'
ensures cbor_match_map_entry (p +. p') x1 x2 ** pure (x2 == x2')
{
  unfold (cbor_match_map_entry p x1 x2);
  unfold (cbor_match_map_entry p' x1 x2');
  Perm.cbor_raw_gather p x1.cbor_map_entry_key (fst x2) p' (fst x2');
  Perm.cbor_raw_gather p x1.cbor_map_entry_value (snd x2) p' (snd x2');
  fold (cbor_match_map_entry (p +. p') x1 x2);
}

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* plain map-entry reader (for the key-presence iterator). *)
inline_for_extraction
fn cbor_read_map_entry_np (input: S.slice byte) (#pm: perm) (#v: Ghost.erased (raw_data_item & raw_data_item))
requires PB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v
returns res: cbor_map_entry
ensures
  cbor_match_map_entry 1.0R res v **
  Trade.trade (cbor_match_map_entry 1.0R res v) (PB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
{
  PB.pts_to_parsed_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input;
  let s1, s2 = LPC.split_nondep_then serialize_raw_data_item (Fmt.jump_raw_data_item ()) serialize_raw_data_item input;
  unfold (LPC.split_nondep_then_post serialize_raw_data_item serialize_raw_data_item input pm v (s1, s2));
  unfold (LPC.split_nondep_then_post' serialize_raw_data_item serialize_raw_data_item input pm v s1 s2);
  with v1. assert (LPB.pts_to_serialized serialize_raw_data_item s1 #pm v1);
  with v2. assert (LPB.pts_to_serialized serialize_raw_data_item s2 #pm v2);
  let res1 = SB.cbor_read s1;
  let res2 = SB.cbor_read s2;
  Trade.prod _ (LPB.pts_to_serialized serialize_raw_data_item s1 #pm v1) _ (LPB.pts_to_serialized serialize_raw_data_item s2 #pm v2);
  Trade.trans _ _ (LPB.pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input #pm v);
  let res : cbor_map_entry = {
    cbor_map_entry_key = res1;
    cbor_map_entry_value = res2;
  };
  Trade.rewrite_with_trade
    (cbor_match 1.0R res1 v1 ** cbor_match 1.0R res2 v2)
    (cbor_match_map_entry 1.0R res (Ghost.reveal v));
  Trade.trans _ _ (LPB.pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input #pm v);
  Trade.trans _ _ (PB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v);
  res
}

#pop-options

(* ================================================================ *)
(* Linear key-position finder: scans the borrowed entries and       *)
(* returns (found, k): if [found], [k] is the position of the       *)
(* (unique) entry whose key equals [vk]; else the key is absent.    *)
(* Restores the mixed_list_match on exit (borrow preserved).        *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

fn cbor_raw_nondet_map_find_key
  (key: cbor_raw)
  (ml: IT.mixed_list U64.t cbor_map_entry)
  (#pm: perm)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#pk: perm)
  (#vk: Ghost.erased raw_data_item)
requires
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk **
  pure (L.for_all V.valid_raw_data_item (L.map fst (Ghost.reveal l)) /\ V.valid_raw_data_item (Ghost.reveal vk))
returns res: (bool & U64.t)
ensures
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk **
  pure (
    (fst res == true ==> (U64.v (snd res) < L.length (Ghost.reveal l) /\
                          V.raw_equiv (fst (L.index (Ghost.reveal l) (U64.v (snd res)))) (Ghost.reveal vk) == true /\
                          L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l)))) /\
    (fst res == false ==> ~ (L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l))))
  )
{
  I.mixed_list_match_length cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l;
  MR.list_narrow_full (Ghost.reveal l);
  let it0 = I.iterator_start
    cbor_match_map_entry IO.u64_ops
    (nondep_then parse_raw_data_item parse_raw_data_item)
    (LPC.jump_nondep_then (Fmt.jump_raw_data_item ()) (Fmt.jump_raw_data_item ()))
    pm ml l
    cbor_match_map_entry_share cbor_match_map_entry_gather;
  with pm0. assert (
    I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 it0 l **
    Trade.trade
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 it0 l)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
  );
  let empt0 = IM.iter_is_empty cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) it0;
  let mut r_it = it0;
  let mut r_found = false;
  let mut r_cont = (not empt0);
  let mut r_k = 0uL;
  while (
    !r_cont
  )
  invariant exists* p_cur cur_it remaining found cont k_val.
    R.pts_to r_it cur_it **
    R.pts_to r_found found **
    R.pts_to r_cont cont **
    R.pts_to r_k k_val **
    cbor_match pk key vk **
    I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
    Trade.trade
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l) **
    pure (
      L.length (Ghost.reveal l) < pow2 64 /\
      U64.v k_val <= L.length (Ghost.reveal l) /\
      V.valid_raw_data_item (Ghost.reveal vk) /\
      L.for_all V.valid_raw_data_item (L.map fst remaining) /\
      (found == false ==> remaining == I.list_narrow (Ghost.reveal l) (U64.v k_val) (L.length (Ghost.reveal l) - U64.v k_val)) /\
      (found == true ==> (U64.v k_val < L.length (Ghost.reveal l) /\
                          V.raw_equiv (fst (L.index (Ghost.reveal l) (U64.v k_val))) (Ghost.reveal vk) == true)) /\
      (found == false ==> (L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l)) <==>
                           L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst remaining))) /\
      (found == true ==> L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l))) /\
      (cont == true ==> (found == false /\ Cons? remaining)) /\
      (cont == false ==> (found == true \/ Nil? remaining))
    )
  {
    with p_cur cur_it remaining found cont k_val. assert (
      R.pts_to r_it cur_it **
      R.pts_to r_found found **
      R.pts_to r_cont cont **
      R.pts_to r_k k_val **
      cbor_match pk key vk **
      I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
      Trade.trade
        (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
    );
    // cont == true here, so found == false and Cons? remaining; establish k < len
    I.list_narrow_length (Ghost.reveal l) (U64.v k_val) (L.length (Ghost.reveal l) - U64.v k_val);
    MR.list_narrow_step (Ghost.reveal l) (U64.v k_val);
    let entry = I.iterator_next
      cbor_match_map_entry IO.u64_ops
      (nondep_then parse_raw_data_item parse_raw_data_item)
      (LPC.jump_nondep_then (Fmt.jump_raw_data_item ()) (Fmt.jump_raw_data_item ()))
      p_cur r_it cur_it remaining
      cbor_match_map_entry_share cbor_match_map_entry_gather
      cbor_read_map_entry_np;
    unfold (I.iterator_next_post cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur r_it cur_it remaining entry);
    with pm_v hd_val tl_l it' pm'. assert (
      cbor_match_map_entry pm_v entry hd_val **
      R.pts_to r_it it' **
      I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l **
      Trade.trade
        (cbor_match_map_entry pm_v entry hd_val **
         I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
        (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
    );
    assert (pure (L.map fst remaining == fst (Ghost.reveal hd_val) :: L.map fst tl_l));
    assert (pure (V.valid_raw_data_item (fst (Ghost.reveal hd_val)) /\ L.for_all V.valid_raw_data_item (L.map fst tl_l)));
    unfold (cbor_match_map_entry pm_v entry hd_val);
    let ck = NondetCompare.cbor_nondet_equiv key entry.cbor_map_entry_key;
    fold (cbor_match_map_entry pm_v entry hd_val);
    // ck == raw_equiv vk (fst hd_val)
    Trade.elim_hyp_l
      (cbor_match_map_entry pm_v entry hd_val)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining);
    Trade.trans
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
    if ck {
      // raw_equiv vk (fst hd_val) == true; the matching key is at position k_val.
      V.raw_equiv_sym (Ghost.reveal vk) (fst (Ghost.reveal hd_val));
      U.list_existsb_intro (V.raw_equiv (Ghost.reveal vk)) (L.map fst remaining) (fst (Ghost.reveal hd_val));
      r_found := true;
      r_cont := false;
    } else {
      // raw_equiv vk (fst hd_val) == false; presence <==> is preserved on the tail.
      assert (pure (L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst remaining) ==
                    L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst tl_l)));
      let kc = !r_k;
      let k1 = kc `U64.add` 1uL;
      r_k := k1;
      let cur2 = !r_it;
      rewrite (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
           as (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' cur2 tl_l);
      let empt = IM.iter_is_empty cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) cur2;
      rewrite (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' cur2 tl_l)
           as (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l);
      r_cont := (not empt);
    }
  };
  with p_cur cur_it remaining found cont k_val. assert (
    R.pts_to r_it cur_it **
    R.pts_to r_found found **
    R.pts_to r_cont cont **
    R.pts_to r_k k_val **
    cbor_match pk key vk **
    I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
    Trade.trade
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
  );
  Trade.elim
    (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
    (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
  let found_val = !r_found;
  let k_final = !r_k;
  (found_val, k_final)
}

#pop-options

(* ================================================================ *)
(* RAW map-entry removal by key: structurally splice out the        *)
(* (unique) entry whose key equals [vk], producing a borrowed view  *)
(* of the FILTERED entries + a trade returning the source + refs.   *)
(* Dual of deterministic map INSERT.                                *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

fn cbor_raw_nondet_map_remove_entry
  (key: cbor_raw)
  (ml: IT.mixed_list U64.t cbor_map_entry)
  (r1 r2 r3 r4: R.ref (IT.mixed_list U64.t cbor_map_entry))
  (#pm: perm)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#pk: perm)
  (#vk: Ghost.erased raw_data_item)
requires
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk **
  (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4) **
  pure (L.for_all V.valid_raw_data_item (L.map fst (Ghost.reveal l)) /\
        V.valid_raw_data_item (Ghost.reveal vk) /\
        U.list_no_setoid_repeats V.raw_equiv (L.map fst (Ghost.reveal l)))
returns res: option (IT.mixed_list U64.t cbor_map_entry)
ensures
  cbor_match pk key vk **
  (match res with
   | Some ml' -> exists* (pm': perm).
       I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
         (filtered_out_equiv (Ghost.reveal vk) (Ghost.reveal l)) **
       Trade.trade
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
            (filtered_out_equiv (Ghost.reveal vk) (Ghost.reveal l)))
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
          (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
       pure (L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l)))
   | None ->
       I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4) **
       pure (~ (L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l)))))
{
  let found, kk = cbor_raw_nondet_map_find_key key ml;
  if found {
    with w1 w2 w3 w4. assert (R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4);
    let n = IT.mixed_list_length IO.u64_ops ml;
    I.mixed_list_match_length cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l;
    map_remove_correct_at_equiv (Ghost.reveal l) (U64.v kk) (Ghost.reveal vk);
    Trade.rewrite_with_trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
      (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) pm ml l);
    I.mixed_list_match_n_share cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) pm ml l cbor_match_map_entry_share;
    let ml_before = I.mixed_list_narrow_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item)
      (LPC.jump_nondep_then (Fmt.jump_raw_data_item ()) (Fmt.jump_raw_data_item ()))
      (Ghost.hide #nat 0) (Ghost.hide #nat (U64.v n)) (pm /. 2.0R) ml l 0uL kk
      cbor_match_map_entry_share cbor_match_map_entry_gather;
    let kp1 = kk `U64.add` 1uL;
    let restn = (n `U64.sub` kk) `U64.sub` 1uL;
    let ml_after = I.mixed_list_narrow_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item)
      (LPC.jump_nondep_then (Fmt.jump_raw_data_item ()) (Fmt.jump_raw_data_item ()))
      (Ghost.hide #nat 0) (Ghost.hide #nat (U64.v n)) (pm /. 2.0R) ml l kp1 restn
      cbor_match_map_entry_share cbor_match_map_entry_gather;
    with la. assert (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_before la);
    with lb. assert (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_after lb);
    let ml_res = Append.mixed_list_append cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item)
      ((pm /. 2.0R) /. 2.0R) ml_before la ml_after lb r1 r2;
    // pure bridge: la == narrow 0 k, lb == narrow (k+1) rest, so la @ lb == filter P l
    assert (pure (la == I.list_narrow (Ghost.reveal l) 0 (U64.v kk)));
    assert (pure (lb == I.list_narrow (Ghost.reveal l) (U64.v kk + 1) (L.length (Ghost.reveal l) - U64.v kk - 1)));
    rewrite (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (L.append la lb))
         as (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (filtered_out_equiv (Ghost.reveal vk) (Ghost.reveal l)));
    Trade.intro_trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (filtered_out_equiv (Ghost.reveal vk) (Ghost.reveal l)))
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
      (Trade.trade
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (L.append la lb))
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_before la **
          I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_after lb **
          (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va)) **
       Trade.trade
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_before la)
         (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) (pm /. 2.0R) ml l) **
       Trade.trade
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_after lb)
         (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) (pm /. 2.0R) ml l) **
       Trade.trade
         (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) pm ml l)
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l) **
       R.pts_to r3 w3 ** R.pts_to r4 w4)
      fn _ {
        rewrite (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (filtered_out_equiv (Ghost.reveal vk) (Ghost.reveal l)))
             as (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (L.append la lb));
        Trade.elim
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (L.append la lb))
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_before la **
           I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_after lb **
           (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va));
        Trade.elim
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_before la)
          (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) (pm /. 2.0R) ml l);
        Trade.elim
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_after lb)
          (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) (pm /. 2.0R) ml l);
        I.mixed_list_match_n_gather cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) (pm /. 2.0R) (pm /. 2.0R) ml l l cbor_match_map_entry_gather;
        rewrite (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) ((pm /. 2.0R) +. (pm /. 2.0R)) ml l)
             as (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) pm ml l);
        Trade.elim
          (I.mixed_list_match_n cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) 0 (U64.v n) pm ml l)
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
        fold (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4);
      };
    Some #(IT.mixed_list U64.t cbor_map_entry) ml_res
  } else {
    None #(IT.mixed_list U64.t cbor_map_entry)
  }
}

#pop-options

(* ================================================================ *)
(* Phase 3-A: raw NONDET map remove-by-key wrapper.                 *)
(*                                                                  *)
(* [cbor_raw_nondet_map_remove x key ...] borrows the entries of    *)
(* the (unique-key, NOT necessarily sorted) nondeterministic CBOR   *)
(* map [x], runs the SOUND [raw_equiv]-based splice engine          *)
(* [cbor_raw_nondet_map_remove_entry], and ALWAYS returns a CBOR    *)
(* map: the filtered map (present) or a rebuilt copy (absent).      *)
(* Dual of [Det.MapRemove.cbor_raw_det_map_remove], but keyed on    *)
(* [raw_equiv] (abstract equality) and with NO sortedness -- only   *)
(* nondet map validity, which still guarantees unique keys.         *)
(* ================================================================ *)

(* Total accessor for the entry list of a (map) [raw_data_item]. *)
let map_payload (x: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match x with
  | Map _ v -> v
  | _ -> []

(* --- filter (predicate on the entry key) preserves nondet validity. --- *)

(* Both the key- and value-lists stay valid under the key-filter. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec filtered_out_equiv_for_all_valid (vk: raw_data_item) (entries: list (raw_data_item & raw_data_item))
: Lemma (requires (L.for_all V.valid_raw_data_item (L.map fst entries) /\
                   L.for_all V.valid_raw_data_item (L.map snd entries)))
        (ensures (L.for_all V.valid_raw_data_item (L.map fst (filtered_out_equiv vk entries)) /\
                  L.for_all V.valid_raw_data_item (L.map snd (filtered_out_equiv vk entries))))
        (decreases entries)
= match entries with
  | [] -> ()
  | hd :: tl -> filtered_out_equiv_for_all_valid vk tl

(* [existsb] is monotone under [filter] (a sublist gains no witness). *)
let rec existsb_filter_mono (#t: Type) (p q: t -> bool) (l: list t)
: Lemma (requires (L.existsb p (L.filter q l) == true))
        (ensures (L.existsb p l == true))
        (decreases l)
= match l with
  | [] -> ()
  | a :: tl -> if q a then (if p a then () else existsb_filter_mono p q tl) else existsb_filter_mono p q tl

(* [filter] preserves setoid no-repeats. *)
let rec list_no_setoid_repeats_filter (#t: Type) (equiv: t -> t -> bool) (p: t -> bool) (l: list t)
: Lemma (requires (U.list_no_setoid_repeats equiv l == true))
        (ensures (U.list_no_setoid_repeats equiv (L.filter p l) == true))
        (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    list_no_setoid_repeats_filter equiv p q;
    if p a
    then (if L.existsb (equiv a) (L.filter p q) then existsb_filter_mono (equiv a) p q)

(* The key list of a key-filtered entry list is the filtered key list. *)
let rec map_fst_filtered_out_equiv (vk: raw_data_item) (entries: list (raw_data_item & raw_data_item))
: Lemma (ensures (L.map fst (filtered_out_equiv vk entries) ==
                  L.filter (fun k -> not (V.raw_equiv k vk)) (L.map fst entries)))
        (decreases entries)
= match entries with
  | [] -> ()
  | hd :: tl -> map_fst_filtered_out_equiv vk tl

(* Filtering out a key preserves no-setoid-repeats of the key list. *)
let filtered_out_equiv_no_setoid_repeats (vk: raw_data_item) (entries: list (raw_data_item & raw_data_item))
: Lemma (requires (U.list_no_setoid_repeats V.raw_equiv (L.map fst entries) == true))
        (ensures (U.list_no_setoid_repeats V.raw_equiv (L.map fst (filtered_out_equiv vk entries)) == true))
= map_fst_filtered_out_equiv vk entries;
  list_no_setoid_repeats_filter V.raw_equiv (fun k -> not (V.raw_equiv k vk)) (L.map fst entries)

(* Result validity: the filtered map is a valid (nondet) map. *)
let filtered_out_equiv_valid_map (len': raw_uint64) (vk: raw_data_item) (entries: list (raw_data_item & raw_data_item))
: Lemma (requires (L.for_all V.valid_raw_data_item (L.map fst entries) /\
                   L.for_all V.valid_raw_data_item (L.map snd entries) /\
                   U.list_no_setoid_repeats V.raw_equiv (L.map fst entries) /\
                   U64.v len'.value == L.length (filtered_out_equiv vk entries)))
        (ensures (V.valid_raw_data_item (Map len' (filtered_out_equiv vk entries)) == true))
= V.valid_eq V.basic_data_model (Map len' (filtered_out_equiv vk entries));
  filtered_out_equiv_for_all_valid vk entries;
  filtered_out_equiv_no_setoid_repeats vk entries

(* Derive the engine's key-list preconditions from nondet map validity. *)
let map_valid_facts (xh: raw_data_item)
: Lemma (requires (Map? xh /\ V.valid_raw_data_item xh == true))
        (ensures (L.for_all V.valid_raw_data_item (L.map fst (Map?.v xh)) /\
                  L.for_all V.valid_raw_data_item (L.map snd (Map?.v xh)) /\
                  U.list_no_setoid_repeats V.raw_equiv (L.map fst (Map?.v xh))))
= V.valid_eq V.basic_data_model xh
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

fn cbor_raw_nondet_map_remove
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
        V.valid_raw_data_item (Ghost.reveal xh) == true /\
        V.valid_raw_data_item (Ghost.reveal vk) == true)
returns res: cbor_raw
ensures exists* (xh_result: raw_data_item).
  cbor_match 1.0R res xh_result **
  cbor_match pk key vk **
  Trade.trade
    (cbor_match 1.0R res xh_result)
    (cbor_match pm x xh **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
  pure (Map? xh_result /\
        map_payload xh_result == filtered_out_equiv (Ghost.reveal vk) (map_payload (Ghost.reveal xh)) /\
        V.valid_raw_data_item xh_result == true)
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
  map_valid_facts (Ghost.reveal xhm);
  let res = cbor_raw_nondet_map_remove_entry key ml0 r1 r2 r3 r4 #pm0 #(Map?.v (Ghost.reveal xhm)) #pk #vk;
  match res {
    Some ml' -> {
      with pm'. assert (
        I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
          (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))) **
        Trade.trade
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
             (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)) **
           (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
      );
      let m = MB.cbor_mk_map_full pm' ml' #(filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)));
      unfold (MB.cbor_map_finalized pm' ml' m (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))));
      with len. assert (
        cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))) **
        Trade.trade
          (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
             (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
      );
      filtered_out_equiv_valid_map len (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm));
      Trade.trans
        (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
           (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4));
      Trade.trans_concl_l
        (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
        (cbor_match pm x (Ghost.reveal xhm))
        (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4);
      rewrite (Trade.trade
        (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (cbor_match pm x (Ghost.reveal xhm) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)))
        as (Trade.trade
        (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xh)))))
        (cbor_match pm x (Ghost.reveal xh) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)));
      rewrite (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        as (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xh)))));
      m
    }
    None -> {
      with dummy. assert (pure (~ (L.existsb (V.raw_equiv (Ghost.reveal vk)) (L.map fst (Map?.v (Ghost.reveal xhm))))));
      filter_all_neq_equiv_absent (Map?.v (Ghost.reveal xhm)) (Ghost.reveal vk);
      rewrite (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
        as (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))));
      rewrite (Trade.trade
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
          (cbor_match pm x (Ghost.reveal xhm)))
        as (Trade.trade
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
          (cbor_match pm x (Ghost.reveal xhm)));
      let m = MB.cbor_mk_map_full pm0 ml0 #(filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)));
      unfold (MB.cbor_map_finalized pm0 ml0 m (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))));
      with len. assert (
        cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))) **
        Trade.trade
          (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
      );
      filtered_out_equiv_valid_map len (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm));
      Trade.trans
        (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm))))
        (cbor_match pm x (Ghost.reveal xhm));
      Trade.weak_concl_r
        (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (cbor_match pm x (Ghost.reveal xhm))
        (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4);
      rewrite (Trade.trade
        (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        (cbor_match pm x (Ghost.reveal xhm) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)))
        as (Trade.trade
        (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xh)))))
        (cbor_match pm x (Ghost.reveal xh) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)));
      rewrite (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xhm)))))
        as (cbor_match 1.0R m (Map len (filtered_out_equiv (Ghost.reveal vk) (Map?.v (Ghost.reveal xh)))));
      m
    }
  }
}

#pop-options
