module CBOR.Pulse.Raw.EverParse.MapRemove
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

(* Key equality used for map-entry removal: two keys are equal iff the
   canonical (deterministic-encoding) comparator returns 0.  By
   [For.cbor_compare_equal] this is EXACTLY structural equality on the
   [raw_data_item] keys, which is what makes the uniqueness reasoning below
   go through for a valid (no-repeated-keys) CBOR map. *)
let key_eq (k1 k2: raw_data_item) : bool = (For.cbor_compare k1 k2 = 0)

(* Spec-level result of removing key [vk]: the entries whose key differs from
   [vk].  Wrapped as a top-level [Tot] function (closing over a *non-erased*
   key) so it can be applied to [Ghost.reveal]ed erased values in the Pulse
   specifications without the [filter] predicate becoming [GTot]. *)
let filtered_out (vk: raw_data_item) (m: list (raw_data_item & raw_data_item))
: list (raw_data_item & raw_data_item)
= L.filter (fun e -> not (key_eq (fst e) vk)) m

(* ================================================================ *)
(* Pure list lemmas: filtering-out a unique key == structural splice *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* [list_narrow] over the concatenation [prefix ++ (matched :: suffix)]:
   the [0,k) view is exactly [prefix], and the [k+1, ..) view is exactly
   [suffix], where [k = length prefix]. *)
let list_narrow_split3
  (#a: Type) (prefix: list a) (matched: a) (suffix: list a)
: Lemma (ensures (
    let l = L.append prefix (matched :: suffix) in
    let k = L.length prefix in
    I.list_narrow l 0 k == prefix /\
    I.list_narrow l (k + 1) (L.length l - k - 1) == suffix))
= let l = L.append prefix (matched :: suffix) in
  let k = L.length prefix in
  // length facts: length l == k + 1 + length suffix, so k <= length l and k+1 <= length l
  L.append_length prefix (matched :: suffix);
  L.append_length prefix [matched];
  L.append_assoc prefix [matched] suffix;
  // splitAt k l == (prefix, matched :: suffix)
  FStar.List.Pure.Properties.lemma_splitAt l prefix (matched :: suffix) k;
  // splitAt (k+1) l == (prefix ++ [matched], suffix)
  FStar.List.Pure.Properties.lemma_splitAt l (L.append prefix [matched]) suffix (k + 1);
  // list_narrow l 0 k == fst (splitAt k (snd (splitAt 0 l))) == fst (splitAt k l)
  assert (snd (L.splitAt 0 l) == l);
  // list_narrow l (k+1) m == fst (splitAt m (snd (splitAt (k+1) l))) == fst (splitAt (length suffix) suffix)
  FStar.List.Pure.Properties.splitAt_length_total suffix

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* [list_narrow l 0 len == l] and [list_narrow l 0 0 == []]: needed to seed
   and (dually) close the linear-scan loop invariant. *)
let list_narrow_full (#a: Type) (l: list a)
: Lemma (ensures (I.list_narrow l 0 (L.length l) == l /\ I.list_narrow l 0 0 == []))
= FStar.List.Pure.Properties.splitAt_length_total l;
  assert (snd (L.splitAt 0 l) == l)

(* Stepping a suffix-narrow: the [k, len-k) view is [index l k] followed by
   the [k+1, len-k-1) view.  This drives the linear scan: each iteration
   consumes the head [index l k] and advances [k]. *)
let list_narrow_step (#a: Type) (l: list a) (k: nat)
: Lemma (requires (k < L.length l))
        (ensures (I.list_narrow l k (L.length l - k) ==
                  L.index l k :: I.list_narrow l (k + 1) (L.length l - k - 1)))
= let a', b, c = L.split3 l k in
  FStar.List.Pure.Properties.lemma_split3_append l k;   // l == a' @ (b :: c)
  FStar.List.Pure.Properties.lemma_split3_index l k;    // b == index l k
  FStar.List.Pure.Properties.lemma_split3_length l k;   // length a' == k, length c == len-k-1
  list_narrow_split3 a' b c;                            // narrow (a'@(b::c)) (k+1) (len-k-1) == c
  // splitAt k l == (a', b :: c), so snd (splitAt k l) == b :: c
  FStar.List.Pure.Properties.lemma_splitAt l a' (b :: c) k;
  // list_narrow l k (len-k) == fst (splitAt (len-k) (b::c)) == b::c
  FStar.List.Pure.Properties.splitAt_length_total (b :: c)

(* Decompose [l] at the unique matching position [k] into [prefix] (the
   [0,k) narrow), the matched element [index l k], and [suffix] (the
   [k+1,..) narrow). *)
let list_decompose_at (#a: Type) (l: list a) (k: nat)
: Lemma (requires (k < L.length l))
        (ensures (l == L.append (I.list_narrow l 0 k)
                                (L.index l k :: I.list_narrow l (k + 1) (L.length l - k - 1))))
= let a', b, c = L.split3 l k in
  FStar.List.Pure.Properties.lemma_split3_append l k;
  FStar.List.Pure.Properties.lemma_split3_index l k;
  FStar.List.Pure.Properties.lemma_split3_length l k;
  list_narrow_split3 a' b c

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"

(* filter distributes over append *)
let rec filter_append (#a: Type) (p: a -> bool) (l1 l2: list a)
: Lemma (ensures L.filter p (L.append l1 l2) == L.append (L.filter p l1) (L.filter p l2))
        (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> filter_append p q l2

(* If [vk] is not among the keys of [m], filtering-out [vk] leaves [m] intact. *)
let rec filter_all_neq
  (m: list (raw_data_item & raw_data_item)) (vk: raw_data_item)
: Lemma (requires (~ (L.memP vk (L.map fst m))))
        (ensures (L.filter (fun e -> not (key_eq (fst e) vk)) m == m))
        (decreases m)
= match m with
  | [] -> ()
  | hd :: tl ->
    For.cbor_compare_equal (fst hd) vk;
    filter_all_neq tl vk

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Core: for a no-repeated-keys list, filtering-out the (unique) key [vk] of
   the middle entry [matched] removes exactly that entry, leaving the
   structural splice [prefix ++ suffix]. *)
let filter_removes_unique_key
  (l prefix suffix: list (raw_data_item & raw_data_item))
  (matched: (raw_data_item & raw_data_item))
  (vk: raw_data_item)
: Lemma
  (requires (l == L.append prefix (matched :: suffix) /\ fst matched == vk /\
             L.no_repeats_p (L.map fst l)))
  (ensures (L.filter (fun e -> not (key_eq (fst e) vk)) l == L.append prefix suffix))
= let p : (raw_data_item & raw_data_item -> bool) = (fun e -> not (key_eq (fst e) vk)) in
  // map fst l == (map fst prefix) @ (vk :: map fst suffix)
  L.map_append fst prefix (matched :: suffix);
  L.no_repeats_p_append_elim (L.map fst prefix) (vk :: L.map fst suffix);
  // vk not in prefix keys, vk not in suffix keys
  filter_all_neq prefix vk;
  filter_all_neq suffix vk;
  // p matched == false since key_eq vk vk == true
  For.cbor_compare_equal vk vk;
  // combine via filter_append
  filter_append p prefix (matched :: suffix)

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* The single bridge lemma the Pulse engine calls: given the split of [l] at
   the (unique) matching entry, the narrow-splice [narrow 0 k ++ narrow (k+1) rest]
   equals the spec-level [filter], and the key is present. *)
let map_remove_correct
  (l prefix suffix: list (raw_data_item & raw_data_item))
  (matched: (raw_data_item & raw_data_item))
  (vk: raw_data_item)
: Lemma
  (requires (l == L.append prefix (matched :: suffix) /\ fst matched == vk /\
             L.no_repeats_p (L.map fst l)))
  (ensures (
    let k = L.length prefix in
    k < L.length l /\
    I.list_narrow l 0 k == prefix /\
    I.list_narrow l (k + 1) (L.length l - k - 1) == suffix /\
    L.append (I.list_narrow l 0 k) (I.list_narrow l (k + 1) (L.length l - k - 1))
      == L.filter (fun e -> not (key_eq (fst e) vk)) l /\
    L.memP vk (L.map fst l)))
= list_narrow_split3 prefix matched suffix;
  filter_removes_unique_key l prefix suffix matched vk;
  L.map_append fst prefix (matched :: suffix);
  L.append_length prefix (matched :: suffix);
  L.append_memP (L.map fst prefix) (vk :: L.map fst suffix) vk

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Post-loop bridge, stated purely in terms of the matching position [k]:
   given that entry [k] carries key [vk] in a no-repeated-keys list, the
   narrow-splice [narrow 0 k ++ narrow (k+1) (len-k-1)] is exactly the
   spec-level [filter], the key is present, and the [0,k) narrow has
   length [k].  This is the single lemma the Pulse [Some] branch calls. *)
let map_remove_correct_at
  (l: list (raw_data_item & raw_data_item)) (k: nat) (vk: raw_data_item)
: Lemma
  (requires (k < L.length l /\ fst (L.index l k) == vk /\ L.no_repeats_p (L.map fst l)))
  (ensures (
    L.append (I.list_narrow l 0 k) (I.list_narrow l (k + 1) (L.length l - k - 1))
      == filtered_out vk l /\
    L.memP vk (L.map fst l) /\
    L.length (I.list_narrow l 0 k) == k))
= let prefix = I.list_narrow l 0 k in
  let suffix = I.list_narrow l (k + 1) (L.length l - k - 1) in
  let matched = L.index l k in
  list_decompose_at l k;              // l == prefix @ (matched :: suffix)
  I.list_narrow_length l 0 k;          // length prefix == k
  map_remove_correct l prefix suffix matched vk

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

fn cbor_raw_map_find_key
  (key: cbor_raw)
  (ml: IT.mixed_list U64.t cbor_map_entry)
  (#pm: perm)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#pk: perm)
  (#vk: Ghost.erased raw_data_item)
requires
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk
returns res: (bool & U64.t)
ensures
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk **
  pure (
    (fst res == true ==> (U64.v (snd res) < L.length (Ghost.reveal l) /\
                          fst (L.index (Ghost.reveal l) (U64.v (snd res))) == Ghost.reveal vk /\
                          L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l)))) /\
    (fst res == false ==> ~ (L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l))))
  )
{
  I.mixed_list_match_length cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l;
  list_narrow_full (Ghost.reveal l);
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
      (found == false ==> remaining == I.list_narrow (Ghost.reveal l) (U64.v k_val) (L.length (Ghost.reveal l) - U64.v k_val)) /\
      (found == true ==> (U64.v k_val < L.length (Ghost.reveal l) /\
                          fst (L.index (Ghost.reveal l) (U64.v k_val)) == Ghost.reveal vk)) /\
      (found == false ==> (L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l)) <==>
                           L.memP (Ghost.reveal vk) (L.map fst remaining))) /\
      (found == true ==> L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l))) /\
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
    list_narrow_step (Ghost.reveal l) (U64.v k_val);
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
    unfold (cbor_match_map_entry pm_v entry hd_val);
    let ck = Cmp.impl_cbor_compare key entry.cbor_map_entry_key;
    fold (cbor_match_map_entry pm_v entry hd_val);
    For.cbor_compare_equal (Ghost.reveal vk) (fst (Ghost.reveal hd_val));
    assert (pure (L.map fst remaining == fst (Ghost.reveal hd_val) :: L.map fst tl_l));
    Trade.elim_hyp_l
      (cbor_match_map_entry pm_v entry hd_val)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining);
    Trade.trans
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
    if (I16.eq ck 0s) {
      // Found at position k_val: hd_val == index l k, and vk == fst hd_val
      assert (pure (L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l))));
      r_found := true;
      r_cont := false;
    } else {
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

fn cbor_raw_map_remove_entry
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
  pure (L.no_repeats_p (L.map fst (Ghost.reveal l)))
returns res: option (IT.mixed_list U64.t cbor_map_entry)
ensures
  cbor_match pk key vk **
  (match res with
   | Some ml' -> exists* (pm': perm).
       I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
         (filtered_out (Ghost.reveal vk) (Ghost.reveal l)) **
       Trade.trade
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml'
            (filtered_out (Ghost.reveal vk) (Ghost.reveal l)))
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
          (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
       pure (L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l)))
   | None ->
       I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4) **
       pure (~ (L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l)))))
{
  let found, kk = cbor_raw_map_find_key key ml;
  if found {
    with w1 w2 w3 w4. assert (R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4);
    let n = IT.mixed_list_length IO.u64_ops ml;
    I.mixed_list_match_length cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l;
    map_remove_correct_at (Ghost.reveal l) (U64.v kk) (Ghost.reveal vk);
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
         as (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (filtered_out (Ghost.reveal vk) (Ghost.reveal l)));
    Trade.intro_trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (filtered_out (Ghost.reveal vk) (Ghost.reveal l)))
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
        rewrite (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) ((pm /. 2.0R) /. 2.0R) ml_res (filtered_out (Ghost.reveal vk) (Ghost.reveal l)))
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
