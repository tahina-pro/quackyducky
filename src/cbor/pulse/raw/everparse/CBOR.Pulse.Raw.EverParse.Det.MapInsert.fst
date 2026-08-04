module CBOR.Pulse.Raw.EverParse.Det.MapInsert
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
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module IM = CBOR.Pulse.Raw.EverParse.Iterator.Mixed
module Sorted = LowParse.PulseParse.Iterator.Sorted
module PB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module LPB = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module Cmp = CBOR.Pulse.Raw.Compare
module Perm = CBOR.Pulse.Raw.Match.Perm
module MB = CBOR.Pulse.Raw.EverParse.MapBuilder
module SB = CBOR.Pulse.Raw.EverParse.Serialized.Base
module Fmt = CBOR.Pulse.Raw.EverParse.Format
module Valid = CBOR.Spec.Raw.Valid
module For = CBOR.Spec.Raw.Format
module MapLexInsert = CBOR.Spec.Raw.MapLexInsert
module SpecMap = CBOR.Spec.Raw.Map
module Optimal = CBOR.Spec.Raw.Optimal
module IO = LowParse.PulseParse.Iterator.IntOps

(* Bridge the lowparse dictionary views [IO.u64_ops.v]/[IO.u64_ops.fits] to  *)
(* the concrete [U64.v]/[< pow2 64]: both hold by computation, and expose    *)
(* the u64 count/overflow facts to SMT.                                       *)
let u64_ops_v_eq (x: U64.t)
  : Lemma (IO.u64_ops.v x == U64.v x)
    [SMTPat (IO.u64_ops.v x)]
= ()

let u64_ops_fits_eq (n: nat)
  : Lemma (IO.u64_ops.fits n == (n < pow2 64 <: prop))
    [SMTPat (IO.u64_ops.fits n)]
= ()

(* ============================================================
   Pure specification-level bridge helpers.
   ============================================================ *)

let map_payload (x: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match x with
  | Map _ v -> v
  | _ -> []

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Combine the engine's existential split position [kpos] with
   [MapLexInsert.map_insert_lex_correct] to recover the key-sorted
   [map_insert] semantics.  The engine's post uses
   [I.list_narrow] whereas [map_insert_lex_correct]'s hypothesis uses
   [MapLexInsert.list_narrow]; the two are definitionally identical, so
   SMT bridges them from their defining equations. *)
let map_insert_lex_correct_ex
  (l: list (raw_data_item & raw_data_item))
  (y: (raw_data_item & raw_data_item))
  (l_result: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    L.sorted (Valid.map_entry_order MapLexInsert.order0 _) l == true /\
    ~ (L.memP (fst y) (L.map fst l)) /\
    L.sorted MapLexInsert.entry_lex_order l_result == true /\
    (exists (kpos: nat).
       kpos <= L.length l /\
       l_result == L.append (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos)))
  ))
  (ensures (
    SpecMap.map_insert For.cbor_compare l y == Some l_result /\
    L.sorted (Valid.map_entry_order MapLexInsert.order0 _) l_result == true
  ))
= eliminate exists (kpos: nat).
    (kpos <= L.length l /\
     l_result == L.append (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos)))
  returns (SpecMap.map_insert For.cbor_compare l y == Some l_result /\
           L.sorted (Valid.map_entry_order MapLexInsert.order0 _) l_result == true)
  with _pf. MapLexInsert.map_insert_lex_correct l y kpos l_result

let map_insert_result_length
  (l: list (raw_data_item & raw_data_item))
  (y: (raw_data_item & raw_data_item))
  (l_result: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    (exists (kpos: nat).
       kpos <= L.length l /\
       l_result == L.append (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos)))
  ))
  (ensures (L.length l_result == L.length l + 1))
= eliminate exists (kpos: nat).
    (kpos <= L.length l /\
     l_result == L.append (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos)))
  returns (L.length l_result == L.length l + 1)
  with _pf. begin
    I.list_narrow_length l 0 kpos;
    I.list_narrow_length l kpos (L.length l - kpos);
    L.append_length (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos))
  end

(* Overflow: if a u64 length equals a nat mod 2^64 and is at its max, then
   [n + 1] does not fit in 64 bits. *)
let length_succ_overflow (la: U64.t) (n: nat)
: Lemma
  (requires (U64.v la == n % pow2 64 /\ U64.v la > U64.v (U64.sub 0xffffffffffffffffuL 1uL)))
  (ensures (~ (FStar.UInt.fits (n + 1) 64)))
= assert_norm (pow2 64 == 0xffffffffffffffff + 1);
  FStar.Math.Lemmas.lemma_mod_lt n (pow2 64)

#pop-options

(* ============================================================
   share / gather for [cbor_match_map_entry] (rebuilt locally:
   the internal versions in CBOR.Pulse.Raw.Format.Serialized are
   not exported).
   ============================================================ *)

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

(* ============================================================
   zero_copy_parse readers (rebuilt locally: the versions in
   CBOR.Pulse.Raw.Format.Serialized are not exported).
   ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* strong-prefix single-item reader (for the sorted-insert engine). *)
inline_for_extraction
fn cbor_read_sp (input: S.slice byte) (#pm: perm) (#v: Ghost.erased raw_data_item)
requires PB.pts_to_parsed_strong_prefix parse_raw_data_item input #pm v
returns res: cbor_raw
ensures
  cbor_match 1.0R res v **
  Trade.trade (cbor_match 1.0R res v) (PB.pts_to_parsed_strong_prefix parse_raw_data_item input #pm v)
{
  let exact = PB.pts_to_parsed_strong_prefix_to_serialized_trade serialize_raw_data_item (Fmt.jump_raw_data_item ()) input;
  let res = SB.cbor_read exact;
  Trade.trans _ _ (PB.pts_to_parsed_strong_prefix parse_raw_data_item input #pm v);
  res
}

(* strong-prefix map-entry reader (for the sorted-insert engine). *)
inline_for_extraction
fn cbor_read_map_entry_sp (input: S.slice byte) (#pm: perm) (#v: Ghost.erased (raw_data_item & raw_data_item))
requires PB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v
returns res: cbor_map_entry
ensures
  cbor_match_map_entry 1.0R res v **
  Trade.trade (cbor_match_map_entry 1.0R res v) (PB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
{
  let s1, s2 = PPC.split_nondep_then_strong_prefix (Fmt.jump_raw_data_item ()) input ();
  unfold (PPC.split_nondep_then_strong_prefix_post parse_raw_data_item parse_raw_data_item input pm v (s1, s2));
  let res1 = cbor_read_sp s1;
  let res2 = cbor_read_sp s2;
  Trade.prod _ (PB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #(pm /. 2.0R) (fst (Ghost.reveal v))) _ (PB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #(pm /. 2.0R) (snd (Ghost.reveal v)));
  Trade.trans _ _ (PB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v);
  let res : cbor_map_entry = {
    cbor_map_entry_key = res1;
    cbor_map_entry_value = res2;
  };
  Trade.rewrite_with_trade
    (cbor_match 1.0R res1 (fst (Ghost.reveal v)) ** cbor_match 1.0R res2 (snd (Ghost.reveal v)))
    (cbor_match_map_entry 1.0R res (Ghost.reveal v));
  Trade.trans _ _ (PB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v);
  res
}

(* plain single-item reader (for the key-presence iterator). *)
inline_for_extraction
fn cbor_read_np (input: S.slice byte) (#pm: perm) (#v: Ghost.erased raw_data_item)
requires PB.pts_to_parsed parse_raw_data_item input #pm v
returns res: cbor_raw
ensures
  cbor_match 1.0R res v **
  Trade.trade (cbor_match 1.0R res v) (PB.pts_to_parsed parse_raw_data_item input #pm v)
{
  PB.pts_to_parsed_serialized serialize_raw_data_item input;
  let res = SB.cbor_read input;
  Trade.trans _ _ (PB.pts_to_parsed parse_raw_data_item input #pm v);
  res
}

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

(* ============================================================
   Runtime comparator for CBOR map entries: the [cmp_t] for the
   lexicographic (key-then-value) total order [entry_lex_order].
   ============================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"

inline_for_extraction
fn impl_map_entry_lex_compare
  (x1: cbor_map_entry)
  (x2: cbor_map_entry)
  (#pm1: perm)
  (#v1: Ghost.erased (raw_data_item & raw_data_item))
  (#pm2: perm)
  (#v2: Ghost.erased (raw_data_item & raw_data_item))
requires
  cbor_match_map_entry pm1 x1 (Ghost.reveal v1) **
  cbor_match_map_entry pm2 x2 (Ghost.reveal v2)
returns r: SZ.t
ensures
  cbor_match_map_entry pm1 x1 (Ghost.reveal v1) **
  cbor_match_map_entry pm2 x2 (Ghost.reveal v2) **
  pure (
    (SZ.v r == 0 <==> MapLexInsert.entry_lex_order (Ghost.reveal v1) (Ghost.reveal v2) == true) /\
    (SZ.v r == 1 <==> (Ghost.reveal v1 == Ghost.reveal v2)) /\
    (SZ.v r == 2 <==> MapLexInsert.entry_lex_order (Ghost.reveal v2) (Ghost.reveal v1) == true) /\
    SZ.v r <= 2
  )
{
  let _ = For.lemma_compare_prop;
  let _ = MapLexInsert.entry_lex_compare_prop;
  unfold (cbor_match_map_entry pm1 x1 (Ghost.reveal v1));
  unfold (cbor_match_map_entry pm2 x2 (Ghost.reveal v2));
  let ck = Cmp.impl_cbor_compare x1.cbor_map_entry_key x2.cbor_map_entry_key;
  if (I16.lt ck 0s) {
    fold (cbor_match_map_entry pm1 x1 (Ghost.reveal v1));
    fold (cbor_match_map_entry pm2 x2 (Ghost.reveal v2));
    0sz
  } else if (I16.gt ck 0s) {
    fold (cbor_match_map_entry pm1 x1 (Ghost.reveal v1));
    fold (cbor_match_map_entry pm2 x2 (Ghost.reveal v2));
    2sz
  } else {
    let cv = Cmp.impl_cbor_compare x1.cbor_map_entry_value x2.cbor_map_entry_value;
    fold (cbor_match_map_entry pm1 x1 (Ghost.reveal v1));
    fold (cbor_match_map_entry pm2 x2 (Ghost.reveal v2));
    if (I16.lt cv 0s) {
      0sz
    } else if (I16.gt cv 0s) {
      2sz
    } else {
      1sz
    }
  }
}

#pop-options

(* Wrapper giving the comparator the *folded* [cmp_t] type the engine
   expects. A Pulse [fn] with explicit requires/ensures has a computation
   type that is not definitionally the [cmp_t] type-abbreviation (its
   trailing implicit binders are represented differently), so it cannot be
   passed directly where [cmp_t vmatch (reveal lt_spec)] is expected. By
   ascribing the result type [cmp_t cbor_match_map_entry entry_lex_order]
   and providing only binders + body, [impl_cmp_for_engine ()] gets that
   folded type, which then unifies with the engine's [cmp] parameter. *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"

inline_for_extraction
fn impl_cmp_for_engine ()
: Sorted.cmp_t cbor_match_map_entry MapLexInsert.entry_lex_order
= (x1: cbor_map_entry)
  (x2: cbor_map_entry)
  (#pm1: perm)
  (#v1: Ghost.erased (raw_data_item & raw_data_item))
  (#pm2: perm)
  (#v2: Ghost.erased (raw_data_item & raw_data_item))
{
  let r = impl_map_entry_lex_compare x1 x2;
  r
}

#pop-options

(* ============================================================
   Key-presence test: scan the borrowed entries (in any mixed-list
   representation) and report whether [key] already occurs among
   the existing keys (by raw structural equality, which for
   deterministic maps is the canonical notion of key equality).
   ============================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

fn cbor_raw_map_key_present
  (key: cbor_raw)
  (ml: IT.mixed_list U64.t cbor_map_entry)
  (#pm: perm)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#pk: perm)
  (#vk: Ghost.erased raw_data_item)
requires
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk
returns res: bool
ensures
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk **
  pure (res == true <==> L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l)))
{
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
  while (
    !r_cont
  )
  invariant exists* p_cur cur_it remaining found cont.
    R.pts_to r_it cur_it **
    R.pts_to r_found found **
    R.pts_to r_cont cont **
    cbor_match pk key vk **
    I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
    Trade.trade
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l) **
    pure (
      (found == true ==> L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l))) /\
      (found == false ==> (L.memP (Ghost.reveal vk) (L.map fst (Ghost.reveal l)) <==>
                           L.memP (Ghost.reveal vk) (L.map fst remaining))) /\
      (cont == true ==> (found == false /\ Cons? remaining)) /\
      (cont == false ==> (found == true \/ Nil? remaining))
    )
  {
    with p_cur cur_it remaining found cont. assert (
      R.pts_to r_it cur_it **
      R.pts_to r_found found **
      R.pts_to r_cont cont **
      cbor_match pk key vk **
      I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
      Trade.trade
        (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
    );
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
    assert (pure (
      L.memP (Ghost.reveal vk) (L.map fst remaining) <==>
      (Ghost.reveal vk == fst (Ghost.reveal hd_val) \/
       L.memP (Ghost.reveal vk) (L.map fst tl_l))
    ));
    Trade.elim_hyp_l
      (cbor_match_map_entry pm_v entry hd_val)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining);
    Trade.trans
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
    if (I16.eq ck 0s) {
      r_found := true;
      r_cont := false;
    } else {
      let cur2 = !r_it;
      rewrite (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
           as (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' cur2 tl_l);
      let empt = IM.iter_is_empty cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) cur2;
      rewrite (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' cur2 tl_l)
           as (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l);
      r_cont := (not empt);
    }
  };
  with p_cur cur_it remaining found cont. assert (
    R.pts_to r_it cur_it **
    R.pts_to r_found found **
    R.pts_to r_cont cont **
    cbor_match pk key vk **
    I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
    Trade.trade
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
  );
  Trade.elim
    (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
    (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
  let res = !r_found;
  res
}

#pop-options

(* ============================================================
   Deterministic RAW map-entry insertion.

   Borrows the existing map [x]'s entries as a mixed-list (any
   representation), runs the pre-proven generic sorted-insert engine
   [Sorted.mixed_list_insert_sorted] on the total lexicographic order
   [entry_lex_order], and rebuilds a [_Gen] map.  No heap allocation:
   the caller supplies 4 mixed-list scratch refs and 1 entry ref.
   Fails ([None]) if the key is already present, or on u64 overflow.
   ============================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

fn cbor_raw_det_map_entry_insert
  (x: cbor_raw)
  (key value: cbor_raw)
  (r1 r2 r3 r4: R.ref (IT.mixed_list U64.t cbor_map_entry))
  (ry: R.ref cbor_map_entry)
  (#pm: perm) (#xh: Ghost.erased raw_data_item)
  (#pkv: perm) (#vk: Ghost.erased raw_data_item) (#vv: Ghost.erased raw_data_item)
requires
  cbor_match pm x xh **
  cbor_match pkv key vk ** cbor_match pkv value vv **
  (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy) **
  pure (Map? (Ghost.reveal xh) /\
        L.sorted (Valid.map_entry_order MapLexInsert.order0 _) (Map?.v (Ghost.reveal xh)) == true)
returns res: option cbor_raw
ensures (match res with
  | None ->
    cbor_match pm x xh **
    cbor_match pkv key vk ** cbor_match pkv value vv **
    (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy) **
    pure (L.memP (Ghost.reveal vk) (L.map fst (map_payload (Ghost.reveal xh))) \/
          ~ (FStar.UInt.fits (L.length (map_payload (Ghost.reveal xh)) + 1) 64))
  | Some m ->
    exists* (pm_result: perm) (xh_result: raw_data_item).
      cbor_match pm_result m xh_result **
      Trade.trade
        (cbor_match pm_result m xh_result)
        (cbor_match pm x xh **
         cbor_match pkv key vk ** cbor_match pkv value vv **
         (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy)) **
      pure (Map? xh_result /\
            SpecMap.map_insert For.cbor_compare (map_payload (Ghost.reveal xh)) (Ghost.reveal vk, Ghost.reveal vv) == Some (map_payload xh_result) /\
            (Map?.len xh_result <: raw_uint64) == Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (map_payload xh_result))) /\
            FStar.UInt.fits (L.length (map_payload xh_result)) U64.n /\
            L.sorted (Valid.map_entry_order MapLexInsert.order0 _) (map_payload xh_result) == true))
{
  let xhm : Ghost.erased (r: raw_data_item { Map? r }) = Ghost.hide (Ghost.reveal xh);
  let l_raw : Ghost.erased (list (raw_data_item & raw_data_item)) = Ghost.hide (Map?.v (Ghost.reveal xhm));
  rewrite (cbor_match pm x (Ghost.reveal xh)) as (cbor_match pm x (Ghost.reveal xhm));
  let ml0 = MB.cbor_map_borrow_entries pm x #xhm;
  with pm0. assert (
    I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)) **
    Trade.trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
      (cbor_match pm x (Ghost.reveal xhm))
  );
  rewrite (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
    as (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw));
  rewrite (Trade.trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Map?.v (Ghost.reveal xhm)))
      (cbor_match pm x (Ghost.reveal xhm)))
    as (Trade.trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
      (cbor_match pm x (Ghost.reveal xh)));
  I.mixed_list_match_length cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw);
  // The map payload length equals a u64 value, hence < pow2 64.
  assert (pure (L.length (Ghost.reveal l_raw) == U64.v (Map?.len (Ghost.reveal xhm)).value));
  assert (pure (map_payload (Ghost.reveal xh) == Ghost.reveal l_raw));
  let total_len = IT.mixed_list_length IO.u64_ops ml0;
  let la64 = total_len;
  let limit = U64.sub 0xffffffffffffffffuL 1uL;
  if (U64.lte la64 limit) {
    let present = cbor_raw_map_key_present key ml0 #pm0 #l_raw #pkv #vk;
    if present {
      Trade.elim
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
        (cbor_match pm x (Ghost.reveal xh));
      None #cbor_raw
    } else {
      // Key absent: build the new entry and run the sorted-insert engine.
      assert (pure (U64.v total_len + 1 < pow2 64));
      let y_elem : cbor_map_entry = { cbor_map_entry_key = key; cbor_map_entry_value = value };
      let y_pair : Ghost.erased (raw_data_item & raw_data_item) = Ghost.hide (Ghost.reveal vk, Ghost.reveal vv);
      Trade.rewrite_with_trade
        (cbor_match pkv key (Ghost.reveal vk) ** cbor_match pkv value (Ghost.reveal vv))
        (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair));
      // Engine preconditions.
      MapLexInsert.sorted_key_implies_lex (Ghost.reveal l_raw);
      let _ = MapLexInsert.entry_lex_compare_prop;
      let res_opt = Sorted.mixed_list_insert_sorted
        cbor_match_map_entry IO.u64_ops
        (nondep_then parse_raw_data_item parse_raw_data_item)
        (LPC.jump_nondep_then (Fmt.jump_raw_data_item ()) (Fmt.jump_raw_data_item ()))
        (Ghost.hide MapLexInsert.entry_lex_order)
        (impl_cmp_for_engine ())
        pm0 pkv ml0 l_raw y_elem y_pair
        r1 r2 r3 r4 ry
        cbor_match_map_entry_share cbor_match_map_entry_gather
        cbor_read_map_entry_sp;
      match res_opt {
        Some ml_result -> {
        unfold (Sorted.mixed_list_insert_sorted_post cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) MapLexInsert.entry_lex_order pm0 pkv ml0 l_raw y_elem y_pair r1 r2 r3 r4 ry (Some ml_result));
        with pm_result l_result. assert (
          I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result **
          Trade.trade
            (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result)
            (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw) **
             cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair) **
             (exists* v1 v2 v3 v4 vy. R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy))
        );
        // Correctness bridge: recover key-sorted map_insert semantics.
        map_insert_lex_correct_ex (Ghost.reveal l_raw) (Ghost.reveal y_pair) l_result;
        map_insert_result_length (Ghost.reveal l_raw) (Ghost.reveal y_pair) l_result;
        I.mixed_list_match_length cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result;
        // Rebuild a CBOR map value.
        let m = MB.cbor_mk_map_full pm_result ml_result #l_result;
        unfold (MB.cbor_map_finalized pm_result ml_result m l_result);
        with len. assert (
          cbor_match 1.0R m (Map len l_result) **
          Trade.trade
            (cbor_match 1.0R m (Map len l_result))
            (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result)
        );
        // Compose all trades back to the original resources.
        Trade.intro_trade
          (cbor_match 1.0R m (Map len l_result))
          (cbor_match pm x (Ghost.reveal xh) **
           cbor_match pkv key (Ghost.reveal vk) **
           cbor_match pkv value (Ghost.reveal vv) **
           (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy))
          (Trade.trade
             (cbor_match 1.0R m (Map len l_result))
             (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result) **
           Trade.trade
             (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result)
             (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw) **
              cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair) **
              (exists* v1 v2 v3 v4 vy. R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy)) **
           Trade.trade
             (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair))
             (cbor_match pkv key (Ghost.reveal vk) ** cbor_match pkv value (Ghost.reveal vv)) **
           Trade.trade
             (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
             (cbor_match pm x (Ghost.reveal xh)))
          fn _ {
            Trade.elim
              (cbor_match 1.0R m (Map len l_result))
              (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result);
            Trade.elim
              (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result)
              (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw) **
               cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair) **
               (exists* v1 v2 v3 v4 vy. R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy));
            Trade.elim
              (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair))
              (cbor_match pkv key (Ghost.reveal vk) ** cbor_match pkv value (Ghost.reveal vv));
            Trade.elim
              (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
              (cbor_match pm x (Ghost.reveal xh));
          };
        Some #cbor_raw m
     }
       None -> {
       unfold (Sorted.mixed_list_insert_sorted_post cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) MapLexInsert.entry_lex_order pm0 pkv ml0 l_raw y_elem y_pair r1 r2 r3 r4 ry (None #(IT.mixed_list U64.t cbor_map_entry)));
       FStar.List.Tot.Properties.memP_map_intro fst (Ghost.reveal y_pair) (Ghost.reveal l_raw);
       Trade.elim
         (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair))
         (cbor_match pkv key (Ghost.reveal vk) ** cbor_match pkv value (Ghost.reveal vv));
       Trade.elim
         (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
         (cbor_match pm x (Ghost.reveal xh));
       None #cbor_raw
     }
     }
   }
  } else {
    // Overflow: total_len == 2^64 - 1, so total_len + 1 does not fit in u64.
    length_succ_overflow la64 (L.length (Ghost.reveal l_raw));
    Trade.elim
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
      (cbor_match pm x (Ghost.reveal xh));
    None #cbor_raw
  }
}

#pop-options
