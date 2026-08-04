module CBOR.Pulse.Raw.EverParse.Nondet.MapInsert
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.Type
open CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.Combinators
open FStar.Real

module SZ = FStar.SizeT
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module IM = CBOR.Pulse.Raw.EverParse.Iterator.Mixed
module PB = LowParse.PulseParse.Base
module LPB = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module Perm = CBOR.Pulse.Raw.Match.Perm
module MB = CBOR.Pulse.Raw.EverParse.MapBuilder
module SB = CBOR.Pulse.Raw.EverParse.Serialized.Base
module Fmt = CBOR.Pulse.Raw.EverParse.Format
module Valid = CBOR.Spec.Raw.Valid
module Optimal = CBOR.Spec.Raw.Optimal
module Append = LowParse.PulseParse.Iterator.Append
module MapPrepend = CBOR.Spec.Raw.MapPrepend
module NondetCompare = CBOR.Pulse.Raw.Nondet.Compare
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
   Pure specification-level helpers.
   ============================================================ *)

(* Total accessor for a map's entry list (returns [] on non-maps), used in the
   postcondition where [xh] is not guarded by a [Map?] conjunct. *)
let map_payload (x: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match x with
  | Map _ v -> v
  | _ -> []

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Overflow: if a u64 length equals a nat mod 2^64 and is at its max, then
   [n + 1] does not fit in 64 bits. (Same lemma as in Det.MapInsert.) *)
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
   not exported).  Copied verbatim from Det.MapInsert.
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
   plain map-entry reader (for the key-presence iterator).  Copied
   verbatim from Det.MapInsert.
   ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

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
   Raw-level key-presence scan over a NONDETERMINISTIC CBOR map's
   entries, based on structural equivalence ([raw_equiv]) rather
   than syntactic equality ([==]).  The nondet analog of
   [Det.MapInsert.cbor_raw_map_key_present].

   Requires validity of the searched key [vk] and of all map keys
   [map fst l], which is exactly what the caller (nondet map insert)
   has on hand from map validity.
   ============================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 48"

fn cbor_raw_nondet_map_key_present
  (key: cbor_raw)
  (ml: IT.mixed_list U64.t cbor_map_entry)
  (#pm: perm)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#pk: perm)
  (#vk: Ghost.erased raw_data_item)
requires
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk **
  pure (
    Valid.valid_raw_data_item (Ghost.reveal vk) == true /\
    L.for_all Valid.valid_raw_data_item (L.map fst (Ghost.reveal l)) == true
  )
returns res: bool
ensures
  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_match pk key vk **
  pure (res == true <==> L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l)))
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
      L.for_all Valid.valid_raw_data_item (L.map fst remaining) == true /\
      (found == true ==> L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l))) /\
      (found == false ==> (L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l)) <==>
                           L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst remaining))) /\
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
    // remaining = hd_val :: tl_l, so map fst remaining = fst hd_val :: map fst tl_l,
    // and the head key (fst hd_val) is valid (it is in map fst remaining).
    assert (pure (L.map fst remaining == fst (Ghost.reveal hd_val) :: L.map fst tl_l));
    assert (pure (Valid.valid_raw_data_item (fst (Ghost.reveal hd_val)) == true));
    assert (pure (L.for_all Valid.valid_raw_data_item (L.map fst tl_l) == true));
    unfold (cbor_match_map_entry pm_v entry hd_val);
    let found_here = NondetCompare.cbor_nondet_equiv key entry.cbor_map_entry_key;
    fold (cbor_match_map_entry pm_v entry hd_val);
    // found_here == raw_equiv vk (fst hd_val)
    assert (pure (found_here == true <==> Valid.raw_equiv (Ghost.reveal vk) (fst (Ghost.reveal hd_val))));
    assert (pure (
      L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst remaining) ==
      (Valid.raw_equiv (Ghost.reveal vk) (fst (Ghost.reveal hd_val)) ||
       L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst tl_l))
    ));
    Trade.elim_hyp_l
      (cbor_match_map_entry pm_v entry hd_val)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining);
    Trade.trans
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm' it' tl_l)
      (I.iterator_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
    if found_here {
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
   Raw-level NONDETERMINISTIC map-entry "prepend".
   ============================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 48"

fn cbor_raw_nondet_map_entry_insert
  (x: cbor_raw)
  (key value: cbor_raw)
  (r1 r2: R.ref (IT.mixed_list U64.t cbor_map_entry))
  (ry: R.ref cbor_map_entry)
  (#pm: perm) (#xh: Ghost.erased raw_data_item)
  (#pkv: perm) (#vk: Ghost.erased raw_data_item) (#vv: Ghost.erased raw_data_item)
requires
  cbor_match pm x xh **
  cbor_match pkv key vk ** cbor_match pkv value vv **
  (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy) **
  pure (Map? (Ghost.reveal xh) /\
        Valid.valid_raw_data_item (Ghost.reveal xh) == true /\
        Valid.valid_raw_data_item (Ghost.reveal vk) == true /\
        Valid.valid_raw_data_item (Ghost.reveal vv) == true)
returns res: option cbor_raw
ensures (match res with
  | None ->
    cbor_match pm x xh **
    cbor_match pkv key vk ** cbor_match pkv value vv **
    (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy) **
    pure (L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst (map_payload (Ghost.reveal xh))) \/
          ~ (FStar.UInt.fits (L.length (map_payload (Ghost.reveal xh)) + 1) 64))
  | Some m ->
    exists* (pm_result: perm) (xh_result: raw_data_item).
      cbor_match pm_result m xh_result **
      Trade.trade
        (cbor_match pm_result m xh_result)
        (cbor_match pm x xh **
         cbor_match pkv key vk ** cbor_match pkv value vv **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy)) **
      pure (Map? xh_result /\
            map_payload xh_result == (Ghost.reveal vk, Ghost.reveal vv) :: map_payload (Ghost.reveal xh) /\
            Valid.valid_raw_data_item xh_result == true /\
            (Map?.len xh_result <: raw_uint64) == Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (map_payload xh_result))) /\
            FStar.UInt.fits (L.length (map_payload xh_result)) U64.n))
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
  assert (pure (L.length (Ghost.reveal l_raw) == U64.v (Map?.len (Ghost.reveal xhm)).value));
  assert (pure (map_payload (Ghost.reveal xh) == Ghost.reveal l_raw));
  let total_len = IT.mixed_list_length IO.u64_ops ml0;
  assert (pure (U64.v total_len == L.length (Ghost.reveal l_raw)));
  let la64 = total_len;
  assert (pure (U64.v la64 == U64.v total_len));
  let limit = U64.sub 0xffffffffffffffffuL 1uL;
  if (U64.lte la64 limit) {
    // Surface validity of all map keys, needed by the dup-check.
    Valid.valid_eq Valid.basic_data_model (Ghost.reveal xh);
    assert (pure (L.for_all Valid.valid_raw_data_item (L.map fst (Ghost.reveal l_raw)) == true));
    let present = cbor_raw_nondet_map_key_present key ml0 #pm0 #l_raw #pkv #vk;
    if present {
      Trade.elim
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
        (cbor_match pm x (Ghost.reveal xh));
      None #cbor_raw
    } else {
      // Key absent: build the new entry and PREPEND it.
      assert (pure (U64.v total_len + 1 < pow2 64));
      let y_elem : cbor_map_entry = { cbor_map_entry_key = key; cbor_map_entry_value = value };
      let y_pair : Ghost.erased (raw_data_item & raw_data_item) =
        Ghost.hide (Ghost.reveal vk, Ghost.reveal vv);
      Trade.rewrite_with_trade
        (cbor_match pkv key (Ghost.reveal vk) ** cbor_match pkv value (Ghost.reveal vv))
        (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair));
      // Build a singleton mixed_list at ambient permission pm0.
      let sing_ml = Append.mixed_list_singleton_gen
        cbor_match_map_entry IO.u64_ops
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm0 pkv y_elem y_pair ry
        cbor_match_map_entry_gather;
      // Prepend: singleton BEFORE the borrowed entries.
      let res_ml = Append.mixed_list_append
        cbor_match_map_entry IO.u64_ops
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm0 sing_ml (Ghost.hide [Ghost.reveal y_pair]) ml0 l_raw r1 r2;
      let l_result : Ghost.erased (list (raw_data_item & raw_data_item)) =
        Ghost.hide (Ghost.reveal y_pair :: Ghost.reveal l_raw);
      rewrite (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml
                (List.Tot.append [Ghost.reveal y_pair] (Ghost.reveal l_raw)))
        as (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result));
      rewrite (Trade.trade
                 (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml
                   (List.Tot.append [Ghost.reveal y_pair] (Ghost.reveal l_raw)))
                 (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair] **
                  I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw) **
                  (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va)))
        as (Trade.trade
              (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result))
              (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair] **
               I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw) **
               (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va)));
      // Rebuild a CBOR map value.
      I.mixed_list_match_length cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result);
      assert (pure (FStar.UInt.fits (U64.v (IT.mixed_list_length IO.u64_ops res_ml)) 64));
      let m = MB.cbor_mk_map_full pm0 res_ml #l_result;
      unfold (MB.cbor_map_finalized pm0 res_ml m (Ghost.reveal l_result));
      with len. assert (
        cbor_match 1.0R m (Map len (Ghost.reveal l_result)) **
        Trade.trade
          (cbor_match 1.0R m (Map len (Ghost.reveal l_result)))
          (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result))
      );
      // The rebuilt length field is the minimal (canonical) encoding.
      assert (pure (U64.v len.value == L.length (Ghost.reveal l_result)));
      assert (pure (U64.v len.value == 1 + U64.v (Map?.len (Ghost.reveal xhm)).value));
      assert (pure ((len <: raw_uint64) == Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (Ghost.reveal l_result)))));
      // Validity of the prepended map.
      MapPrepend.mk_cbor_map_prepend_valid
        (Map?.len (Ghost.reveal xhm))
        (Map?.v (Ghost.reveal xhm))
        (Ghost.reveal vk)
        (Ghost.reveal vv)
        len;
      assert (pure (Valid.valid_raw_data_item (Map len (Ghost.reveal l_result)) == true));
      // Compose all trades back to the original resources.
      Trade.intro_trade
        (cbor_match 1.0R m (Map len (Ghost.reveal l_result)))
        (cbor_match pm x (Ghost.reveal xh) **
         cbor_match pkv key (Ghost.reveal vk) **
         cbor_match pkv value (Ghost.reveal vv) **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy))
        (Trade.trade
           (cbor_match 1.0R m (Map len (Ghost.reveal l_result)))
           (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result)) **
         Trade.trade
           (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result))
           (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair] **
            I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw) **
            (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va)) **
         Trade.trade
           (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair])
           (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair) **
            (exists* vy. R.pts_to ry vy)) **
         Trade.trade
           (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair))
           (cbor_match pkv key (Ghost.reveal vk) ** cbor_match pkv value (Ghost.reveal vv)) **
         Trade.trade
           (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
           (cbor_match pm x (Ghost.reveal xh)))
        fn _ {
          Trade.elim
            (cbor_match 1.0R m (Map len (Ghost.reveal l_result)))
            (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result));
          Trade.elim
            (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result))
            (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair] **
             I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw) **
             (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va));
          Trade.elim
            (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair])
            (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair) **
             (exists* vy. R.pts_to ry vy));
          Trade.elim
            (cbor_match_map_entry pkv y_elem (Ghost.reveal y_pair))
            (cbor_match pkv key (Ghost.reveal vk) ** cbor_match pkv value (Ghost.reveal vv));
          Trade.elim
            (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
            (cbor_match pm x (Ghost.reveal xh));
        };
      Some #cbor_raw m
    }
  } else {
    // total_len == 2^64 - 1: total_len + 1 does not fit in u64.
    length_succ_overflow la64 (L.length (Ghost.reveal l_raw));
    Trade.elim
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
      (cbor_match pm x (Ghost.reveal xh));
    None #cbor_raw
  }
}

#pop-options
