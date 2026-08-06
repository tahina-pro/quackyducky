module CBOR.Pulse.Raw.EverParse.Det.ArrayBuilder
#lang-pulse
friend CBOR.Pulse.API.Det.Type
friend CBOR.Pulse.API.Det.Common
(* Needed so the abstract cell type [cbor_det_array_append_cell_t] (declared in
   the relocated raw/ interface) is transparently [IT.mixed_list U64.t cbor_raw]
   here:
     cbor_det_array_append_cell_t == ML.cbor_raw_mixed_list cbor_raw  (friend Det.Type)
                                   == IT.mixed_list U64.t cbor_raw     (friend MixedList) *)
friend CBOR.Pulse.Raw.Format.MixedList

open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Type
open CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Base

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module RV = CBOR.Spec.Raw.Optimal
module RF = CBOR.Spec.Raw.Format
module Det = CBOR.Pulse.API.Det.Common
module AB = CBOR.Pulse.Raw.EverParse.ArrayBuilder
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module IT = LowParse.PulseParse.Iterator.Type
module I = LowParse.PulseParse.Iterator
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module L = FStar.List.Tot

(* ================================================================ *)
(* Translation of a spec-level element list to raw data items       *)
(* ================================================================ *)

let det_raw_list (l: list Spec.cbor) : list raw_data_item =
  L.map SpecRaw.mk_det_raw_cbor l

(* det_raw_list preserves length *)
let length_det_raw_list (l: list Spec.cbor)
: Lemma (L.length (det_raw_list l) == L.length l)
= L.map_lemma SpecRaw.mk_det_raw_cbor l

(* det_raw_list distributes over append *)
let det_raw_list_append (l1 l2: list Spec.cbor)
: Lemma (det_raw_list (L.append l1 l2) ==
         L.append (det_raw_list l1) (det_raw_list l2))
= L.map_append SpecRaw.mk_det_raw_cbor l1 l2

(* ================================================================ *)
(* Ownership at the deterministic-CBOR Spec level                   *)
(* ================================================================ *)

let cbor_det_array_owned (x: cbor_mixed_list_array) (l: list Spec.cbor) : slprop =
  AB.cbor_array_owned x (det_raw_list l)

(* ================================================================ *)
(* Empty array                                                      *)
(* ================================================================ *)

inline_for_extraction
fn cbor_det_array_empty (_: unit)
requires emp
returns res: cbor_mixed_list_array
ensures cbor_det_array_owned res []
{
  let res = AB.cbor_array_empty ();
  rewrite (AB.cbor_array_owned res [])
    as (AB.cbor_array_owned res (det_raw_list ([] <: list Spec.cbor)));
  fold (cbor_det_array_owned res ([] <: list Spec.cbor));
  res
}

(* ================================================================ *)
(* Singleton array                                                  *)
(* ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_det_array_singleton
  (x: cbor_raw) (ry: R.ref cbor_raw)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_raw)
requires
  Det.cbor_det_match pm x v ** R.pts_to ry w0
returns res: cbor_mixed_list_array
ensures
  cbor_det_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_det_array_owned res [Ghost.reveal v])
    (Det.cbor_det_match pm x v ** (exists* w. R.pts_to ry w))
{
  unfold (Det.cbor_det_match pm x v);
  let res = AB.cbor_array_singleton x ry
    #pm #(Ghost.hide (SpecRaw.mk_det_raw_cbor (Ghost.reveal v)));
  rewrite (AB.cbor_array_owned res [SpecRaw.mk_det_raw_cbor (Ghost.reveal v)])
    as (AB.cbor_array_owned res (det_raw_list [Ghost.reveal v]));
  fold (cbor_det_array_owned res [Ghost.reveal v]);
  Trade.intro_trade
    (cbor_det_array_owned res [Ghost.reveal v])
    (Det.cbor_det_match pm x v ** (exists* w. R.pts_to ry w))
    (Trade.trade
      (AB.cbor_array_owned res [SpecRaw.mk_det_raw_cbor (Ghost.reveal v)])
      (cbor_match pm x (SpecRaw.mk_det_raw_cbor (Ghost.reveal v)) ** (exists* w. R.pts_to ry w)))
    fn _ {
      unfold (cbor_det_array_owned res [Ghost.reveal v]);
      rewrite (AB.cbor_array_owned res (det_raw_list [Ghost.reveal v]))
        as (AB.cbor_array_owned res [SpecRaw.mk_det_raw_cbor (Ghost.reveal v)]);
      Trade.elim
        (AB.cbor_array_owned res [SpecRaw.mk_det_raw_cbor (Ghost.reveal v)])
        (cbor_match pm x (SpecRaw.mk_det_raw_cbor (Ghost.reveal v)) ** (exists* w. R.pts_to ry w));
      fold (Det.cbor_det_match pm x v);
    };
  res
}

#pop-options

(* ================================================================ *)
(* Length of an owned array fits in a u64                           *)
(* ================================================================ *)

ghost
fn cbor_det_array_owned_length_fits
  (x: cbor_mixed_list_array) (#l: Ghost.erased (list Spec.cbor))
requires cbor_det_array_owned x l
ensures cbor_det_array_owned x l ** pure (FStar.UInt.fits (L.length (Ghost.reveal l)) 64)
{
  unfold (cbor_det_array_owned x l);
  AB.cbor_array_owned_length_fits x;
  length_det_raw_list l;
  fold (cbor_det_array_owned x l);
}

(* ================================================================ *)
(* Append two owned arrays                                           *)
(*                                                                  *)
(* NOTE: element counts are now [U64.t] (the CBOR wire count type),  *)
(* so forming the underlying [Append] node's [fits (len1 + len2)]     *)
(* obligation is exactly the plain u64 non-overflow test performed at *)
(* runtime by the raw [cbor_array_append]; no unsound [size_t]-width  *)
(* platform assumption is required.                                   *)
(* ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_det_array_append
  (x1 x2: cbor_mixed_list_array)
  (r_before r_after: R.ref (IT.mixed_list U64.t cbor_raw))
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
  R.pts_to r_before vb0 ** R.pts_to r_after va0
returns res: option cbor_mixed_list_array
ensures
  (match res with
   | None ->
     cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
     pure (~ (FStar.UInt.fits (L.length (Ghost.reveal l1) + L.length (Ghost.reveal l2)) 64))
   | Some r ->
     cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
     Trade.trade
       (cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
       (cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
{
  unfold (cbor_det_array_owned x1 l1);
  unfold (cbor_det_array_owned x2 l2);
  let res = AB.cbor_array_append x1 x2 r_before r_after
    #(det_raw_list l1) #(det_raw_list l2);
  match res {
    None -> {
      length_det_raw_list l1;
      length_det_raw_list l2;
      fold (cbor_det_array_owned x1 l1);
      fold (cbor_det_array_owned x2 l2);
      None #cbor_mixed_list_array
    }
    Some r -> {
      det_raw_list_append l1 l2;
      rewrite (AB.cbor_array_owned r (L.append (det_raw_list l1) (det_raw_list l2)))
        as (AB.cbor_array_owned r (det_raw_list (L.append (Ghost.reveal l1) (Ghost.reveal l2))));
      fold (cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)));
      Trade.intro_trade
        (cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
        (cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
         (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va))
        (Trade.trade
          (AB.cbor_array_owned r (L.append (det_raw_list l1) (det_raw_list l2)))
          (AB.cbor_array_owned x1 (det_raw_list l1) **
           AB.cbor_array_owned x2 (det_raw_list l2) **
           (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
        fn _ {
          unfold (cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)));
          rewrite (AB.cbor_array_owned r (det_raw_list (L.append (Ghost.reveal l1) (Ghost.reveal l2))))
            as (AB.cbor_array_owned r (L.append (det_raw_list l1) (det_raw_list l2)));
          Trade.elim
            (AB.cbor_array_owned r (L.append (det_raw_list l1) (det_raw_list l2)))
            (AB.cbor_array_owned x1 (det_raw_list l1) **
             AB.cbor_array_owned x2 (det_raw_list l2) **
             (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va));
          fold (cbor_det_array_owned x1 l1);
          fold (cbor_det_array_owned x2 l2);
        };
      Some #cbor_mixed_list_array r
    }
  }
}

#pop-options

(* ================================================================ *)
(* Bridge lemma: the deterministic raw encoding of an array          *)
(*                                                                  *)
(* These re-derive the two (private) helpers of                      *)
(* [CBOR.Spec.API.Format.cbor_det_serialize_array_length_gt_list]    *)
(* and repackage its proof to expose the structural EQUALITY         *)
(*   mk_det_raw_cbor (pack (CArray lw))                              *)
(*     == Array (mk_raw_uint64 (uint_to_t (length lw))) (det_raw_list lw) *)
(* (the public Format lemma only exposes a serialized-length bound). *)
(* ================================================================ *)

let rec list_map_mk_det_raw_cbor_correct (l: list Spec.cbor)
: Lemma
  (ensures (
    let l' = L.map SpecRaw.mk_det_raw_cbor l in
    L.for_all SpecRaw.raw_data_item_ints_optimal l' /\
    L.for_all (SpecRaw.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) l'
  ))
= match l with
  | [] -> ()
  | _ :: q -> list_map_mk_det_raw_cbor_correct q

let rec list_map_mk_cbor_mk_det_raw_cbor (l: list Spec.cbor)
: Lemma
  (ensures (L.map SpecRaw.mk_cbor (L.map SpecRaw.mk_det_raw_cbor l) == l))
= match l with
  | [] -> ()
  | _ :: q -> list_map_mk_cbor_mk_det_raw_cbor q

let mk_det_raw_cbor_array_eq
  (lw: (l: list Spec.cbor { FStar.UInt.fits (L.length l) U64.n }))
: Lemma
  (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CArray lw)) ==
   Array (RV.mk_raw_uint64 (U64.uint_to_t (L.length lw))) (det_raw_list lw))
= let len = RV.mk_raw_uint64 (U64.uint_to_t (L.length lw)) in
  assert (RV.raw_uint64_optimal len);
  let l' = L.map SpecRaw.mk_det_raw_cbor lw in
  let x = Array len l' in
  list_map_mk_cbor_mk_det_raw_cbor lw;
  list_map_mk_det_raw_cbor_correct lw;
  assert_norm (SpecRaw.raw_data_item_ints_optimal ==
    SpecRaw.holds_on_raw_data_item SpecRaw.raw_data_item_ints_optimal_elem);
  SpecRaw.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order x;
  SpecRaw.mk_cbor_eq x;
  SpecRaw.mk_det_raw_cbor_mk_cbor x;
  assert (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CArray lw)) == x)

(* ================================================================ *)
(* Finalize: owned array handle -> deterministic CBOR object         *)
(* ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_det_array_finalize
  (x: cbor_mixed_list_array)
  (#l: Ghost.erased (list Spec.cbor))
requires
  cbor_det_array_owned x l
returns y: cbor_raw
ensures
  exists* (l': (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n })).
    Det.cbor_det_match 1.0R y (Spec.pack (Spec.CArray l')) **
    Trade.trade
      (Det.cbor_det_match 1.0R y (Spec.pack (Spec.CArray l')))
      (cbor_det_array_owned x l) **
    pure ((l' <: list Spec.cbor) == Ghost.reveal l)
{
  unfold (cbor_det_array_owned x l);
  AB.cbor_array_owned_length_fits x;
  length_det_raw_list l;
  let lw : Ghost.erased (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n }) =
    Ghost.hide (Ghost.reveal l);
  let y = AB.cbor_array_finalize x;
  unfold (AB.cbor_array_finalized x y (det_raw_list l));
  with len. assert (cbor_match 1.0R y (Array len (det_raw_list l)));
  mk_det_raw_cbor_array_eq (Ghost.reveal lw);
  rewrite (cbor_match 1.0R y (Array len (det_raw_list l)))
    as (cbor_match 1.0R y (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CArray (Ghost.reveal lw)))));
  fold (Det.cbor_det_match 1.0R y (Spec.pack (Spec.CArray (Ghost.reveal lw))));
  Trade.intro_trade
    (Det.cbor_det_match 1.0R y (Spec.pack (Spec.CArray (Ghost.reveal lw))))
    (cbor_det_array_owned x l)
    (Trade.trade
      (cbor_match 1.0R y (Array len (det_raw_list l)))
      (AB.cbor_array_owned x (det_raw_list l)))
    fn _ {
      unfold (Det.cbor_det_match 1.0R y (Spec.pack (Spec.CArray (Ghost.reveal lw))));
      rewrite (cbor_match 1.0R y (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CArray (Ghost.reveal lw)))))
        as (cbor_match 1.0R y (Array len (det_raw_list l)));
      Trade.elim
        (cbor_match 1.0R y (Array len (det_raw_list l)))
        (AB.cbor_array_owned x (det_raw_list l));
      fold (cbor_det_array_owned x l);
    };
  y
}

#pop-options

(* ================================================================ *)
(* Init: view an existing deterministic-CBOR ARRAY object as an      *)
(* owned array handle (the reverse of [cbor_det_array_finalize]).     *)
(*                                                                  *)
(* Wraps the raw [AB.cbor_array_init].  Since [Spec.CArray?          *)
(* (Spec.unpack l)], the deterministic raw encoding                  *)
(* [mk_det_raw_cbor l] is an [Array] node whose element list is      *)
(* [det_raw_list l'] (with [l' = Spec.CArray?.v (Spec.unpack l)]);   *)
(* this is exactly the [mk_det_raw_cbor_array_eq] bridge used (in the *)
(* forward direction) by [cbor_det_array_finalize].                  *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_det_array_init
  (x: cbor_raw) (r1 r2: R.ref (IT.mixed_list U64.t cbor_raw))
  (#p: perm) (#l: Ghost.erased Spec.cbor) (#w1 #w2: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  Det.cbor_det_match p x l ** R.pts_to r1 w1 ** R.pts_to r2 w2 **
  pure (Spec.CArray? (Spec.unpack l))
returns y: cbor_mixed_list_array
ensures
  exists* (l': list Spec.cbor).
    cbor_det_array_owned y l' **
    Trade.trade
      (cbor_det_array_owned y l')
      (Det.cbor_det_match p x l ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)) **
    pure (Spec.CArray? (Spec.unpack l) /\ l' == Spec.CArray?.v (Spec.unpack l))
{
  unfold (Det.cbor_det_match p x l);
  let lw : Ghost.erased (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n }) =
    Ghost.hide (Spec.CArray?.v (Spec.unpack (Ghost.reveal l)));
  mk_det_raw_cbor_array_eq (Ghost.reveal lw);
  (* [mk_det_raw_cbor l] is an [Array] whose contents are [det_raw_list lw]. *)
  let xh : Ghost.erased (r: raw_data_item { Array? r }) =
    Ghost.hide (SpecRaw.mk_det_raw_cbor (Ghost.reveal l));
  rewrite (cbor_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal l)))
    as (cbor_match p x (Ghost.reveal xh));
  let y = AB.cbor_array_init p x r1 r2 #xh #w1 #w2;
  rewrite (AB.cbor_array_owned y (Array?.v (Ghost.reveal xh)))
    as (AB.cbor_array_owned y (det_raw_list (Ghost.reveal lw)));
  fold (cbor_det_array_owned y (Ghost.reveal lw));
  Trade.intro_trade
    (cbor_det_array_owned y (Ghost.reveal lw))
    (Det.cbor_det_match p x l ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2))
    (Trade.trade
      (AB.cbor_array_owned y (Array?.v (Ghost.reveal xh)))
      (cbor_match p x (Ghost.reveal xh) **
       (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)))
    fn _ {
      unfold (cbor_det_array_owned y (Ghost.reveal lw));
      rewrite (AB.cbor_array_owned y (det_raw_list (Ghost.reveal lw)))
        as (AB.cbor_array_owned y (Array?.v (Ghost.reveal xh)));
      Trade.elim
        (AB.cbor_array_owned y (Array?.v (Ghost.reveal xh)))
        (cbor_match p x (Ghost.reveal xh) **
         (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2));
      rewrite (cbor_match p x (Ghost.reveal xh))
        as (cbor_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal l)));
      fold (Det.cbor_det_match p x l);
    };
  y
}

#pop-options

(* ================================================================ *)
(* Slice: zero-copy sub-range [i,j) of a deterministic-CBOR ARRAY.   *)
(* Wraps the raw [AB.cbor_array_slice], bridging the raw slice-spec  *)
(* [AB.array_slice_spec] to the deterministic-CBOR level via         *)
(* [cbor_det_array_slice_spec] (the two commute).                    *)
(* ================================================================ *)

(* map commutes with the (fst of) splitAt *)
let rec list_map_fst_splitAt (#t1 #t2: Type) (f: t1 -> t2) (l: list t1) (n: nat)
: Lemma (ensures (L.map f (fst (L.splitAt n l)) == fst (L.splitAt n (L.map f l))))
        (decreases n)
= if n = 0 then () else (match l with | [] -> () | _ :: q -> list_map_fst_splitAt f q (n - 1))

(* map commutes with the (snd of) splitAt *)
let rec list_map_snd_splitAt (#t1 #t2: Type) (f: t1 -> t2) (l: list t1) (n: nat)
: Lemma (ensures (L.map f (snd (L.splitAt n l)) == snd (L.splitAt n (L.map f l))))
        (decreases n)
= if n = 0 then () else (match l with | [] -> () | _ :: q -> list_map_snd_splitAt f q (n - 1))

(* map commutes with the splitAt-based sub-range extraction *)
let list_map_narrow (#t1 #t2: Type) (f: t1 -> t2) (l: list t1) (skip n: nat)
: Lemma (ensures (L.map f (fst (L.splitAt n (snd (L.splitAt skip l)))) ==
                  fst (L.splitAt n (snd (L.splitAt skip (L.map f l))))))
= list_map_fst_splitAt f (snd (L.splitAt skip l)) n;
  list_map_snd_splitAt f l skip

(* for non-negative arguments, [list_narrow] is the splitAt-based range *)
let list_narrow_nonneg (#a: Type) (l: list a) (skip n: nat)
: Lemma (I.list_narrow l skip n == fst (L.splitAt n (snd (L.splitAt skip l))))
= ()

(* [cbor_det_array_slice_spec] is defined transparently in the interface. *)

#push-options "--fuel 2 --ifuel 2"
(* Slicing the raw list [det_raw_list l] equals [det_raw_list] of the   *)
(* deterministic-CBOR slice: the raw slice-spec commutes with           *)
(* [det_raw_list = map mk_det_raw_cbor].                                *)
let cbor_det_array_slice_spec_commutes (l: list Spec.cbor) (i j: U64.t)
: Lemma (ensures
    AB.array_slice_spec (det_raw_list l) i j == det_raw_list (cbor_det_array_slice_spec l i j))
= length_det_raw_list l;
  if (U64.v i < U64.v j && U64.v j <= L.length l)
  then begin
    list_narrow_nonneg (det_raw_list l) (U64.v i) (U64.v j - U64.v i);
    list_map_narrow SpecRaw.mk_det_raw_cbor l (U64.v i) (U64.v j - U64.v i)
  end
  else ()
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_det_array_slice_bridge
  (x: cbor_raw) (i j: U64.t)
  (r1 r2 r3 r4: R.ref (IT.mixed_list U64.t cbor_raw))
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#w1 #w2 #w3 #w4: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  Det.cbor_det_match p x v **
  R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
  pure (Spec.CArray? (Spec.unpack v))
returns res: cbor_raw
ensures exists* (v': Spec.cbor).
  Det.cbor_det_match 1.0R res v' **
  Trade.trade
    (Det.cbor_det_match 1.0R res v')
    (Det.cbor_det_match p x v **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
  pure (Spec.CArray? (Spec.unpack v) /\ Spec.CArray? (Spec.unpack v') /\
        (Spec.CArray?.v (Spec.unpack v') <: list Spec.cbor) ==
          cbor_det_array_slice_spec (Spec.CArray?.v (Spec.unpack v)) i j)
{
  unfold (Det.cbor_det_match p x v);
  let lw : Ghost.erased (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n }) =
    Ghost.hide (Spec.CArray?.v (Spec.unpack (Ghost.reveal v)));
  mk_det_raw_cbor_array_eq (Ghost.reveal lw);
  let xh : Ghost.erased (r: raw_data_item { Array? r }) =
    Ghost.hide (SpecRaw.mk_det_raw_cbor (Ghost.reveal v));
  rewrite (cbor_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal v)))
    as (cbor_match p x (Ghost.reveal xh));
  let res = AB.cbor_array_slice p x i j r1 r2 r3 r4 #xh #w1 #w2 #w3 #w4;
  with yh. assert (cbor_match 1.0R res yh);
  cbor_det_array_slice_spec_commutes (Ghost.reveal lw) i j;
  length_det_raw_list (cbor_det_array_slice_spec (Ghost.reveal lw) i j);
  let ls : Ghost.erased (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n }) =
    Ghost.hide (cbor_det_array_slice_spec (Ghost.reveal lw) i j);
  mk_det_raw_cbor_array_eq (Ghost.reveal ls);
  RV.raw_uint64_optimal_unique (Array?.len yh)
    (RV.mk_raw_uint64 (U64.uint_to_t (L.length (Ghost.reveal ls))));
  rewrite (cbor_match 1.0R res yh)
    as (cbor_match 1.0R res (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CArray (Ghost.reveal ls)))));
  fold (Det.cbor_det_match 1.0R res (Spec.pack (Spec.CArray (Ghost.reveal ls))));
  Trade.intro_trade
    (Det.cbor_det_match 1.0R res (Spec.pack (Spec.CArray (Ghost.reveal ls))))
    (Det.cbor_det_match p x v **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
    (Trade.trade
       (cbor_match 1.0R res yh)
       (cbor_match p x (Ghost.reveal xh) **
        (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)))
    fn _ {
      unfold (Det.cbor_det_match 1.0R res (Spec.pack (Spec.CArray (Ghost.reveal ls))));
      rewrite (cbor_match 1.0R res (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CArray (Ghost.reveal ls)))))
        as (cbor_match 1.0R res yh);
      Trade.elim
        (cbor_match 1.0R res yh)
        (cbor_match p x (Ghost.reveal xh) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4));
      rewrite (cbor_match p x (Ghost.reveal xh))
        as (cbor_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal v)));
      fold (Det.cbor_det_match p x v);
    };
  res
}

#pop-options
