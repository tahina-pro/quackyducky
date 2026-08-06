module CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder
#lang-pulse
friend CBOR.Pulse.Raw.Nondet
friend CBOR.Pulse.Raw.EverParse.ArrayBuilder
friend CBOR.Pulse.Raw.Format.MixedList
friend CBOR.Pulse.Raw.Format.Match
(* Needed so that the abstract [cbor_nondet_array_append_cell_t] declared in the
   raw/-relocated .fsti unfolds (via Nondet.Type -> ML.cbor_raw_mixed_list, then
   the existing [friend MixedList] -> IT.mixed_list) to the concrete
   [IT.mixed_list U64.t cbor_raw] used in the ref types below.  Ref types unchanged. *)
friend CBOR.Pulse.API.Nondet.Type

open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Type
open CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Optimal

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module SpecRawBase = CBOR.Spec.Raw.Base
module Valid = CBOR.Spec.Raw.Valid
module Optimal = CBOR.Spec.Raw.Optimal
module Nondet = CBOR.Pulse.Raw.Nondet
module AB = CBOR.Pulse.Raw.EverParse.ArrayBuilder
module MP = CBOR.Pulse.Raw.Match.Perm
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module Append = LowParse.PulseParse.Iterator.Append
module IO = LowParse.PulseParse.Iterator.IntOps
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module L = FStar.List.Tot

let u64_ops_v_eq (x: U64.t) : Lemma (IO.u64_ops.v x == U64.v x) [SMTPat (IO.u64_ops.v x)] = ()
let u64_ops_fits_eq (n: nat) : Lemma (IO.u64_ops.fits n == (n < pow2 64 <: prop)) [SMTPat (IO.u64_ops.fits n)] = ()

(* ================================================================ *)
(* Ownership predicate                                              *)
(* ================================================================ *)

let cbor_nondet_array_owned (x: cbor_mixed_list_array) (l: list Spec.cbor) : slprop =
  exists* (lraw: list SpecRawBase.raw_data_item).
    AB.cbor_array_owned x lraw **
    pure (L.for_all SpecRaw.valid_raw_data_item lraw /\
          l == L.map SpecRaw.mk_cbor lraw)

(* ================================================================ *)
(* Manual array constructor exposing the mixed_list pointer          *)
(*                                                                  *)
(* Same as [AB.cbor_array_of_ml] but additionally exposes the pure   *)
(* fact [res.cbor_array_gen_ptr == ml], which the O(1) builders need *)
(* in their back-trade closures to recover the (existentially        *)
(* quantified) raw contents from an owned handle by unfolding the    *)
(* KNOWN structural node they built.                                 *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
inline_for_extraction
fn mk_array_owned_with_ptr
  (ml: IT.mixed_list U64.t cbor_raw)
  (#l: Ghost.erased (list SpecRawBase.raw_data_item))
requires
  I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l)
returns res: cbor_mixed_list_array
ensures
  AB.cbor_array_owned res (Ghost.reveal l) **
  pure ((res.cbor_array_gen_ptr <: IT.mixed_list U64.t cbor_raw) == ml)
{
  let mll = IT.mixed_list_length IO.u64_ops ml;
  AB.minimal_len_size_prop mll;
  let res : cbor_mixed_list_array = {
    cbor_array_gen_length_size = AB.minimal_len_size mll;
    cbor_array_gen_ptr = ml;
    cbor_array_gen_perm = 1.0R;
  };
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l))
    as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R res.cbor_array_gen_ptr (Ghost.reveal l));
  fold (AB.cbor_array_owned res (Ghost.reveal l));
  res
}
#pop-options

(* ================================================================ *)
(* Empty array                                                      *)
(* ================================================================ *)

inline_for_extraction
fn cbor_nondet_array_empty (_: unit)
requires emp
returns res: cbor_mixed_list_array
ensures cbor_nondet_array_owned res []
{
  let res = AB.cbor_array_empty ();
  rewrite (AB.cbor_array_owned res [])
    as (AB.cbor_array_owned res ([] <: list SpecRawBase.raw_data_item));
  fold (cbor_nondet_array_owned res ([] <: list Spec.cbor));
  res
}

(* ================================================================ *)
(* Length of an owned array fits in a u64                           *)
(* ================================================================ *)

ghost
fn cbor_nondet_array_owned_length_fits
  (x: cbor_mixed_list_array) (#l: Ghost.erased (list Spec.cbor))
requires cbor_nondet_array_owned x l
ensures cbor_nondet_array_owned x l ** pure (FStar.UInt.fits (L.length (Ghost.reveal l)) 64)
{
  unfold (cbor_nondet_array_owned x l);
  with lraw. assert (AB.cbor_array_owned x lraw);
  AB.cbor_array_owned_length_fits x;
  L.map_lemma SpecRaw.mk_cbor lraw;
  fold (cbor_nondet_array_owned x l);
}

(* ================================================================ *)
(* Singleton array                                                  *)
(* ================================================================ *)

fn cbor_nondet_array_singleton
  (x: cbor_raw) (ry: R.ref cbor_raw)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_raw)
requires
  Nondet.cbor_nondet_match pm x v ** R.pts_to ry w0
returns res: cbor_mixed_list_array
ensures
  cbor_nondet_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_nondet_array_owned res [Ghost.reveal v])
    (Nondet.cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w))
{
  (* Eliminate the nondet match to a raw match [cbor_match pm x v'] with
     [v'] valid and [mk_cbor v' == v]. *)
  unfold (Nondet.cbor_nondet_match pm x v);
  with v'. assert (cbor_match pm x v');
  (* Build the singleton mixed_list manually, keeping half of ry's pts_to. *)
  R.write ry x;
  R.share ry;
  let sp_val : Ghost.erased perm = 1.0R /. 2.0R;
  let sv_val : Ghost.erased perm = pm;
  let ml : IT.mixed_list U64.t cbor_raw = IT.Base #U64.t #cbor_raw (IT.Singleton #U64.t #cbor_raw (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry);
  rewrite (R.pts_to ry #(1.0R /. 2.0R) x)
    as (R.pts_to ry #(1.0R *. Ghost.reveal sp_val) x);
  rewrite (cbor_match pm x (Ghost.reveal v'))
    as (cbor_match (1.0R *. Ghost.reveal sv_val) x (Ghost.reveal v'));
  fold (I.base_mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 1 1.0R
    (IT.Singleton #U64.t #cbor_raw (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal v']);
  fold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 1 1.0R
    (IT.Base #U64.t #cbor_raw (IT.Singleton #U64.t #cbor_raw (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal v']);
  rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 1 1.0R
    (IT.Base #U64.t #cbor_raw (IT.Singleton #U64.t #cbor_raw (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal v'])
    as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml)) 1.0R ml [Ghost.reveal v']);
  fold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml [Ghost.reveal v']);
  (* Build the owned handle with KNOWN pointer. *)
  let res = mk_array_owned_with_ptr ml #[Ghost.reveal v'];
  fold (cbor_nondet_array_owned res [Ghost.reveal v]);
  Trade.intro_trade
    (cbor_nondet_array_owned res [Ghost.reveal v])
    (Nondet.cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w))
    (R.pts_to ry #(1.0R /. 2.0R) x **
     pure ((res.cbor_array_gen_ptr <: IT.mixed_list U64.t cbor_raw) == ml /\
           U64.v (IT.mixed_list_length IO.u64_ops ml) == 1))
    fn _ {
      unfold (cbor_nondet_array_owned res [Ghost.reveal v]);
      with lraw. assert (AB.cbor_array_owned res lraw);
      unfold (AB.cbor_array_owned res lraw);
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R res.cbor_array_gen_ptr lraw)
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml lraw);
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml lraw)
        as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 1 1.0R
              (IT.Base #U64.t #cbor_raw (IT.Singleton #U64.t #cbor_raw (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) lraw);
      unfold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 1 1.0R
              (IT.Base #U64.t #cbor_raw (IT.Singleton #U64.t #cbor_raw (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) lraw);
      unfold (I.base_mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 1 1.0R
              (IT.Singleton #U64.t #cbor_raw (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) lraw);
      with xc yc. assert (
        R.pts_to ry #(1.0R *. Ghost.reveal sp_val) xc **
        cbor_match (1.0R *. Ghost.reveal sv_val) xc yc);
      rewrite (R.pts_to ry #(1.0R *. Ghost.reveal sp_val) xc)
        as (R.pts_to ry #(1.0R /. 2.0R) xc);
      R.gather ry;
      rewrite (cbor_match (1.0R *. Ghost.reveal sv_val) xc yc)
        as (cbor_match pm x yc);
      rewrite (R.pts_to ry #(1.0R /. 2.0R +. 1.0R /. 2.0R) x)
        as (R.pts_to ry x);
      fold (Nondet.cbor_nondet_match pm x v);
      fold (exists* w. R.pts_to ry w);
    };
  res
}

(* ================================================================ *)
(* Append                                                           *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
fn cbor_nondet_array_append
  (x1 x2: cbor_mixed_list_array)
  (r_before r_after: R.ref (IT.mixed_list U64.t cbor_raw))
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
  R.pts_to r_before vb0 ** R.pts_to r_after va0
returns res: option cbor_mixed_list_array
ensures
  (match res with
   | None ->
     cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
     pure (~ (FStar.UInt.fits (L.length (Ghost.reveal l1) + L.length (Ghost.reveal l2)) 64))
   | Some r ->
     cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
     Trade.trade
       (cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
       (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
{
  unfold (cbor_nondet_array_owned x1 l1);
  with lraw1. assert (AB.cbor_array_owned x1 lraw1);
  unfold (cbor_nondet_array_owned x2 l2);
  with lraw2. assert (AB.cbor_array_owned x2 lraw2);

  (* Capture the structural pure facts about x1, x2 (perm and length_size).
     They persist in the SMT context and feed the back-trade. *)
  unfold (AB.cbor_array_owned x1 lraw1);
  fold (AB.cbor_array_owned x1 lraw1);
  unfold (AB.cbor_array_owned x2 lraw2);
  fold (AB.cbor_array_owned x2 lraw2);

  (* Eliminate ownership to the underlying mixed lists. *)
  let ml_a = AB.cbor_array_owned_elim x1 #lraw1;
  let ml_b = AB.cbor_array_owned_elim x2 #lraw2;
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal lraw1);
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal lraw2);
  let len_a = IT.mixed_list_length IO.u64_ops ml_a;
  let len_b = IT.mixed_list_length IO.u64_ops ml_b;
  let limit = U64.sub 0xffffffffffffffffuL len_b;
  if (U64.gt len_a limit) {
    (* Overflow: restore both ownership predicates and report failure. *)
    Trade.elim
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal lraw1))
      (AB.cbor_array_owned x1 lraw1);
    Trade.elim
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal lraw2))
      (AB.cbor_array_owned x2 lraw2);
    fold (cbor_nondet_array_owned x1 l1);
    fold (cbor_nondet_array_owned x2 l2);
    AB.array_append_overflow len_a len_b (U64.v len_a) (U64.v len_b);
    L.map_lemma SpecRaw.mk_cbor lraw1;
    L.map_lemma SpecRaw.mk_cbor lraw2;
    None #cbor_mixed_list_array
  } else {
    assert_norm (pow2 64 == 0xffffffffffffffff + 1);
    let tot : (t: U64.t { U64.v t == U64.v len_a + U64.v len_b }) = U64.add len_a len_b;

    (* ---- Build the Append node manually, keeping ref halves outside. ---- *)
    let depth : Ghost.erased nat =
      (if I.mixed_list_depth ml_a > I.mixed_list_depth ml_b
       then I.mixed_list_depth ml_a else I.mixed_list_depth ml_b) + 1;
    let bp : Ghost.erased perm = (1.0R /. 2.0R) /. 1.0R;
    R.write r_before ml_a;
    R.share r_before;
    R.write r_after ml_b;
    R.share r_after;
    let ml_res : IT.mixed_list U64.t cbor_raw =
      IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a len_b tot 0uL (Ghost.reveal bp) r_before 0uL (Ghost.reveal bp) r_after 1.0R;
    let lres : Ghost.erased (list SpecRawBase.raw_data_item) = L.append (Ghost.reveal lraw1) (Ghost.reveal lraw2);
    Append.perm_mul_div_cancel' 1.0R (1.0R /. 2.0R);
    rewrite (R.pts_to r_before #(1.0R /. 2.0R) ml_a)
      as (R.pts_to r_before #(1.0R *. Ghost.reveal bp) ml_a);
    rewrite (R.pts_to r_after #(1.0R /. 2.0R) ml_b)
      as (R.pts_to r_after #(1.0R *. Ghost.reveal bp) ml_b);
    rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal lraw1))
      as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_before 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) 1.0R ml_a (Ghost.reveal lraw1));
    rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal lraw2))
      as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_after 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) 1.0R ml_b (Ghost.reveal lraw2));
    List.Tot.Properties.append_length (Ghost.reveal lraw1) (Ghost.reveal lraw2);
    intro_pure (
      0 + U64.v (IT.mixed_list_length IO.u64_ops ml_res) <= U64.v len_a + U64.v len_b /\
      U64.v 0uL + U64.v len_a <= U64.v (IT.mixed_list_length IO.u64_ops ml_a) /\
      U64.v 0uL + U64.v len_b <= U64.v (IT.mixed_list_length IO.u64_ops ml_b) /\
      List.Tot.length (Ghost.reveal lraw1) == I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a) /\
      List.Tot.length (Ghost.reveal lraw2) == I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a) /\
      Ghost.reveal lres == L.append (Ghost.reveal lraw1) (Ghost.reveal lraw2) /\
      I.mixed_list_depth ml_a < Ghost.reveal depth /\
      I.mixed_list_depth ml_b < Ghost.reveal depth
    ) ();
    fold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R
      (IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a len_b tot 0uL (Ghost.reveal bp) r_before 0uL (Ghost.reveal bp) r_after 1.0R)
      (Ghost.reveal lres));
    rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R
      (IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a len_b tot 0uL (Ghost.reveal bp) r_before 0uL (Ghost.reveal bp) r_after 1.0R)
      (Ghost.reveal lres))
      as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R ml_res (Ghost.reveal lres));
    fold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res (Ghost.reveal lres));
    (* The elim trades for x1/x2 are no longer usable; drop them. *)
    drop_ (Trade.trade
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal lraw1))
      (AB.cbor_array_owned x1 lraw1));
    drop_ (Trade.trade
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal lraw2))
      (AB.cbor_array_owned x2 lraw2));

    (* ---- Build owned for res from the node. ---- *)
    let res = mk_array_owned_with_ptr ml_res #lres;

    (* nondet ownership of res, over l1 ++ l2 *)
    L.map_append SpecRaw.mk_cbor (Ghost.reveal lraw1) (Ghost.reveal lraw2);
    L.for_all_append SpecRaw.valid_raw_data_item (Ghost.reveal lraw1) (Ghost.reveal lraw2);
    fold (cbor_nondet_array_owned res (L.append (Ghost.reveal l1) (Ghost.reveal l2)));

    (* ---- Back-trade. ---- *)
    Trade.intro_trade
      (cbor_nondet_array_owned res (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
      (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
       (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va))
      (R.pts_to r_before #(1.0R /. 2.0R) ml_a **
       R.pts_to r_after #(1.0R /. 2.0R) ml_b **
       pure (
         (res.cbor_array_gen_ptr <: IT.mixed_list U64.t cbor_raw) == ml_res /\
         (Ghost.reveal ml_res ==
            IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a len_b tot 0uL (Ghost.reveal bp) r_before 0uL (Ghost.reveal bp) r_after 1.0R) /\
         U64.v (IT.mixed_list_length IO.u64_ops ml_res) == U64.v len_a + U64.v len_b /\
         U64.v (IT.mixed_list_length IO.u64_ops ml_a) == U64.v len_a /\
         U64.v (IT.mixed_list_length IO.u64_ops ml_b) == U64.v len_b /\
         I.append_off_before 0 (U64.v 0uL) (U64.v len_a) == 0 /\
         I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a) == U64.v len_a /\
         I.append_off_after 0 (U64.v 0uL) (U64.v len_a) == 0 /\
         I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a) == U64.v len_b /\
         1.0R *. Ghost.reveal bp == 1.0R /. 2.0R /\
         (x1.cbor_array_gen_ptr <: IT.mixed_list U64.t cbor_raw) == ml_a /\
         x1.cbor_array_gen_perm == 1.0R /\
         x1.cbor_array_gen_length_size == (mk_raw_uint64 (IT.mixed_list_length IO.u64_ops x1.cbor_array_gen_ptr)).size /\
         (x2.cbor_array_gen_ptr <: IT.mixed_list U64.t cbor_raw) == ml_b /\
         x2.cbor_array_gen_perm == 1.0R /\
         x2.cbor_array_gen_length_size == (mk_raw_uint64 (IT.mixed_list_length IO.u64_ops x2.cbor_array_gen_ptr)).size /\
         U64.v len_a == L.length (Ghost.reveal lraw1) /\
         U64.v len_b == L.length (Ghost.reveal lraw2) /\
         Ghost.reveal l1 == L.map SpecRaw.mk_cbor (Ghost.reveal lraw1) /\
         Ghost.reveal l2 == L.map SpecRaw.mk_cbor (Ghost.reveal lraw2)
       ))
      fn _ {
        unfold (cbor_nondet_array_owned res (L.append (Ghost.reveal l1) (Ghost.reveal l2)));
        with lr. assert (AB.cbor_array_owned res lr);
        unfold (AB.cbor_array_owned res lr);
        rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R res.cbor_array_gen_ptr lr)
          as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res lr);
        unfold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res lr);
        rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R ml_res lr)
          as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R
                (IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a len_b tot 0uL (Ghost.reveal bp) r_before 0uL (Ghost.reveal bp) r_after 1.0R)
                lr);
        unfold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R
                (IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a len_b tot 0uL (Ghost.reveal bp) r_before 0uL (Ghost.reveal bp) r_after 1.0R)
                lr);
        with ib_u ia_u l1_u l2_u. assert (
          R.pts_to r_before #(1.0R *. Ghost.reveal bp) ib_u **
          I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_before 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) 1.0R ib_u l1_u **
          R.pts_to r_after #(1.0R *. Ghost.reveal bp) ia_u **
          I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_after 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) 1.0R ia_u l2_u
        );
        rewrite (R.pts_to r_before #(1.0R *. Ghost.reveal bp) ib_u)
          as (R.pts_to r_before #(1.0R /. 2.0R) ib_u);
        R.gather r_before;
        rewrite (R.pts_to r_before #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml_a)
          as (R.pts_to r_before ml_a);
        rewrite (R.pts_to r_after #(1.0R *. Ghost.reveal bp) ia_u)
          as (R.pts_to r_after #(1.0R /. 2.0R) ia_u);
        R.gather r_after;
        rewrite (R.pts_to r_after #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml_b)
          as (R.pts_to r_after ml_b);
        I.mixed_list_match_n_length cbor_match IO.u64_ops parse_raw_data_item (I.append_off_before 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) 1.0R ib_u l1_u;
        I.mixed_list_match_n_length cbor_match IO.u64_ops parse_raw_data_item (I.append_off_after 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) 1.0R ia_u l2_u;
        rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_before 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) 1.0R ib_u l1_u)
          as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a l1_u);
        rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_after 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) 1.0R ia_u l2_u)
          as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b l2_u);
        (* relate split lists to the spec lists *)
        L.map_append SpecRaw.mk_cbor l1_u l2_u;
        List.Tot.Properties.append_injective
          (L.map SpecRaw.mk_cbor l1_u) (Ghost.reveal l1)
          (L.map SpecRaw.mk_cbor l2_u) (Ghost.reveal l2);
        L.for_all_append SpecRaw.valid_raw_data_item l1_u l2_u;
        L.map_lemma SpecRaw.mk_cbor l1_u;
        L.map_lemma SpecRaw.mk_cbor l2_u;
        (* rebuild ownership for x1, x2 from the recovered sub-lists *)
        rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a l1_u)
          as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x1.cbor_array_gen_ptr l1_u);
        fold (AB.cbor_array_owned x1 l1_u);
        rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b l2_u)
          as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x2.cbor_array_gen_ptr l2_u);
        fold (AB.cbor_array_owned x2 l2_u);
        fold (cbor_nondet_array_owned x1 l1);
        fold (cbor_nondet_array_owned x2 l2);
        fold (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va);
      };
    Some #cbor_mixed_list_array res
  }
}
#pop-options

(* ================================================================ *)
(* Finalize                                                         *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
fn cbor_nondet_array_finalize
  (x: cbor_mixed_list_array)
  (#l: Ghost.erased (list Spec.cbor))
requires
  cbor_nondet_array_owned x l
returns y: cbor_raw
ensures
  exists* (l': (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n })).
    Nondet.cbor_nondet_match 1.0R y (Spec.pack (Spec.CArray l')) **
    Trade.trade
      (Nondet.cbor_nondet_match 1.0R y (Spec.pack (Spec.CArray l')))
      (cbor_nondet_array_owned x l) **
    pure ((l' <: list Spec.cbor) == Ghost.reveal l)
{
  unfold (cbor_nondet_array_owned x l);
  with lraw. assert (AB.cbor_array_owned x lraw);
  AB.cbor_array_owned_length_fits x;
  L.map_lemma SpecRaw.mk_cbor lraw;
  let lw : Ghost.erased (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n }) =
    Ghost.hide (Ghost.reveal l);
  (* Trade folding the raw owned array back into the nondet owned array. *)
  Trade.intro_trade
    (AB.cbor_array_owned x lraw)
    (cbor_nondet_array_owned x l)
    (pure (L.for_all SpecRaw.valid_raw_data_item lraw /\
           Ghost.reveal l == L.map SpecRaw.mk_cbor lraw))
    fn _ {
      fold (cbor_nondet_array_owned x l);
    };
  (* Finalize the raw builder to obtain the full [cbor_match] view. *)
  let y0 = AB.cbor_array_finalize x;
  unfold (AB.cbor_array_finalized x y0 lraw);
  with len. assert (cbor_match 1.0R y0 (Array len lraw));
  Trade.trans
    (cbor_match 1.0R y0 (Array len lraw))
    (AB.cbor_array_owned x lraw)
    (cbor_nondet_array_owned x l);
  (* Spec: the raw array item is valid, and its abstraction is [pack (CArray l)]. *)
  Valid.valid_eq Valid.basic_data_model (Array len lraw);
  SpecRaw.mk_cbor_eq (Array len lraw);
  Spec.pack_unpack (SpecRaw.mk_cbor (Array len lraw));
  (* Introduce the nondet match (at half permission, with a gather-based trade). *)
  Nondet.cbor_nondet_match_intro y0 #1.0R #(Array len lraw);
  Trade.trans
    (Nondet.cbor_nondet_match (1.0R /. 2.0R) y0 (SpecRaw.mk_cbor (Array len lraw)))
    (cbor_match 1.0R y0 (Array len lraw))
    (cbor_nondet_array_owned x l);
  rewrite each (SpecRaw.mk_cbor (Array len lraw)) as (Spec.pack (Spec.CArray (Ghost.reveal lw)));
  (* Reset the permission to 1.0R (fresh handle) to satisfy the postcondition. *)
  let y = Nondet.cbor_nondet_reset_perm () y0 1.0R;
  Trade.trans
    (Nondet.cbor_nondet_match 1.0R y (Spec.pack (Spec.CArray (Ghost.reveal lw))))
    (Nondet.cbor_nondet_match (1.0R /. 2.0R) y0 (Spec.pack (Spec.CArray (Ghost.reveal lw))))
    (cbor_nondet_array_owned x l);
  y
}
#pop-options

(* ================================================================ *)
(* Native-permission, ref-free borrow of an array's entries.        *)
(*                                                                  *)
(* Like [AB.cbor_array_borrow_entries] but TOTAL (no                *)
(* [cbor_array_borrow_pre] restriction) and WITHOUT allocating a    *)
(* full-ownership handle: the entries are presented at their NATIVE  *)
(* ambient permission [q] (existentially quantified) at a stable     *)
(* pointer, together with a trade back to [cbor_match].  No scratch   *)
(* references are consumed, leaving the caller free to use its own   *)
(* refs to re-wrap a SHARE of the entries under a fresh handle.      *)
(* ================================================================ *)

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"
inline_for_extraction
fn array_borrow_native
  (pm: perm) (x: cbor_raw)
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
requires
  cbor_match pm x (Ghost.reveal xh)
returns ml: IT.mixed_list U64.t cbor_raw
ensures
  exists* (q: perm).
    I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Array?.v (Ghost.reveal xh)) **
    Trade.trade
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Array?.v (Ghost.reveal xh)))
      (cbor_match pm x (Ghost.reveal xh))
{
  cbor_match_cases x;
  match x {
    norewrite
    CBOR_Case_Array v -> {
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh));
      let ml = AB.cbor_array_borrow_entries_inline pm v #xh;
      Trade.trans
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        (cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh))
        (cbor_match pm x (Ghost.reveal xh));
      ml
    }
    norewrite
    CBOR_Case_Serialized_Array v -> {
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh));
      let ml = AB.cbor_array_borrow_entries_serialized pm v #xh;
      Trade.trans
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh))
        (cbor_match pm x (Ghost.reveal xh));
      ml
    }
    norewrite
    CBOR_Case_Array_Gen v -> {
      cbor_match_eq_array_gen pm v (Ghost.reveal xh);
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match);
      unfold (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match);
      ghost
      fn prf_fwd (c: cbor_raw) (pm0: perm)
        (yv: raw_data_item { List.Tot.memP yv (Array?.v (Ghost.reveal xh)) })
        requires cbor_match_bounded (Ghost.reveal xh) cbor_match pm0 c yv
        ensures cbor_match pm0 c yv
      {
        array_elem_precedes (Ghost.reveal xh) yv;
        cbor_match_bounded_eq (Ghost.reveal xh) cbor_match pm0 c yv;
        rewrite (cbor_match_bounded (Ghost.reveal xh) cbor_match pm0 c yv)
          as (cbor_match pm0 c yv);
      };
      I.mixed_list_match_weaken
        (cbor_match_bounded (Ghost.reveal xh) cbor_match) cbor_match
        IO.u64_ops parse_raw_data_item (pm *. v.cbor_array_gen_perm) v.cbor_array_gen_ptr
        (Array?.v (Ghost.reveal xh)) prf_fwd;
      Trade.intro_trade
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item (pm *. v.cbor_array_gen_perm)
           v.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh)))
        (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match)
        (pure (v.cbor_array_gen_length_size == (Array?.len (Ghost.reveal xh)).size))
        fn _ {
          ghost
          fn prf_bwd (c: cbor_raw) (pm0: perm)
            (yv: raw_data_item { List.Tot.memP yv (Array?.v (Ghost.reveal xh)) })
            requires cbor_match pm0 c yv
            ensures cbor_match_bounded (Ghost.reveal xh) cbor_match pm0 c yv
          {
            array_elem_precedes (Ghost.reveal xh) yv;
            cbor_match_bounded_eq (Ghost.reveal xh) cbor_match pm0 c yv;
            rewrite (cbor_match pm0 c yv)
              as (cbor_match_bounded (Ghost.reveal xh) cbor_match pm0 c yv);
          };
          I.mixed_list_match_weaken
            cbor_match (cbor_match_bounded (Ghost.reveal xh) cbor_match)
            IO.u64_ops parse_raw_data_item (pm *. v.cbor_array_gen_perm) v.cbor_array_gen_ptr
            (Array?.v (Ghost.reveal xh)) prf_bwd;
          fold (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match);
        };
      Trade.trans
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item (pm *. v.cbor_array_gen_perm)
           v.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh)))
        (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match)
        (cbor_match pm x (Ghost.reveal xh));
      v.cbor_array_gen_ptr
    }
  }
}
#pop-options

(* ================================================================ *)
(* Local share / gather instances for the top-level cbor_match.      *)
(* ================================================================ *)

ghost
fn cm_share (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires cbor_match p x1 x2
ensures cbor_match (p /. 2.0R) x1 x2 ** cbor_match (p /. 2.0R) x1 x2
{
  MP.cbor_raw_share p x1 x2;
}

ghost
fn cm_gather (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires cbor_match p x1 x2 ** cbor_match p' x1 x2'
ensures cbor_match (p +. p') x1 x2 ** pure (x2 == x2')
{
  MP.cbor_raw_gather p x1 x2 p' x2';
}

(* ================================================================ *)
(* Init                                                             *)
(* ================================================================ *)

#push-options "--z3rlimit 48 --fuel 2 --ifuel 2"
fn cbor_nondet_array_init
  (x: cbor_raw) (r1 r2: R.ref (IT.mixed_list U64.t cbor_raw))
  (#p: perm) (#l: Ghost.erased Spec.cbor) (#w1 #w2: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  Nondet.cbor_nondet_match p x l ** R.pts_to r1 w1 ** R.pts_to r2 w2 **
  pure (Spec.CArray? (Spec.unpack l))
returns y: cbor_mixed_list_array
ensures
  exists* (l': list Spec.cbor).
    cbor_nondet_array_owned y l' **
    Trade.trade
      (cbor_nondet_array_owned y l')
      (Nondet.cbor_nondet_match p x l ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)) **
    pure (Spec.CArray? (Spec.unpack l) /\ l' == Spec.CArray?.v (Spec.unpack l))
{
  (* Eliminate to a raw match [cbor_match p x v'] with [v'] valid and
     [mk_cbor v' == l]. Drop the elim trade: we re-fold the nondet match
     directly in the back-trade closure. *)
  let v' = Nondet.cbor_nondet_match_elim x #p #l;
  drop_ (Trade.trade
    (cbor_match p x (Ghost.reveal v'))
    (Nondet.cbor_nondet_match p x l));
  (* [v'] is an [Array] raw item, and its entries map to the spec list. *)
  SpecRaw.mk_cbor_eq (Ghost.reveal v');
  Spec.pack_unpack (Ghost.reveal l);
  Valid.valid_eq Valid.basic_data_model (Ghost.reveal v');
  let lraw : Ghost.erased (list SpecRawBase.raw_data_item) =
    Ghost.hide (Array?.v (Ghost.reveal v'));
  let l' : Ghost.erased (list Spec.cbor) =
    Ghost.hide (Spec.CArray?.v (Spec.unpack (Ghost.reveal l)));
  rewrite (cbor_match p x (Ghost.reveal v'))
    as (cbor_match p x (Array (Array?.len (Ghost.reveal v')) (Ghost.reveal lraw)));
  let vh : Ghost.erased (r: raw_data_item { Array? r }) =
    Ghost.hide (Array (Array?.len (Ghost.reveal v')) (Ghost.reveal lraw));
  rewrite (cbor_match p x (Array (Array?.len (Ghost.reveal v')) (Ghost.reveal lraw)))
    as (cbor_match p x (Ghost.reveal vh));

  (* Borrow the entries at native ambient permission [q] without touching
     r1/r2, keeping a trade back to [cbor_match]. *)
  let ml = array_borrow_native p x #vh;
  with q. assert (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Array?.v (Ghost.reveal vh)));
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Array?.v (Ghost.reveal vh)))
    as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Ghost.reveal lraw));
  rewrite (Trade.trade
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Array?.v (Ghost.reveal vh)))
      (cbor_match p x (Ghost.reveal vh)))
    as (Trade.trade
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Ghost.reveal lraw))
      (cbor_match p x (Ghost.reveal vh)));

  (* Share the borrowed entries: one half is wrapped up to full ownership,
     the other half is kept as a determinism witness. *)
  I.mixed_list_match_share cbor_match IO.u64_ops parse_raw_data_item q ml (Ghost.reveal lraw) cm_share;
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item (q /. 2.0R) ml (Ghost.reveal lraw);

  (* ---- Manually wrap the own-half under a fresh Append node at 1.0R. ---- *)
  Append.mixed_list_empty cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R));
  let len_a = IT.mixed_list_length IO.u64_ops ml;
  let depth : Ghost.erased nat =
    (if I.mixed_list_depth ml > I.mixed_list_depth (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw))
     then I.mixed_list_depth ml else I.mixed_list_depth (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw))) + 1;
  let bp : Ghost.erased perm = (1.0R /. 2.0R) /. 1.0R;
  R.write r1 ml;
  R.share r1;
  R.write r2 (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw));
  R.share r2;
  let ml_res : IT.mixed_list U64.t cbor_raw =
    IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a 0uL len_a 0uL (Ghost.reveal bp) r1 0uL (Ghost.reveal bp) r2 ((q /. 2.0R));
  let lres : Ghost.erased (list SpecRawBase.raw_data_item) = L.append (Ghost.reveal lraw) [];
  List.Tot.Properties.append_l_nil (Ghost.reveal lraw);
  Append.perm_mul_div_cancel' 1.0R (1.0R /. 2.0R);
  rewrite (R.pts_to r1 #(1.0R /. 2.0R) ml)
    as (R.pts_to r1 #(1.0R *. Ghost.reveal bp) ml);
  rewrite (R.pts_to r2 #(1.0R /. 2.0R) (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)))
    as (R.pts_to r2 #(1.0R *. Ghost.reveal bp) (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)));
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R)) ml (Ghost.reveal lraw))
    as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_before 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) ((q /. 2.0R)) ml (Ghost.reveal lraw));
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R)) (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) [])
    as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_after 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) ((q /. 2.0R)) (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) []);
  List.Tot.Properties.append_length (Ghost.reveal lraw) [];
  intro_pure (
    0 + U64.v (IT.mixed_list_length IO.u64_ops ml_res) <= U64.v len_a + U64.v 0uL /\
    U64.v 0uL + U64.v len_a <= U64.v (IT.mixed_list_length IO.u64_ops ml) /\
    U64.v 0uL + U64.v 0uL <= U64.v (IT.mixed_list_length IO.u64_ops (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw))) /\
    List.Tot.length (Ghost.reveal lraw) == I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a) /\
    List.Tot.length (Nil #SpecRawBase.raw_data_item) == I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a) /\
    Ghost.reveal lres == L.append (Ghost.reveal lraw) [] /\
    I.mixed_list_depth ml < Ghost.reveal depth /\
    I.mixed_list_depth (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) < Ghost.reveal depth
  ) ();
  fold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R
    (IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a 0uL len_a 0uL (Ghost.reveal bp) r1 0uL (Ghost.reveal bp) r2 ((q /. 2.0R)))
    (Ghost.reveal lres));
  rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R
    (IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a 0uL len_a 0uL (Ghost.reveal bp) r1 0uL (Ghost.reveal bp) r2 ((q /. 2.0R)))
    (Ghost.reveal lres))
    as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R ml_res (Ghost.reveal lres));
  fold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res (Ghost.reveal lres));
  rewrite each (Ghost.reveal lres) as (Ghost.reveal lraw);

  (* Build the owned handle over the KNOWN node. *)
  let res = mk_array_owned_with_ptr ml_res #lraw;

  (* nondet ownership of res over l' *)
  fold (cbor_nondet_array_owned res (Ghost.reveal l'));

  (* ---- Back-trade. ---- *)
  Trade.intro_trade
    (cbor_nondet_array_owned res (Ghost.reveal l'))
    (Nondet.cbor_nondet_match p x l ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2))
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R)) ml (Ghost.reveal lraw) **
     R.pts_to r1 #(1.0R /. 2.0R) ml **
     R.pts_to r2 #(1.0R /. 2.0R) (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) **
     Trade.trade
       (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Ghost.reveal lraw))
       (cbor_match p x (Ghost.reveal vh)) **
     pure (
       (res.cbor_array_gen_ptr <: IT.mixed_list U64.t cbor_raw) == ml_res /\
       (Ghost.reveal ml_res ==
          IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a 0uL len_a 0uL (Ghost.reveal bp) r1 0uL (Ghost.reveal bp) r2 ((q /. 2.0R))) /\
       U64.v (IT.mixed_list_length IO.u64_ops ml_res) == U64.v len_a /\
       U64.v (IT.mixed_list_length IO.u64_ops ml) == U64.v len_a /\
       I.append_off_before 0 (U64.v 0uL) (U64.v len_a) == 0 /\
       I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a) == U64.v len_a /\
       I.append_off_after 0 (U64.v 0uL) (U64.v len_a) == 0 /\
       I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a) == 0 /\
       1.0R *. Ghost.reveal bp == 1.0R /. 2.0R /\
       (q /. 2.0R) +. (q /. 2.0R) == q /\
       Ghost.reveal vh == Array (Array?.len (Ghost.reveal v')) (Ghost.reveal lraw) /\
       SpecRaw.valid_raw_data_item (Ghost.reveal vh) /\
       SpecRaw.mk_cbor (Ghost.reveal vh) == Ghost.reveal l /\
       Ghost.reveal l' == L.map SpecRaw.mk_cbor (Ghost.reveal lraw) /\
       L.for_all SpecRaw.valid_raw_data_item (Ghost.reveal lraw)
     ))
    fn _ {
      unfold (cbor_nondet_array_owned res (Ghost.reveal l'));
      with lr. assert (AB.cbor_array_owned res lr);
      unfold (AB.cbor_array_owned res lr);
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R res.cbor_array_gen_ptr lr)
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res lr);
      unfold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res lr);
      rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R ml_res lr)
        as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R
              (IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a 0uL len_a 0uL (Ghost.reveal bp) r1 0uL (Ghost.reveal bp) r2 ((q /. 2.0R)))
              lr);
      unfold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) 1.0R
              (IT.Append #U64.t #cbor_raw (Ghost.reveal depth) len_a 0uL len_a 0uL (Ghost.reveal bp) r1 0uL (Ghost.reveal bp) r2 ((q /. 2.0R)))
              lr);
      with ib_u ia_u l1_u l2_u. assert (
        R.pts_to r1 #(1.0R *. Ghost.reveal bp) ib_u **
        I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_before 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) ((q /. 2.0R)) ib_u l1_u **
        R.pts_to r2 #(1.0R *. Ghost.reveal bp) ia_u **
        I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_after 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) ((q /. 2.0R)) ia_u l2_u
      );
      rewrite (R.pts_to r1 #(1.0R *. Ghost.reveal bp) ib_u)
        as (R.pts_to r1 #(1.0R /. 2.0R) ib_u);
      R.gather r1;
      rewrite (R.pts_to r1 #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml)
        as (R.pts_to r1 ml);
      rewrite (R.pts_to r2 #(1.0R *. Ghost.reveal bp) ia_u)
        as (R.pts_to r2 #(1.0R /. 2.0R) ia_u);
      R.gather r2;
      rewrite (R.pts_to r2 #(1.0R /. 2.0R +. 1.0R /. 2.0R) (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)))
        as (R.pts_to r2 (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)));
      I.mixed_list_match_n_length cbor_match IO.u64_ops parse_raw_data_item (I.append_off_before 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) ((q /. 2.0R)) ib_u l1_u;
      I.mixed_list_match_n_length cbor_match IO.u64_ops parse_raw_data_item (I.append_off_after 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) ((q /. 2.0R)) ia_u l2_u;
      rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_before 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_before 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) ((q /. 2.0R)) ib_u l1_u)
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R)) ml l1_u);
      rewrite (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item (I.append_off_after 0 (U64.v 0uL) (U64.v len_a)) (I.append_n_after 0 (U64.v (IT.mixed_list_length IO.u64_ops ml_res)) (U64.v len_a)) ((q /. 2.0R)) ia_u l2_u)
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R)) (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) []);
      drop_ (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R)) (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) []);
      (* Gather the own-half with the kept witness to pin the arbitrary list. *)
      I.mixed_list_match_gather cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R)) ((q /. 2.0R)) ml l1_u (Ghost.reveal lraw) cm_gather;
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item ((q /. 2.0R) +. (q /. 2.0R)) ml l1_u)
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Ghost.reveal lraw));
      Trade.elim
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item q ml (Ghost.reveal lraw))
        (cbor_match p x (Ghost.reveal vh));
      rewrite (cbor_match p x (Ghost.reveal vh))
        as (cbor_match p x (Ghost.reveal v'));
      fold (Nondet.cbor_nondet_match p x l);
      fold (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2);
    };
  res
}
#pop-options

(* ================================================================ *)
(* Slice: zero-copy sub-range [i,j) of a nondeterministic-CBOR ARRAY. *)
(* Wraps the raw [AB.cbor_array_slice], bridging the raw slice-spec  *)
(* [AB.array_slice_spec] to the nondeterministic-CBOR level via      *)
(* [cbor_nondet_array_slice_spec] (which commutes with [mk_cbor]).   *)
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

(* [L.for_all] is preserved by the (fst of) splitAt *)
let rec for_all_fst_splitAt (#t: Type) (p: t -> bool) (l: list t) (n: nat)
: Lemma (requires (L.for_all p l))
        (ensures (L.for_all p (fst (L.splitAt n l))))
        (decreases n)
= if n = 0 then () else (match l with | [] -> () | _ :: q -> for_all_fst_splitAt p q (n - 1))

(* [L.for_all] is preserved by the (snd of) splitAt *)
let rec for_all_snd_splitAt (#t: Type) (p: t -> bool) (l: list t) (n: nat)
: Lemma (requires (L.for_all p l))
        (ensures (L.for_all p (snd (L.splitAt n l))))
        (decreases n)
= if n = 0 then () else (match l with | [] -> () | _ :: q -> for_all_snd_splitAt p q (n - 1))

#push-options "--fuel 2 --ifuel 2"
(* Slicing a raw list preserves validity of every element (the slice is a  *)
(* sub-range of the original valid list).                                  *)
let for_all_valid_array_slice_spec (l: list raw_data_item) (i j: U64.t)
: Lemma (requires (L.for_all SpecRaw.valid_raw_data_item l))
        (ensures (L.for_all SpecRaw.valid_raw_data_item (AB.array_slice_spec l i j)))
= if (U64.v i < U64.v j && U64.v j <= L.length l)
  then begin
    list_narrow_nonneg l (U64.v i) (U64.v j - U64.v i);
    for_all_snd_splitAt SpecRaw.valid_raw_data_item l (U64.v i);
    for_all_fst_splitAt SpecRaw.valid_raw_data_item (snd (L.splitAt (U64.v i) l)) (U64.v j - U64.v i)
  end
  else ()

(* Slicing the raw list [l] then mapping [mk_cbor] equals the             *)
(* nondeterministic-CBOR slice of [map mk_cbor l]: the raw slice-spec     *)
(* commutes with [map mk_cbor].                                           *)
let cbor_nondet_array_slice_spec_commutes (l: list raw_data_item) (i j: U64.t)
: Lemma (ensures
    L.map SpecRaw.mk_cbor (AB.array_slice_spec l i j) ==
    cbor_nondet_array_slice_spec (L.map SpecRaw.mk_cbor l) i j)
= L.map_lemma SpecRaw.mk_cbor l;
  if (U64.v i < U64.v j && U64.v j <= L.length l)
  then begin
    list_narrow_nonneg l (U64.v i) (U64.v j - U64.v i);
    list_map_narrow SpecRaw.mk_cbor l (U64.v i) (U64.v j - U64.v i)
  end
  else ()
#pop-options

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_nondet_array_slice_bridge
  (x: cbor_raw) (i j: U64.t)
  (r1 r2 r3 r4: R.ref (IT.mixed_list U64.t cbor_raw))
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#w1 #w2 #w3 #w4: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  Nondet.cbor_nondet_match p x v **
  R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
  pure (Spec.CArray? (Spec.unpack v))
returns res: cbor_raw
ensures exists* (v': Spec.cbor).
  Nondet.cbor_nondet_match 1.0R res v' **
  Trade.trade
    (Nondet.cbor_nondet_match 1.0R res v')
    (Nondet.cbor_nondet_match p x v **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
  pure (Spec.CArray? (Spec.unpack v) /\ Spec.CArray? (Spec.unpack v') /\
        (Spec.CArray?.v (Spec.unpack v') <: list Spec.cbor) ==
          cbor_nondet_array_slice_spec (Spec.CArray?.v (Spec.unpack v)) i j)
{
  (* 1. Eliminate the nondet match to a raw [cbor_match] on a valid raw item. *)
  let vr = Nondet.cbor_nondet_match_elim x #p #v;
  SpecRaw.mk_cbor_eq (Ghost.reveal vr);
  Spec.pack_unpack (Ghost.reveal v);
  Valid.valid_eq Valid.basic_data_model (Ghost.reveal vr);
  (* [vr] is an [Array] whose element list [Array?.v vr] is a list of valid raw
     items with [map mk_cbor (Array?.v vr) == CArray?.v (unpack v)]. *)
  let xh : Ghost.erased (r: raw_data_item { Array? r }) = Ghost.hide (Ghost.reveal vr);
  rewrite (cbor_match p x (Ghost.reveal vr)) as (cbor_match p x (Ghost.reveal xh));
  (* 2. Call the raw slice. *)
  let res = AB.cbor_array_slice p x i j r1 r2 r3 r4 #xh #w1 #w2 #w3 #w4;
  with yh. assert (cbor_match 1.0R res yh);
  (* Spec facts about [yh]: it is a valid [Array] whose element list is the raw
     slice of [Array?.v xh], and [mk_cbor yh == pack (CArray ls)]. *)
  Valid.valid_eq Valid.basic_data_model (Ghost.reveal yh);
  for_all_valid_array_slice_spec (Array?.v (Ghost.reveal xh)) i j;
  SpecRaw.mk_cbor_eq (Ghost.reveal yh);
  Spec.pack_unpack (SpecRaw.mk_cbor (Ghost.reveal yh));
  cbor_nondet_array_slice_spec_commutes (Array?.v (Ghost.reveal xh)) i j;
  let ls : Ghost.erased (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n }) =
    Ghost.hide (cbor_nondet_array_slice_spec (Spec.CArray?.v (Spec.unpack (Ghost.reveal v))) i j);
  Spec.unpack_pack (Spec.CArray (Ghost.reveal ls));
  (* 3. Recover the nondet source from the raw slice trade (T_src). *)
  Trade.intro_trade
    (cbor_match 1.0R res (Ghost.reveal yh))
    (Nondet.cbor_nondet_match p x v **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
    (Trade.trade
       (cbor_match 1.0R res (Ghost.reveal yh))
       (cbor_match p x (Ghost.reveal xh) **
        (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
     Trade.trade
       (cbor_match p x (Ghost.reveal vr))
       (Nondet.cbor_nondet_match p x v))
    fn _ {
      Trade.elim
        (cbor_match 1.0R res (Ghost.reveal yh))
        (cbor_match p x (Ghost.reveal xh) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4));
      rewrite (cbor_match p x (Ghost.reveal xh)) as (cbor_match p x (Ghost.reveal vr));
      Trade.elim
        (cbor_match p x (Ghost.reveal vr))
        (Nondet.cbor_nondet_match p x v);
    };
  (* 4. Introduce the nondet match on [res] (half permission) and thread T_src. *)
  Nondet.cbor_nondet_match_intro res #1.0R #(Ghost.reveal yh);
  Trade.trans
    (Nondet.cbor_nondet_match (1.0R /. 2.0R) res (SpecRaw.mk_cbor (Ghost.reveal yh)))
    (cbor_match 1.0R res (Ghost.reveal yh))
    (Nondet.cbor_nondet_match p x v **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4));
  rewrite each (SpecRaw.mk_cbor (Ghost.reveal yh)) as (Spec.pack (Spec.CArray (Ghost.reveal ls)));
  (* 5. Reset the permission to 1.0R (fresh handle) and thread T_src again. *)
  let resF = Nondet.cbor_nondet_reset_perm () res 1.0R;
  Trade.trans
    (Nondet.cbor_nondet_match 1.0R resF (Spec.pack (Spec.CArray (Ghost.reveal ls))))
    (Nondet.cbor_nondet_match (1.0R /. 2.0R) res (Spec.pack (Spec.CArray (Ghost.reveal ls))))
    (Nondet.cbor_nondet_match p x v **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4));
  resF
}
#pop-options
