module CBOR.Pulse.Raw.EverParse.ArrayBuilder
#lang-pulse
friend CBOR.Pulse.Raw.Format.Match
friend CBOR.Pulse.Raw.Format.MixedList
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Optimal
open CBOR.Pulse.Raw.Match

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module IO = LowParse.PulseParse.Iterator.IntOps
module Append = LowParse.PulseParse.Iterator.Append
module MP = CBOR.Pulse.Raw.Match.Perm
module PB = LowParse.PulseParse.Base
module LPB = LowParse.Pulse.Base
module Util = CBOR.Pulse.Raw.Util
module S = Pulse.Lib.Slice
module PM = Pulse.Lib.SeqMatch
open LowParse.Spec.VCList

(* Bridge the lowparse dictionary views [IO.u64_ops.v]/[IO.u64_ops.fits] to  *)
(* the concrete [U64.v]/[< pow2 64]: both are definitionally the identity/    *)
(* comparison, proved by computation.  Lets the u64 length/overflow facts     *)
(* connect [io.v (mixed_list_length io ..)] to plain [U64.v].                 *)
let u64_ops_v_eq (x: U64.t)
  : Lemma (IO.u64_ops.v x == U64.v x)
    [SMTPat (IO.u64_ops.v x)]
= ()

let u64_ops_fits_eq (n: nat)
  : Lemma (IO.u64_ops.fits n == (n < pow2 64 <: prop))
    [SMTPat (IO.u64_ops.fits n)]
= ()

(* ================================================================ *)
(* minimal_len_size_prop                                            *)
(* ================================================================ *)

let minimal_len_size_prop (len: U64.t)
  : Lemma (raw_uint64_size_prop (minimal_len_size len) len)
= ()

(* ================================================================ *)
(* Ownership predicate                                              *)
(*                                                                  *)
(* An owned array [x] is: the raw structural mixed_list held at      *)
(* full permission [1.0R] under the TOP-LEVEL (unbounded) match      *)
(* [cbor_match], together with the pure facts that its structural    *)
(* permission is full and its length-size field is the minimal       *)
(* (canonical) encoding of the element count.                        *)
(* ================================================================ *)

let cbor_array_owned (x: cbor_mixed_list_array) (l: list raw_data_item) : slprop =
  I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr l **
  pure (x.cbor_array_gen_perm == 1.0R /\
        x.cbor_array_gen_length_size ==
          (mk_raw_uint64 (IT.mixed_list_length IO.u64_ops x.cbor_array_gen_ptr)).size)

(* gather_t instance for the top-level cbor_match, needed by the      *)
(* singleton builder.                                                 *)
ghost
fn cbor_match_gather_t
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires cbor_match p x1 x2 ** cbor_match p' x1 x2'
ensures cbor_match (p +. p') x1 x2 ** pure (x2 == x2')
{
  MP.cbor_raw_gather p x1 x2 p' x2';
}

(* ================================================================ *)
(* Core builder: wrap a raw mixed_list into an owned array handle,   *)
(* with a trade back to the raw mixed_list.                          *)
(* ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
inline_for_extraction
fn cbor_array_of_ml
  (ml: IT.mixed_list U64.t cbor_raw)
  (#l: Ghost.erased (list raw_data_item))
requires
  I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l)
returns res: cbor_mixed_list_array
ensures
  cbor_array_owned res (Ghost.reveal l) **
  Trade.trade
    (cbor_array_owned res (Ghost.reveal l))
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l))
{
  let mll = IT.mixed_list_length IO.u64_ops ml;
  minimal_len_size_prop mll;
  let res : cbor_mixed_list_array = {
    cbor_array_gen_length_size = minimal_len_size mll;
    cbor_array_gen_ptr = ml;
    cbor_array_gen_perm = 1.0R;
  };
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l))
    as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R res.cbor_array_gen_ptr (Ghost.reveal l));
  fold (cbor_array_owned res (Ghost.reveal l));
  Trade.intro_trade
    (cbor_array_owned res (Ghost.reveal l))
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l))
    emp
    fn _ {
      unfold (cbor_array_owned res (Ghost.reveal l));
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R res.cbor_array_gen_ptr (Ghost.reveal l))
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l));
    };
  res
}
#pop-options

(* ================================================================ *)
(* Eliminate an owned handle back to its raw mixed_list.            *)
(* ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
inline_for_extraction
fn cbor_array_owned_elim
  (x: cbor_mixed_list_array)
  (#l: Ghost.erased (list raw_data_item))
requires cbor_array_owned x (Ghost.reveal l)
returns ml: IT.mixed_list U64.t cbor_raw
ensures
  I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l) **
  Trade.trade
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l))
    (cbor_array_owned x (Ghost.reveal l)) **
  pure (ml == x.cbor_array_gen_ptr /\
        FStar.UInt.fits (U64.v (IT.mixed_list_length IO.u64_ops ml)) 64)
{
  unfold (cbor_array_owned x (Ghost.reveal l));
  let ml = x.cbor_array_gen_ptr;
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l))
    as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l));
  Trade.intro_trade
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l))
    (cbor_array_owned x (Ghost.reveal l))
    (pure (x.cbor_array_gen_perm == 1.0R /\
           x.cbor_array_gen_length_size ==
             (mk_raw_uint64 (IT.mixed_list_length IO.u64_ops x.cbor_array_gen_ptr)).size))
    fn _ {
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Ghost.reveal l))
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l));
      fold (cbor_array_owned x (Ghost.reveal l));
    };
  ml
}
#pop-options

(* ================================================================ *)
(* cbor_array_owned_length_fits                                     *)
(* ================================================================ *)

#push-options "--z3rlimit 8 --fuel 2 --ifuel 2"
ghost
fn cbor_array_owned_length_fits
  (x: cbor_mixed_list_array) (#l: Ghost.erased (list raw_data_item))
requires cbor_array_owned x (Ghost.reveal l)
ensures cbor_array_owned x (Ghost.reveal l) **
  pure (FStar.UInt.fits (List.Tot.length (Ghost.reveal l)) 64)
{
  unfold (cbor_array_owned x (Ghost.reveal l));
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l);
  fold (cbor_array_owned x (Ghost.reveal l));
}
#pop-options

(* ================================================================ *)
(* cbor_array_empty                                                 *)
(* ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
fn cbor_array_empty (_: unit)
requires emp
returns res: cbor_mixed_list_array
ensures cbor_array_owned res []
{
  Append.mixed_list_empty cbor_match IO.u64_ops parse_raw_data_item 1.0R;
  let res = cbor_array_of_ml (IT.Base IT.Empty) #(Ghost.hide ([] <: list raw_data_item));
  drop_ (Trade.trade
    (cbor_array_owned res [])
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R (IT.Base IT.Empty) []));
  res
}
#pop-options

(* ================================================================ *)
(* cbor_array_singleton                                             *)
(* ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
fn cbor_array_singleton
  (x: cbor_raw) (ry: R.ref cbor_raw)
  (#pm: perm) (#v: Ghost.erased raw_data_item) (#w0: Ghost.erased cbor_raw)
requires cbor_match pm x (Ghost.reveal v) ** R.pts_to ry (Ghost.reveal w0)
returns res: cbor_mixed_list_array
ensures
  cbor_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_array_owned res [Ghost.reveal v])
    (cbor_match pm x (Ghost.reveal v) ** (exists* w. R.pts_to ry w))
{
  let ml =
    Append.mixed_list_singleton cbor_match IO.u64_ops parse_raw_data_item pm x v ry cbor_match_gather_t;
  (* ml : mixed_list cbor_raw, with
       mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml [reveal v]
       ** trade (that) (cbor_match pm x v ** exists* vy. pts_to ry vy)
       ** pure (mixed_list_length ml == 1sz) *)
  let res = cbor_array_of_ml ml #(Ghost.hide [Ghost.reveal v]);
  Trade.trans
    (cbor_array_owned res [Ghost.reveal v])
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml [Ghost.reveal v])
    (cbor_match pm x (Ghost.reveal v) ** (exists* w. R.pts_to ry w));
  res
}
#pop-options

(* ================================================================ *)
(* cbor_array_append                                                *)
(* ================================================================ *)

(* The overflow check [U64.gt la (0xffffffffffffffff - lb)] taken in the      *)
(* failure branch witnesses that the sum of the two lengths does not fit in a *)
(* u64.  Phrased over the (possibly truncated) u64 views so the conclusion    *)
(* holds without assuming the size_t values are themselves below 2^64.        *)
let array_append_overflow (la lb: U64.t) (na nb: nat)
: Lemma
    (requires
      U64.v la > U64.v (U64.sub 0xffffffffffffffffuL lb) /\
      U64.v la == na % pow2 64 /\
      U64.v lb == nb % pow2 64)
    (ensures ~ (FStar.UInt.fits (na + nb) U64.n))
= FStar.Math.Lemmas.lemma_mod_lt na (pow2 64);
  FStar.Math.Lemmas.lemma_mod_lt nb (pow2 64);
  assert_norm (pow2 64 == 0xffffffffffffffff + 1)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
fn cbor_array_append
  (x1 x2: cbor_mixed_list_array)
  (r_before r_after: R.ref (IT.mixed_list U64.t cbor_raw))
  (#l1 #l2: Ghost.erased (list raw_data_item))
  (#vb0 #va0: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  cbor_array_owned x1 (Ghost.reveal l1) ** cbor_array_owned x2 (Ghost.reveal l2) **
  R.pts_to r_before (Ghost.reveal vb0) ** R.pts_to r_after (Ghost.reveal va0)
returns res: option cbor_mixed_list_array
ensures
  (match res with
   | None ->
     cbor_array_owned x1 (Ghost.reveal l1) ** cbor_array_owned x2 (Ghost.reveal l2) **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
     pure (~ (FStar.UInt.fits
       (List.Tot.length (Ghost.reveal l1) + List.Tot.length (Ghost.reveal l2)) 64))
   | Some r ->
     cbor_array_owned r (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)) **
     Trade.trade
       (cbor_array_owned r (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
       (cbor_array_owned x1 (Ghost.reveal l1) ** cbor_array_owned x2 (Ghost.reveal l2) **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
{
  let ml_a = cbor_array_owned_elim x1 #l1;
  let ml_b = cbor_array_owned_elim x2 #l2;
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal l1);
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal l2);
  let len_a = IT.mixed_list_length IO.u64_ops ml_a;
  let len_b = IT.mixed_list_length IO.u64_ops ml_b;
  let limit = U64.sub 0xffffffffffffffffuL len_b;
  if (U64.gt len_a limit) {
    (* sum would not fit in a u64: restore both owned handles, return None *)
    array_append_overflow len_a len_b (U64.v len_a) (U64.v len_b);
    Trade.elim
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal l1))
      (cbor_array_owned x1 (Ghost.reveal l1));
    Trade.elim
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal l2))
      (cbor_array_owned x2 (Ghost.reveal l2));
    None #cbor_mixed_list_array
  } else {
    let ml_res =
      Append.mixed_list_append cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a l1 ml_b l2 r_before r_after;
    List.Tot.Properties.append_length (Ghost.reveal l1) (Ghost.reveal l2);
    let res =
      cbor_array_of_ml ml_res #(Ghost.hide (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)));
    Trade.intro_trade
      (cbor_array_owned res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
      (cbor_array_owned x1 (Ghost.reveal l1) ** cbor_array_owned x2 (Ghost.reveal l2) **
       (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va))
      (Trade.trade
         (cbor_array_owned res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res
            (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2))) **
       Trade.trade
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res
            (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal l1) **
          I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal l2) **
          (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)) **
       Trade.trade
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal l1))
         (cbor_array_owned x1 (Ghost.reveal l1)) **
       Trade.trade
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal l2))
         (cbor_array_owned x2 (Ghost.reveal l2)))
      fn _ {
        Trade.elim
          (cbor_array_owned res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res
             (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)));
        Trade.elim
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res
             (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal l1) **
           I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal l2) **
           (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va));
        Trade.elim
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_a (Ghost.reveal l1))
          (cbor_array_owned x1 (Ghost.reveal l1));
        Trade.elim
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_b (Ghost.reveal l2))
          (cbor_array_owned x2 (Ghost.reveal l2));
      };
    Some #cbor_mixed_list_array res
  }
}
#pop-options

(* ================================================================ *)
(* cbor_array_finalize                                              *)
(* ================================================================ *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
fn cbor_array_finalize
  (x: cbor_mixed_list_array) (#l: Ghost.erased (list raw_data_item))
requires cbor_array_owned x (Ghost.reveal l)
returns y: cbor_raw
ensures
  cbor_array_finalized x y (Ghost.reveal l) **
  pure (y == CBOR_Case_Array_Gen x)
{
  unfold (cbor_array_owned x (Ghost.reveal l));
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l);
  let len : raw_uint64 =
    mk_raw_uint64 (IT.mixed_list_length IO.u64_ops x.cbor_array_gen_ptr);
  let xh0 : Ghost.erased (r: raw_data_item { Array? r }) =
    Ghost.hide (Array len (Ghost.reveal l));
  let y : cbor_raw = CBOR_Case_Array_Gen x;
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l))
    as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item
          (1.0R *. x.cbor_array_gen_perm) x.cbor_array_gen_ptr
          (Array?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_raw) (pm0: perm)
    (yv: raw_data_item { List.Tot.memP yv (Array?.v (Ghost.reveal xh0)) })
    requires cbor_match pm0 x1 yv
    ensures cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 yv
  {
    array_elem_precedes (Ghost.reveal xh0) yv;
    cbor_match_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 yv;
    rewrite (cbor_match pm0 x1 yv)
      as (cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 yv);
  };
  I.mixed_list_match_weaken
    cbor_match (cbor_match_bounded (Ghost.reveal xh0) cbor_match)
    IO.u64_ops parse_raw_data_item (1.0R *. x.cbor_array_gen_perm) x.cbor_array_gen_ptr
    (Array?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_array 1.0R x (Ghost.reveal xh0) cbor_match);
  cbor_match_eq_array_gen 1.0R x (Ghost.reveal xh0);
  Trade.rewrite_with_trade
    (cbor_match_mixed_list_array 1.0R x (Ghost.reveal xh0) cbor_match)
    (cbor_match 1.0R y (Ghost.reveal xh0));
  Trade.intro_trade
    (cbor_match_mixed_list_array 1.0R x (Ghost.reveal xh0) cbor_match)
    (cbor_array_owned x (Ghost.reveal l))
    emp
    fn _ {
      unfold (cbor_match_mixed_list_array 1.0R x (Ghost.reveal xh0) cbor_match);
      ghost
      fn prf_fwd (x1: cbor_raw) (pm0: perm)
        (yv: raw_data_item { List.Tot.memP yv (Array?.v (Ghost.reveal xh0)) })
        requires cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 yv
        ensures cbor_match pm0 x1 yv
      {
        array_elem_precedes (Ghost.reveal xh0) yv;
        cbor_match_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 yv;
        rewrite (cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 yv)
          as (cbor_match pm0 x1 yv);
      };
      I.mixed_list_match_weaken
        (cbor_match_bounded (Ghost.reveal xh0) cbor_match) cbor_match
        IO.u64_ops parse_raw_data_item (1.0R *. x.cbor_array_gen_perm) x.cbor_array_gen_ptr
        (Array?.v (Ghost.reveal xh0)) prf_fwd;
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item
                 (1.0R *. x.cbor_array_gen_perm) x.cbor_array_gen_ptr
                 (Array?.v (Ghost.reveal xh0)))
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l));
      fold (cbor_array_owned x (Ghost.reveal l));
    };
  Trade.trans
    (cbor_match 1.0R y (Ghost.reveal xh0))
    (cbor_match_mixed_list_array 1.0R x (Ghost.reveal xh0) cbor_match)
    (cbor_array_owned x (Ghost.reveal l));
  rewrite (cbor_match 1.0R y (Ghost.reveal xh0))
    as (cbor_match 1.0R y (Array len (Ghost.reveal l)));
  rewrite (Trade.trade (cbor_match 1.0R y (Ghost.reveal xh0)) (cbor_array_owned x (Ghost.reveal l)))
    as (Trade.trade (cbor_match 1.0R y (Array len (Ghost.reveal l))) (cbor_array_owned x (Ghost.reveal l)));
  fold (cbor_array_finalized x y (Ghost.reveal l));
  y
}
#pop-options

(* ================================================================ *)
(* cbor_array_finalize_with_len                                      *)
(*                                                                   *)
(* Like [cbor_array_finalize] but stamps the caller-chosen length    *)
(* header [len] (need not be minimal) onto a FRESH handle [x'] that   *)
(* shares [x]'s pointer/permission; the trade back restores the      *)
(* original (minimal-encoded) owned handle [x].                       *)
(* ================================================================ *)

#restart-solver
#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
fn cbor_array_finalize_with_len
  (x: cbor_mixed_list_array)
  (len: raw_uint64)
  (#l: Ghost.erased (l: list raw_data_item { cbor_array_len_ok len l }))
requires cbor_array_owned_with_len x len (Ghost.reveal l)
returns y: cbor_raw
ensures
  cbor_array_finalized_val x y (Array len (Ghost.reveal l))
{
  unfold (cbor_array_owned_with_len x len (Ghost.reveal l));
  unfold (cbor_array_owned x (Ghost.reveal l));
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l);
  // [U64.v (mixed_list_length x.ptr) == length l == U64.v len.value], hence the
  // fresh handle [x'] with size [len.size] is well-formed
  assert (pure (U64.v (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length x.cbor_array_gen_ptr) == U64.v len.value));
  assert (pure (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length x.cbor_array_gen_ptr == len.value));
  let x' : cbor_mixed_list_array = {
    cbor_array_gen_length_size = len.size;
    cbor_array_gen_ptr = x.cbor_array_gen_ptr;
    cbor_array_gen_perm = x.cbor_array_gen_perm;
  };
  let xh0 : Ghost.erased (r: raw_data_item { Array? r }) =
    Ghost.hide (Array len (Ghost.reveal l));
  let y : cbor_raw = CBOR_Case_Array_Gen x';
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l))
    as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item
          (1.0R *. x'.cbor_array_gen_perm) x'.cbor_array_gen_ptr
          (Array?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_raw) (pm0: perm)
    (yv: raw_data_item { List.Tot.memP yv (Array?.v (Ghost.reveal xh0)) })
    requires cbor_match pm0 x1 yv
    ensures cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 yv
  {
    array_elem_precedes (Ghost.reveal xh0) yv;
    cbor_match_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 yv;
    rewrite (cbor_match pm0 x1 yv)
      as (cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 yv);
  };
  I.mixed_list_match_weaken
    cbor_match (cbor_match_bounded (Ghost.reveal xh0) cbor_match)
    IO.u64_ops parse_raw_data_item (1.0R *. x'.cbor_array_gen_perm) x'.cbor_array_gen_ptr
    (Array?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_array 1.0R x' (Ghost.reveal xh0) cbor_match);
  cbor_match_eq_array_gen 1.0R x' (Ghost.reveal xh0);
  Trade.rewrite_with_trade
    (cbor_match_mixed_list_array 1.0R x' (Ghost.reveal xh0) cbor_match)
    (cbor_match 1.0R y (Ghost.reveal xh0));
  // Expose [x']'s field equalities as outer pure facts so they propagate into
  // the trade-elimination closure below (x' is a local let, so its defining
  // equation would otherwise not be visible inside the lifted closure).
  assert (pure (x'.cbor_array_gen_perm == 1.0R));
  assert (pure (x'.cbor_array_gen_ptr == x.cbor_array_gen_ptr));
  Trade.intro_trade
    (cbor_match_mixed_list_array 1.0R x' (Ghost.reveal xh0) cbor_match)
    (cbor_array_owned x (Ghost.reveal l))
    emp
    fn _ {
      unfold (cbor_match_mixed_list_array 1.0R x' (Ghost.reveal xh0) cbor_match);
      ghost
      fn prf_fwd (x1: cbor_raw) (pm0: perm)
        (yv: raw_data_item { List.Tot.memP yv (Array?.v (Ghost.reveal xh0)) })
        requires cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 yv
        ensures cbor_match pm0 x1 yv
      {
        array_elem_precedes (Ghost.reveal xh0) yv;
        cbor_match_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 yv;
        rewrite (cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 yv)
          as (cbor_match pm0 x1 yv);
      };
      I.mixed_list_match_weaken
        (cbor_match_bounded (Ghost.reveal xh0) cbor_match) cbor_match
        IO.u64_ops parse_raw_data_item (1.0R *. x'.cbor_array_gen_perm) x'.cbor_array_gen_ptr
        (Array?.v (Ghost.reveal xh0)) prf_fwd;
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item
                 (1.0R *. x'.cbor_array_gen_perm) x'.cbor_array_gen_ptr
                 (Array?.v (Ghost.reveal xh0)))
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R x.cbor_array_gen_ptr (Ghost.reveal l));
      fold (cbor_array_owned x (Ghost.reveal l));
    };
  Trade.trans
    (cbor_match 1.0R y (Ghost.reveal xh0))
    (cbor_match_mixed_list_array 1.0R x' (Ghost.reveal xh0) cbor_match)
    (cbor_array_owned x (Ghost.reveal l));
  rewrite (cbor_match 1.0R y (Ghost.reveal xh0))
    as (cbor_match 1.0R y (Array len (Ghost.reveal l)));
  rewrite (Trade.trade (cbor_match 1.0R y (Ghost.reveal xh0)) (cbor_array_owned x (Ghost.reveal l)))
    as (Trade.trade (cbor_match 1.0R y (Array len (Ghost.reveal l)))
          (cbor_array_owned x (Array?.v (Array len (Ghost.reveal l)))));
  fold (cbor_array_finalized_val x y (Array len (Ghost.reveal l)));
  y
}
#pop-options

(* ================================================================ *)
(* Borrow helpers (array analogue of MapBuilder's borrow machinery) *)
(* ================================================================ *)

let perm_one_r (q: perm) : Lemma (q *. 1.0R == q) = ()

let perm_one_l (q: perm) : Lemma (1.0R *. q == q) = ()

(* The element-list parser [parse_nlist n parse_raw_data_item] is strong    *)
(* for any [n]: needed to weaken a serialized payload to a                   *)
(* [pts_to_parsed_strong_prefix].                                            *)
let array_payload_kind_strong (n: nat)
: Lemma
    ((parse_nlist_kind n parse_raw_data_item_kind).parser_kind_subkind
      == Some ParserStrong)
= parse_nlist_kind_subkind n parse_raw_data_item_kind;
  assert_norm (parse_raw_data_item_kind.parser_kind_subkind == Some ParserStrong)

(* Local elimination of a serialized array into its raw serialized payload   *)
(* (a [pts_to_serialized] over the element-list serializer), with a trade    *)
(* back.  Mirrors [MapBuilder.map_serialized_elim].                          *)
ghost
fn array_serialized_elim
  (v: cbor_serialized) (pm: perm) (r: raw_data_item { Array? r })
requires
  cbor_match_serialized_array v pm r
ensures exists* pm'.
  LPB.pts_to_serialized
    (serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item)
    (to_slice v.cbor_serialized_payload) #pm' (Array?.v r) **
  Trade.trade
    (LPB.pts_to_serialized
      (serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item)
      (to_slice v.cbor_serialized_payload) #pm' (Array?.v r))
    (cbor_match_serialized_array v pm r) **
  pure (v.cbor_serialized_header == Array?.len r)
{
  unfold (cbor_match_serialized_array v pm r);
  unfold (cbor_match_serialized_payload_array (to_slice v.cbor_serialized_payload)
            (pm `Util.perm_mul` v.cbor_serialized_perm) (Array?.v r));
  with pm'. assert (LPB.pts_to_serialized
    (serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item)
    (to_slice v.cbor_serialized_payload) #pm' (Array?.v r));
  Trade.intro_trade
    (LPB.pts_to_serialized
      (serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item)
      (to_slice v.cbor_serialized_payload) #pm' (Array?.v r))
    (cbor_match_serialized_array v pm r)
    emp
    fn _ {
      fold (cbor_match_serialized_payload_array (to_slice v.cbor_serialized_payload)
              (pm `Util.perm_mul` v.cbor_serialized_perm) (Array?.v r));
      fold (cbor_match_serialized_array v pm r);
    };
}

(* ================================================================ *)
(* cbor_array_borrow_entries_serialized                            *)
(*                                                                  *)
(* Serialized-array arm: turn the serialized payload into a         *)
(* [Base (Serialized ...)] mixed_list node at AMBIENT 1.0R, pushing *)
(* the fractional part [pm_s/2] into the node's [sp], with a trade  *)
(* back.                                                            *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
fn cbor_array_borrow_entries_serialized
  (pm: perm) (v: cbor_serialized)
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
requires
  cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh)
returns ml: IT.mixed_list U64.t cbor_raw
ensures
  I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)) **
  Trade.trade
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
    (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh))
{
  Trade.rewrite_with_trade
    (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh))
    (cbor_match_serialized_array v pm (Ghost.reveal xh));
  array_serialized_elim v pm (Ghost.reveal xh);
  with pm_s. _;
  (* Derive [SZ.fits (U64.v count)] from the serialized payload: an nlist of  *)
  (* N raw_data_items (each >= 1 byte) occupies >= N bytes, and the payload    *)
  (* slice length is a [size_t], so N <= SZ-addressable length, hence fits.    *)
  LPB.pts_to_serialized_length
    (serialize_nlist (U64.v (Array?.len (Ghost.reveal xh)).value) serialize_raw_data_item)
    (to_slice v.cbor_serialized_payload);
  parse_nlist_kind_low (U64.v (Array?.len (Ghost.reveal xh)).value) parse_raw_data_item_kind;
  assert_norm (parse_raw_data_item_kind.parser_kind_low == 1);
  SZ.fits_lte
    (U64.v (Array?.len (Ghost.reveal xh)).value)
    (SZ.v (S.len (to_slice v.cbor_serialized_payload)));
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh));
  PB.pts_to_serialized_parsed (to_slice v.cbor_serialized_payload);
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh));
  array_payload_kind_strong (U64.v (Array?.len (Ghost.reveal xh)).value);
  PB.pts_to_parsed_weaken_strong_prefix
    (parse_nlist (U64.v (Array?.len (Ghost.reveal xh)).value) parse_raw_data_item)
    (to_slice v.cbor_serialized_payload);
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh));
  let count = v.cbor_serialized_header.value;
  perm_one_l (pm_s /. 2.0R);
  rewrite (PB.pts_to_parsed_strong_prefix
             (parse_nlist (U64.v (Array?.len (Ghost.reveal xh)).value) parse_raw_data_item)
             (to_slice v.cbor_serialized_payload) #(pm_s /. 2.0R) (Array?.v (Ghost.reveal xh)))
    as (PB.pts_to_parsed_strong_prefix
          (parse_nlist (0 + U64.v count) parse_raw_data_item)
          (to_slice v.cbor_serialized_payload) #(1.0R *. (pm_s /. 2.0R)) (Array?.v (Ghost.reveal xh)));
  fold (I.base_mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v count) 1.0R
          (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload))
          (Array?.v (Ghost.reveal xh)));
  fold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v count) 1.0R
          (IT.Base #U64.t #cbor_raw
             (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload)))
          (Array?.v (Ghost.reveal xh)));
  fold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
          (IT.Base #U64.t #cbor_raw
             (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload)))
          (Array?.v (Ghost.reveal xh)));
  let ml : IT.mixed_list U64.t cbor_raw =
    IT.Base #U64.t #cbor_raw
      (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload));
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
             (IT.Base #U64.t #cbor_raw
                (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload)))
             (Array?.v (Ghost.reveal xh)))
    as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)));
  Trade.intro_trade
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
    (PB.pts_to_parsed_strong_prefix
       (parse_nlist (U64.v (Array?.len (Ghost.reveal xh)).value) parse_raw_data_item)
       (to_slice v.cbor_serialized_payload) #(pm_s /. 2.0R) (Array?.v (Ghost.reveal xh)))
    (pure (U64.v (Array?.len (Ghost.reveal xh)).value == 0 + U64.v count))
    fn _ {
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
              (IT.Base #U64.t #cbor_raw
                 (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload)))
              (Array?.v (Ghost.reveal xh)));
      unfold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
                (IT.Base #U64.t #cbor_raw
                   (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload)))
                (Array?.v (Ghost.reveal xh)));
      unfold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v count) 1.0R
                (IT.Base #U64.t #cbor_raw
                   (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload)))
                (Array?.v (Ghost.reveal xh)));
      unfold (I.base_mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v count) 1.0R
                (IT.Serialized #U64.t #cbor_raw (pm_s /. 2.0R) count (to_slice v.cbor_serialized_payload))
                (Array?.v (Ghost.reveal xh)));
      with l_all. _;
      perm_one_l (pm_s /. 2.0R);
      rewrite (PB.pts_to_parsed_strong_prefix
                 (parse_nlist (0 + U64.v count) parse_raw_data_item)
                 (to_slice v.cbor_serialized_payload) #(1.0R *. (pm_s /. 2.0R)) l_all)
        as (PB.pts_to_parsed_strong_prefix
              (parse_nlist (U64.v (Array?.len (Ghost.reveal xh)).value) parse_raw_data_item)
              (to_slice v.cbor_serialized_payload) #(pm_s /. 2.0R) (Array?.v (Ghost.reveal xh)));
    };
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh));
  ml
}
#pop-options

(* ================================================================ *)
(* cbor_array_borrow_entries_inline                                *)
(*                                                                  *)
(* Inline-array arm: view the inline slice [v.cbor_array_ptr] as a  *)
(* [Base (Slice ...)] mixed_list node at AMBIENT 1.0R, pushing the  *)
(* fractional part [pm *. array_perm] / [pm *. payload_perm] into    *)
(* the node's [sp]/[sv], with a trade back.  Simpler than the map    *)
(* analogue: arrays use [cbor_match] DIRECTLY as element matcher     *)
(* (no [entry0] wrapper).                                            *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
fn cbor_array_borrow_entries_inline
  (pm: perm) (v: cbor_array)
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
requires
  cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh)
returns ml: IT.mixed_list U64.t cbor_raw
ensures
  I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)) **
  Trade.trade
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
    (cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh))
{
  cbor_match_eq_array pm v (Ghost.reveal xh);
  Trade.rewrite_with_trade
    (cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh))
    (cbor_match_array v pm (Ghost.reveal xh) cbor_match);
  unfold (cbor_match_array v pm (Ghost.reveal xh) cbor_match);
  with w. _;
  S.pts_to_len v.cbor_array_ptr;
  (* Element count as a u64 (the [cbor_array_ptr] refinement guarantees the  *)
  (* slice length fits in 64 bits), for the [Slice] node's [count] field.    *)
  let count = IO.u64_ops.of_sizet (S.len v.cbor_array_ptr);
  ghost
  fn weaken_fwd (c: cbor_raw)
    (yv: (yv: raw_data_item { yv << Array?.v (Ghost.reveal xh) }))
    requires cbor_match (pm `Util.perm_mul` v.cbor_array_payload_perm) c yv
    ensures cbor_match (1.0R *. (pm *. v.cbor_array_payload_perm)) c yv
  {
    perm_one_l (pm *. v.cbor_array_payload_perm);
    rewrite (cbor_match (pm `Util.perm_mul` v.cbor_array_payload_perm) c yv)
      as (cbor_match (1.0R *. (pm *. v.cbor_array_payload_perm)) c yv);
  };
  PM.seq_list_match_weaken
    w (Array?.v (Ghost.reveal xh))
    (cbor_match (pm `Util.perm_mul` v.cbor_array_payload_perm))
    (cbor_match (1.0R *. (pm *. v.cbor_array_payload_perm)))
    weaken_fwd;
  perm_one_l (pm *. v.cbor_array_array_perm);
  rewrite (S.pts_to v.cbor_array_ptr #(pm `Util.perm_mul` v.cbor_array_array_perm) w)
    as (S.pts_to v.cbor_array_ptr #(1.0R *. (pm *. v.cbor_array_array_perm)) w);
  assert (pure (w `Seq.equal`
    Seq.slice w 0 (0 + U64.v count)));
  fold (I.base_mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item
          0 (U64.v count) 1.0R
          (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count)
          (Array?.v (Ghost.reveal xh)));
  fold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item
          0 (U64.v count) 1.0R
          (IT.Base #U64.t #cbor_raw
             (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count))
          (Array?.v (Ghost.reveal xh)));
  fold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
          (IT.Base #U64.t #cbor_raw
             (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count))
          (Array?.v (Ghost.reveal xh)));
  let ml : IT.mixed_list U64.t cbor_raw =
    IT.Base #U64.t #cbor_raw
      (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count);
  rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
             (IT.Base #U64.t #cbor_raw
                (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count))
             (Array?.v (Ghost.reveal xh)))
    as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)));
  Trade.intro_trade
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
    (cbor_match_array v pm (Ghost.reveal xh) cbor_match)
    (pure (v.cbor_array_length_size == (Array?.len (Ghost.reveal xh)).size /\
           SZ.v (S.len v.cbor_array_ptr) == U64.v (Array?.len (Ghost.reveal xh)).value))
    fn _ {
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
              (IT.Base #U64.t #cbor_raw
                 (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count))
              (Array?.v (Ghost.reveal xh)));
      unfold (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
                (IT.Base #U64.t #cbor_raw
                   (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count))
                (Array?.v (Ghost.reveal xh)));
      unfold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item
                0 (U64.v count) 1.0R
                (IT.Base #U64.t #cbor_raw
                   (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count))
                (Array?.v (Ghost.reveal xh)));
      unfold (I.base_mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item
                0 (U64.v count) 1.0R
                (IT.Slice #U64.t #cbor_raw (pm *. v.cbor_array_array_perm) (pm *. v.cbor_array_payload_perm) v.cbor_array_ptr count)
                (Array?.v (Ghost.reveal xh)));
      with l' l1. _;
      S.pts_to_len v.cbor_array_ptr;
      assert (pure (l1 `Seq.equal` l'));
      ghost
      fn weaken_bwd (c: cbor_raw)
        (yv: (yv: raw_data_item { yv << Array?.v (Ghost.reveal xh) }))
        requires cbor_match (1.0R *. (pm *. v.cbor_array_payload_perm)) c yv
        ensures cbor_match (pm `Util.perm_mul` v.cbor_array_payload_perm) c yv
      {
        perm_one_l (pm *. v.cbor_array_payload_perm);
        rewrite (cbor_match (1.0R *. (pm *. v.cbor_array_payload_perm)) c yv)
          as (cbor_match (pm `Util.perm_mul` v.cbor_array_payload_perm) c yv);
      };
      PM.seq_list_match_weaken
        l1 (Array?.v (Ghost.reveal xh))
        (cbor_match (1.0R *. (pm *. v.cbor_array_payload_perm)))
        (cbor_match (pm `Util.perm_mul` v.cbor_array_payload_perm))
        weaken_bwd;
      perm_one_l (pm *. v.cbor_array_array_perm);
      rewrite (S.pts_to v.cbor_array_ptr #(1.0R *. (pm *. v.cbor_array_array_perm)) l')
        as (S.pts_to v.cbor_array_ptr #(pm `Util.perm_mul` v.cbor_array_array_perm) l');
      rewrite (PM.seq_list_match l1 (Array?.v (Ghost.reveal xh))
                 (cbor_match (pm `Util.perm_mul` v.cbor_array_payload_perm)))
        as (PM.seq_list_match l' (Array?.v (Ghost.reveal xh))
              (cbor_match (pm `Util.perm_mul` v.cbor_array_payload_perm)));
      fold (cbor_match_array v pm (Ghost.reveal xh) cbor_match);
    };
  Trade.trans _ _ (cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh));
  ml
}
#pop-options

(* ================================================================ *)
(* cbor_array_borrow_entries (dispatcher)                          *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
fn cbor_array_borrow_entries
  (pm: perm) (x: cbor_raw)
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
requires
  cbor_match pm x (Ghost.reveal xh) **
  pure (cbor_array_borrow_pre pm x)
returns ml: IT.mixed_list U64.t cbor_raw
ensures
  I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)) **
  Trade.trade
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
    (cbor_match pm x (Ghost.reveal xh))
{
  cbor_match_cases x;
  match x {
    norewrite
    CBOR_Case_Array v -> {
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh));
      let ml = cbor_array_borrow_entries_inline pm v #xh;
      Trade.trans _ _ (cbor_match pm x (Ghost.reveal xh));
      ml
    }
    norewrite
    CBOR_Case_Serialized_Array v -> {
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh));
      let ml = cbor_array_borrow_entries_serialized pm v #xh;
      Trade.trans _ _ (cbor_match pm x (Ghost.reveal xh));
      ml
    }
    norewrite
    CBOR_Case_Array_Gen v -> {
      cbor_match_eq_array_gen pm v (Ghost.reveal xh);
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match);
      unfold (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match);
      (* the _Gen restriction [cbor_array_borrow_pre] gives full effective perm *)
      assert (pure (pm *. v.cbor_array_gen_perm == 1.0R));
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
      let ml = v.cbor_array_gen_ptr;
      rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item
                 (pm *. v.cbor_array_gen_perm) v.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh)))
        as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)));
      Trade.intro_trade
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match)
        (pure (v.cbor_array_gen_length_size == (Array?.len (Ghost.reveal xh)).size /\
               pm *. v.cbor_array_gen_perm == 1.0R))
        fn _ {
          rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
            as (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item
                  (pm *. v.cbor_array_gen_perm) v.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh)));
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
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match)
        (cbor_match pm x (Ghost.reveal xh));
      ml
    }
  }
}
#pop-options

(* ================================================================ *)
(* cbor_array_init_borrow (TOTAL, scaled borrow dispatcher)         *)
(*                                                                  *)
(* Like [cbor_array_borrow_entries], but TOTAL (no                  *)
(* [cbor_array_borrow_pre] restriction) at the price of two extra   *)
(* caller-supplied scratch references [r1]/[r2].  Produces a        *)
(* mixed_list at ambient [1.0R] together with a trade back to       *)
(* [cbor_match] AND the (existentially-quantified) two refs.        *)
(*                                                                  *)
(* - inline / serialized arms: reuse the existing borrow helpers    *)
(*   (already ambient [1.0R]); the refs are framed through unused   *)
(*   and simply re-attached to the trade's conclusion via           *)
(*   [Trade.weak_concl_r].                                          *)
(* - structural [_Gen] arm (ANY permission): weaken the bounded     *)
(*   element match to the unbounded [cbor_match], then call         *)
(*   [Append.mixed_list_wrap_scaled] to re-present the fractional   *)
(*   [pm *. gen_perm]-ambient sub-list under a full-ownership        *)
(*   ([1.0R]) handle (consuming [r1]/[r2] into a fresh [Append]      *)
(*   node), and compose the trades.                                 *)
(* ================================================================ *)

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"
inline_for_extraction
fn cbor_array_init_borrow
  (pm: perm) (x: cbor_raw)
  (r1 r2: R.ref (IT.mixed_list U64.t cbor_raw))
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
  (#w1 #w2: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  cbor_match pm x (Ghost.reveal xh) ** R.pts_to r1 w1 ** R.pts_to r2 w2
returns ml: IT.mixed_list U64.t cbor_raw
ensures
  I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)) **
  Trade.trade
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
    (cbor_match pm x (Ghost.reveal xh) **
     (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2))
{
  cbor_match_cases x;
  match x {
    norewrite
    CBOR_Case_Array v -> {
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh));
      let ml = cbor_array_borrow_entries_inline pm v #xh;
      Trade.trans
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        (cbor_match pm (CBOR_Case_Array v) (Ghost.reveal xh))
        (cbor_match pm x (Ghost.reveal xh));
      Trade.weak_concl_r
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        (cbor_match pm x (Ghost.reveal xh))
        (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2);
      ml
    }
    norewrite
    CBOR_Case_Serialized_Array v -> {
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh));
      let ml = cbor_array_borrow_entries_serialized pm v #xh;
      Trade.trans
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        (cbor_match pm (CBOR_Case_Serialized_Array v) (Ghost.reveal xh))
        (cbor_match pm x (Ghost.reveal xh));
      Trade.weak_concl_r
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
        (cbor_match pm x (Ghost.reveal xh))
        (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2);
      ml
    }
    norewrite
    CBOR_Case_Array_Gen v -> {
      cbor_match_eq_array_gen pm v (Ghost.reveal xh);
      Trade.rewrite_with_trade (cbor_match pm x (Ghost.reveal xh))
        (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match);
      unfold (cbor_match_mixed_list_array pm v (Ghost.reveal xh) cbor_match);
      (* forward-weaken the bounded element match to the unbounded [cbor_match] *)
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
      (* trade back [MM at q] -> [cbor_match_mixed_list_array] (refold) *)
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
      (* re-scale the fractional sub-list to ambient [1.0R], consuming r1/r2 *)
      I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item (pm *. v.cbor_array_gen_perm)
        v.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh));
      let ml_res =
        Append.mixed_list_wrap_scaled cbor_match IO.u64_ops parse_raw_data_item
          (pm *. v.cbor_array_gen_perm) v.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh)) r1 r2;
      Trade.trans_concl_l
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res (Array?.v (Ghost.reveal xh)))
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item (pm *. v.cbor_array_gen_perm)
           v.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh)))
        (cbor_match pm x (Ghost.reveal xh))
        (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2);
      ml_res
    }
  }
}
#pop-options

(* ================================================================ *)
(* cbor_array_init  (TOTAL: all representations, any permission)   *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
fn cbor_array_init
  (pm: perm) (x: cbor_raw)
  (r1 r2: R.ref (IT.mixed_list U64.t cbor_raw))
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
  (#w1 #w2: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  cbor_match pm x (Ghost.reveal xh) ** R.pts_to r1 w1 ** R.pts_to r2 w2
returns y: cbor_mixed_list_array
ensures
  cbor_array_owned y (Array?.v (Ghost.reveal xh)) **
  Trade.trade
    (cbor_array_owned y (Array?.v (Ghost.reveal xh)))
    (cbor_match pm x (Ghost.reveal xh) **
     (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2))
{
  let ml = cbor_array_init_borrow pm x r1 r2 #xh #w1 #w2;
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh));
  let y = cbor_array_of_ml ml #(Ghost.hide (Array?.v (Ghost.reveal xh)));
  Trade.trans
    (cbor_array_owned y (Array?.v (Ghost.reveal xh)))
    (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml (Array?.v (Ghost.reveal xh)))
    (cbor_match pm x (Ghost.reveal xh) **
     (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2));
  y
}
#pop-options

(* ================================================================ *)
(* cbor_array_slice                                                 *)
(*                                                                  *)
(* Zero-copy sub-range [i, j) of an input _Gen array [x], produced  *)
(* as a BORROWED VIEW (result match at 1.0R) together with a trade  *)
(* returning ownership of the source [x] and the four scratch refs. *)
(* TOTAL over [i], [j]: an empty or out-of-bounds range yields the  *)
(* empty array (source left untouched).                             *)
(* ================================================================ *)

ghost
fn cbor_match_share_t
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires cbor_match p x1 x2
ensures cbor_match (p /. 2.0R) x1 x2 ** cbor_match (p /. 2.0R) x1 x2
{
  MP.cbor_raw_share p x1 x2;
}

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
fn cbor_array_slice
  (pm: perm) (x: cbor_raw) (i j: U64.t)
  (r1 r2 r3 r4: R.ref (IT.mixed_list U64.t cbor_raw))
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
  (#w1 #w2 #w3 #w4: Ghost.erased (IT.mixed_list U64.t cbor_raw))
requires
  cbor_match pm x (Ghost.reveal xh) **
  R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4
returns res: cbor_raw
ensures exists* (yh: raw_data_item).
  cbor_match 1.0R res yh **
  Trade.trade
    (cbor_match 1.0R res yh)
    (cbor_match pm x (Ghost.reveal xh) **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
  pure (Array? yh /\ (Array?.v yh <: list raw_data_item) == array_slice_spec (Array?.v (Ghost.reveal xh)) i j /\
        raw_uint64_optimal (Array?.len yh))
{
  let yInit = cbor_array_init pm x r1 r2;
  let ml0 = cbor_array_owned_elim yInit;
  I.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item 1.0R ml0 (Array?.v (Ghost.reveal xh));
  let n = IT.mixed_list_length IO.u64_ops ml0;
  // Compute the in-bounds test via an explicit if-then-else rather than [&&]:
  // [n] is [mixed_list_length] (inline_for_extraction), so it inlines into a
  // large expression; keeping it inside a short-circuiting [&&] operand trips
  // KaRaMeL's Warning 20 (let-hoisting would change short-circuit semantics).
  // [a && b] is definitionally [if a then b else false], so this is proof-neutral.
  let in_bounds : bool = (if U64.lt i j then U64.lte j n else false);
  if in_bounds {
    let nn = j `U64.sub` i;
    Trade.rewrite_with_trade
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml0 (Array?.v (Ghost.reveal xh)))
      (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v n) 1.0R ml0 (Array?.v (Ghost.reveal xh)));
    let il' = I.mixed_list_narrow_n cbor_match IO.u64_ops parse_raw_data_item
                (CBOR.Pulse.Raw.EverParse.Format.jump_raw_data_item ())
                (Ghost.hide #nat 0) (Ghost.hide #nat (U64.v n)) 1.0R ml0 (Array?.v (Ghost.reveal xh)) i nn
                cbor_match_share_t cbor_match_gather_t;
    let ml_res =
      Append.mixed_list_wrap_scaled cbor_match IO.u64_ops parse_raw_data_item
        (1.0R /. 2.0R) il' (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)) r3 r4;
    let yH = cbor_array_of_ml ml_res #(Ghost.hide (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)));
    let res = cbor_array_finalize yH;
    unfold (cbor_array_finalized yH res (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)));
    with len. _;
    Trade.intro_trade
      (cbor_match 1.0R res (Array len (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn))))
      (cbor_match pm x (Ghost.reveal xh) **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
      (Trade.trade
         (cbor_match 1.0R res (Array len (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn))))
         (cbor_array_owned yH (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn))) **
       Trade.trade
         (cbor_array_owned yH (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)))
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res
            (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn))) **
       Trade.trade
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res
            (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)))
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item (1.0R /. 2.0R) il'
            (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)) **
          (exists* v3 v4. R.pts_to r3 v3 ** R.pts_to r4 v4)) **
       Trade.trade
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item (1.0R /. 2.0R) il'
            (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)))
         (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v n) 1.0R ml0 (Array?.v (Ghost.reveal xh))) **
       Trade.trade
         (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v n) 1.0R ml0 (Array?.v (Ghost.reveal xh)))
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml0 (Array?.v (Ghost.reveal xh))) **
       Trade.trade
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml0 (Array?.v (Ghost.reveal xh)))
         (cbor_array_owned yInit (Array?.v (Ghost.reveal xh))) **
       Trade.trade
         (cbor_array_owned yInit (Array?.v (Ghost.reveal xh)))
         (cbor_match pm x (Ghost.reveal xh) **
          (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)))
      fn _ {
        Trade.elim
          (cbor_match 1.0R res (Array len (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn))))
          (cbor_array_owned yH (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)));
        Trade.elim
          (cbor_array_owned yH (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)))
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res
             (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)));
        Trade.elim
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml_res
             (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)))
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item (1.0R /. 2.0R) il'
             (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)) **
           (exists* v3 v4. R.pts_to r3 v3 ** R.pts_to r4 v4));
        Trade.elim
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item (1.0R /. 2.0R) il'
             (I.list_narrow (Array?.v (Ghost.reveal xh)) (IO.u64_ops.v i - 0) (IO.u64_ops.v nn)))
          (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v n) 1.0R ml0 (Array?.v (Ghost.reveal xh)));
        Trade.elim
          (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 (U64.v n) 1.0R ml0 (Array?.v (Ghost.reveal xh)))
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml0 (Array?.v (Ghost.reveal xh)));
        Trade.elim
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml0 (Array?.v (Ghost.reveal xh)))
          (cbor_array_owned yInit (Array?.v (Ghost.reveal xh)));
        Trade.elim
          (cbor_array_owned yInit (Array?.v (Ghost.reveal xh)))
          (cbor_match pm x (Ghost.reveal xh) **
           (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2));
      };
    res
  } else {
    (* EMPTY / OUT-OF-BOUNDS: release the source borrow, return an empty array *)
    Trade.elim
      (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml0 (Array?.v (Ghost.reveal xh)))
      (cbor_array_owned yInit (Array?.v (Ghost.reveal xh)));
    Trade.elim
      (cbor_array_owned yInit (Array?.v (Ghost.reveal xh)))
      (cbor_match pm x (Ghost.reveal xh) **
       (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2));
    Append.mixed_list_empty cbor_match IO.u64_ops parse_raw_data_item 1.0R;
    let yE = cbor_array_of_ml (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw))
               #(Ghost.hide ([] <: list raw_data_item));
    let resE = cbor_array_finalize yE;
    unfold (cbor_array_finalized yE resE ([] <: list raw_data_item));
    with lenE. _;
    Trade.intro_trade
      (cbor_match 1.0R resE (Array lenE ([] <: list raw_data_item)))
      (cbor_match pm x (Ghost.reveal xh) **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
      ((cbor_match pm x (Ghost.reveal xh) **
        (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
       Trade.trade
         (cbor_match 1.0R resE (Array lenE ([] <: list raw_data_item)))
         (cbor_array_owned yE ([] <: list raw_data_item)) **
       Trade.trade
         (cbor_array_owned yE ([] <: list raw_data_item))
         (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
            (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) ([] <: list raw_data_item)))
      fn _ {
        Trade.elim
          (cbor_match 1.0R resE (Array lenE ([] <: list raw_data_item)))
          (cbor_array_owned yE ([] <: list raw_data_item));
        Trade.elim
          (cbor_array_owned yE ([] <: list raw_data_item))
          (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
             (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) ([] <: list raw_data_item));
        rewrite (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R
                   (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) ([] <: list raw_data_item))
          as (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 0 1.0R
                (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) ([] <: list raw_data_item));
        unfold (I.mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 0 1.0R
                  (IT.Base #U64.t #cbor_raw (IT.Empty #U64.t #cbor_raw)) ([] <: list raw_data_item));
        unfold (I.base_mixed_list_match_n cbor_match IO.u64_ops parse_raw_data_item 0 0 1.0R
                  (IT.Empty #U64.t #cbor_raw) ([] <: list raw_data_item));
      };
    resE
  }
}
#pop-options
