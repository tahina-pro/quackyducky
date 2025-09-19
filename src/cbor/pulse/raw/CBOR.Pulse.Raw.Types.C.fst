module CBOR.Pulse.Raw.Types.C
#lang-pulse
include CBOR.Pulse.Raw.Types.Gen
module A = Pulse.Lib.ArrayPtr
module Spec = CBOR.Spec.Raw.Format
open Pulse.Lib.Pervasives
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

noeq
type cbor_string = {
  cbor_string_type : Spec.major_type_byte_string_or_text_string;
  cbor_string_ptr: A.ptr U8.t;
  cbor_string_len: Spec.raw_uint64;
  cbor_string_perm: perm;
}

let cbor_string_match
  (pm: perm)
  (x: cbor_string)
  (y: Spec.raw_data_item)
: Tot slprop
= exists* v . A.pts_to x.cbor_string_ptr #(pm *. x.cbor_string_perm) v **
  pure (
    Spec.String? y /\
    x.cbor_string_type = Spec.String?.typ y /\
    x.cbor_string_len = Spec.String?.len y /\
    v == Spec.String?.v y
  )

fn cbor_string_match_intro
  (typ: Spec.major_type_byte_string_or_text_string)
  (len: Spec.raw_uint64)
  (a: A.ptr U8.t)
  (#pm: perm)
  (#y: Ghost.erased (Seq.seq U8.t))
requires
  A.pts_to a #pm y **
  pure (Seq.length y == U64.v len.value /\
    (typ == Spec.cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct y)
  )
returns res: cbor_string
ensures exists* v .
  cbor_string_match 1.0R res v **
  Trade.trade
    (cbor_string_match 1.0R res v)
    (A.pts_to a #pm y) **
  pure (
    Spec.String? v /\
    Spec.String?.typ v == typ /\
    Spec.String?.len v == len /\
    Ghost.reveal y == Spec.String?.v v
  )
{
  let res = {
    cbor_string_type = typ;
    cbor_string_len = len;
    cbor_string_ptr = a;
    cbor_string_perm = pm;
  };
  let y' : Ghost.erased (Seq.lseq U8.t (U64.v len.value)) = Ghost.hide (Ghost.reveal y);
  let vres : Ghost.erased Spec.raw_data_item = Ghost.hide (Spec.String typ len y');
  Trade.rewrite_with_trade
    (A.pts_to a #pm y)
    (A.pts_to res.cbor_string_ptr #(1.0R *. res.cbor_string_perm) y);
  fold (cbor_string_match 1.0R res vres);
  intro
    (Trade.trade
      (cbor_string_match 1.0R res vres)
      (A.pts_to res.cbor_string_ptr #(1.0R *. res.cbor_string_perm) y)
    )
    #_
    fn () {
      unfold (cbor_string_match 1.0R res vres);
    };
  Trade.trans _ _ (A.pts_to a #pm y);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_string_match_intro_slice (_: unit) :
  cbor_string_match_intro_t #_ cbor_string_match
=
  (typ: Spec.major_type_byte_string_or_text_string)
  (len: Spec.raw_uint64)
  (x: S.slice U8.t)
  (#pm: perm)
  (#y: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len x;
  let a = S.slice_to_arrayptr_intro_trade x;
  let res = cbor_string_match_intro typ len a;
  Trade.trans _ _ (S.pts_to x #pm y);
  res
}

ghost
fn cbor_string_match_prop
  (x: cbor_string)
  (#pm: perm)
  (#y: Ghost.erased Spec.raw_data_item)
requires
  cbor_string_match pm x y
ensures
  cbor_string_match pm x y **
  pure (
    Spec.String? y /\
    Spec.String?.typ y == x.cbor_string_type /\
    Spec.String?.len y == x.cbor_string_len
  )
{
  unfold (cbor_string_match pm x y);
  fold (cbor_string_match pm x y);
}

fn cbor_string_match_get_typ (_: unit) : cbor_string_match_get_typ_t #_ cbor_string_match
=
  (x: cbor_string)
  (#pm: perm)
  (#y: Ghost.erased Spec.raw_data_item)
{
  cbor_string_match_prop x;
  x.cbor_string_type
}

fn cbor_string_match_get_len (_: unit) : cbor_string_match_get_len_t #_ cbor_string_match
=
  (x: cbor_string)
  (#pm: perm)
  (#y: Ghost.erased Spec.raw_data_item)
{
  cbor_string_match_prop x;
  x.cbor_string_len
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_string_match_elim (_: unit) : cbor_string_match_elim_t #_ cbor_string_match
=
  (x: cbor_string)
  (#pm: perm)
  (#y: Ghost.erased Spec.raw_data_item)
{
  unfold (cbor_string_match pm x y);
  with v . assert (A.pts_to x.cbor_string_ptr #(pm *. x.cbor_string_perm) v);
  let res = S.arrayptr_to_slice_intro_trade x.cbor_string_ptr (SZ.uint64_to_sizet x.cbor_string_len.value);
  intro
    (Trade.trade
      (S.pts_to res #(pm *. x.cbor_string_perm) v)
      (cbor_string_match pm x y)
    )
    #(Trade.trade
      (S.pts_to res #(pm *. x.cbor_string_perm) v)
      (A.pts_to x.cbor_string_ptr #(pm *. x.cbor_string_perm) v)
    )
    fn () {
      Trade.elim _ _;
      fold (cbor_string_match pm x y)
    };
  res
}

noeq
type cbor_array_or_map
  ([@@@strictly_positive] item: Type0)
= {
  cbor_array_or_map_ptr: A.ptr item;
  cbor_array_or_map_len: Spec.raw_uint64;
  cbor_array_or_map_ptr_perm: perm;
  cbor_array_or_map_elem_perm: perm;
}

module SM = Pulse.Lib.SeqMatch.Util

let cbor_array_or_map_match
  (#item: Type0)
  (#item_v: Type0)
  (pm: perm)
  (x: cbor_array_or_map item)
  (len: Spec.raw_uint64)
  (y: list item_v)
  (item_match: perm -> item -> (v: item_v {v << y}) -> slprop)
: Tot slprop
= exists* s .
    A.pts_to x.cbor_array_or_map_ptr #(pm *. x.cbor_array_or_map_ptr_perm) s **
    SM.seq_list_match s y (item_match (pm *. x.cbor_array_or_map_elem_perm)) **
    pure (List.Tot.length y == U64.v len.value /\
      len == x.cbor_array_or_map_len
    )

ghost fn cbor_array_or_map_match_length
  (#item: Type0)
  (#item_v: Type0)
  (pm: perm)
  (x: cbor_array_or_map item)
  (len: Spec.raw_uint64)
  (y: list item_v)
  (item_match: perm -> item -> (v: item_v {v << y}) -> slprop)
requires
  cbor_array_or_map_match pm x len y item_match
ensures
  cbor_array_or_map_match pm x len y item_match **
  pure (
    List.Tot.length y == U64.v len.value
  )
{
  unfold (cbor_array_or_map_match pm x len y item_match);
  fold (cbor_array_or_map_match pm x len y item_match)
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_array_or_map_match_len
  (#item: Type0)
  (#item_v: Type0)
  (pm: perm)
  (x: cbor_array_or_map item)
  (glen: Ghost.erased Spec.raw_uint64)
  (y: Ghost.erased (list item_v))
  (item_match: perm -> item -> (v: item_v {v << Ghost.reveal y}) -> slprop)
requires
  cbor_array_or_map_match pm x glen y item_match
returns len: Spec.raw_uint64
ensures
  cbor_array_or_map_match pm x glen y item_match **
  pure (
    List.Tot.length y == U64.v (Ghost.reveal glen).value /\
    Ghost.reveal glen == len
  )
{
  unfold (cbor_array_or_map_match pm x glen y item_match);
  fold (cbor_array_or_map_match pm x glen y item_match);
  x.cbor_array_or_map_len
}

ghost fn rec seq_list_match_length_gen
  (#t1 #t2: Type0)
  (c: Seq.seq t1)
  (l: list t2)
  (p: t1 -> (x: t2 {x << l}) -> slprop)
requires
    (SM.seq_list_match c l p)
ensures
    (SM.seq_list_match c l p ** pure (
      Seq.length c == List.Tot.length l
    ))
decreases l
{
  if Nil? l {
    SM.seq_list_match_nil_elim c l p;
    SM.seq_list_match_nil_intro c l p
  } else {
    let h = SM.seq_list_match_cons_elim c l p;
    Seq.cons_head_tail c;
    let l' = (List.Tot.tl l);
    seq_list_match_length_gen (Seq.tail c) l' (p <: (t1 -> (x: t2 {x << l'}) -> slprop));
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd l) (Seq.tail c) l' p;
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd l :: List.Tot.tl l) p)
      as (SM.seq_list_match c l p)
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_array_or_map_match_intro
  (#item: Type)
  (#item_v: Type)
  (len: Spec.raw_uint64)
  (a: A.ptr item)
  (#pm1: perm)
  (#va: Ghost.erased (Seq.seq item))
  (pm2: perm)
  (l: Ghost.erased (list item_v))
  (item_match: perm -> item -> (v: item_v {v << Ghost.reveal l}) -> slprop)
requires
  A.pts_to a #pm1 va **
  SM.seq_list_match va l (item_match pm2) **
  pure (List.Tot.length l == U64.v len.value)
returns res: cbor_array_or_map item
ensures
  cbor_array_or_map_match 1.0R res len l item_match **
  Trade.trade
    (cbor_array_or_map_match 1.0R res len l item_match)
    (
      A.pts_to a #pm1 va **
      SM.seq_list_match va l (item_match pm2)
    ) **
  pure (
    len == res.cbor_array_or_map_len
  )
{
  seq_list_match_length_gen va l (item_match pm2);
  A.share a;
  let res = {
    cbor_array_or_map_ptr = a;
    cbor_array_or_map_len = len;
    cbor_array_or_map_ptr_perm = pm1 /. 2.0R;
    cbor_array_or_map_elem_perm = pm2;
  };
  rewrite (A.pts_to a #(pm1 /. 2.0R) va) as (A.pts_to res.cbor_array_or_map_ptr #(1.0R *. res.cbor_array_or_map_ptr_perm) va);
  rewrite (SM.seq_list_match va l (item_match pm2)) as (SM.seq_list_match va l (item_match (1.0R *. res.cbor_array_or_map_elem_perm)));
  fold (cbor_array_or_map_match 1.0R res len l item_match);
  intro
    (Trade.trade
      (cbor_array_or_map_match 1.0R res len l item_match)
      (
        A.pts_to a #pm1 va **
        SM.seq_list_match va l (item_match pm2)
      )
    )
    #(A.pts_to a #(pm1 /. 2.0R) va)
    fn _ {
      unfold (cbor_array_or_map_match 1.0R res len l item_match);
      with va' . assert (A.pts_to res.cbor_array_or_map_ptr #(1.0R *. res.cbor_array_or_map_ptr_perm) va');
      rewrite (A.pts_to res.cbor_array_or_map_ptr #(1.0R *. res.cbor_array_or_map_ptr_perm) va') as (A.pts_to a #(pm1 /. 2.0R) va');
      seq_list_match_length_gen va' l (item_match (1.0R *. res.cbor_array_or_map_elem_perm));
      A.gather a;
      rewrite (SM.seq_list_match va' l (item_match (1.0R *. res.cbor_array_or_map_elem_perm)))
        as (SM.seq_list_match va l (item_match pm2));    };
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_array_or_map_match_intro_slice
  (#item: Type)
  (#item_v: Type)
  (len: Spec.raw_uint64)
  (s: S.slice item)
  (#pm1: perm)
  (#va: Ghost.erased (Seq.seq item))
  (pm2: perm)
  (l: Ghost.erased (list item_v))
  (item_match: perm -> item -> (v: item_v {v << Ghost.reveal l}) -> slprop)
requires
  S.pts_to s #pm1 va **
  SM.seq_list_match va l (item_match pm2) **
  pure (List.Tot.length l == U64.v len.value)
returns res: cbor_array_or_map item
ensures
  cbor_array_or_map_match 1.0R res len l item_match **
  Trade.trade
    (cbor_array_or_map_match 1.0R res len l item_match)
    (
      S.pts_to s #pm1 va **
      SM.seq_list_match va l (item_match pm2)
    ) **
  pure (
    len == res.cbor_array_or_map_len
  )
{
  let a = S.slice_to_arrayptr_intro_trade s;
  let res = cbor_array_or_map_match_intro len a pm2 l item_match;
  Trade.trans_concl_l _ _ _ _;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_array_or_map_match_elim
  (#item: Type)
  (#item_v: Type)
  (x: cbor_array_or_map item)
  (#pm: perm)
  (#len: Ghost.erased Spec.raw_uint64)
  (#va: Ghost.erased (Seq.seq item))
  (l: Ghost.erased (list item_v))
  (item_match: perm -> item -> (v: item_v {v << Ghost.reveal l}) -> slprop)
requires
  cbor_array_or_map_match pm x len l item_match
returns res: S.slice item
ensures exists* pm1 va pm2 .
  S.pts_to res #pm1 va **
  SM.seq_list_match va l (item_match pm2) **
  Trade.trade
    (S.pts_to res #pm1 va ** SM.seq_list_match va l (item_match pm2))
    (cbor_array_or_map_match pm x len l item_match)
{
  unfold (cbor_array_or_map_match pm x len l item_match);
  with va . assert (A.pts_to x.cbor_array_or_map_ptr #(pm *. x.cbor_array_or_map_ptr_perm) va);
  intro
    (Trade.trade
      (A.pts_to x.cbor_array_or_map_ptr #(pm *. x.cbor_array_or_map_ptr_perm) va **
        SM.seq_list_match va l (item_match (pm *. x.cbor_array_or_map_elem_perm))
      )
      (cbor_array_or_map_match pm x len l item_match)
    )
    fn _ {
      fold (cbor_array_or_map_match pm x len l item_match)
    };
  assume (pure (SZ.fits_u64));
  seq_list_match_length_gen va l (item_match (pm *. x.cbor_array_or_map_elem_perm));
  let res = S.arrayptr_to_slice_intro_trade x.cbor_array_or_map_ptr (SZ.uint64_to_sizet x.cbor_array_or_map_len.value);
  Trade.trans_hyp_l _ _ _ _;
  res
}
