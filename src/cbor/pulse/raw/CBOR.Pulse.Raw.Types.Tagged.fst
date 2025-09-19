module CBOR.Pulse.Raw.Types.Tagged
#lang-pulse
module Spec = CBOR.Spec.Raw.Format
open Pulse.Lib.Pervasives
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

noeq
type cbor_tagged ([@@@strictly_positive] cbor_t: Type0) : Type0 = {
  cbor_tagged_tag: Spec.raw_uint64;
  cbor_tagged_ptr: R.ref cbor_t;
  cbor_tagged_ptr_perm: perm;
  cbor_tagged_elem_perm: perm;
}

let cbor_tagged_match
  (#cbor_t: Type0)
  (pm: perm)
  (x: cbor_tagged cbor_t)
  (y: Spec.raw_data_item)
  (item_match: perm -> cbor_t -> (z: Spec.raw_data_item {z << y}) -> slprop)
: Tot slprop
= exists* s z . R.pts_to x.cbor_tagged_ptr #(pm *. x.cbor_tagged_ptr_perm) s **
  item_match (pm *. x.cbor_tagged_elem_perm) s z **
  pure (
    Spec.Tagged? y /\
    Spec.Tagged?.tag y == x.cbor_tagged_tag /\
    Spec.Tagged?.v y == z
  )

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_tagged_match_intro
  (#cbor_t: Type0)
  (tag: Spec.raw_uint64)
  (ptr: R.ref cbor_t)
  (#pm1: perm)
  (#pm2: perm)
  (#vptr: cbor_t)
  (y: Ghost.erased Spec.raw_data_item)
  (z: Ghost.erased Spec.raw_data_item { Ghost.reveal z << Ghost.reveal y})
  (item_match: perm -> cbor_t -> (z: Spec.raw_data_item {z << Ghost.reveal y}) -> slprop)
requires
  R.pts_to ptr #pm1 vptr **
  item_match pm2 vptr z **
  pure (
    Ghost.reveal y == Spec.Tagged tag z
  )
returns res: cbor_tagged cbor_t
ensures
  cbor_tagged_match 1.0R res y item_match **
  Trade.trade
    (cbor_tagged_match 1.0R res y item_match)
    (R.pts_to ptr #pm1 vptr **
      item_match pm2 vptr z)
{
  R.share ptr;
  let res = {
    cbor_tagged_tag = tag;
    cbor_tagged_ptr = ptr;
    cbor_tagged_ptr_perm = (pm1 /. 2.0R);
    cbor_tagged_elem_perm = pm2;
  };
  rewrite (R.pts_to ptr #(pm1 /. 2.0R) vptr) as (R.pts_to res.cbor_tagged_ptr #(1.0R *. res.cbor_tagged_ptr_perm)) vptr;
  rewrite (item_match pm2 vptr z) as (item_match (1.0R *. res.cbor_tagged_elem_perm) vptr z);
  fold (cbor_tagged_match 1.0R res y item_match);
  intro
    (Trade.trade
      (cbor_tagged_match 1.0R res y item_match)
      (R.pts_to ptr #pm1 vptr **
        item_match pm2 vptr z)
    )
    #(R.pts_to ptr #(pm1 /. 2.0R) vptr)
    fn _ {
      unfold (cbor_tagged_match 1.0R res y item_match);
      with vptr' z' . assert (R.pts_to res.cbor_tagged_ptr #(1.0R *. res.cbor_tagged_ptr_perm) vptr' ** item_match (1.0R *. res.cbor_tagged_elem_perm) vptr' z');
      rewrite (R.pts_to res.cbor_tagged_ptr #(1.0R *. res.cbor_tagged_ptr_perm) vptr') as (R.pts_to ptr #(pm1 /. 2.0R) vptr');
      R.gather ptr #vptr #vptr';
      rewrite (item_match (1.0R *. res.cbor_tagged_elem_perm) vptr' z') as (item_match pm2 vptr z);
    };
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_tagged_match_get_tag
  (#cbor_t: Type0)
  (pm: perm)
  (x: cbor_tagged cbor_t)
  (y: Spec.raw_data_item)
  (item_match: perm -> cbor_t -> (z: Spec.raw_data_item {z << y}) -> slprop)
requires
  cbor_tagged_match pm x y item_match
returns res: Spec.raw_uint64
ensures
  cbor_tagged_match pm x y item_match **
  pure (Spec.Tagged? y /\
    res == Spec.Tagged?.tag y
  )
{
  unfold (cbor_tagged_match pm x y);
  fold (cbor_tagged_match pm x y);
  x.cbor_tagged_tag
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_tagged_match_get_payload
  (#cbor_t: Type0)
  (pm: perm)
  (x: cbor_tagged cbor_t)
  (y: Spec.raw_data_item)
  (item_match: perm -> cbor_t -> (z: Spec.raw_data_item {z << y}) -> slprop)
requires
  cbor_tagged_match pm x y item_match
returns res: cbor_t
ensures exists* pm' z .
  item_match pm' res z **
  Trade.trade
    (item_match pm' res z)
    (cbor_tagged_match pm x y item_match) **
  pure (Spec.Tagged? y /\
    Spec.Tagged?.v y == z
  )
{
  unfold (cbor_tagged_match pm x y item_match);
  let res = !(x.cbor_tagged_ptr);
  with z . assert (item_match (pm *. x.cbor_tagged_elem_perm) res z);
  intro
    (Trade.trade
      (item_match (pm *. x.cbor_tagged_elem_perm) res z)
      (cbor_tagged_match pm x y item_match)
    )
    #(R.pts_to x.cbor_tagged_ptr #(pm *. x.cbor_tagged_ptr_perm) res)
    fn _ {
      fold (cbor_tagged_match pm x y item_match);
    };
  res
}
