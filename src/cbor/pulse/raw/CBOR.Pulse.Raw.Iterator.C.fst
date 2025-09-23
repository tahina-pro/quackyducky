module CBOR.Pulse.Raw.Iterator.C
#lang-pulse
open CBOR.Pulse.Raw.Util
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch.Util
module S = Pulse.Lib.Slice.Util
module A = Pulse.Lib.ArrayPtr
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module SliceIter = CBOR.Pulse.Raw.Iterator

noeq
type cbor_raw_arrayptr_iterator (elt: Type0) = {
  s: A.ptr elt;
  len: U64.t;
  slice_perm: perm;
  payload_perm: perm;
}

let cbor_raw_arrayptr_iterator_match
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pm: perm)
  (c: cbor_raw_arrayptr_iterator elt_low)
  (l: list elt_high)
: Tot slprop
= exists* sq .
     A.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm)) **
     pure (
       U64.v c.len == List.Tot.length l
     )

ghost
fn cbor_raw_arrayptr_iterator_match_unfold
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pm: perm)
  (c: cbor_raw_arrayptr_iterator elt_low)
  (l: list elt_high)
requires
  cbor_raw_arrayptr_iterator_match elt_match pm c l
ensures
  exists* sq .
     pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm)) **
     trade
       (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
       )
       (cbor_raw_arrayptr_iterator_match elt_match pm c l) **
    pure (
      List.Tot.length l == U64.v c.len
    )
{
  unfold (cbor_raw_arrayptr_iterator_match elt_match pm c l);
  with sq . assert (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
  );
  intro
    (Trade.trade
      (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
        PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
      )
      (cbor_raw_arrayptr_iterator_match elt_match pm c l)
    )
    #emp
    fn _
  {
    fold (cbor_raw_arrayptr_iterator_match elt_match pm c l);
  };
}

#restart-solver

ghost
fn cbor_raw_arrayptr_iterator_match_fold
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (a: A.ptr elt_low)
  (pm1: perm)
  (sq: Seq.seq elt_low)
  (pm2: perm)
  (l: list elt_high)
  (c': cbor_raw_arrayptr_iterator elt_low)
  (pm: perm)
requires
  pts_to a #pm1 sq **
  PM.seq_list_match sq l (elt_match pm2) **
  pure (
    c'.s == a /\
    c'.slice_perm == (pm1 /. 2.0R) /. pm /\
    c'.payload_perm == pm2 /. pm /\
    List.Tot.length l == U64.v c'.len
  )
ensures
  cbor_raw_arrayptr_iterator_match elt_match pm c' l **
     trade
       (cbor_raw_arrayptr_iterator_match elt_match pm c' l)
       (pts_to a #pm1 sq **
         PM.seq_list_match sq l (elt_match pm2)
       )
{
  PM.seq_list_match_length (elt_match pm2) sq l;
  A.share a;
//  half_mul pm c.slice_perm;
  with _pm _sq .
    rewrite pts_to a #_pm _sq as pts_to c'.s #(pm *. c'.slice_perm) sq;
  rewrite (PM.seq_list_match sq l (elt_match pm2))
    as (PM.seq_list_match sq l (elt_match (pm *. c'.payload_perm)));
  fold (cbor_raw_arrayptr_iterator_match elt_match pm c' l);
  intro
    (Trade.trade
      (cbor_raw_arrayptr_iterator_match elt_match pm c' l)
      (pts_to a #pm1 sq **
         PM.seq_list_match sq l (elt_match pm2)
      )
    )
    #(pts_to a #(pm1 /. 2.0R) sq)
    fn _
  {
    unfold (cbor_raw_arrayptr_iterator_match elt_match pm c' l);
    with _pm1 _pm2 _sq. assert (A.pts_to c'.s #_pm1 _sq ** PM.seq_list_match _sq l (elt_match _pm2));
    assert (pure (_pm2 == pm *. c'.payload_perm)); // FIXME: WHY WHY WHY?
    assert (pure (pm2 == c'.payload_perm *. pm)); // FIXME: WHY WHY WHY?
    SliceIter.perm_mul_comm pm c'.payload_perm;
    assert (pure (pm2 == pm *. c'.payload_perm)); // FIXME: WHY WHY WHY?
    assert (pure (_pm2 == pm *. c'.payload_perm)); // FIXME: WHY WHY WHY?
    PM.seq_list_match_length (elt_match _pm2) _sq l;
    rewrite (A.pts_to c'.s #_pm1 _sq) as A.pts_to a #_pm1 _sq;
    A.gather a;
    rewrite PM.seq_list_match #elt_low #elt_high _sq l (elt_match _pm2)
      as PM.seq_list_match #elt_low #elt_high sq l (elt_match pm2);
    assert (pure (perm_mul pm (Mkcbor_raw_arrayptr_iterator?.slice_perm #elt_low c') == pm1 /. 2.0R));
    assert (pure (pm1 /. 2.0R +. pm1 /. 2.0R == pm1));
    ();
  };
}

#restart-solver

inline_for_extraction
fn cbor_raw_arrayptr_iterator_match_intro
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pm: perm)
  (c: SliceIter.cbor_raw_slice_iterator elt_low)
  (l: Ghost.erased (list elt_high))
requires
  SliceIter.cbor_raw_slice_iterator_match elt_match pm c l
returns res: cbor_raw_arrayptr_iterator elt_low
ensures
  cbor_raw_arrayptr_iterator_match elt_match pm res l **
  Trade.trade
    (cbor_raw_arrayptr_iterator_match elt_match pm res l)
    (SliceIter.cbor_raw_slice_iterator_match elt_match pm c l)
{
  SliceIter.cbor_raw_slice_iterator_match_unfold elt_match pm c l;
  with _pm1 sq _pm2 . assert (
    S.pts_to c.s #_pm1 sq **
    PM.seq_list_match sq l (elt_match _pm2)
  );
  S.pts_to_len c.s;
  PM.seq_list_match_length (elt_match _pm2) sq l;
  assume (pure (SZ.fits_u64));
  let a = S.slice_to_arrayptr_intro_trade c.s;
  Trade.trans_hyp_l _ _ _ _;
  let res : cbor_raw_arrayptr_iterator elt_low = {
    s = a;
    slice_perm = (_pm1 /. 2.0R) /. pm;
    payload_perm = _pm2 /. pm;
    len = SZ.sizet_to_uint64 (S.len c.s);
  };
  cbor_raw_arrayptr_iterator_match_fold elt_match a _pm1 sq _pm2 l res pm;
  Trade.trans (cbor_raw_arrayptr_iterator_match elt_match pm res l) _ _;
  res
}

inline_for_extraction
fn cbor_raw_arrayptr_iterator_match_elim
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pm: perm)
  (c: cbor_raw_arrayptr_iterator elt_low)
  (l: Ghost.erased (list elt_high))
requires
  cbor_raw_arrayptr_iterator_match elt_match pm c l 
returns res: SliceIter.cbor_raw_slice_iterator elt_low
ensures
  SliceIter.cbor_raw_slice_iterator_match elt_match pm res l **
  Trade.trade
    (SliceIter.cbor_raw_slice_iterator_match elt_match pm res l)
    (cbor_raw_arrayptr_iterator_match elt_match pm c l)
{
  cbor_raw_arrayptr_iterator_match_unfold elt_match pm c l;
  with _pm1 sq _pm2 . assert (
    A.pts_to c.s #_pm1 sq **
    PM.seq_list_match sq l (elt_match _pm2)
  );
  PM.seq_list_match_length (elt_match _pm2) sq l;
  assume (pure (SZ.fits_u64));
  let a = S.arrayptr_to_slice_intro_trade c.s (SZ.uint64_to_sizet c.len);
  S.pts_to_len a;
  Trade.trans_hyp_l _ _ _ _;
  let res : SliceIter.cbor_raw_slice_iterator elt_low = {
    s = a;
    sq = ();
    slice_perm = (_pm1 /. 2.0R) /. pm;
    payload_perm = _pm2 /. pm;
  };
  SliceIter.cbor_raw_slice_iterator_match_fold_gen elt_match a _pm1 sq _pm2 l res pm;
  Trade.trans (SliceIter.cbor_raw_slice_iterator_match elt_match pm res l) _ _;
  res
}
