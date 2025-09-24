module CBOR.Pulse.Raw.EverParse.Iterator.C
#lang-pulse
open CBOR.Spec.Util
open CBOR.Pulse.Raw.Util
open CBOR.Pulse.Raw.Iterator.C
open Pulse.Lib.Slice open Pulse.Lib.Pervasives open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.ArrayPtr
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module LP = LowParse.Pulse.VCList
module LPC = LowParse.Pulse.C
module U64 = FStar.UInt64
module SliceIter = CBOR.Pulse.Raw.EverParse.Iterator

let cbor_raw_serialized_iterator_match
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: list elt_high)
: Tot slprop
= exists* l' . LPC.pts_to_serialized (LP.serialize_nlist c.glen s) c.s #(pm *. c.p) l' ** pure (
     SZ.v c.slen == Seq.length (LP.serialize (LP.serialize_nlist c.glen s) l') /\
     U64.v c.len <= c.glen /\
     l == fst (List.Tot.splitAt (U64.v c.len) l')
  )

inline_for_extraction
fn cbor_raw_serialized_iterator_match_unfold
  (#elt_high: Type0)
  (#k: Ghost.erased LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p)
  (sq: squash ((Ghost.reveal k).parser_kind_subkind == Some LP.ParserStrong))
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: Ghost.erased (list elt_high))
requires
  cbor_raw_serialized_iterator_match s pm c l
returns res: SliceIter.cbor_raw_serialized_iterator
ensures
  SliceIter.cbor_raw_serialized_iterator_match s pm res l **
  Trade.trade
    (SliceIter.cbor_raw_serialized_iterator_match s pm res l)
    (cbor_raw_serialized_iterator_match s pm c l)
{
  unfold (cbor_raw_serialized_iterator_match s pm c l);
  with l' . assert (LPC.pts_to_serialized (LP.serialize_nlist c.glen s) c.s #(pm *. c.p) l');
  intro
    (Trade.trade
      (LPC.pts_to_serialized (LP.serialize_nlist c.glen s) c.s #(pm *. c.p) l')
      (cbor_raw_serialized_iterator_match s pm c l)
    )
    fn _ {
      fold (cbor_raw_serialized_iterator_match s pm c l)
    };
  let cs = LPC.pts_to_serialized_arrayptr_to_slice
    #(LP.parse_nlist_kind c.glen k) #(LP.nlist c.glen elt_high) #(coerce_eq () (LP.parse_nlist c.glen p))
    (coerce_eq () (LP.serialize_nlist c.glen s <: LP.serializer (LP.parse_nlist c.glen p)))
    c.s c.slen;
  Trade.trans _ _ (cbor_raw_serialized_iterator_match s pm c l);
  let res : SliceIter.cbor_raw_serialized_iterator = {
    s = cs;
    p = c.p /. 2.0R;
    glen = c.glen;
    len = c.len;
  };
  SliceIter.cbor_raw_serialized_iterator_fold_with_perm s c.glen _ _ l' res pm l;
  Trade.trans _ _ (cbor_raw_serialized_iterator_match s pm c l);
  res
}

inline_for_extraction
fn cbor_raw_serialized_iterator_match_fold
  (#elt_high: Type0)
  (#k: Ghost.erased LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p)
  (sq: squash ((Ghost.reveal k).parser_kind_subkind == Some LP.ParserStrong))
  (pm: perm)
  (c: SliceIter.cbor_raw_serialized_iterator)
  (l: Ghost.erased (list elt_high))
requires
  SliceIter.cbor_raw_serialized_iterator_match s pm c l
returns res: cbor_raw_serialized_iterator
ensures
  cbor_raw_serialized_iterator_match s pm res l **
  Trade.trade
    (cbor_raw_serialized_iterator_match s pm res l)
    (SliceIter.cbor_raw_serialized_iterator_match s pm c l)
{
  SliceIter.cbor_raw_serialized_iterator_unfold s pm c l;
  with l' . assert (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l');
  LP.pts_to_serialized_length (LP.serialize_nlist (c.glen) s) c.s;
  let a = LPC.pts_to_serialized_slice_to_arrayptr #(LP.parse_nlist_kind c.glen k) #(LP.nlist c.glen elt_high) #(coerce_eq () (LP.parse_nlist c.glen p))
    (coerce_eq () (LP.serialize_nlist c.glen s <: LP.serializer (LP.parse_nlist c.glen p)))
    c.s;
  Trade.trans _ _ (SliceIter.cbor_raw_serialized_iterator_match s pm c l);
  LPC.pts_to_serialized_share
    (LP.serialize_nlist (c.glen) s) a;
  let res : cbor_raw_serialized_iterator = {
    s = a;
    slen = S.len c.s;
    p = c.p /. 2.0R;
    glen = c.glen;
    len = c.len;
  };
  rewrite
    (LPC.pts_to_serialized (LP.serialize_nlist c.glen s) a #((pm *. c.p) /. 2.0R) l')
    as (LPC.pts_to_serialized (LP.serialize_nlist c.glen s) res.s #(pm *. res.p) l');
  fold (cbor_raw_serialized_iterator_match s pm res l);
  intro
    (Trade.trade
      (cbor_raw_serialized_iterator_match s pm res l)
      (LPC.pts_to_serialized (LP.serialize_nlist (c.glen) s) a #(pm *. c.p) l')
    )
    #(LPC.pts_to_serialized (LP.serialize_nlist c.glen s) a #((pm *. c.p) /. 2.0R) l')
    fn _ {
      unfold (cbor_raw_serialized_iterator_match s pm res l);
      with pm2 l2 . rewrite (LPC.pts_to_serialized (LP.serialize_nlist (c.glen) s) res.s #pm2 l2)
        as (LPC.pts_to_serialized (LP.serialize_nlist (c.glen) s) a #pm2 l2);
      LPC.pts_to_serialized_gather
        (LP.serialize_nlist (c.glen) s) a;
      ()
    };
  Trade.trans _ _ (SliceIter.cbor_raw_serialized_iterator_match s pm c l);
  res
}
