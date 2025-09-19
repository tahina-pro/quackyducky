module LowParse.Pulse.C
#lang-pulse

module LPS = LowParse.Pulse.Base
module S = Pulse.Lib.Slice.Util
module A = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

include LowParse.Spec.Base
open FStar.Tactics.V2
open Pulse.Lib.Pervasives

let pts_to_serialized
  (#k: parser_kind) (#t: Type) (#p: parser k t)
  (s: serializer p)
  ([@@@mkey]input: A.ptr byte)
  (#[exact (`1.0R)] pm: perm)
  (v: t)
: slprop =
  A.pts_to input #pm (bare_serialize s v)

inline_for_extraction
fn pts_to_serialized_arrayptr_to_slice
  (#k: Ghost.erased parser_kind) (#t: Type0) (#p: parser k t)
  (s: serializer p)
  (input: A.ptr byte)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased t)
requires
  pts_to_serialized s input #pm v **
  pure (SZ.v len == Seq.length (bare_serialize s v))
returns res: S.slice byte
ensures
  LPS.pts_to_serialized s res #pm v **
  Trade.trade
    (LPS.pts_to_serialized s res #pm v)
    (pts_to_serialized s input #pm v)
{
  unfold (pts_to_serialized s input #pm v);
  let res = S.arrayptr_to_slice_intro_trade input len;
  LPS.pts_to_serialized_intro_trade s res v;
  Trade.trans _ _ (pts_to_serialized s input #pm v);
  res
}

inline_for_extraction
fn pts_to_serialized_slice_to_arrayptr
  (#k: Ghost.erased parser_kind) (#t: Type0) (#p: parser k t)
  (s: serializer p)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
requires
  LPS.pts_to_serialized s input #pm v
returns res: A.ptr byte
ensures
  pts_to_serialized s res #pm v **
  Trade.trade
    (pts_to_serialized s res #pm v)
    (LPS.pts_to_serialized s input #pm v)
{
  LPS.pts_to_serialized_elim_trade s input;
  let res = S.slice_to_arrayptr_intro_trade input;
  Trade.trans _ _ (LPS.pts_to_serialized s input #pm v);
  fold (pts_to_serialized s res #pm v);
  res
}

ghost
fn pts_to_serialized_share
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: A.ptr byte) (#pm: perm) (#v: t)
  requires (pts_to_serialized s input #pm v)
  ensures (pts_to_serialized s input #(pm /. 2.0R) v ** pts_to_serialized s input #(pm /. 2.0R) v)
{
  unfold (pts_to_serialized s input #pm v);
  A.share input;
  fold (pts_to_serialized s input #(pm /. 2.0R) v);
  fold (pts_to_serialized s input #(pm /. 2.0R) v)
}

[@@allow_ambiguous]
ghost
fn pts_to_serialized_gather
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: A.ptr byte) (#pm0 #pm1: perm) (#v0 #v1: t)
  requires (pts_to_serialized s input #pm0 v0 ** pts_to_serialized s input #pm1 v1 **
  pure (Seq.length (serialize s v0) == Seq.length (serialize s v1)))
  ensures (pts_to_serialized s input #(pm0 +. pm1) v0 ** pure (v0 == v1))
{
  unfold (pts_to_serialized s input #pm0 v0);
  unfold (pts_to_serialized s input #pm1 v1);
  A.gather input;
  serializer_injective _ s v0 v1;
  fold (pts_to_serialized s input #(pm0 +. pm1) v0)
}

inline_for_extraction
fn pts_to_serialized_copy
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (src: A.ptr byte)
  (len: SZ.t)
  (#psrc: perm)
  (#vsrc: Ghost.erased t)
  (dst: A.ptr byte)
requires
  exists* vdst . pts_to dst vdst ** pts_to_serialized s src #psrc vsrc **
    pure (
      Seq.length (bare_serialize s vsrc) == SZ.v len /\
      Seq.length vdst == SZ.v len
    )
ensures
  pts_to_serialized s src #psrc vsrc **
  pts_to_serialized s dst vsrc
{
  unfold (pts_to_serialized s src #psrc vsrc);
  A.memcpy src 0sz dst 0sz len;
  fold (pts_to_serialized s src #psrc vsrc);
  with vdst . assert (pts_to dst vdst);
  assert (pure (Seq.length vdst == SZ.v len));
  assert (pure (Seq.equal (Ghost.reveal vdst <: Seq.seq byte) (bare_serialize s vsrc)));
  fold (pts_to_serialized s dst vsrc);
}
