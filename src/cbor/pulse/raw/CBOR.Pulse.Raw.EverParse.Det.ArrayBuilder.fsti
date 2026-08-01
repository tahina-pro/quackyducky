module CBOR.Pulse.Raw.EverParse.Det.ArrayBuilder
#lang-pulse

(* Layer-2 (raw/) interface of the deterministic-CBOR structural array builder.

   The implementation ([.fst]) lives in [everparse/] and is written against the
   lowparse [IT.mixed_list cbor_raw] type; it [friend]s [CBOR.Pulse.API.Det.Type]
   (and [CBOR.Pulse.Raw.Format.MixedList]) so that, inside it,
     [cbor_det_array_append_cell_t == IT.mixed_list cbor_raw]  and
     [cbor_det_t == cbor_raw],
   which is how the concrete [.fst] realizes this abstract-typed interface.

   This interface deliberately mentions NO lowparse type, so that raw/ clients
   (notably [CBOR.Pulse.API.Det.C]) can consume it. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Type
open CBOR.Pulse.API.Det.Type

module Spec = CBOR.Spec.API.Format
module Det = CBOR.Pulse.API.Det.Common
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module L = FStar.List.Tot

(* Ownership of a structurally-built deterministic-CBOR array whose
   spec-level element list is [l]. *)
val cbor_det_array_owned (x: cbor_mixed_list_array) (l: list Spec.cbor) : slprop

(* Empty array. *)
inline_for_extraction
fn cbor_det_array_empty (_: unit)
requires emp
returns res: cbor_mixed_list_array
ensures cbor_det_array_owned res []

(* Singleton array from a single element (plus a scratch reference [ry]). *)
inline_for_extraction
fn cbor_det_array_singleton
  (x: cbor_det_t) (ry: R.ref cbor_det_t)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_det_t)
requires
  Det.cbor_det_match pm x v ** R.pts_to ry w0
returns res: cbor_mixed_list_array
ensures
  cbor_det_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_det_array_owned res [Ghost.reveal v])
    (Det.cbor_det_match pm x v ** (exists* w. R.pts_to ry w))

(* The length of an owned array fits in a u64. *)
ghost
fn cbor_det_array_owned_length_fits
  (x: cbor_mixed_list_array) (#l: Ghost.erased (list Spec.cbor))
requires cbor_det_array_owned x l
ensures cbor_det_array_owned x l ** pure (FStar.UInt.fits (L.length (Ghost.reveal l)) 64)

(* Append two owned arrays.

   NOTE (deviation): like the underlying raw [cbor_array_append], this requires
   [pure SZ.fits_u64] (the platform size_t is at least 64-bit): forming the
   underlying [Append] node needs [SZ.fits (len1 + len2)], only obtainable from
   [SZ.fits_u64] once the u64 sum is known not to overflow. *)
inline_for_extraction
fn cbor_det_array_append
  (x1 x2: cbor_mixed_list_array)
  (r_before r_after: R.ref cbor_det_array_append_cell_t)
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased cbor_det_array_append_cell_t)
requires
  cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
  R.pts_to r_before vb0 ** R.pts_to r_after va0 **
  pure (SZ.fits_u64)
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

(* Finalize: turn an owned array into a normal deterministic-CBOR object. *)
inline_for_extraction
fn cbor_det_array_finalize
  (x: cbor_mixed_list_array)
  (#l: Ghost.erased (list Spec.cbor))
requires
  cbor_det_array_owned x l
returns y: cbor_det_t
ensures
  exists* (l': (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n })).
    Det.cbor_det_match 1.0R y (Spec.pack (Spec.CArray l')) **
    Trade.trade
      (Det.cbor_det_match 1.0R y (Spec.pack (Spec.CArray l')))
      (cbor_det_array_owned x l) **
    pure ((l' <: list Spec.cbor) == Ghost.reveal l)

(* Init: view an existing deterministic-CBOR ARRAY object as an owned-array
   handle (the reverse of [cbor_det_array_finalize]).

   NOTE (deviation): requires [pure SZ.fits_u64] (see [cbor_det_array_append]). *)
inline_for_extraction
fn cbor_det_array_init
  (x: cbor_det_t) (r1 r2: R.ref cbor_det_array_append_cell_t)
  (#p: perm) (#l: Ghost.erased Spec.cbor) (#w1 #w2: Ghost.erased cbor_det_array_append_cell_t)
requires
  Det.cbor_det_match p x l ** R.pts_to r1 w1 ** R.pts_to r2 w2 **
  pure (Spec.CArray? (Spec.unpack l) /\ SZ.fits_u64)
returns y: cbor_mixed_list_array
ensures
  exists* (l': list Spec.cbor).
    cbor_det_array_owned y l' **
    Trade.trade
      (cbor_det_array_owned y l')
      (Det.cbor_det_match p x l ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)) **
    pure (Spec.CArray? (Spec.unpack l) /\ l' == Spec.CArray?.v (Spec.unpack l))
