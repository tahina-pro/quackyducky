module CBOR.Pulse.Raw.EverParse.Det.ArrayBuilder
#lang-pulse

(* Layer-2 (raw/) interface of the deterministic-CBOR structural array builder.

   The implementation ([.fst]) lives in [everparse/] and is written against the
   lowparse [IT.mixed_list U64.t cbor_raw] type; it [friend]s
   [CBOR.Pulse.API.Det.Type] (and [CBOR.Pulse.Raw.Format.MixedList]) so that,
   inside it,
     [cbor_det_array_append_cell_t == IT.mixed_list U64.t cbor_raw]  and
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

   Element counts are now [U64.t] (the CBOR wire count type), so the underlying
   [Append] node's [fits (len1 + len2)] obligation is exactly the plain u64
   non-overflow test performed at runtime by the raw [cbor_array_append]; no
   unsound [size_t]-width platform assumption is required. *)
inline_for_extraction
fn cbor_det_array_append
  (x1 x2: cbor_mixed_list_array)
  (r_before r_after: R.ref cbor_det_array_append_cell_t)
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased cbor_det_array_append_cell_t)
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

   Element counts are now [U64.t], so (as in [cbor_det_array_append]) no
   unsound [size_t]-width platform assumption is required. *)
inline_for_extraction
fn cbor_det_array_init
  (x: cbor_det_t) (r1 r2: R.ref cbor_det_array_append_cell_t)
  (#p: perm) (#l: Ghost.erased Spec.cbor) (#w1 #w2: Ghost.erased cbor_det_array_append_cell_t)
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

(* Deterministic-CBOR slice spec: the sub-range [i,j) of the element list
   (empty if the range is empty or out of bounds). *)
let cbor_det_array_slice_spec (l: list Spec.cbor) (i j: U64.t) : list Spec.cbor =
  if U64.v i < U64.v j && U64.v j <= L.length l
  then fst (L.splitAt (U64.v j - U64.v i) (snd (L.splitAt (U64.v i) l)))
  else []

(* Slice: zero-copy sub-range [i,j) of a deterministic-CBOR ARRAY, as a
   borrowed view with a trade back to the source.  Total over i,j: empty or
   out-of-bounds ranges yield the empty array.  Wraps the raw
   [AB.cbor_array_slice]. *)
inline_for_extraction
fn cbor_det_array_slice_bridge
  (x: cbor_det_t) (i j: U64.t)
  (r1 r2 r3 r4: R.ref cbor_det_array_append_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_det_array_append_cell_t)
requires
  Det.cbor_det_match p x v **
  R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
  pure (Spec.CArray? (Spec.unpack v))
returns res: cbor_det_t
ensures exists* (v': Spec.cbor).
  Det.cbor_det_match 1.0R res v' **
  Trade.trade
    (Det.cbor_det_match 1.0R res v')
    (Det.cbor_det_match p x v **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
  pure (Spec.CArray? (Spec.unpack v) /\ Spec.CArray? (Spec.unpack v') /\
        (Spec.CArray?.v (Spec.unpack v') <: list Spec.cbor) ==
          cbor_det_array_slice_spec (Spec.CArray?.v (Spec.unpack v)) i j)
