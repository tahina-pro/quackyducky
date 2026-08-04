module CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder
#lang-pulse

(* Layer-2 (raw/) interface of the nondeterministic-CBOR structural array
   builder.

   The implementation ([.fst]) lives in [everparse/] and is written against the
   lowparse [IT.mixed_list cbor_raw] type; it [friend]s [CBOR.Pulse.API.Nondet.Type]
   (and [CBOR.Pulse.Raw.Format.MixedList]) so that, inside it,
     [cbor_nondet_array_append_cell_t == IT.mixed_list cbor_raw]  and
     [cbor_nondet_t == cbor_raw],
   which is how the concrete [.fst] realizes this abstract-typed interface.

   This interface deliberately mentions NO lowparse type, so that raw/ clients
   (notably [CBOR.Pulse.API.Nondet.C]) can consume it.  The op ORDER below
   matches the definition order in the [.fst]. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Type
open CBOR.Pulse.API.Nondet.Type

module Spec = CBOR.Spec.API.Format
module Nondet = CBOR.Pulse.Raw.Nondet
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module L = FStar.List.Tot

(* Ownership of a structurally-built nondeterministic-CBOR array whose
   spec-level element list is [l].  In contrast to the deterministic version,
   the raw element list is existentially quantified and only required to be a
   list of VALID raw items whose [mk_cbor] image is [l]. *)
val cbor_nondet_array_owned (x: cbor_mixed_list_array) (l: list Spec.cbor) : slprop

(* Empty array. *)
inline_for_extraction
fn cbor_nondet_array_empty (_: unit)
requires emp
returns res: cbor_mixed_list_array
ensures cbor_nondet_array_owned res []

(* The length of an owned array fits in a u64. *)
ghost
fn cbor_nondet_array_owned_length_fits
  (x: cbor_mixed_list_array) (#l: Ghost.erased (list Spec.cbor))
requires cbor_nondet_array_owned x l
ensures cbor_nondet_array_owned x l ** pure (FStar.UInt.fits (L.length (Ghost.reveal l)) 64)

(* Singleton array from a single element (plus a scratch reference [ry]). *)
fn cbor_nondet_array_singleton
  (x: cbor_nondet_t) (ry: R.ref cbor_nondet_t)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_nondet_t)
requires
  Nondet.cbor_nondet_match pm x v ** R.pts_to ry w0
returns res: cbor_mixed_list_array
ensures
  cbor_nondet_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_nondet_array_owned res [Ghost.reveal v])
    (Nondet.cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w))

(* Append two owned arrays.

   The element counts are now [U64.t] values, so forming the underlying
   [Append] node no longer needs any assumption about the platform integer
   width: once the [U64.t] length sum is known not to overflow, that bound
   directly discharges the iterator's overflow obligation. *)
fn cbor_nondet_array_append
  (x1 x2: cbor_mixed_list_array)
  (r_before r_after: R.ref cbor_nondet_array_append_cell_t)
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased cbor_nondet_array_append_cell_t)
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

(* Finalize: turn an owned array into a normal nondeterministic-CBOR object. *)
fn cbor_nondet_array_finalize
  (x: cbor_mixed_list_array)
  (#l: Ghost.erased (list Spec.cbor))
requires
  cbor_nondet_array_owned x l
returns y: cbor_nondet_t
ensures
  exists* (l': (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n })).
    Nondet.cbor_nondet_match 1.0R y (Spec.pack (Spec.CArray l')) **
    Trade.trade
      (Nondet.cbor_nondet_match 1.0R y (Spec.pack (Spec.CArray l')))
      (cbor_nondet_array_owned x l) **
    pure ((l' <: list Spec.cbor) == Ghost.reveal l)

(* Init: view an existing nondeterministic-CBOR ARRAY object as an owned-array
   handle (the reverse of [cbor_nondet_array_finalize]).

   The element counts are now [U64.t], so this needs no platform integer-width
   assumption (see [cbor_nondet_array_append]). *)
fn cbor_nondet_array_init
  (x: cbor_nondet_t) (r1 r2: R.ref cbor_nondet_array_append_cell_t)
  (#p: perm) (#l: Ghost.erased Spec.cbor) (#w1 #w2: Ghost.erased cbor_nondet_array_append_cell_t)
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
