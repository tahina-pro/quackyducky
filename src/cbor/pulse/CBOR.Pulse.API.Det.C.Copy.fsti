module CBOR.Pulse.API.Det.C.Copy
include CBOR.Pulse.API.Det.C
open Pulse.Lib.Pervasives

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT

[@@CAbstractStruct]
val cbor_det_freeable_t: Type0

val freeable: cbor_det_freeable_t -> slprop

val cbor_get_from_freeable: cbor_det_freeable_t -> cbor_det_t

(* Deep-copying a value allocates one flat [size_t]-length vector per array/map
   node, so it requires the value's recursive [raw_data_item_size] to fit in
   [size_t].  This is a GHOST precondition: it is erased at extraction (the
   emitted C/Rust [cbor_copy] signature is unchanged).  It soundly replaces the
   former global platform axiom (that every 64-bit count fits [size_t]) for the
   mixed-list ([_Gen]) array/map cases, discharging the size bound locally
   through the copy recursion. *)
inline_for_extraction
let cbor_det_copy_t =
  (x: cbor_det_t) ->
  (#p: perm) ->
  (#v: Ghost.erased Spec.cbor) ->
  stt cbor_det_freeable_t
    (cbor_det_match p x v **
      pure (SZ.fits (CBOR.Spec.Raw.Base.raw_data_item_size (SpecRaw.mk_det_raw_cbor v))))
    (fun res ->
      cbor_det_match p x v **
      cbor_det_match 1.0R (cbor_get_from_freeable res) v **
      Trade.trade
        (cbor_det_match 1.0R (cbor_get_from_freeable res) v)
        (freeable res)
    )

val cbor_copy () : cbor_det_copy_t

val cbor_free () : cbor_free_t freeable
