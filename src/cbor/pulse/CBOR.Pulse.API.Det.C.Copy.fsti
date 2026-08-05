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

(* Deep-copying a value requires no [size_t] bound: the inline array/map and
   string/serialized nodes allocate vectors sized by slice lengths (already
   [size_t]), and the structural ([_Gen]) array/map nodes are rebuilt with only
   O(1)-per-element heap allocations, folded via a [U64.t] loop counter.  Hence
   [cbor_copy] carries no precondition beyond the input match. *)
inline_for_extraction
let cbor_det_copy_t =
  (x: cbor_det_t) ->
  (#p: perm) ->
  (#v: Ghost.erased Spec.cbor) ->
  stt cbor_det_freeable_t
    (cbor_det_match p x v)
    (fun res ->
      cbor_det_match p x v **
      cbor_det_match 1.0R (cbor_get_from_freeable res) v **
      Trade.trade
        (cbor_det_match 1.0R (cbor_get_from_freeable res) v)
        (freeable res)
    )

val cbor_copy () : cbor_det_copy_t

val cbor_free () : cbor_free_t freeable
