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

val cbor_copy () : cbor_copy_t cbor_det_match freeable cbor_get_from_freeable

val cbor_free () : cbor_free_t freeable
