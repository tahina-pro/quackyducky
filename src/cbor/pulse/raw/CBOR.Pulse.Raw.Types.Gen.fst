module CBOR.Pulse.Raw.Types.Gen
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
type cbor_int = {
  cbor_int_type: Spec.major_type_uint64_or_neg_int64;
  cbor_int_value: Spec.raw_uint64;
}

let cbor_int_match (x: cbor_int) (ty: Spec.major_type_uint64_or_neg_int64) (v: Spec.raw_uint64) : slprop =
  pure (x.cbor_int_type == ty /\
    x.cbor_int_value == v
  )

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_string_match_intro_t
  (#cbor_string: Type0)
  (cbor_string_match: perm -> cbor_string -> Spec.raw_data_item -> slprop)
=
  (typ: Spec.major_type_byte_string_or_text_string) ->
  (len: Spec.raw_uint64) ->
  (x: S.slice U8.t) ->
  (#pm: perm) ->
  (#y: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_string
(requires
  S.pts_to x #pm y **
  pure (Seq.length y == U64.v len.value /\
    (typ == Spec.cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct y)
  )
)
(ensures fun res -> exists* v .
  cbor_string_match 1.0R res v **
  Trade.trade
    (cbor_string_match 1.0R res v)
    (S.pts_to x #pm y) **
  pure (
    Spec.String? v /\
    Spec.String?.typ v == typ /\
    Spec.String?.len v == len /\
    Ghost.reveal y == Spec.String?.v v
  )
)

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_string_match_get_typ_t
  (#cbor_string: Type0)
  (cbor_string_match: perm -> cbor_string -> Spec.raw_data_item -> slprop)
=
  (x: cbor_string) ->
  (#pm: perm) ->
  (#y: Ghost.erased Spec.raw_data_item) ->
  stt Spec.major_type_byte_string_or_text_string
(requires
  cbor_string_match pm x y
)
(ensures fun res ->
  cbor_string_match pm x y **
  pure (
    Spec.String? y /\
    Spec.String?.typ y == res
  )
)

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_string_match_get_len_t
  (#cbor_string: Type0)
  (cbor_string_match: perm -> cbor_string -> Spec.raw_data_item -> slprop)
=
  (x: cbor_string) ->
  (#pm: perm) ->
  (#y: Ghost.erased Spec.raw_data_item) ->
  stt Spec.raw_uint64
(requires
  cbor_string_match pm x y
)
(ensures fun res ->
  cbor_string_match pm x y **
  pure (
    Spec.String? y /\
    Spec.String?.len y == res
  )
)

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_string_match_elim_t
  (#cbor_string: Type0)
  (cbor_string_match: perm -> cbor_string -> Spec.raw_data_item -> slprop)
=
  (x: cbor_string) ->
  (#pm: perm) ->
  (#y: Ghost.erased Spec.raw_data_item) ->
  stt (S.slice U8.t)
(requires
  cbor_string_match pm x y **
  pure (SZ.fits_u64)
)
(ensures fun res -> exists* pm' v .
  S.pts_to res #pm' v **
  Trade.trade
    (pts_to res #pm' v)
    (cbor_string_match pm x y) **
  pure (
    Spec.String? y /\
    v == Spec.String?.v y
  )
)

noeq
type cbor_cases
  (cbor_string: Type0)
  ([@@@strictly_positive] cbor_tagged: Type0)
  ([@@@strictly_positive] cbor_array: Type0)
  ([@@@strictly_positive] cbor_map: Type0)
: Type0
= | CborInt of cbor_int
  | CborString of cbor_string
  | CborTagged of cbor_tagged
  | CborArray of cbor_array
  | CborMap of cbor_map

let cbor_cases_match
  (#cbor_string: Type0)
  (#cbor_tagged: Type0)
  (#cbor_array: Type0)
  (#cbor_map: Type0)
  (pm: perm)
  (x: cbor_cases cbor_string cbor_tagged cbor_array cbor_map)
  (y: Spec.raw_data_item)
  (string_match: perm -> cbor_string -> Spec.major_type_byte_string_or_text_string -> Spec.raw_uint64 -> Seq.seq U8.t -> slprop)
  (tagged_match: perm -> cbor_tagged -> Spec.raw_uint64 -> (z: Spec.raw_data_item { z << y}) -> slprop)
  (array_match: perm -> cbor_array -> Spec.raw_uint64 -> (z: list Spec.raw_data_item { z << y}) -> slprop)
  (map_match: perm -> cbor_map -> Spec.raw_uint64 -> (z: list (Spec.raw_data_item & Spec.raw_data_item) { z << y}) -> slprop)
: slprop
= match x, y with
  | CborInt u, Spec.Int64 ty v -> cbor_int_match u ty v
  | CborString u, Spec.String ty len v -> string_match pm u ty len v
  | CborTagged u, Spec.Tagged tag v -> tagged_match pm u tag v
  | CborArray u, Spec.Array len v -> array_match pm u len v
  | CborMap u, Spec.Map len v -> map_match pm u len v
  | _ -> pure (squash False)
