module CBOR.Pulse.Raw.EverParse.Serialized.Rust
open LowParse.Spec.Base
open LowParse.Pulse.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.Match.Gen.Base

module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module Match = CBOR.Pulse.Raw.Match

val cbor_read
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
: stt (cbor_serialized_raw Match.cbor_string Match.cbor_serialized)
  (requires
    pts_to_serialized serialize_raw_data_item input #pm v
  )
  (ensures fun res ->
      cbor_serialized_raw_match Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged 1.0R res v **
      Trade.trade
        (cbor_serialized_raw_match Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged 1.0R res v)
        (pts_to_serialized serialize_raw_data_item input #pm v)
  )
