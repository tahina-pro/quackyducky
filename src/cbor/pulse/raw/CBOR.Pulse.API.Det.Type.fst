module CBOR.Pulse.API.Det.Type
module Raw = CBOR.Pulse.Raw.Type
module ML = CBOR.Pulse.Raw.Format.MixedList

let cbor_det_t = Raw.cbor_raw
let cbor_det_map_entry_t = Raw.cbor_map_entry
let cbor_det_array_iterator_t = CBOR.Pulse.Raw.Read.cbor_array_iterator
let cbor_det_map_iterator_t = CBOR.Pulse.Raw.Read.cbor_map_iterator
let cbor_det_array_append_cell_t = ML.cbor_raw_mixed_list Raw.cbor_raw
let cbor_det_map_entry_insert_cell_t = ML.cbor_raw_mixed_list Raw.cbor_map_entry
