module CBOR.Pulse.API.Nondet.Type
open CBOR.Pulse.Raw.Match
module ML = CBOR.Pulse.Raw.Format.MixedList

type cbor_nondet_t = cbor_raw

let cbor_nondet_array_iterator_t = CBOR.Pulse.Raw.Read.cbor_array_iterator

let cbor_nondet_map_iterator_t = CBOR.Pulse.Raw.Read.cbor_map_iterator

let cbor_nondet_map_entry_t = cbor_map_entry

let cbor_nondet_array_append_cell_t = ML.cbor_raw_mixed_list cbor_raw

let cbor_nondet_map_entry_insert_cell_t = ML.cbor_raw_mixed_list cbor_map_entry
