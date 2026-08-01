module CBOR.Pulse.API.Nondet.Dummy

(* The dummy placeholder values used by the Nondet C and Rust APIs live here
   rather than in CBOR.Pulse.API.Nondet.Type so that the Type bundle stays
   header-only.  This module is `friend`ed to Nondet.Type to construct the
   abstract cell/entry types.  Mirrors CBOR.Pulse.API.Det.Dummy. *)

friend CBOR.Pulse.API.Nondet.Type

module Raw = CBOR.Pulse.Raw.Type
module T = CBOR.Pulse.API.Nondet.Type
module ML = CBOR.Pulse.Raw.Format.MixedList

let dummy_cbor_nondet_t _ = Raw.CBOR_Case_Simple 0uy

let dummy_cbor_nondet_array_append_cell _ = ML.cbor_raw_mixed_list_dummy #Raw.cbor_raw ()

let dummy_cbor_nondet_map_entry_insert_cell _ = ML.cbor_raw_mixed_list_dummy #Raw.cbor_map_entry ()

let dummy_cbor_nondet_map_entry _ = {
  Raw.cbor_map_entry_key = dummy_cbor_nondet_t ();
  Raw.cbor_map_entry_value = dummy_cbor_nondet_t ();
}
