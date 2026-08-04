module CBOR.Pulse.Raw.EverParse.MapBuilder
#lang-pulse
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Optimal
open Pulse.Lib.Pervasives
open LowParse.Spec.Combinators

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module IO = LowParse.PulseParse.Iterator.IntOps

(* ================================================================ *)
(* Minimal (canonical) integer_size for a u64 length                *)
(*                                                                  *)
(* Identical to [ArrayBuilder.minimal_len_size]: the [size] field   *)
(* of the minimal (shortest) header encoding of [len].              *)
(* ================================================================ *)

let minimal_len_size (len: U64.t) : integer_size =
  (mk_raw_uint64 len).size

val minimal_len_size_prop (len: U64.t)
  : Lemma (raw_uint64_size_prop (minimal_len_size len) len)

(* ================================================================ *)
(* cbor_mk_map_full                                                 *)
(*                                                                  *)
(* Build a full [cbor_raw] MAP from an (unbounded) [mixed_list] of  *)
(* map entries.  Mirrors [ArrayBuilder.cbor_array_finalize] but     *)
(* takes the raw [mixed_list_match] directly (no owned wrapper),    *)
(* since the map-insert engine produces its result in exactly this  *)
(* form.                                                            *)
(*                                                                  *)
(* Entry vmatch: the (unbounded) [cbor_match_map_entry] from        *)
(* [CBOR.Pulse.Raw.Match], at ambient permission [1.0R].           *)
(* Element parser: [nondep_then parse_raw_data_item                 *)
(* parse_raw_data_item].                                           *)
(* ================================================================ *)

(* [cbor_map_finalized ml y l]: [y] is the full [cbor_raw] MAP view   *)
(* of the mixed_list [ml] (entries [l]), together with a trade back   *)
(* to the raw entry match.  The existential [len] is the minimal-     *)
(* length encoding of the entry count.                                *)
(*                                                                    *)
(* NOTE (deviation, same as ArrayBuilder): the result is packaged in  *)
(* this transparent [let] instead of an inline [exists*] in the       *)
(* [ensures], to sidestep Pulse's [fn] [ensures] elaboration which    *)
(* cannot scope a refined [exists*] binder over a dependent type      *)
(* (here [Map len l] requires [length l == U64.v len.value] at the    *)
(* TYPE level, only available from the binder refinement).            *)
let cbor_map_finalized
  (pm: perm)
  (ml: IT.mixed_list U64.t cbor_map_entry) (y: cbor_raw)
  (l: list (raw_data_item & raw_data_item))
: slprop
= exists* (len: (len: raw_uint64 { U64.v len.value == List.Tot.length l })).
    cbor_match 1.0R y (Map len l) **
    Trade.trade
      (cbor_match 1.0R y (Map len l))
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops
        (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l) **
    pure ((len <: raw_uint64) == mk_raw_uint64 len.value)

val cbor_mk_map_full
  (pm: perm)
  (ml: IT.mixed_list U64.t cbor_map_entry)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
: stt cbor_raw
    (I.mixed_list_match cbor_match_map_entry IO.u64_ops
      (nondep_then parse_raw_data_item parse_raw_data_item) pm ml (Ghost.reveal l))
    (fun y ->
      cbor_map_finalized pm ml y (Ghost.reveal l) **
      pure (CBOR_Case_Map_Gen? y))

(* ================================================================ *)
(* cbor_map_borrow_entries                                          *)
(*                                                                  *)
(* View an existing MAP [x] (ANY of the three representations:      *)
(* inline [CBOR_Case_Map], serialized [CBOR_Case_Serialized_Map],   *)
(* or structural [CBOR_Case_Map_Gen]) as a [mixed_list] of map      *)
(* entries, together with a trade back to [cbor_match].             *)
(*                                                                  *)
(* Entry vmatch: [cbor_match_map_entry]; element parser:            *)
(* [nondep_then parse_raw_data_item parse_raw_data_item].           *)
(*                                                                  *)
(* The output ambient permission [pm'] is existentially quantified  *)
(* (the three representations yield genuinely different natural      *)
(* ambients: [pm *. gen_perm] for [_Gen], a half of                 *)
(* [pm *. serialized_perm] for the serialized case, and             *)
(* [pm *. array_perm] for the inline case).                         *)
(*                                                                  *)
(* The entry count is now a [U64.t] (the CBOR wire count type), so   *)
(* the serialized case reads the u64 header length directly: no      *)
(* [SZ.t] conversion and no [SZ.fits_u64] assumption are needed.     *)
(* ================================================================ *)

val cbor_map_borrow_entries
  (pm: perm) (x: cbor_raw)
  (#xh: Ghost.erased (r: raw_data_item { Map? r }))
: stt (IT.mixed_list U64.t cbor_map_entry)
    (cbor_match pm x (Ghost.reveal xh))
    (fun ml -> exists* (pm': perm).
      I.mixed_list_match cbor_match_map_entry IO.u64_ops
        (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml
        (Map?.v (Ghost.reveal xh)) **
      Trade.trade
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml
          (Map?.v (Ghost.reveal xh)))
        (cbor_match pm x (Ghost.reveal xh)))
