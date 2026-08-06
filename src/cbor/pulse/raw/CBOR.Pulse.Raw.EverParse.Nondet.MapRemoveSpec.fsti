module CBOR.Pulse.Raw.EverParse.Nondet.MapRemoveSpec
#lang-pulse

(* Layer-2 (raw/) interface of the NONdeterministic-CBOR structural map
   remove-by-key.  The implementation ([.fst]) lives in [everparse/], is
   written against the lowparse [IT.mixed_list cbor_map_entry] /
   [cbor_map_entry] types, and [friend]s [CBOR.Pulse.API.Nondet.Type] (and
   [CBOR.Pulse.Raw.Format.MixedList]) so that, inside it,
     [cbor_nondet_map_entry_insert_cell_t == IT.mixed_list U64.t cbor_map_entry]
     and [cbor_nondet_t == cbor_raw].

   This interface deliberately mentions NO lowparse type.  Dual of
   [CBOR.Pulse.Raw.EverParse.Det.MapRemoveSpec], but keyed on [raw_equiv]
   (abstract equality) rather than deterministic structural equality; the
   result is exposed at HALF the input permission via the
   [cbor_nondet_match_intro] round-trip (mirrors
   [CBOR.Pulse.Raw.EverParse.Nondet.MapInsertSpec]). *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Nondet
open CBOR.Pulse.Raw.Type

module Spec = CBOR.Spec.API.Format
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module U64 = FStar.UInt64

(* Spec-level map remove-by-key: keep every entry whose key differs from
   [k].  The filter predicate closes over the *concrete* parameter [k]
   (NOT a ghost value), so it is a [Tot] function as [cbor_map_filter]
   requires; callers instantiate [k] with the (auto-revealed) ghost key. *)
noextract [@@noextract_to "krml"]
let map_remove_key (k: Spec.cbor) (m: Spec.cbor_map) : Spec.cbor_map =
  Spec.cbor_map_filter (fun (kv': (Spec.cbor & Spec.cbor)) -> not (fst kv' = k)) m

(* Remove the entry with key (up to [raw_equiv]) [vk] from a nondeterministic-
   CBOR map [x] (whose spec value [y] satisfies [CMap? (unpack y)]).  ALWAYS
   returns a nondeterministic-CBOR map [res]: the filtered map (== the abstract
   [x] when [vk] was absent), owned at some permission [p_res], together with a
   trade returning the borrow (and the four scratch references) to the source.

   The [key]'s ownership [cbor_nondet_match pk key vk] is returned OUTSIDE the
   trade (read-only).

   The result value [v'] satisfies [CMap? (unpack v')] and its map component is
   [cbor_map_filter (fun kv' -> not (fst kv' = vk))] of the source map. *)
inline_for_extraction
fn cbor_nondet_map_remove_bridge
  (x key: cbor_nondet_t)
  (r1 r2 r3 r4: R.ref cbor_nondet_map_entry_insert_cell_t)
  (#p: perm) (#y: Ghost.erased (v: Spec.cbor { Spec.CMap? (Spec.unpack v) }))
  (#pk: perm) (#vk: Ghost.erased Spec.cbor)
requires
  cbor_nondet_match p x y **
  cbor_nondet_match pk key vk **
  (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4) **
  pure (Spec.CMap? (Spec.unpack y))
returns res: cbor_nondet_t
ensures exists* (p_res: perm) (v': Spec.cbor).
  cbor_nondet_match p_res res v' **
  cbor_nondet_match pk key vk **
  Trade.trade
    (cbor_nondet_match p_res res v')
    (cbor_nondet_match p x y **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
  pure (Spec.CMap? (Spec.unpack v') /\
        (Spec.CMap?.c (Spec.unpack v') <: Spec.cbor_map) ==
          map_remove_key vk (Spec.CMap?.c (Spec.unpack y)))
