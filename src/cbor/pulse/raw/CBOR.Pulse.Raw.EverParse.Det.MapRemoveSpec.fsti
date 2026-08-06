module CBOR.Pulse.Raw.EverParse.Det.MapRemoveSpec
#lang-pulse

(* Layer-2 (raw/) interface of the deterministic-CBOR structural map
   remove-by-key.  The implementation ([.fst]) lives in [everparse/], is
   written against the lowparse [IT.mixed_list cbor_map_entry] /
   [cbor_map_entry] types, and [friend]s [CBOR.Pulse.API.Det.Type] (and
   [CBOR.Pulse.Raw.Format.MixedList]) so that, inside it,
     [cbor_det_map_entry_insert_cell_t == IT.mixed_list U64.t cbor_map_entry]
     and [cbor_det_t == cbor_raw].

   This interface deliberately mentions NO lowparse type. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Det.Type
open CBOR.Pulse.API.Det.Common

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

(* Remove the entry with key [vk] (if any) from a deterministic-CBOR map
   [x] (whose spec value [y] satisfies [CMap? (unpack y)]).  ALWAYS returns
   a deterministic-CBOR map [res]: the filtered map (== [x] when [vk] was
   absent), owned with FULL permission, together with a trade returning the
   borrow (and the four scratch references) to the source.

   The [key]'s ownership [cbor_det_match pk key vk] is returned OUTSIDE the
   trade (read-only).

   The result value [v'] satisfies [CMap? (unpack v')] and its map component
   is [cbor_map_filter (fun kv' -> not (fst kv' = vk))] of the source map. *)
inline_for_extraction
fn cbor_det_map_remove_bridge
  (x key: cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (#p: perm) (#y: Ghost.erased (v: Spec.cbor { Spec.CMap? (Spec.unpack v) }))
  (#pk: perm) (#vk: Ghost.erased Spec.cbor)
requires
  cbor_det_match p x y **
  cbor_det_match pk key vk **
  (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4) **
  pure (Spec.CMap? (Spec.unpack y))
returns res: cbor_det_t
ensures exists* (v': Spec.cbor).
  cbor_det_match 1.0R res v' **
  cbor_det_match pk key vk **
  Trade.trade
    (cbor_det_match 1.0R res v')
    (cbor_det_match p x y **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
  pure (Spec.CMap? (Spec.unpack v') /\
        (Spec.CMap?.c (Spec.unpack v') <: Spec.cbor_map) ==
          map_remove_key vk (Spec.CMap?.c (Spec.unpack y)))
