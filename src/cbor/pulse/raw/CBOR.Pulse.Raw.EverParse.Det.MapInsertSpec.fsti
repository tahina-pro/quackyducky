module CBOR.Pulse.Raw.EverParse.Det.MapInsertSpec
#lang-pulse

(* Layer-2 (raw/) interface of the deterministic-CBOR structural map-entry
   insertion.  The implementation ([.fst]) lives in [everparse/], is written
   against the lowparse [IT.mixed_list cbor_map_entry] / [cbor_map_entry] types,
   and [friend]s [CBOR.Pulse.API.Det.Type] (and [CBOR.Pulse.Raw.Format.MixedList])
   so that, inside it,
     [cbor_det_map_entry_insert_cell_t == IT.mixed_list cbor_map_entry],
     [cbor_det_map_entry_t == cbor_map_entry],  and  [cbor_det_t == cbor_raw].

   This interface deliberately mentions NO lowparse type. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Det.Type
open CBOR.Pulse.API.Det.Common

module Spec = CBOR.Spec.API.Format
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module U64 = FStar.UInt64
module SZ = FStar.SizeT

(* Insert a (key, value) entry into a deterministic-CBOR map [x] (whose spec
   value [y] satisfies [CMap? (unpack y)]).

   On [None] the map already defined the key, or the resulting length would
   overflow a u64; the inputs are returned unchanged.

   On [Some m], [m] owns the spec value [vres] obtained by unioning the
   original map with the singleton {vk -> vv}.  We expose this via the
   EXISTENTIAL form (see the .fst for the rationale): we existentially
   quantify [vres : Spec.cbor] and assert that [CMap? (unpack vres)] holds
   and that [CMap?.c (unpack vres)] equals the union map. *)
inline_for_extraction
fn cbor_det_map_entry_insert_spec
  (f64: squash SZ.fits_u64)
  (x key value: cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (ry: R.ref cbor_det_map_entry_t)
  (#p: perm) (#y: Ghost.erased (v: Spec.cbor { Spec.CMap? (Spec.unpack v) }))
  (#pkv: perm) (#vk #vv: Ghost.erased Spec.cbor)
requires
  cbor_det_match p x y **
  cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
  (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy) **
  pure (Spec.CMap? (Spec.unpack y))
returns res: option cbor_det_t
ensures (match res with
  | None ->
    cbor_det_match p x y **
    cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
    (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy) **
    pure (Spec.cbor_map_defined vk (Spec.CMap?.c (Spec.unpack y)) \/
          ~ (FStar.UInt.fits (Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) + 1) U64.n))
  | Some m ->
    exists* (p_res: perm) (vres: Spec.cbor).
      cbor_det_match p_res m vres **
      Trade.trade
        (cbor_det_match p_res m vres)
        (cbor_det_match p x y **
         cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
         (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy)) **
      pure (Spec.CMap? (Spec.unpack vres) /\
            (Spec.CMap?.c (Spec.unpack vres) <: Spec.cbor_map) ==
              Spec.cbor_map_union (Spec.CMap?.c (Spec.unpack y)) (Spec.cbor_map_singleton vk vv)))
