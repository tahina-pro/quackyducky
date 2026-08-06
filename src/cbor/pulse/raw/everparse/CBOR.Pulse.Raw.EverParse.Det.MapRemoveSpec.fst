module CBOR.Pulse.Raw.EverParse.Det.MapRemoveSpec
#lang-pulse
friend CBOR.Pulse.API.Det.Type
friend CBOR.Pulse.API.Det.Common
(* Needed so the abstract cell type (declared in the relocated raw/
   interface) is transparent here:
     cbor_det_map_entry_insert_cell_t == IT.mixed_list U64.t cbor_map_entry *)
friend CBOR.Pulse.Raw.Format.MixedList

(* Bridge from the verified raw deterministic-CBOR map remove-by-key core
   ([MR.cbor_raw_det_map_remove]) to the specification-level CBOR data model.
   Mirrors [CBOR.Pulse.Raw.EverParse.Det.MapInsertSpec]. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Det.Common
open CBOR.Pulse.Raw.Type

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module SpecRawBase = CBOR.Spec.Raw.Base
module MapLexInsert = CBOR.Spec.Raw.MapLexInsert
module RF = CBOR.Spec.Raw.Format
module MR = CBOR.Pulse.Raw.EverParse.Det.MapRemove
module MRE = CBOR.Pulse.Raw.EverParse.MapRemove
module RawMatch = CBOR.Pulse.Raw.Match
module RV = CBOR.Spec.Raw.Optimal
module Valid = CBOR.Spec.Raw.Valid
module IT = LowParse.PulseParse.Iterator.Type
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module U64 = FStar.UInt64

#push-options "--fuel 2 --ifuel 2 --z3rlimit 16"

let order0_eq ()
: Lemma (MapLexInsert.order0 == RF.deterministically_encoded_cbor_map_key_order)
= assert_norm (MapLexInsert.order0 == RF.deterministically_encoded_cbor_map_key_order)

(* [L.filter] only depends on the predicate pointwise. *)
let rec filter_ext
  (#a: Type) (p1 p2: a -> bool) (l: list a)
: Lemma (requires (forall (x: a). p1 x == p2 x))
        (ensures (L.filter p1 l == L.filter p2 l))
        (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> filter_ext p1 p2 q

(* The engine's [filtered_out] (defined via [MRE.key_eq k = (cbor_compare k _ = 0)])
   is exactly the [cbor_compare]-based filter used by
   [SpecRaw.mk_det_raw_cbor_map_raw_filter_neq]. *)
let filtered_out_is_compare_filter
  (raw_vk: SpecRawBase.raw_data_item)
  (l: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
: Lemma (MRE.filtered_out raw_vk l ==
         L.filter (fun (e: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
                     not (RF.cbor_compare (fst e) raw_vk = 0)) l)
= filter_ext
    (fun (e: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) -> not (MRE.key_eq (fst e) raw_vk))
    (fun (e: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) -> not (RF.cbor_compare (fst e) raw_vk = 0))
    l

(* [map_remove_key] (which closes over the concrete key [k]) unfolds to the
   [cbor_compare]-based filter on the raw encoding, via
   [SpecRaw.mk_det_raw_cbor_map_raw_filter_neq]. *)
let map_remove_key_unfold
  (k: Spec.cbor) (m: Spec.cbor_map)
: Lemma
    (SpecRaw.mk_det_raw_cbor_map_raw (map_remove_key k m) ==
     L.filter (fun (e: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
                 not (RF.cbor_compare (fst e) (SpecRaw.mk_det_raw_cbor k) = 0))
       (SpecRaw.mk_det_raw_cbor_map_raw m))
= SpecRaw.mk_det_raw_cbor_map_raw_filter_neq m k

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"

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
{
  let m_hl : Ghost.erased Spec.cbor_map =
    Ghost.hide (Spec.CMap?.c (Spec.unpack (Ghost.reveal y)));
  (* Shape of the raw encoding of [y]. *)
  SpecRaw.mk_cbor_eq_map (Ghost.reveal y);
  assert (pure (SpecRawBase.Map? (SpecRaw.mk_det_raw_cbor (Ghost.reveal y))));
  assert (pure (SpecRawBase.Map?.v (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) ==
                SpecRaw.mk_det_raw_cbor_map_raw (Ghost.reveal m_hl)));
  assert (pure (L.sorted (Valid.map_entry_order RF.deterministically_encoded_cbor_map_key_order _)
                  (SpecRawBase.Map?.v (SpecRaw.mk_det_raw_cbor (Ghost.reveal y))) == true));
  order0_eq ();
  assert (pure (L.sorted (Valid.map_entry_order MapLexInsert.order0 _)
                  (SpecRawBase.Map?.v (SpecRaw.mk_det_raw_cbor (Ghost.reveal y))) == true));
  (* Expose raw resources and run the verified raw core. *)
  unfold (cbor_det_match p x y);
  unfold (cbor_det_match pk key vk);
  let res = MR.cbor_raw_det_map_remove x key r1 r2 r3 r4;
  with xh_result. assert (
    RawMatch.cbor_match 1.0R res xh_result **
    Trade.trade
      (RawMatch.cbor_match 1.0R res xh_result)
      (RawMatch.cbor_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
  );
  (* Build the spec-level result value: filter out key [vk]. *)
  let m_filt : Ghost.erased Spec.cbor_map =
    Ghost.hide (map_remove_key (Ghost.reveal vk) (Ghost.reveal m_hl));
  let cm : Ghost.erased Spec.cbor_case = Ghost.hide (Spec.CMap (Ghost.reveal m_filt));
  let vres : Ghost.erased Spec.cbor = Ghost.hide (Spec.pack (Ghost.reveal cm));
  Spec.unpack_pack (Ghost.reveal cm);
  assert (pure (Spec.CMap? (Spec.unpack (Ghost.reveal vres))));
  assert (pure (Spec.CMap?.c (Spec.unpack (Ghost.reveal vres)) == Ghost.reveal m_filt));
  (* Shape of the raw encoding of [vres]. *)
  SpecRaw.mk_cbor_eq_map (Ghost.reveal vres);
  (* Payload equality: map_payload xh_result == mk_det_raw_cbor_map_raw m_filt. *)
  (* Step 1: the borrowed payload of [y] is the raw encoding of [m_hl]. *)
  assert (pure (MR.map_payload (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) ==
                SpecRaw.mk_det_raw_cbor_map_raw (Ghost.reveal m_hl)));
  (* Step 2: rephrase the raw post via [step 1]. *)
  assert (pure (MR.map_payload xh_result ==
                MRE.filtered_out (SpecRaw.mk_det_raw_cbor (Ghost.reveal vk))
                  (SpecRaw.mk_det_raw_cbor_map_raw (Ghost.reveal m_hl))));
  (* Step 3: engine [filtered_out] == the [cbor_compare]-based filter. *)
  filtered_out_is_compare_filter
    (SpecRaw.mk_det_raw_cbor (Ghost.reveal vk))
    (SpecRaw.mk_det_raw_cbor_map_raw (Ghost.reveal m_hl));
  (* Step 4+5: raw encoding of [m_filt] == that same [cbor_compare]-based filter. *)
  map_remove_key_unfold (Ghost.reveal vk) (Ghost.reveal m_hl);
  assert (pure (MR.map_payload xh_result ==
                SpecRaw.mk_det_raw_cbor_map_raw (Ghost.reveal m_filt)));
  (* Header equality via optimal-uniqueness. *)
  SpecRaw.mk_det_raw_cbor_map_raw_length (Ghost.reveal m_filt);
  RV.raw_uint64_optimal_unique
    (SpecRawBase.Map?.len xh_result)
    (SpecRawBase.Map?.len (SpecRaw.mk_det_raw_cbor (Ghost.reveal vres)));
  assert (pure (xh_result == SpecRaw.mk_det_raw_cbor (Ghost.reveal vres)));
  rewrite (RawMatch.cbor_match 1.0R res xh_result)
    as (RawMatch.cbor_match 1.0R res (SpecRaw.mk_det_raw_cbor (Ghost.reveal vres)));
  fold (cbor_det_match 1.0R res (Ghost.reveal vres));
  Trade.intro_trade
    (cbor_det_match 1.0R res (Ghost.reveal vres))
    (cbor_det_match p x y **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
    (Trade.trade
      (RawMatch.cbor_match 1.0R res xh_result)
      (RawMatch.cbor_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)))
    fn _ {
      unfold (cbor_det_match 1.0R res (Ghost.reveal vres));
      rewrite (RawMatch.cbor_match 1.0R res (SpecRaw.mk_det_raw_cbor (Ghost.reveal vres)))
        as (RawMatch.cbor_match 1.0R res xh_result);
      Trade.elim
        (RawMatch.cbor_match 1.0R res xh_result)
        (RawMatch.cbor_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) **
         (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4));
      fold (cbor_det_match p x y);
    };
  fold (cbor_det_match pk key vk);
  res
}

#pop-options
