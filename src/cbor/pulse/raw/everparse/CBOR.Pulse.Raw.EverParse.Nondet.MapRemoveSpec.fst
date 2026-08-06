module CBOR.Pulse.Raw.EverParse.Nondet.MapRemoveSpec
#lang-pulse
friend CBOR.Pulse.Raw.Nondet
friend CBOR.Pulse.API.Nondet.Type
(* Needed so that the abstract [cbor_nondet_map_entry_insert_cell_t] declared in
   the raw/-relocated .fsti unfolds (via Nondet.Type -> ML.cbor_raw_mixed_list,
   then MixedList -> IT.mixed_list) to the concrete [IT.mixed_list U64.t cbor_map_entry]
   used in the ref types below. *)
friend CBOR.Pulse.Raw.Format.MixedList

(* Bridge from the verified raw NONdeterministic-CBOR map remove-by-key wrapper
   ([NMR.cbor_raw_nondet_map_remove]) to the specification-level CBOR data
   model.  Mirrors [CBOR.Pulse.Raw.EverParse.Nondet.MapInsertSpec]. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Nondet
open CBOR.Pulse.Raw.Type

module Spec = CBOR.Spec.API.Format
module SAT = CBOR.Spec.API.Type
module SpecRaw = CBOR.Spec.Raw
module SpecRawBase = CBOR.Spec.Raw.Base
module SpecMapRemove = CBOR.Spec.Raw.MapRemove
module Valid = CBOR.Spec.Raw.Valid
module NMR = CBOR.Pulse.Raw.EverParse.Nondet.MapRemove
module RawMatch = CBOR.Pulse.Raw.Match
module RN = CBOR.Pulse.Raw.Nondet
module IT = LowParse.PulseParse.Iterator.Type
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module U64 = FStar.UInt64

(* ============================================================
   Pure spec-level bridge lemma.
   ============================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"

(* [L.filter] only depends on the predicate pointwise. *)
let rec filter_ext
  (#a: Type) (p1 p2: a -> bool) (l: list a)
: Lemma (requires (forall (x: a). p1 x == p2 x))
        (ensures (L.filter p1 l == L.filter p2 l))
        (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> filter_ext p1 p2 q

(* Relates the raw remove result [xh_result] (whose payload is the engine's
   [filtered_out_equiv]) to the abstract [cbor_map_filter].  Key ingredient:
   [SpecMapRemove.mk_cbor_map_remove] (SOUND because [raw_equiv] IS abstract
   equality). *)
let remove_bridge_lemma
  (xh xh_result vk_raw: SpecRawBase.raw_data_item)
  (y vk vres: Spec.cbor)
: Lemma
  (requires (
    SpecRawBase.Map? xh /\ Valid.valid_raw_data_item xh == true /\ SpecRaw.mk_cbor xh == y /\
    SpecRawBase.Map? xh_result /\ Valid.valid_raw_data_item xh_result == true /\
      SpecRaw.mk_cbor xh_result == vres /\
    NMR.map_payload xh_result == NMR.filtered_out_equiv vk_raw (NMR.map_payload xh) /\
    Valid.valid_raw_data_item vk_raw == true /\ SpecRaw.mk_cbor vk_raw == vk /\
    Spec.CMap? (Spec.unpack y)
  ))
  (ensures (
    Spec.CMap? (Spec.unpack vres) /\
    (Spec.CMap?.c (Spec.unpack vres) <: Spec.cbor_map) ==
      map_remove_key vk (Spec.CMap?.c (Spec.unpack y))
  ))
= let len = SpecRawBase.Map?.len xh in
  let entries : SpecRawBase.nlist (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item) (U64.v len.value) =
    SpecRawBase.Map?.v xh in
  assert (NMR.map_payload xh == entries);
  (* bridge the engine's [key_equiv]-filter to the spec lemma's [raw_equiv]-filter *)
  filter_ext
    (fun (e: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) -> not (NMR.key_equiv (fst e) vk_raw))
    (fun (e: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) -> not (SpecRaw.raw_equiv (fst e) vk_raw))
    entries;
  let filtered = L.filter (fun (e: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
                             not (SpecRaw.raw_equiv (fst e) vk_raw)) entries in
  assert (NMR.map_payload xh_result == filtered);
  assert (SpecRawBase.Map?.v xh_result == filtered);
  let len' : (l: SpecRawBase.raw_uint64 { U64.v l.value == L.length filtered }) =
    SpecRawBase.Map?.len xh_result in
  assert (SpecRawBase.Map len entries == xh);
  assert (SpecRawBase.Map len' filtered == xh_result);
  SpecMapRemove.mk_cbor_map_remove len entries vk_raw len';
  SAT.cbor_map_filter_ext
    (fun (kv: (Spec.cbor & Spec.cbor)) -> not (fst kv = SpecRaw.mk_cbor vk_raw))
    (fun (kv: (Spec.cbor & Spec.cbor)) -> not (fst kv = vk))
    (Spec.CMap?.c (Spec.unpack y))

#pop-options

(* ============================================================
   Pulse wrapper around the verified raw NONDET map remove-by-key.
   ============================================================ *)

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_nondet_map_remove_bridge
  (x key: cbor_nondet_t)
  (r1 r2 r3 r4: R.ref (IT.mixed_list U64.t cbor_map_entry))
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
{
  (* Expose the raw [cbor_match] resources for the verified raw core, together
     with the trades that restore each nondet match. *)
  let xh = RN.cbor_nondet_match_elim x;
  let vkr = RN.cbor_nondet_match_elim key;
  (* [CMap? (unpack (mk_cbor xh))] forces [xh] to be a [Map]. *)
  SpecRaw.mk_cbor_eq (Ghost.reveal xh);
  assert (pure (SpecRawBase.Map? (Ghost.reveal xh)));
  (* Run the verified raw wrapper (implicits inferred from the raw matches). *)
  let res = NMR.cbor_raw_nondet_map_remove x key r1 r2 r3 r4;
  with xh_result. assert (
    RawMatch.cbor_match 1.0R res xh_result **
    Trade.trade
      (RawMatch.cbor_match 1.0R res xh_result)
      (RawMatch.cbor_match p x (Ghost.reveal xh) **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4))
  );
  (* Restore the key nondet match (returned OUTSIDE the result trade). *)
  Trade.elim (RawMatch.cbor_match pk key (Ghost.reveal vkr)) (cbor_nondet_match pk key vk);
  (* Bridge the raw post to the abstract [cbor_map_filter]. *)
  remove_bridge_lemma (Ghost.reveal xh) xh_result (Ghost.reveal vkr)
                      (Ghost.reveal y) (Ghost.reveal vk) (SpecRaw.mk_cbor xh_result);
  (* Fold the raw result into a nondet match (at half permission), obtaining the
     trade back to the raw match. *)
  RN.cbor_nondet_match_intro res;
  (* Chain: nondet_result -> raw_result -> (raw x ** refs) -> (nondet x ** refs). *)
  Trade.trans
    (cbor_nondet_match (1.0R /. 2.0R) res (SpecRaw.mk_cbor xh_result))
    (RawMatch.cbor_match 1.0R res xh_result)
    (RawMatch.cbor_match p x (Ghost.reveal xh) **
     (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4));
  Trade.trans_concl_l
    (cbor_nondet_match (1.0R /. 2.0R) res (SpecRaw.mk_cbor xh_result))
    (RawMatch.cbor_match p x (Ghost.reveal xh))
    (cbor_nondet_match p x y)
    (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4);
  res
}

#pop-options
