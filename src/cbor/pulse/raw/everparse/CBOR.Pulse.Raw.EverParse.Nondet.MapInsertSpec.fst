module CBOR.Pulse.Raw.EverParse.Nondet.MapInsertSpec
#lang-pulse
friend CBOR.Pulse.Raw.Nondet
friend CBOR.Pulse.API.Nondet.Type
(* Needed so that the abstract [cbor_nondet_map_entry_insert_cell_t] declared in
   the raw/-relocated .fsti unfolds (via Nondet.Type -> ML.cbor_raw_mixed_list,
   then MixedList -> IT.mixed_list) to the concrete [IT.mixed_list cbor_map_entry]
   used in the ref types below.  Ref types unchanged. *)
friend CBOR.Pulse.Raw.Format.MixedList

(* NOTE on the Some-branch result value (same rationale as the DET analogue):

   The specification-level result of prepending (vk, vv) to the map [y] is
   [Spec.pack (Spec.CMap (cbor_map_union (CMap?.c (unpack y)) (singleton vk vv)))].
   Writing [Spec.CMap (...)] literally in the [ensures] triggers the refinement
   obligation [FStar.UInt.fits (cbor_map_length (...)) U64.n] at the
   ensures-well-formedness stage, which cannot be discharged abstractly.  We
   therefore use the EXISTENTIAL form: we existentially quantify a spec value
   [vres : Spec.cbor] and merely assert, as a pure fact, that [CMap? (unpack vres)]
   holds and that [CMap?.c (unpack vres)] equals the union map.  This avoids ever
   writing [Spec.CMap (...)] literally and is equally strong for callers. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Nondet
open CBOR.Pulse.Raw.Type

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module SpecRawBase = CBOR.Spec.Raw.Base
module MapPrepend = CBOR.Spec.Raw.MapPrepend
module Valid = CBOR.Spec.Raw.Valid
module MI = CBOR.Pulse.Raw.EverParse.Nondet.MapInsert
module RawMatch = CBOR.Pulse.Raw.Match
module RN = CBOR.Pulse.Raw.Nondet
module IT = LowParse.PulseParse.Iterator.Type
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module U64 = FStar.UInt64
module SZ = FStar.SizeT

(* ============================================================
   Pure spec-level bridge lemmas.
   ============================================================ *)

#push-options "--z3rlimit 8 --fuel 2 --ifuel 2"

(* Some-branch bridge: relates the raw prepend result [xh_result] to the
   abstract left-biased union.  Key ingredient: [MapPrepend.mk_cbor_map_prepend]
   (which needs key-absence, itself derived from validity of [xh_result]). *)
let some_bridge
  (xh xh_result vk_raw vv_raw: SpecRawBase.raw_data_item)
  (y vk vv vres: Spec.cbor)
: Lemma
  (requires (
    SpecRawBase.Map? xh /\ Valid.valid_raw_data_item xh == true /\ SpecRaw.mk_cbor xh == y /\
    SpecRawBase.Map? xh_result /\ Valid.valid_raw_data_item xh_result == true /\
      SpecRaw.mk_cbor xh_result == vres /\
    MI.map_payload xh_result == (vk_raw, vv_raw) :: MI.map_payload xh /\
    Valid.valid_raw_data_item vk_raw == true /\ SpecRaw.mk_cbor vk_raw == vk /\
    Valid.valid_raw_data_item vv_raw == true /\ SpecRaw.mk_cbor vv_raw == vv /\
    Spec.CMap? (Spec.unpack y)
  ))
  (ensures (
    Spec.CMap? (Spec.unpack vres) /\
    (Spec.CMap?.c (Spec.unpack vres) <: Spec.cbor_map) ==
      Spec.cbor_map_union (Spec.CMap?.c (Spec.unpack y)) (Spec.cbor_map_singleton vk vv)
  ))
= let len = SpecRawBase.Map?.len xh in
  let entries : SpecRawBase.nlist (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item) (U64.v len.value) =
    SpecRawBase.Map?.v xh in
  (* Payload equalities. *)
  assert (MI.map_payload xh == entries);
  assert (MI.map_payload xh_result == SpecRawBase.Map?.v xh_result);
  assert (SpecRawBase.Map?.v xh_result == (vk_raw, vv_raw) :: entries);
  (* Length header of the result is one more than that of the input. *)
  assert (L.length (SpecRawBase.Map?.v xh_result) == U64.v (SpecRawBase.Map?.len xh_result).value);
  assert (L.length entries == U64.v len.value);
  assert (U64.v (SpecRawBase.Map?.len xh_result).value == 1 + U64.v len.value);
  let len' : (l: SpecRawBase.raw_uint64 { U64.v l.value == 1 + U64.v len.value }) =
    SpecRawBase.Map?.len xh_result in
  (* Reconstruct the raw maps as literal [Map] applications. *)
  assert (SpecRawBase.Map len entries == xh);
  assert (SpecRawBase.Map len' ((vk_raw, vv_raw) :: entries) == xh_result);
  (* Key-absence follows from validity of the (valid) prepended map. *)
  Valid.valid_eq Valid.basic_data_model (SpecRawBase.Map len' ((vk_raw, vv_raw) :: entries));
  assert (~ (L.existsb (Valid.raw_equiv vk_raw) (L.map fst entries)));
  (* The union lemma. *)
  MapPrepend.mk_cbor_map_prepend len entries vk_raw vv_raw len'

(* None-branch bridge: the raw None-disjunction (existsb dup-key OR u64
   overflow) implies the Spec-level None-disjunction
   ([cbor_map_defined] OR overflow). *)
let none_bridge
  (xh vk_raw: SpecRawBase.raw_data_item)
  (y vk: Spec.cbor)
: Lemma
  (requires (
    SpecRawBase.Map? xh /\ Valid.valid_raw_data_item xh == true /\ SpecRaw.mk_cbor xh == y /\
    Valid.valid_raw_data_item vk_raw == true /\ SpecRaw.mk_cbor vk_raw == vk /\
    Spec.CMap? (Spec.unpack y) /\
    (L.existsb (Valid.raw_equiv vk_raw) (L.map fst (MI.map_payload xh)) \/
     ~ (FStar.UInt.fits (L.length (MI.map_payload xh) + 1) 64))
  ))
  (ensures (
    Spec.cbor_map_defined vk (Spec.CMap?.c (Spec.unpack y)) \/
    ~ (FStar.UInt.fits (Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) + 1) U64.n)
  ))
= let len = SpecRawBase.Map?.len xh in
  let entries : SpecRawBase.nlist (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item) (U64.v len.value) =
    SpecRawBase.Map?.v xh in
  assert (MI.map_payload xh == entries);
  assert (SpecRawBase.Map len entries == xh);
  (* cbor_map_length (unpack y).c == length of the raw entry list. *)
  SpecRaw.mk_cbor_eq xh;
  (* existsb ==> cbor_map_defined (dual reasoning). *)
  FStar.Classical.move_requires (MapPrepend.mk_cbor_map_defined_of_existsb len entries) vk_raw

#pop-options

(* ============================================================
   Pulse wrapper around the verified raw NONDET map-entry prepend.
   ============================================================ *)

#push-options "--z3rlimit 8 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_nondet_map_entry_insert_spec
  (f64: squash SZ.fits_u64)
  (x key value: cbor_nondet_t)
  (r1 r2: R.ref (IT.mixed_list cbor_map_entry))
  (ry: R.ref cbor_map_entry)
  (#p: perm) (#y: Ghost.erased (v: Spec.cbor { Spec.CMap? (Spec.unpack v) }))
  (#pkv: perm) (#vk #vv: Ghost.erased Spec.cbor)
requires
  cbor_nondet_match p x y **
  cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
  (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy) **
  pure (Spec.CMap? (Spec.unpack y))
returns res: option cbor_nondet_t
ensures (match res with
  | None ->
    cbor_nondet_match p x y **
    cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
    (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy) **
    pure (Spec.cbor_map_defined vk (Spec.CMap?.c (Spec.unpack y)) \/
          ~ (FStar.UInt.fits (Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) + 1) U64.n))
  | Some m ->
    exists* (p_res: perm) (vres: Spec.cbor).
      cbor_nondet_match p_res m vres **
      Trade.trade
        (cbor_nondet_match p_res m vres)
        (cbor_nondet_match p x y **
         cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy)) **
      pure (Spec.CMap? (Spec.unpack vres) /\
            (Spec.CMap?.c (Spec.unpack vres) <: Spec.cbor_map) ==
              Spec.cbor_map_union (Spec.CMap?.c (Spec.unpack y)) (Spec.cbor_map_singleton vk vv)))
{
  (* Expose the raw [cbor_match] resources for the verified raw core, together
     with the trades that restore each nondet match. *)
  let xh = RN.cbor_nondet_match_elim x;
  let vkr = RN.cbor_nondet_match_elim key;
  let vvr = RN.cbor_nondet_match_elim value;
  (* [CMap? (unpack (mk_cbor xh))] forces [xh] to be a [Map]. *)
  SpecRaw.mk_cbor_eq (Ghost.reveal xh);
  assert (pure (SpecRawBase.Map? (Ghost.reveal xh)));
  (* Run the verified raw core (implicits inferred from the raw matches). *)
  let res = MI.cbor_raw_nondet_map_entry_insert f64 x key value r1 r2 ry;
  match res {
    None -> {
      none_bridge (Ghost.reveal xh) (Ghost.reveal vkr) (Ghost.reveal y) (Ghost.reveal vk);
      (* Restore the three nondet matches from the raw matches. *)
      Trade.elim (RawMatch.cbor_match p x (Ghost.reveal xh)) (cbor_nondet_match p x y);
      Trade.elim (RawMatch.cbor_match pkv key (Ghost.reveal vkr)) (cbor_nondet_match pkv key vk);
      Trade.elim (RawMatch.cbor_match pkv value (Ghost.reveal vvr)) (cbor_nondet_match pkv value vv);
      None #cbor_nondet_t
    }
    Some m -> {
      with pm_result xh_result. assert (
        RawMatch.cbor_match pm_result m xh_result **
        Trade.trade
          (RawMatch.cbor_match pm_result m xh_result)
          (RawMatch.cbor_match p x (Ghost.reveal xh) **
           RawMatch.cbor_match pkv key (Ghost.reveal vkr) **
           RawMatch.cbor_match pkv value (Ghost.reveal vvr) **
           (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy))
      );
      some_bridge (Ghost.reveal xh) xh_result (Ghost.reveal vkr) (Ghost.reveal vvr)
                  (Ghost.reveal y) (Ghost.reveal vk) (Ghost.reveal vv) (SpecRaw.mk_cbor xh_result);
      (* Fold the raw result into a nondet match (at half permission), obtaining
         the trade back to the raw match. *)
      RN.cbor_nondet_match_intro m;
      (* Build the restore trade from the nondet result to the three nondet
         inputs, by chaining: nondet_result -> raw_result -> raw_inputs ->
         nondet_inputs. *)
      Trade.intro_trade
        (cbor_nondet_match (pm_result /. 2.0R) m (SpecRaw.mk_cbor xh_result))
        (cbor_nondet_match p x y **
         cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy))
        (Trade.trade
           (cbor_nondet_match (pm_result /. 2.0R) m (SpecRaw.mk_cbor xh_result))
           (RawMatch.cbor_match pm_result m xh_result) **
         Trade.trade
           (RawMatch.cbor_match pm_result m xh_result)
           (RawMatch.cbor_match p x (Ghost.reveal xh) **
            RawMatch.cbor_match pkv key (Ghost.reveal vkr) **
            RawMatch.cbor_match pkv value (Ghost.reveal vvr) **
            (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy)) **
         Trade.trade
           (RawMatch.cbor_match p x (Ghost.reveal xh)) (cbor_nondet_match p x y) **
         Trade.trade
           (RawMatch.cbor_match pkv key (Ghost.reveal vkr)) (cbor_nondet_match pkv key vk) **
         Trade.trade
           (RawMatch.cbor_match pkv value (Ghost.reveal vvr)) (cbor_nondet_match pkv value vv))
        fn _ {
          Trade.elim
            (cbor_nondet_match (pm_result /. 2.0R) m (SpecRaw.mk_cbor xh_result))
            (RawMatch.cbor_match pm_result m xh_result);
          Trade.elim
            (RawMatch.cbor_match pm_result m xh_result)
            (RawMatch.cbor_match p x (Ghost.reveal xh) **
             RawMatch.cbor_match pkv key (Ghost.reveal vkr) **
             RawMatch.cbor_match pkv value (Ghost.reveal vvr) **
             (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy));
          Trade.elim (RawMatch.cbor_match p x (Ghost.reveal xh)) (cbor_nondet_match p x y);
          Trade.elim (RawMatch.cbor_match pkv key (Ghost.reveal vkr)) (cbor_nondet_match pkv key vk);
          Trade.elim (RawMatch.cbor_match pkv value (Ghost.reveal vvr)) (cbor_nondet_match pkv value vv);
        };
      Some #cbor_nondet_t m
    }
  }
}

#pop-options
