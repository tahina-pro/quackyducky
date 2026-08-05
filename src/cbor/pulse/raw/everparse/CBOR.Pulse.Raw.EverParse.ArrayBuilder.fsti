module CBOR.Pulse.Raw.EverParse.ArrayBuilder
#lang-pulse
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Optimal
open Pulse.Lib.Pervasives

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
(* ================================================================ *)

let minimal_len_size (len: U64.t) : integer_size =
  (mk_raw_uint64 len).size

val minimal_len_size_prop (len: U64.t)
  : Lemma (raw_uint64_size_prop (minimal_len_size len) len)

(* ================================================================ *)
(* Ownership predicate for a structural (_Gen) CBOR array           *)
(*                                                                  *)
(* [cbor_array_owned x l] states that [x] is a fully-owned          *)
(* (structural permission 1.0R), minimal-length-encoded [_Gen]      *)
(* array whose spec-level element list is [l].                      *)
(* ================================================================ *)

val cbor_array_owned (x: cbor_mixed_list_array) (l: list raw_data_item) : slprop

(* The length of an owned array fits in a u64.  Used by callers to    *)
(* discharge the [fits] refinement that [finalize]/[append] require.  *)
val cbor_array_owned_length_fits
  (x: cbor_mixed_list_array) (#l: Ghost.erased (list raw_data_item))
: stt_ghost unit emp_inames
    (cbor_array_owned x l)
    (fun _ -> cbor_array_owned x l **
      pure (FStar.UInt.fits (List.Tot.length (Ghost.reveal l)) 64))

(* ================================================================ *)
(* Empty array: O(1), no allocation                                 *)
(* ================================================================ *)

val cbor_array_empty (_: unit)
: stt cbor_mixed_list_array emp (fun res -> cbor_array_owned res [])

(* ================================================================ *)
(* Singleton array: O(1), stores [x] into caller-supplied ref [ry]  *)
(* ================================================================ *)

val cbor_array_singleton
  (x: cbor_raw) (ry: R.ref cbor_raw)
  (#pm: perm) (#v: Ghost.erased raw_data_item) (#w0: Ghost.erased cbor_raw)
: stt cbor_mixed_list_array
    (cbor_match pm x v ** R.pts_to ry w0)
    (fun res ->
      cbor_array_owned res [Ghost.reveal v] **
      Trade.trade
        (cbor_array_owned res [Ghost.reveal v])
        (cbor_match pm x v ** (exists* w. R.pts_to ry w)))

(* ================================================================ *)
(* Append two arrays: O(1), nests under a fresh Append node, using   *)
(* the caller-supplied refs [r_before]/[r_after].  Returns [None] if  *)
(* the combined length would not fit in a u64.                        *)
(*                                                                    *)
(* Element counts are now [U64.t] (the CBOR wire count type), so the   *)
(* [Append] node's [io.fits (len1 + len2)] obligation is exactly the   *)
(* plain u64 non-overflow test performed at runtime; no [SZ.fits_u64]  *)
(* platform assumption is required.                                    *)
(* ================================================================ *)

val cbor_array_append
  (x1 x2: cbor_mixed_list_array)
  (r_before r_after: R.ref (IT.mixed_list U64.t cbor_raw))
  (#l1 #l2: Ghost.erased (list raw_data_item))
  (#vb0 #va0: Ghost.erased (IT.mixed_list U64.t cbor_raw))
: stt (option cbor_mixed_list_array)
    (cbor_array_owned x1 l1 ** cbor_array_owned x2 l2 **
     R.pts_to r_before vb0 ** R.pts_to r_after va0)
    (fun res ->
      match res with
      | None ->
        cbor_array_owned x1 l1 ** cbor_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
        pure (~ (FStar.UInt.fits
          (List.Tot.length (Ghost.reveal l1) + List.Tot.length (Ghost.reveal l2)) 64))
      | Some r ->
        cbor_array_owned r (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)) **
        Trade.trade
          (cbor_array_owned r (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
          (cbor_array_owned x1 l1 ** cbor_array_owned x2 l2 **
           (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))

(* ================================================================ *)
(* Finalize: turn an owned array handle into a full cbor_raw, with a *)
(* trade back to the handle.                                          *)
(*                                                                    *)
(* NOTE (deviation): the array result is packaged in the predicate    *)
(* [cbor_array_finalized] below (a transparent [let]) instead of an    *)
(* inline [exists*] in the [ensures].  This is NECESSARY: Pulse's [fn] *)
(* [ensures] elaboration cannot scope a refined [exists*] binder over  *)
(* a dependent type (here [Array len l] requires                       *)
(* [length l == U64.v len.value] at the TYPE level, only available     *)
(* from the binder refinement).  Wrapping the [exists*] in a top-level *)
(* [let]-defined slprop (checked by F* core, which does scope the      *)
(* binder) sidesteps the limitation; callers unfold it as usual.       *)
(* ================================================================ *)

(* [cbor_array_finalized x y l]: [y] is the full [cbor_raw] view of the *)
(* owned array [x] (elements [l]), together with a trade returning the  *)
(* ownership of [x].  The existential [len] is the minimal-length       *)
(* encoding of the element count.                                       *)
let cbor_array_finalized
  (x: cbor_mixed_list_array) (y: cbor_raw) (l: list raw_data_item)
: slprop
= exists* (len: (len: raw_uint64 { U64.v len.value == List.Tot.length l })).
    cbor_match 1.0R y (Array len l) **
    Trade.trade
      (cbor_match 1.0R y (Array len l))
      (cbor_array_owned x l) **
    pure ((len <: raw_uint64) == mk_raw_uint64 len.value)

val cbor_array_finalize
  (x: cbor_mixed_list_array) (#l: Ghost.erased (list raw_data_item))
: stt cbor_raw
    (cbor_array_owned x l)
    (fun y ->
      cbor_array_finalized x y (Ghost.reveal l) **
      pure (y == CBOR_Case_Array_Gen x))

(* ================================================================ *)
(* Finalize with a caller-chosen length encoding [len].              *)
(*                                                                   *)
(* Identical to [cbor_array_finalize] except the resulting           *)
(* [cbor_raw] carries the length header [len] supplied by the caller *)
(* (which need NOT be the minimal encoding), so that a deep-copy can  *)
(* reproduce a source array's EXACT (possibly non-canonical) length   *)
(* header.  The element count [U64.v len.value] must equal the number *)
(* of elements (enforced by [cbor_array_len_ok] on [l]).             *)
(*                                                                   *)
(* The postcondition [cbor_array_finalized_val] exposes the CONCRETE  *)
(* match on the whole (refined) array value [Array len l] with NO     *)
(* existential length witness, so a consumer can [unfold] it and then *)
(* relabel the match to a known array value without a Skolem length   *)
(* defeating downstream [Trade.trans] frame inference.               *)
(* ================================================================ *)

(* Precondition wrapper: [x] owns [l] AND [len] is a (possibly           *)
(* non-minimal) encoding of the element count.  The [U64.v]/[nat]        *)
(* comparison is deliberately kept inside this transparent [let] so that *)
(* its [do_not_unrefine] coercion is elaborated by F* core rather than   *)
(* Pulse's [fn] signature elaboration (which either rejects it as        *)
(* "Ill-typed" for the [uint]-left order, or loops on the [nat]-left     *)
(* order when matching the reflexive precondition).                      *)
let cbor_array_owned_with_len
  (x: cbor_mixed_list_array) (len: raw_uint64) (l: list raw_data_item)
: slprop
= cbor_array_owned x l ** pure (U64.v len.value == List.Tot.length l)

(* [cbor_array_len_ok len l]: [len] is a (possibly non-minimal) encoding of the *)
(* element count of [l].  Wrapped in a top-level [prop]-returning [let] so that  *)
(* it can appear as a refinement on the [#l] binder of                          *)
(* [cbor_array_finalize_with_len] WITHOUT tripping Pulse's [fn] signature        *)
(* elaboration on the raw [U64.v _ == length _] comparison (which mis-handles    *)
(* the [do_not_unrefine] coercion; the wrapper defers it to F* core / SMT).      *)
let cbor_array_len_ok (len: raw_uint64) (l: list raw_data_item) : prop
= U64.v len.value == List.Tot.length l

(* [cbor_array_finalized_val x y a]: concrete-match finalize result for the     *)
(* WHOLE (erased) array value [a] (refined [Array? a]).  It carries NO           *)
(* existential length witness: [a] is a refined parameter, so [cbor_match 1.0R   *)
(* y a] typechecks directly and a consumer that [unfold]s it obtains a match on  *)
(* the concrete [a] (no Skolem length that would defeat downstream               *)
(* [Trade.trans] frame inference).                                               *)
let cbor_array_finalized_val
  (x: cbor_mixed_list_array) (y: cbor_raw) (a: (a: raw_data_item { Array? a }))
: slprop
= cbor_match 1.0R y a **
  Trade.trade
    (cbor_match 1.0R y a)
    (cbor_array_owned x (Array?.v a))

val cbor_array_finalize_with_len
  (x: cbor_mixed_list_array)
  (len: raw_uint64)
  (#l: Ghost.erased (l: list raw_data_item { cbor_array_len_ok len l }))
: stt cbor_raw
    (cbor_array_owned_with_len x len (Ghost.reveal l))
    (fun y ->
      cbor_array_finalized_val x y (Array len (Ghost.reveal l)))

(* ================================================================ *)
(* cbor_array_borrow_entries / cbor_array_init                      *)
(*                                                                  *)
(* View an existing ARRAY [x] (ANY of the three representations:    *)
(* inline [CBOR_Case_Array], serialized [CBOR_Case_Serialized_Array],*)
(* or structural [CBOR_Case_Array_Gen]) as a [mixed_list] of        *)
(* elements, together with a trade back to [cbor_match].            *)
(*                                                                  *)
(* Element vmatch: [cbor_match]; element parser:                    *)
(* [parse_raw_data_item].                                           *)
(*                                                                  *)
(* Unlike [MapBuilder.cbor_map_borrow_entries] (which yields an      *)
(* existentially-quantified FRACTIONAL ambient [pm']), the array     *)
(* borrow produces the ambient permission EXACTLY [1.0R]: the        *)
(* fractional part of the borrow is pushed into the mixed_list NODE  *)
(* permissions [sp]/[sv], so the result is directly composable with  *)
(* [cbor_array_owned] / the O(1) builders, which all fix ambient     *)
(* [1.0R].                                                          *)
(* ================================================================ *)

(* Precondition restricting ONLY the structural [_Gen] case: its      *)
(* natural ambient is [pm *. gen_perm], and re-scaling an ARBITRARY   *)
(* mixed_list (which may contain [Append] nodes whose sub-lists live  *)
(* behind fractionally-owned references) to ambient [1.0R] is not a   *)
(* local operation.  We therefore require the effective permission of *)
(* a [_Gen] array to already be full.  The inline and serialized      *)
(* cases are unrestricted ([True]).                                   *)
let cbor_array_borrow_pre (pm: perm) (x: cbor_raw) : prop =
  match x with
  | CBOR_Case_Array_Gen v -> pm *. v.cbor_array_gen_perm == 1.0R
  | _ -> True

val cbor_array_borrow_entries
  (pm: perm) (x: cbor_raw)
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
: stt (IT.mixed_list U64.t cbor_raw)
    (cbor_match pm x (Ghost.reveal xh) **
     pure (cbor_array_borrow_pre pm x))
    (fun ml ->
      I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml
        (Array?.v (Ghost.reveal xh)) **
      Trade.trade
        (I.mixed_list_match cbor_match IO.u64_ops parse_raw_data_item 1.0R ml
          (Array?.v (Ghost.reveal xh)))
        (cbor_match pm x (Ghost.reveal xh)))

(* Package the borrowed mixed_list into an owned array handle          *)
(* [cbor_mixed_list_array] at ambient/record permission [1.0R], with a *)
(* trade back to [cbor_match].                                          *)
(*                                                                      *)
(* TOTAL: handles ALL three array representations (inline               *)
(* [CBOR_Case_Array], serialized [CBOR_Case_Serialized_Array], and      *)
(* structural [CBOR_Case_Array_Gen]) at ANY permission [pm].  Unlike    *)
(* [cbor_array_borrow_entries], NO [cbor_array_borrow_pre] restriction  *)
(* is required: the structural [_Gen] case (whose natural ambient is    *)
(* the possibly-fractional [pm *. gen_perm]) is re-scaled to ambient    *)
(* [1.0R] using [LowParse.PulseParse.Iterator.Append.mixed_list_wrap_   *)
(* scaled], which consumes the two caller-supplied scratch references   *)
(* [r1]/[r2] into a fresh full-ownership [Append] node.  The inline and *)
(* serialized cases already produce an ambient-[1.0R] mixed_list, so    *)
(* they simply frame [r1]/[r2] through unused.  In all cases the refs   *)
(* are returned (existentially) as part of the trade back.             *)
val cbor_array_init
  (pm: perm) (x: cbor_raw)
  (r1 r2: R.ref (IT.mixed_list U64.t cbor_raw))
  (#xh: Ghost.erased (r: raw_data_item { Array? r }))
  (#w1 #w2: Ghost.erased (IT.mixed_list U64.t cbor_raw))
: stt cbor_mixed_list_array
    (cbor_match pm x (Ghost.reveal xh) ** R.pts_to r1 w1 ** R.pts_to r2 w2)
    (fun y ->
      cbor_array_owned y (Array?.v (Ghost.reveal xh)) **
      Trade.trade
        (cbor_array_owned y (Array?.v (Ghost.reveal xh)))
        (cbor_match pm x (Ghost.reveal xh) ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)))
