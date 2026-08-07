module CBOR.Pulse.API.Det.C
#lang-pulse
include CBOR.Pulse.API.Det.Type
include CBOR.Pulse.API.Det.Dummy
include CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.Constants

module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8

module SU = Pulse.Lib.Slice.Util
module AP = Pulse.Lib.ArrayPtr
module R = Pulse.Lib.Reference
module L = FStar.List.Tot

val cbor_det_match: perm -> cbor_det_t -> Spec.cbor -> slprop

val cbor_det_reset_perm () : reset_perm_t cbor_det_match

val cbor_det_share () : share_t cbor_det_match
val cbor_det_gather () : gather_t cbor_det_match

val cbor_det_validate
  (input: AP.ptr U8.t)
  (input_len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (pts_to input #pm v ** pure (SZ.v input_len == Seq.length v))
    (fun res -> pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))

val cbor_det_parse
  (input: AP.ptr U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt cbor_det_t
    (pts_to input #pm v ** pure (
      exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    ))
    (fun res -> exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade (cbor_det_match 1.0R res v') (pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == Spec.cbor_det_serialize v'
    ))

val cbor_det_size
  (x: cbor_det_t)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt SZ.t
    (cbor_det_match pm x y)
    (fun res -> cbor_det_match pm x y ** pure (
      cbor_det_size_post bound y res
    ))

val cbor_det_serialize
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt SZ.t
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
    (fun res -> exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      SZ.v output_len == Seq.length v /\
      cbor_det_serialize_fits_postcond y res v
    ))

val cbor_det_serialize_safe
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
: stt SZ.t
    (cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
    (fun res -> exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      SZ.v output_len == Seq.length v' /\
      cbor_det_serialize_postcond_c y v v' res
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_serialize_to_slice
  (x: cbor_det_t)
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (Seq.length (Spec.cbor_det_serialize y) <= SZ.v (S.len output)))
returns res: SZ.t
ensures
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      cbor_det_serialize_fits_postcond y res v
    ))
{
  S.pts_to_len output;
  let len = S.len output;
  let ou = S.slice_to_arrayptr_intro output;
  let res = cbor_det_serialize x ou len;
  S.slice_to_arrayptr_elim ou;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_impl_utf8_correct_from_array_t =
  (s: AP.ptr U8.t) ->
  (len: SZ.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to s #p v ** pure (SZ.v len == Seq.length v))
    (fun res -> pts_to s #p v ** pure (res == CBOR.Spec.API.UTF8.correct v))

val cbor_det_impl_utf8_correct_from_array (_: unit) : cbor_det_impl_utf8_correct_from_array_t

(* Constructors *)

val cbor_det_mk_simple_value () : mk_simple_t cbor_det_match
val cbor_det_mk_int64 () : mk_int64_t cbor_det_match
val cbor_det_mk_tagged () : mk_tagged_t cbor_det_match

val cbor_det_mk_byte_string_from_arrayptr (_: unit) : mk_string_from_arrayptr_t cbor_det_match cbor_major_type_byte_string

val cbor_det_mk_text_string_from_arrayptr (_: unit) : mk_string_from_arrayptr_t cbor_det_match cbor_major_type_text_string

val cbor_det_mk_array_from_array (_: unit) : mk_array_from_array_t cbor_det_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_array_from_array' = mk_array_from_array' (cbor_det_mk_array_from_array ())

(* Structural array builder operations.

   These build CBOR arrays by O(1) structural composition (no element copy or
   re-encoding), on top of fully-owned arrays. [cbor_det_array_owned x l] means
   [x] is a fully-owned (permission 1.0R, canonical length encoding) CBOR array
   whose elements are [l]. Such arrays can be combined with [cbor_det_array_append]
   and turned back into a normal CBOR object with [cbor_det_array_finalize].

   No heap allocation: the application provides the (fixed number of) scratch
   references the operations need. *)

val cbor_det_array_owned (x: cbor_det_array_t) (l: list Spec.cbor) : slprop

val cbor_det_array_init
  (x: cbor_det_t)
  (r1 r2: R.ref cbor_det_array_append_cell_t)
  (#p: perm)
  (#l: Ghost.erased Spec.cbor)
  (#w1 #w2: Ghost.erased cbor_det_array_append_cell_t)
: stt cbor_det_array_t
    (cbor_det_match p x l ** R.pts_to r1 w1 ** R.pts_to r2 w2 ** pure (Spec.CArray? (Spec.unpack l)))
    (fun y ->
      exists* (l' : list Spec.cbor) .
        cbor_det_array_owned y l' **
        Trade.trade
          (cbor_det_array_owned y l')
          (cbor_det_match p x l ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)) **
        pure (Spec.CArray? (Spec.unpack l) /\ l' == Spec.CArray?.v (Spec.unpack l))
    )

val cbor_det_array_empty (_: unit)
: stt cbor_det_array_t
    emp
    (fun res -> cbor_det_array_owned res [])

val cbor_det_array_singleton
  (x: cbor_det_t) (ry: R.ref cbor_det_t)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_det_t)
: stt cbor_det_array_t
    (cbor_det_match pm x v ** R.pts_to ry w0)
    (fun res ->
      cbor_det_array_owned res [Ghost.reveal v] **
      Trade.trade
        (cbor_det_array_owned res [Ghost.reveal v])
        (cbor_det_match pm x v ** (exists* w. R.pts_to ry w)))

(* [cbor_det_array_append] appends [x2] onto [x1], writing the combined
   array into the outparameter [dest] and returning [true] on success.
   On overflow (the combined element count would not fit in a [U64.t]) it
   returns [false] and leaves [dest] unchanged. *)

let cbor_det_array_append_post_true
  (x1 x2: cbor_det_array_t)
  (r_before r_after: R.ref cbor_det_array_append_cell_t)
  (l1 l2: list Spec.cbor)
  (vdest': cbor_det_array_t)
: Tot slprop
= cbor_det_array_owned vdest' (L.append l1 l2) **
  Trade.trade
    (cbor_det_array_owned vdest' (L.append l1 l2))
    (cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va))

let cbor_det_array_append_post_false
  (x1 x2: cbor_det_array_t)
  (r_before r_after: R.ref cbor_det_array_append_cell_t)
  (l1 l2: list Spec.cbor)
  (vdest vdest': cbor_det_array_t)
: Tot slprop
= cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
  (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
  pure (vdest' == vdest /\ ~ (FStar.UInt.fits (L.length l1 + L.length l2) U64.n))

let cbor_det_array_append_post
  (x1 x2: cbor_det_array_t)
  (r_before r_after: R.ref cbor_det_array_append_cell_t)
  (l1 l2: list Spec.cbor)
  (vdest vdest': cbor_det_array_t)
  (res: bool)
: Tot slprop
= if res
  then cbor_det_array_append_post_true x1 x2 r_before r_after l1 l2 vdest'
  else cbor_det_array_append_post_false x1 x2 r_before r_after l1 l2 vdest vdest'

val cbor_det_array_append
  (x1 x2: cbor_det_array_t)
  (dest: R.ref cbor_det_array_t)
  (r_before r_after: R.ref cbor_det_array_append_cell_t)
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vdest: Ghost.erased cbor_det_array_t)
  (#vb0 #va0: Ghost.erased cbor_det_array_append_cell_t)
: stt bool
    (cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
     R.pts_to dest vdest ** R.pts_to r_before vb0 ** R.pts_to r_after va0)
    (fun res -> exists* (vdest': cbor_det_array_t).
       R.pts_to dest vdest' **
       cbor_det_array_append_post x1 x2 r_before r_after l1 l2 vdest vdest' res)

val cbor_det_array_finalize
  (x: cbor_det_array_t)
  (#l: Ghost.erased (list Spec.cbor))
: stt cbor_det_t
    (cbor_det_array_owned x l)
    (fun y ->
      exists* (l': (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n })).
        cbor_det_match 1.0R y (Spec.pack (Spec.CArray l')) **
        Trade.trade
          (cbor_det_match 1.0R y (Spec.pack (Spec.CArray l')))
          (cbor_det_array_owned x l) **
        pure ((l' <: list Spec.cbor) == Ghost.reveal l))

(* The length of an owned array fits in a u64; lets callers discharge the
   refinement of [cbor_det_array_finalize] after a chain of [cbor_det_array_append]s. *)
val cbor_det_array_owned_length_fits
  (x: cbor_det_array_t) (#l: Ghost.erased (list Spec.cbor))
: stt_ghost unit emp_inames
    (cbor_det_array_owned x l)
    (fun _ -> cbor_det_array_owned x l **
      pure (FStar.UInt.fits (L.length (Ghost.reveal l)) U64.n))

val cbor_det_map_entry_match: perm -> cbor_det_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_det_mk_map_entry () : mk_map_entry_t cbor_det_match cbor_det_map_entry_match

val cbor_det_mk_map_from_array : mk_map_from_array_t cbor_det_match cbor_det_map_entry_match

val cbor_det_mk_map_from_array_safe () : mk_map_from_array_safe_t cbor_det_match cbor_det_map_entry_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_map_from_array' = mk_map_from_array' cbor_det_mk_map_from_array

(* Destructors *)

val cbor_det_equal () : equal_t cbor_det_match
val cbor_det_major_type () : get_major_type_t cbor_det_match
val cbor_det_read_simple_value () : read_simple_value_t cbor_det_match
val cbor_det_elim_simple () : elim_simple_t cbor_det_match
val cbor_det_read_uint64 () : read_uint64_t cbor_det_match
val cbor_det_elim_int64 () : elim_int64_t cbor_det_match
val cbor_det_get_string_length () : get_string_length_t cbor_det_match
val cbor_det_get_tagged_tag () : get_tagged_tag_t cbor_det_match
val cbor_det_get_tagged_payload () : get_tagged_payload_t cbor_det_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_get_string_t
= (x: cbor_det_t) ->
  (#p: perm) ->
  (#y: Ghost.erased Spec.cbor) ->
  stt (AP.ptr FStar.UInt8.t)
    (cbor_det_match p x y ** pure (Spec.CString? (Spec.unpack y)))
    (fun res -> exists* p' v' .
      pts_to res #p' v' **
      Trade.trade
        (pts_to res #p' v')
        (cbor_det_match p x y) **
      pure (get_string_post y v')
    )

val cbor_det_get_string () : cbor_det_get_string_t


val cbor_det_get_array_length () : get_array_length_t cbor_det_match

val cbor_det_array_iterator_match : perm -> cbor_det_array_iterator_t -> list Spec.cbor -> slprop

val cbor_det_array_iterator_start () : array_iterator_start_t cbor_det_match cbor_det_array_iterator_match

val cbor_det_array_iterator_is_empty () : array_iterator_is_empty_t cbor_det_array_iterator_match

val cbor_det_array_iterator_length () : array_iterator_length_t cbor_det_array_iterator_match

val cbor_det_array_iterator_next () : array_iterator_next_t cbor_det_match cbor_det_array_iterator_match

val cbor_det_array_iterator_truncate () : array_iterator_truncate_t cbor_det_array_iterator_match

val cbor_det_array_iterator_share () : share_t cbor_det_array_iterator_match

val cbor_det_array_iterator_gather () : gather_t cbor_det_array_iterator_match

val cbor_det_get_array_item () : get_array_item_t cbor_det_match

(* ================================================================== *)
(* Zero-copy array sub-range (slice).                                 *)
(*                                                                    *)
(* [cbor_det_array_slice x i j r1 r2 r3 r4] produces the deterministic *)
(* array whose elements are the sub-range [i, j) of the input array   *)
(* [x], as a borrowed view (full-permission handle) together with a   *)
(* trade returning the borrow (and the four scratch references) to    *)
(* the source.  It is TOTAL over [i], [j]: if the requested range is  *)
(* empty or out of bounds it produces the EMPTY array.                *)
(*                                                                    *)
(* Realized on top of the raw/ adapter                                *)
(*   ADet = CBOR.Pulse.Raw.EverParse.Det.ArrayBuilder                 *)
(* (implementation in everparse/ delegates to the raw slice op        *)
(*  [CBOR.Pulse.Raw.EverParse.ArrayBuilder.cbor_array_slice]).        *)
(* ================================================================== *)

(* Specification of the slice at the deterministic-CBOR level: the     *)
(* sub-list of elements at indices [i, j) (empty when the range is     *)
(* empty or out of bounds).  Uses only [FStar.List.Tot] so the         *)
(* interface stays free of any raw/lowparse dependency.                *)
noextract [@@noextract_to "krml"]
let cbor_det_array_slice_spec (l: list Spec.cbor) (i j: U64.t) : list Spec.cbor =
  if U64.v i < U64.v j && U64.v j <= L.length l
  then fst (L.splitAt (U64.v j - U64.v i) (snd (L.splitAt (U64.v i) l)))
  else []

val cbor_det_array_slice
  (x: cbor_det_t) (i j: U64.t)
  (r1 r2 r3 r4: R.ref cbor_det_array_append_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_det_array_append_cell_t)
: stt cbor_det_t
    (cbor_det_match p x v ** R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4
       ** pure (Spec.CArray? (Spec.unpack v)))
    (fun res -> exists* (v': Spec.cbor).
       cbor_det_match 1.0R res v' **
       Trade.trade (cbor_det_match 1.0R res v')
         (cbor_det_match p x v ** (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
       pure (Spec.CArray? (Spec.unpack v) /\ Spec.CArray? (Spec.unpack v') /\
             (Spec.CArray?.v (Spec.unpack v') <: list Spec.cbor) == cbor_det_array_slice_spec (Spec.CArray?.v (Spec.unpack v)) i j))

(* Safe (no-precondition) variant: checks at runtime that [dest] is a  *)
(* non-null destination reference and that [x] is an array; on success *)
(* writes the sliced array into [dest] and returns [true]; otherwise   *)
(* leaves [dest] unchanged, retains ownership of [x] and the scratch   *)
(* references, and returns [false].                                    *)
let cbor_det_array_slice_safe_res
  (dest: R.ref cbor_det_t)
  (v: Spec.cbor)
: GTot bool
= not (R.is_null dest) && Spec.CArray? (Spec.unpack v)

let cbor_det_array_slice_safe_post_true
  (x: cbor_det_t) (i j: U64.t) (p: perm) (v: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_det_array_append_cell_t)
  (vdest': cbor_det_t)
: Tot slprop
= exists* (v': Spec.cbor).
    cbor_det_match 1.0R vdest' v' **
    Trade.trade
      (cbor_det_match 1.0R vdest' v')
      (cbor_det_match p x v **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
    pure (Spec.CArray? (Spec.unpack v) /\ Spec.CArray? (Spec.unpack v') /\
          (Spec.CArray?.v (Spec.unpack v') <: list Spec.cbor) == cbor_det_array_slice_spec (Spec.CArray?.v (Spec.unpack v)) i j)

let cbor_det_array_slice_safe_post_false
  (x: cbor_det_t) (p: perm) (v: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_det_array_append_cell_t)
  (w1 w2 w3 w4: cbor_det_array_append_cell_t)
  (vdest vdest': cbor_det_t)
: Tot slprop
= cbor_det_match p x v **
  R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
  pure (vdest' == vdest)

let cbor_det_array_slice_safe_post
  (x: cbor_det_t) (i j: U64.t) (dest: R.ref cbor_det_t) (p: perm) (v: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_det_array_append_cell_t)
  (w1 w2 w3 w4: cbor_det_array_append_cell_t)
  (vdest vdest': cbor_det_t)
: Tot slprop
= if cbor_det_array_slice_safe_res dest v
  then cbor_det_array_slice_safe_post_true x i j p v r1 r2 r3 r4 vdest'
  else cbor_det_array_slice_safe_post_false x p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest'

val cbor_det_array_slice_safe
  (x: cbor_det_t) (i j: U64.t)
  (dest: R.ref cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_array_append_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor) (#vdest: Ghost.erased cbor_det_t)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_det_array_append_cell_t)
: stt bool
    (cbor_det_match p x v ** ref_pts_to_or_null dest 1.0R vdest **
     R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)
    (fun res -> exists* (vdest': cbor_det_t).
       ref_pts_to_or_null dest 1.0R vdest' **
       cbor_det_array_slice_safe_post x i j dest p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest' **
       pure (res == cbor_det_array_slice_safe_res dest v))

val cbor_det_get_map_length () : get_map_length_t cbor_det_match

val cbor_det_map_iterator_match : perm -> cbor_det_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_det_map_iterator_start () : map_iterator_start_t cbor_det_match cbor_det_map_iterator_match

val cbor_det_map_iterator_is_empty () : map_iterator_is_empty_t cbor_det_map_iterator_match

val cbor_det_map_iterator_next () : map_iterator_next_t cbor_det_map_entry_match cbor_det_map_iterator_match

val cbor_det_map_iterator_share () : share_t cbor_det_map_iterator_match

val cbor_det_map_iterator_gather () : gather_t cbor_det_map_iterator_match

val cbor_det_map_entry_key () : map_entry_key_t cbor_det_map_entry_match cbor_det_match

val cbor_det_map_entry_value () : map_entry_value_t cbor_det_map_entry_match cbor_det_match

val cbor_det_map_entry_share () : share_t cbor_det_map_entry_match

val cbor_det_map_entry_gather () : gather_t cbor_det_map_entry_match

val cbor_det_map_get () : map_get_by_ref_t cbor_det_match

(* Structural map-entry insertion (sorted, deterministic) operating directly on
   a [cbor_det_t]. On success the resulting map is written into the
   outparameter [dest] and the operation returns [true]. It gracefully fails
   (returns [false], leaving [dest] unchanged) if [x] is not a map, if the key
   is already defined in the map, or if inserting the entry would overflow a
   u64 length.

   The entry (key, value) is inserted in canonical (sorted) position so that the
   result is still a valid deterministically-encoded CBOR map.

   No heap allocation: the application provides the (fixed number of) scratch
   references the operation needs, namely four
   [cbor_det_map_entry_insert_cell_t] references and one [cbor_det_map_entry_t]
   reference; use [dummy_cbor_det_map_entry_insert_cell] and
   [dummy_cbor_det_map_entry] to initialize them. *)
let cbor_det_map_entry_insert_refs
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (ry: R.ref cbor_det_map_entry_t)
: Tot slprop
= exists* w1 w2 w3 w4 wy.
    R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
    R.pts_to ry wy

(* Post-condition helpers, following the [_safe]-variant convention: on
   success ([res == true]) the outparameter holds the combined map together
   with a borrow trade returning ownership to the inputs and scratch refs; on
   failure ([res == false]) the inputs and scratch refs are retained and
   [dest] is unchanged. *)
let cbor_det_map_entry_insert_post_true
  (x key value: cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (ry: R.ref cbor_det_map_entry_t)
  (p: perm) (y: Spec.cbor)
  (pkv: perm) (vk vv: Spec.cbor)
  (vdest': cbor_det_t)
: Tot slprop
= exists* (p_res: perm) (vres: Spec.cbor).
    cbor_det_match p_res vdest' vres **
    Trade.trade
      (cbor_det_match p_res vdest' vres)
      (cbor_det_match p x y **
       cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
       (exists* w1 w2 w3 w4 wy.
          R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
          R.pts_to ry wy)) **
    pure (
      Spec.CMap? (Spec.unpack y) /\
      Spec.CMap? (Spec.unpack vres) /\
      (Spec.CMap?.c (Spec.unpack vres) <: Spec.cbor_map) ==
        Spec.cbor_map_union (Spec.CMap?.c (Spec.unpack y)) (Spec.cbor_map_singleton vk vv))

let cbor_det_map_entry_insert_post_false
  (x key value: cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (ry: R.ref cbor_det_map_entry_t)
  (p: perm) (y: Spec.cbor)
  (pkv: perm) (vk vv: Spec.cbor)
  (vdest vdest': cbor_det_t)
: Tot slprop
= cbor_det_match p x y **
  cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
  (exists* w1 w2 w3 w4 wy.
     R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
     R.pts_to ry wy) **
  pure (
    vdest' == vdest /\
    (~ (Spec.CMap? (Spec.unpack y)) \/
     (Spec.CMap? (Spec.unpack y) /\
       (Spec.cbor_map_defined vk (Spec.CMap?.c (Spec.unpack y)) \/
        ~ (FStar.UInt.fits (Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) + 1) U64.n)))))

let cbor_det_map_entry_insert_post
  (x key value: cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (ry: R.ref cbor_det_map_entry_t)
  (p: perm) (y: Spec.cbor)
  (pkv: perm) (vk vv: Spec.cbor)
  (vdest vdest': cbor_det_t)
  (res: bool)
: Tot slprop
= if res
  then cbor_det_map_entry_insert_post_true x key value r1 r2 r3 r4 ry p y pkv vk vv vdest'
  else cbor_det_map_entry_insert_post_false x key value r1 r2 r3 r4 ry p y pkv vk vv vdest vdest'

val cbor_det_map_entry_insert
  (x key value: cbor_det_t)
  (dest: R.ref cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (ry: R.ref cbor_det_map_entry_t)
  (#p: perm) (#y: Ghost.erased Spec.cbor)
  (#pkv: perm) (#vk #vv: Ghost.erased Spec.cbor)
  (#vdest: Ghost.erased cbor_det_t)
: stt bool
    (cbor_det_match p x y **
     cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
     R.pts_to dest vdest **
     cbor_det_map_entry_insert_refs r1 r2 r3 r4 ry)
    (fun res -> exists* (vdest': cbor_det_t).
       R.pts_to dest vdest' **
       cbor_det_map_entry_insert_post x key value r1 r2 r3 r4 ry p y pkv vk vv vdest vdest' res)

(* ================================================================== *)
(* Structural map remove-by-key (deterministic).                      *)
(*                                                                    *)
(* [cbor_det_map_remove x key r1 r2 r3 r4] removes the (unique) entry *)
(* whose key equals [key] from the deterministic-CBOR map [x],        *)
(* producing a full-permission handle to the resulting map together   *)
(* with a trade returning the borrow (and the four scratch            *)
(* references) to the source.  The operation ALWAYS returns a map: if *)
(* [key] is absent the result equals [x].  The key's ownership        *)
(* [cbor_det_match pk key vk] is returned OUTSIDE the trade           *)
(* (read-only).                                                       *)
(*                                                                    *)
(* Realized on top of the raw/ adapter                                *)
(*   DMRS = CBOR.Pulse.Raw.EverParse.Det.MapRemoveSpec.               *)
(* No heap allocation: the application provides four                  *)
(* [cbor_det_map_entry_insert_cell_t] scratch references (the same    *)
(* abstract cell type used by map insertion).                         *)
(* ================================================================== *)

(* Specification of remove-by-key at the deterministic-CBOR level: the *)
(* sub-map of entries whose key differs from [k].  The filter          *)
(* predicate closes over the CONCRETE key [k] (not a ghost value), so  *)
(* it is [Tot] as [cbor_map_filter] requires.  By definition this is   *)
(* exactly [cbor_map_filter (fun kv -> not (fst kv = k))].             *)
noextract [@@noextract_to "krml"]
let cbor_det_map_remove_spec (k: Spec.cbor) (m: Spec.cbor_map) : Spec.cbor_map =
  Spec.cbor_map_filter (fun (kv: (Spec.cbor & Spec.cbor)) -> not (fst kv = k)) m

val cbor_det_map_remove
  (x key: cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#pk: perm) (#vk: Ghost.erased Spec.cbor)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_det_map_entry_insert_cell_t)
: stt cbor_det_t
    (cbor_det_match p x v ** cbor_det_match pk key vk **
     R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
     pure (Spec.CMap? (Spec.unpack v)))
    (fun res -> exists* (v': Spec.cbor).
       cbor_det_match 1.0R res v' **
       cbor_det_match pk key vk **
       Trade.trade (cbor_det_match 1.0R res v')
         (cbor_det_match p x v ** (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
       pure (Spec.CMap? (Spec.unpack v) /\ Spec.CMap? (Spec.unpack v') /\
             (Spec.CMap?.c (Spec.unpack v') <: Spec.cbor_map) ==
               cbor_det_map_remove_spec vk (Spec.CMap?.c (Spec.unpack v))))

(* Safe (no-precondition) variant: checks at runtime that [dest] is a  *)
(* non-null destination reference and that [x] is a map; on success    *)
(* writes the removed map into [dest] and returns [true]; otherwise     *)
(* leaves [dest] unchanged, retains ownership of [x], [key] and the     *)
(* scratch references, and returns [false].                            *)
let cbor_det_map_remove_safe_res
  (dest: R.ref cbor_det_t)
  (v: Spec.cbor)
: GTot bool
= not (R.is_null dest) && Spec.CMap? (Spec.unpack v)

let cbor_det_map_remove_safe_post_true
  (x key: cbor_det_t) (p: perm) (v: Spec.cbor) (pk: perm) (vk: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (vdest': cbor_det_t)
: Tot slprop
= exists* (v': Spec.cbor).
    cbor_det_match 1.0R vdest' v' **
    cbor_det_match pk key vk **
    Trade.trade
      (cbor_det_match 1.0R vdest' v')
      (cbor_det_match p x v **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
    pure (Spec.CMap? (Spec.unpack v) /\ Spec.CMap? (Spec.unpack v') /\
          (Spec.CMap?.c (Spec.unpack v') <: Spec.cbor_map) ==
            cbor_det_map_remove_spec vk (Spec.CMap?.c (Spec.unpack v)))

let cbor_det_map_remove_safe_post_false
  (x key: cbor_det_t) (p: perm) (v: Spec.cbor) (pk: perm) (vk: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (w1 w2 w3 w4: cbor_det_map_entry_insert_cell_t)
  (vdest vdest': cbor_det_t)
: Tot slprop
= cbor_det_match p x v **
  cbor_det_match pk key vk **
  R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
  pure (vdest' == vdest)

let cbor_det_map_remove_safe_post
  (x key: cbor_det_t) (dest: R.ref cbor_det_t) (p: perm) (v: Spec.cbor) (pk: perm) (vk: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (w1 w2 w3 w4: cbor_det_map_entry_insert_cell_t)
  (vdest vdest': cbor_det_t)
: Tot slprop
= if cbor_det_map_remove_safe_res dest v
  then cbor_det_map_remove_safe_post_true x key p v pk vk r1 r2 r3 r4 vdest'
  else cbor_det_map_remove_safe_post_false x key p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest'

val cbor_det_map_remove_safe
  (x key: cbor_det_t)
  (dest: R.ref cbor_det_t)
  (r1 r2 r3 r4: R.ref cbor_det_map_entry_insert_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#pk: perm) (#vk: Ghost.erased Spec.cbor) (#vdest: Ghost.erased cbor_det_t)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_det_map_entry_insert_cell_t)
: stt bool
    (cbor_det_match p x v ** cbor_det_match pk key vk ** ref_pts_to_or_null dest 1.0R vdest **
     R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)
    (fun res -> exists* (vdest': cbor_det_t).
       ref_pts_to_or_null dest 1.0R vdest' **
       cbor_det_map_remove_safe_post x key dest p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest' **
       pure (res == cbor_det_map_remove_safe_res dest v))

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_map_get_gen () : map_get_t cbor_det_match = map_get_as_option (cbor_det_map_get ())

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_tag_to_array_t
=
  (tag: U64.t) ->
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v ** pure (SZ.v out_len == Seq.length v))
  (fun res -> exists* v . pts_to out v ** pure (
     cbor_det_serialize_tag_postcond tag out_len res v
  ))

val cbor_det_serialize_tag_to_array (_: unit) : cbor_det_serialize_tag_to_array_t

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_array_to_array_t
= (len: U64.t) ->
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  (l: Ghost.erased (list Spec.cbor)) ->
  (off: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_det_serialize_array_precond len l off v /\
      Seq.length v == SZ.v out_len
    )
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_det_serialize_array_postcond l res v /\
      Seq.length v == SZ.v out_len
    )
  )

val cbor_det_serialize_array_to_array (_: unit) : cbor_det_serialize_array_to_array_t

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_string_to_array_t
= (ty: major_type_byte_string_or_text_string) ->
  (off: U64.t) ->
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
  (pts_to out v **
    pure (cbor_det_serialize_string_precond ty off v /\
      Seq.length v == SZ.v out_len
    )
  )
  (fun res -> exists* v' .
    pts_to out v' **
    pure (cbor_det_serialize_string_postcond ty off v res v' /\
      Seq.length v' == SZ.v out_len
    )
  )

val cbor_det_serialize_string_to_array (_: unit) : cbor_det_serialize_string_to_array_t

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_map_insert_to_array_t =
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  (m: Ghost.erased Spec.cbor_map) ->
  (off2: SZ.t) ->
  (key: Ghost.erased Spec.cbor) ->
  (off3: SZ.t) ->
  (value: Ghost.erased Spec.cbor) ->
  stt bool
    (exists* v .
      pts_to out v **
      pure (cbor_det_serialize_map_insert_pre m off2 key off3 value v /\
        SZ.v out_len == Seq.length v
      )
    )
    (fun res -> exists* v .
      pts_to out v **
      pure (cbor_det_serialize_map_insert_post m key value res v /\
        SZ.v out_len == Seq.length v
      )
    )

val cbor_det_serialize_map_insert_to_array (_: unit) : cbor_det_serialize_map_insert_to_array_t

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_map_to_array_t =
  (len: U64.t) ->
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  (l: Ghost.erased (Spec.cbor_map)) ->
  (off: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_det_serialize_map_precond len l off v /\
      SZ.v out_len == Seq.length v
    )
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_det_serialize_map_postcond l res v /\
      SZ.v out_len == Seq.length v
    )
  )

val cbor_det_serialize_map_to_array (_: unit) : cbor_det_serialize_map_to_array_t
