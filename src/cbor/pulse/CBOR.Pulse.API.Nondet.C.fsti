module CBOR.Pulse.API.Nondet.C
include CBOR.Pulse.API.Nondet.Type
open CBOR.Spec.Constants
open CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives

module Spec = CBOR.Spec.API.Format
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util
module SM = Pulse.Lib.SeqMatch.Util
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module L = FStar.List.Tot

val cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop

inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_nondet_reset_perm (_: unit) : reset_perm_t #_ cbor_nondet_match

val cbor_nondet_share
  (_: unit)
: CBOR.Pulse.API.Base.share_t u#0 u#0 #_ #_ cbor_nondet_match

val cbor_nondet_gather
  (_: unit)
: CBOR.Pulse.API.Base.gather_t u#0 u#0 #_ #_ cbor_nondet_match

val cbor_nondet_parse (_: unit) : cbor_nondet_parse_from_arrayptr_t #cbor_nondet_t cbor_nondet_match

val cbor_nondet_match_with_size
  (size: nat)
  (p: perm)
  (c: cbor_nondet_t)
  (v: Spec.cbor)
: Tot slprop

val cbor_nondet_match_with_size_intro (_: unit) : ghost_get_size_t #_ cbor_nondet_match cbor_nondet_match_with_size

val cbor_nondet_size (_: unit) : get_size_t #_ cbor_nondet_match_with_size

val cbor_nondet_serialize
  (_: unit)
: cbor_nondet_serialize_to_arrayptr_t #cbor_nondet_t cbor_nondet_match_with_size

(* Destructors *)

val cbor_nondet_major_type (_: unit) : get_major_type_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_simple_value (_: unit) : read_simple_value_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_simple (_: unit) : elim_simple_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_uint64 (_: unit) : read_uint64_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_int64 (_: unit) : read_int64_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_int64 (_: unit) : elim_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_string (_: unit) : get_string_as_arrayptr_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_byte_string (_: unit) : get_string_as_arrayptr_safe_gen_t u#0 (Some cbor_major_type_byte_string) #_ cbor_nondet_match

val cbor_nondet_get_text_string (_: unit) : get_string_as_arrayptr_safe_gen_t u#0 (Some cbor_major_type_text_string) #_ cbor_nondet_match

val cbor_nondet_get_tagged (_: unit) : get_tagged_safe_t #_ cbor_nondet_match

val cbor_nondet_get_array_length (_: unit) : get_array_length_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_array_iterator_match: perm -> cbor_nondet_array_iterator_t -> list Spec.cbor -> slprop

val cbor_nondet_array_iterator_start (_: unit) : array_iterator_start_safe_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_length (_: unit) : array_iterator_length_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_next (_: unit) : array_iterator_next_safe_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_truncate (_: unit) : array_iterator_truncate_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_get_array_item (_: unit) : get_array_item_safe_t #_ cbor_nondet_match

(* Structural array builder operations.

   These build CBOR arrays by O(1) structural composition (no element copy or
   re-encoding), on top of fully-owned arrays. [cbor_nondet_array_owned x l]
   means [x] is a fully-owned (permission 1.0R, canonical length encoding) CBOR
   array whose elements are [l]. Such arrays can be combined with
   [cbor_nondet_array_append] and turned back into a normal CBOR object with
   [cbor_nondet_array_finalize].

   No heap allocation: the application provides the (fixed number of) scratch
   references the operations need. *)

val cbor_nondet_array_t : Type0

val cbor_nondet_array_owned (x: cbor_nondet_array_t) (l: list Spec.cbor) : slprop

val cbor_nondet_array_init
  (x: cbor_nondet_t)
  (r1 r2: R.ref cbor_nondet_array_append_cell_t)
  (#p: perm)
  (#l: Ghost.erased Spec.cbor)
  (#w1 #w2: Ghost.erased cbor_nondet_array_append_cell_t)
: stt cbor_nondet_array_t
    (cbor_nondet_match p x l ** R.pts_to r1 w1 ** R.pts_to r2 w2 ** pure (Spec.CArray? (Spec.unpack l)))
    (fun y ->
      exists* (l' : list Spec.cbor) .
        cbor_nondet_array_owned y l' **
        Trade.trade
          (cbor_nondet_array_owned y l')
          (cbor_nondet_match p x l ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)) **
        pure (Spec.CArray? (Spec.unpack l) /\ l' == Spec.CArray?.v (Spec.unpack l))
    )

val cbor_nondet_array_empty (_: unit)
: stt cbor_nondet_array_t
    emp
    (fun res -> cbor_nondet_array_owned res [])

val cbor_nondet_array_singleton
  (x: cbor_nondet_t) (ry: R.ref cbor_nondet_t)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_nondet_t)
: stt cbor_nondet_array_t
    (cbor_nondet_match pm x v ** R.pts_to ry w0)
    (fun res ->
      cbor_nondet_array_owned res [Ghost.reveal v] **
      Trade.trade
        (cbor_nondet_array_owned res [Ghost.reveal v])
        (cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w)))

val cbor_nondet_array_append
  (x1 x2: cbor_nondet_array_t)
  (r_before r_after: R.ref cbor_nondet_array_append_cell_t)
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased cbor_nondet_array_append_cell_t)
: stt (option cbor_nondet_array_t)
    (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
     R.pts_to r_before vb0 ** R.pts_to r_after va0)
    (fun res ->
      match res with
      | None ->
        cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
        pure (~ (FStar.UInt.fits (L.length (Ghost.reveal l1) + L.length (Ghost.reveal l2)) U64.n))
      | Some r ->
        cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
        Trade.trade
          (cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
          (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
           (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))

val cbor_nondet_array_finalize
  (x: cbor_nondet_array_t)
  (#l: Ghost.erased (list Spec.cbor))
: stt cbor_nondet_t
    (cbor_nondet_array_owned x l)
    (fun y ->
      exists* (l': (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n })).
        cbor_nondet_match 1.0R y (Spec.pack (Spec.CArray l')) **
        Trade.trade
          (cbor_nondet_match 1.0R y (Spec.pack (Spec.CArray l')))
          (cbor_nondet_array_owned x l) **
        pure ((l' <: list Spec.cbor) == Ghost.reveal l))

(* The length of an owned array fits in a u64; lets callers discharge the
   refinement of [cbor_nondet_array_finalize] after a chain of [cbor_nondet_array_append]s. *)
val cbor_nondet_array_owned_length_fits
  (x: cbor_nondet_array_t) (#l: Ghost.erased (list Spec.cbor))
: stt_ghost unit emp_inames
    (cbor_nondet_array_owned x l)
    (fun _ -> cbor_nondet_array_owned x l **
      pure (FStar.UInt.fits (L.length (Ghost.reveal l)) U64.n))

val cbor_nondet_get_map_length (_: unit) : get_map_length_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_map_iterator_match: perm -> cbor_nondet_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_nondet_map_iterator_start (_: unit) : map_iterator_start_safe_t #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t u#0 #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_match: perm -> cbor_nondet_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_nondet_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_iterator_next (_: unit) : map_iterator_next_safe_t #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_share
  (_: unit)
: share_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match

val cbor_nondet_map_entry_gather
  (_: unit)
: gather_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match

(* Equality *)

val cbor_nondet_equal
  (x1: cbor_nondet_t)
  (#p1: perm)
  (#v1: Ghost.erased Spec.cbor)
  (x2: cbor_nondet_t)
  (#p2: perm)
  (#v2: Ghost.erased Spec.cbor)
: stt bool
(requires
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2
)
(ensures fun res ->
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2 **
  pure (res == true <==> Ghost.reveal v1 == Ghost.reveal v2)
)

val cbor_nondet_map_get (_: unit)
: map_get_by_ref_safe_t #_ cbor_nondet_match

(* Constructors *)

val cbor_nondet_mk_simple_value (_: unit) : mk_simple_safe_t #_ cbor_nondet_match

val cbor_nondet_mk_uint64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match cbor_major_type_uint64

val cbor_nondet_mk_neg_int64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match cbor_major_type_neg_int64

val cbor_nondet_mk_int64 (_: unit) : mk_signed_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_byte_string (_: unit) : mk_string_from_arrayptr_t #_ cbor_nondet_match cbor_major_type_byte_string

val cbor_nondet_mk_text_string (_: unit) : mk_string_from_arrayptr_t #_ cbor_nondet_match cbor_major_type_text_string

val cbor_nondet_mk_tagged (_: unit) : mk_tagged_safe_t #_ cbor_nondet_match

val cbor_nondet_mk_array (_: unit) : mk_array_from_arrayptr_t #_ cbor_nondet_match

val cbor_nondet_mk_map_entry (_: unit) : mk_map_entry_t #_ #_ cbor_nondet_match cbor_nondet_map_entry_match

val cbor_nondet_mk_map (_: unit)
: mk_map_from_arrayptr_safe_t #cbor_nondet_t #cbor_nondet_map_entry_t cbor_nondet_match cbor_nondet_map_entry_match

type cbor_nondet_map_get_multiple_entry_t = cbor_map_get_multiple_entry_t cbor_nondet_t

val cbor_nondet_map_get_multiple (_: unit) : cbor_map_get_multiple_as_arrayptr_t #_ cbor_nondet_match cbor_nondet_map_get_multiple_entry_t

(* Structural map-entry insertion (prepend, nondeterministic) operating directly
   on a [cbor_nondet_t]. The operation gracefully fails (returns [None]) if [x]
   is not a map, if the key is already defined in the map (up to the abstract
   equality on keys), or if inserting the entry would overflow a u64 length.

   The entry (key, value) is prepended (the nondeterministic encoding does not
   require sorted keys).

   No heap allocation: the application provides the (fixed number of) scratch
   references the operation needs, namely two [cbor_nondet_map_entry_insert_cell_t]
   references and one [cbor_nondet_map_entry_t] reference; use
   [dummy_cbor_nondet_map_entry_insert_cell] and [dummy_cbor_nondet_map_entry] to
   initialize them. *)

inline_for_extraction
val dummy_cbor_nondet_map_entry_insert_cell (_: unit) : cbor_nondet_map_entry_insert_cell_t

inline_for_extraction
val dummy_cbor_nondet_map_entry (_: unit) : cbor_nondet_map_entry_t

let cbor_nondet_map_entry_insert_refs
  (r1 r2: R.ref cbor_nondet_map_entry_insert_cell_t)
  (ry: R.ref cbor_nondet_map_entry_t)
: Tot slprop
= exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy

val cbor_nondet_map_entry_insert
  (x key value: cbor_nondet_t)
  (r1 r2: R.ref cbor_nondet_map_entry_insert_cell_t)
  (ry: R.ref cbor_nondet_map_entry_t)
  (#p: perm) (#y: Ghost.erased Spec.cbor)
  (#pkv: perm) (#vk #vv: Ghost.erased Spec.cbor)
: stt (option cbor_nondet_t)
    (cbor_nondet_match p x y **
     cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
     cbor_nondet_map_entry_insert_refs r1 r2 ry)
    (fun res ->
      match res with
      | None ->
        cbor_nondet_match p x y **
        cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
        cbor_nondet_map_entry_insert_refs r1 r2 ry **
        pure (
          ~ (Spec.CMap? (Spec.unpack y)) \/
          (Spec.CMap? (Spec.unpack y) /\
            (Spec.cbor_map_defined vk (Spec.CMap?.c (Spec.unpack y)) \/
             ~ (FStar.UInt.fits (Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) + 1) U64.n))))
      | Some m ->
        exists* (p_res: perm) (vres: Spec.cbor).
          cbor_nondet_match p_res m vres **
          Trade.trade
            (cbor_nondet_match p_res m vres)
            (cbor_nondet_match p x y **
             cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
             cbor_nondet_map_entry_insert_refs r1 r2 ry) **
          pure (
            Spec.CMap? (Spec.unpack y) /\
            Spec.CMap? (Spec.unpack vres) /\
            (Spec.CMap?.c (Spec.unpack vres) <: Spec.cbor_map) ==
              Spec.cbor_map_union (Spec.CMap?.c (Spec.unpack y)) (Spec.cbor_map_singleton vk vv)))

(* ================================================================== *)
(* Zero-copy array sub-range (slice) — nondeterministic API.          *)
(*                                                                    *)
(* [cbor_nondet_array_slice x i j r1 r2 r3 r4] produces the           *)
(* nondeterministic array whose elements are the sub-range [i, j) of  *)
(* the input array [x], as a borrowed view (full-permission handle)   *)
(* together with a trade returning the borrow (and the four scratch   *)
(* references) to the source.  It is TOTAL over [i], [j]: if the      *)
(* requested range is empty or out of bounds it produces the EMPTY    *)
(* array.  Realized on top of the raw/ adapter                        *)
(*   ANondet = CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder.          *)
(* ================================================================== *)

(* Specification of the slice at the nondeterministic-CBOR level: the  *)
(* sub-list of elements at indices [i, j) (empty when the range is     *)
(* empty or out of bounds).                                            *)
noextract [@@noextract_to "krml"]
let cbor_nondet_array_slice_spec (l: list Spec.cbor) (i j: U64.t) : list Spec.cbor =
  if U64.v i < U64.v j && U64.v j <= L.length l
  then fst (L.splitAt (U64.v j - U64.v i) (snd (L.splitAt (U64.v i) l)))
  else []

val cbor_nondet_array_slice
  (x: cbor_nondet_t) (i j: U64.t)
  (r1 r2 r3 r4: R.ref cbor_nondet_array_append_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_nondet_array_append_cell_t)
: stt cbor_nondet_t
    (cbor_nondet_match p x v ** R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4
       ** pure (Spec.CArray? (Spec.unpack v)))
    (fun res -> exists* (v': Spec.cbor).
       cbor_nondet_match 1.0R res v' **
       Trade.trade (cbor_nondet_match 1.0R res v')
         (cbor_nondet_match p x v ** (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
       pure (Spec.CArray? (Spec.unpack v) /\ Spec.CArray? (Spec.unpack v') /\
             (Spec.CArray?.v (Spec.unpack v') <: list Spec.cbor) == cbor_nondet_array_slice_spec (Spec.CArray?.v (Spec.unpack v)) i j))

(* Safe (no-precondition) variant: checks at runtime that [dest] is a  *)
(* non-null destination reference and that [x] is an array; on success *)
(* writes the sliced array into [dest] and returns [true]; otherwise   *)
(* leaves [dest] unchanged, retains ownership of [x] and the scratch   *)
(* references, and returns [false].                                    *)
let cbor_nondet_array_slice_safe_res
  (dest: R.ref cbor_nondet_t)
  (v: Spec.cbor)
: GTot bool
= not (R.is_null dest) && Spec.CArray? (Spec.unpack v)

let cbor_nondet_array_slice_safe_post_true
  (x: cbor_nondet_t) (i j: U64.t) (p: perm) (v: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_nondet_array_append_cell_t)
  (vdest': cbor_nondet_t)
: Tot slprop
= exists* (v': Spec.cbor).
    cbor_nondet_match 1.0R vdest' v' **
    Trade.trade
      (cbor_nondet_match 1.0R vdest' v')
      (cbor_nondet_match p x v **
       (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
    pure (Spec.CArray? (Spec.unpack v) /\ Spec.CArray? (Spec.unpack v') /\
          (Spec.CArray?.v (Spec.unpack v') <: list Spec.cbor) == cbor_nondet_array_slice_spec (Spec.CArray?.v (Spec.unpack v)) i j)

let cbor_nondet_array_slice_safe_post_false
  (x: cbor_nondet_t) (p: perm) (v: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_nondet_array_append_cell_t)
  (w1 w2 w3 w4: cbor_nondet_array_append_cell_t)
  (vdest vdest': cbor_nondet_t)
: Tot slprop
= cbor_nondet_match p x v **
  R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
  pure (vdest' == vdest)

let cbor_nondet_array_slice_safe_post
  (x: cbor_nondet_t) (i j: U64.t) (dest: R.ref cbor_nondet_t) (p: perm) (v: Spec.cbor)
  (r1 r2 r3 r4: R.ref cbor_nondet_array_append_cell_t)
  (w1 w2 w3 w4: cbor_nondet_array_append_cell_t)
  (vdest vdest': cbor_nondet_t)
: Tot slprop
= if cbor_nondet_array_slice_safe_res dest v
  then cbor_nondet_array_slice_safe_post_true x i j p v r1 r2 r3 r4 vdest'
  else cbor_nondet_array_slice_safe_post_false x p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest'

val cbor_nondet_array_slice_safe
  (x: cbor_nondet_t) (i j: U64.t)
  (dest: R.ref cbor_nondet_t)
  (r1 r2 r3 r4: R.ref cbor_nondet_array_append_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor) (#vdest: Ghost.erased cbor_nondet_t)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_nondet_array_append_cell_t)
: stt bool
    (cbor_nondet_match p x v ** ref_pts_to_or_null dest 1.0R vdest **
     R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)
    (fun res -> exists* (vdest': cbor_nondet_t).
       ref_pts_to_or_null dest 1.0R vdest' **
       cbor_nondet_array_slice_safe_post x i j dest p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest' **
       pure (res == cbor_nondet_array_slice_safe_res dest v))
