module CBOR.Pulse.Raw.Format.Serialize.Gen
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.Base
open LowParse.Pulse.Base
open CBOR.Pulse.Raw.Match
open CBOR.Pulse.Raw.EverParse.Format

module SZ = FStar.SizeT
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module DEP = CBOR.Pulse.Raw.Format.Match.Depth
module VC = LowParse.Spec.VCList
module LSC = LowParse.Spec.Combinators

(* Generic left-to-right writer for the mixed-list payload of a
   CBOR_Case_Array_Gen node.  The element writer [w] serializes a single child
   at depth [n] (via [DEP.depth_match n]); this core reads the runtime element
   count and drives the generic mixed-list writer, leaving the abstract
   [cbor_match_mixed_list_array] resource restored.  The output serializer is
   the nlist serializer whose length is fixed by the array header. *)
inline_for_extraction
val write_gen_array_core
  (n: Ghost.erased nat)
  (w: (pm': perm) -> l2r_writer (DEP.depth_match n pm') serialize_raw_data_item)
  (a: cbor_mixed_list_array)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Array? r }))
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
: stt SZ.t
    (pts_to out v **
      cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0) **
      pure (
        l2r_writer_for_pre (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0) offset v))
    (fun res -> exists* v'.
      pts_to out v' **
      cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0) **
      pure (l2r_writer_for_post (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0) offset v res v'))

inline_for_extraction
val size_gen_array_core
  (n: Ghost.erased nat)
  (cr: (pm': perm) -> compute_remaining_size (DEP.depth_match n pm') serialize_raw_data_item)
  (a: cbor_mixed_list_array)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Array? r }))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
: stt bool
    (R.pts_to out v **
      cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0) **
      pure True)
    (fun res -> exists* v'.
      R.pts_to out v' **
      cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0) **
      pure (
        let bs = Seq.length (bare_serialize (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0)) in
        (res == true <==> bs <= SZ.v v) /\
        (res == true ==> bs + SZ.v v' == SZ.v v)))

inline_for_extraction
val write_gen_map_core
  (n: Ghost.erased nat)
  (w: (pm': perm) -> l2r_writer (DEP.depth_match n pm') serialize_raw_data_item)
  (a: cbor_mixed_list_map)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Map? r }))
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
: stt SZ.t
    (pts_to out v **
      cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0) **
      pure (
        l2r_writer_for_pre (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0) offset v))
    (fun res -> exists* v'.
      pts_to out v' **
      cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0) **
      pure (l2r_writer_for_post (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0) offset v res v'))

inline_for_extraction
val size_gen_map_core
  (n: Ghost.erased nat)
  (cr: (pm': perm) -> compute_remaining_size (DEP.depth_match n pm') serialize_raw_data_item)
  (a: cbor_mixed_list_map)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Map? r }))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
: stt bool
    (R.pts_to out v **
      cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0) **
      pure True)
    (fun res -> exists* v'.
      R.pts_to out v' **
      cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0) **
      pure (
        let bs = Seq.length (bare_serialize (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0)) in
        (res == true <==> bs <= SZ.v v) /\
        (res == true ==> bs + SZ.v v' == SZ.v v)))

(* Non-depth (full-recursion) variants: identical shape, but the per-element
   callback is the full [cbor_match] relation rather than [depth_cb n].  Used by
   the (non-depth) recursive serializer stack. *)
val write_gen_array_core_nd
  (w: (pm': perm) -> l2r_writer (cbor_match pm') serialize_raw_data_item)
  (a: cbor_mixed_list_array)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Array? r }))
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
: stt SZ.t
    (pts_to out v **
      cbor_match_mixed_list_array pp a xh0 cbor_match **
      pure (
        l2r_writer_for_pre (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0) offset v))
    (fun res -> exists* v'.
      pts_to out v' **
      cbor_match_mixed_list_array pp a xh0 cbor_match **
      pure (l2r_writer_for_post (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0) offset v res v'))

val size_gen_array_core_nd
  (cr: (pm': perm) -> compute_remaining_size (cbor_match pm') serialize_raw_data_item)
  (a: cbor_mixed_list_array)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Array? r }))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
: stt bool
    (R.pts_to out v **
      cbor_match_mixed_list_array pp a xh0 cbor_match **
      pure True)
    (fun res -> exists* v'.
      R.pts_to out v' **
      cbor_match_mixed_list_array pp a xh0 cbor_match **
      pure (
        let bs = Seq.length (bare_serialize (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0)) in
        (res == true <==> bs <= SZ.v v) /\
        (res == true ==> bs + SZ.v v' == SZ.v v)))

val write_gen_map_core_nd
  (w: (pm': perm) -> l2r_writer (cbor_match pm') serialize_raw_data_item)
  (a: cbor_mixed_list_map)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Map? r }))
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
: stt SZ.t
    (pts_to out v **
      cbor_match_mixed_list_map pp a xh0 cbor_match **
      pure (
        l2r_writer_for_pre (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0) offset v))
    (fun res -> exists* v'.
      pts_to out v' **
      cbor_match_mixed_list_map pp a xh0 cbor_match **
      pure (l2r_writer_for_post (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0) offset v res v'))

val size_gen_map_core_nd
  (cr: (pm': perm) -> compute_remaining_size (cbor_match pm') serialize_raw_data_item)
  (a: cbor_mixed_list_map)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Map? r }))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
: stt bool
    (R.pts_to out v **
      cbor_match_mixed_list_map pp a xh0 cbor_match **
      pure True)
    (fun res -> exists* v'.
      R.pts_to out v' **
      cbor_match_mixed_list_map pp a xh0 cbor_match **
      pure (
        let bs = Seq.length (bare_serialize (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0)) in
        (res == true <==> bs <= SZ.v v) /\
        (res == true ==> bs + SZ.v v' == SZ.v v)))
