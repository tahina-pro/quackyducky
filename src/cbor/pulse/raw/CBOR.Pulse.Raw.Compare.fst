module CBOR.Pulse.Raw.Compare
#lang-pulse
include CBOR.Pulse.Raw.Read
include CBOR.Spec.Raw.Format
include CBOR.Pulse.Raw.Compare.Bytes
include CBOR.Pulse.Raw.Compare.Iterator
open CBOR.Pulse.Raw.Format.Serialized
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Sort.Base
module SM = Pulse.Lib.SeqMatch.Util
module SZ = FStar.SizeT
module I16 = FStar.Int16
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Ser = CBOR.Pulse.Raw.Format.Compare
module Sl = Pulse.Lib.Slice
module ML = CBOR.Pulse.Raw.Format.MixedList

let size_lt (depth: nat) (e: raw_data_item) : bool =
  raw_data_item_size e < depth

let map_size_lt (depth: nat) (e: (raw_data_item & raw_data_item)) : bool =
  raw_data_item_size (fst e) < depth &&
  raw_data_item_size (snd e) < depth

let rec list_elts_size_bound (l: list raw_data_item) (depth: nat)
  : Lemma (requires CBOR.Spec.Util.list_sum raw_data_item_size l + 2 <= depth)
          (ensures List.Tot.for_all (size_lt depth) l)
          (decreases l)
  = match l with
    | [] -> ()
    | a :: q -> list_elts_size_bound q depth

let array_elts_size_bound (v: raw_data_item {Array? v}) (depth: nat)
  : Lemma (requires raw_data_item_size v <= depth)
          (ensures List.Tot.for_all (size_lt depth) (Array?.v v))
  = raw_data_item_size_eq v;
    list_elts_size_bound (Array?.v v) depth

let rec map_entries_size_bound_aux
  (l: list (raw_data_item & raw_data_item)) (depth: nat)
  : Lemma (requires
      CBOR.Spec.Util.list_sum
        (CBOR.Spec.Util.pair_sum raw_data_item_size raw_data_item_size) l + 2 <= depth)
          (ensures List.Tot.for_all (map_size_lt depth) l)
          (decreases l)
  = match l with
    | [] -> ()
    | a :: q -> map_entries_size_bound_aux q depth

let map_entries_size_bound (v: raw_data_item {Map? v}) (depth: nat)
  : Lemma (requires raw_data_item_size v <= depth)
          (ensures List.Tot.for_all (map_size_lt depth) (Map?.v v))
  = raw_data_item_size_eq v;
    map_entries_size_bound_aux (Map?.v v) depth

let rec cbor_compare_array_eq
  (x1 x2: list raw_data_item)
: Lemma
  (requires (List.Tot.length x1 == List.Tot.length x2))
  (ensures (cbor_compare_array x1 x2 == lex_compare cbor_compare x1 x2))
  (decreases x1)
= match x1, x2 with
  | [], [] -> ()
  | a1 :: q1, a2 :: q2 ->
    let c = cbor_compare a1 a2 in
    if c = 0
    then cbor_compare_array_eq q1 q2
    else ()

let cbor_compare_key_value
  (x1 x2: (raw_data_item & raw_data_item))
: Tot int
= let c = cbor_compare (fst x1) (fst x2) in
  if c = 0
  then cbor_compare (snd x1) (snd x2)
  else c

let rec cbor_compare_map_eq
  (x1 x2: list (raw_data_item & raw_data_item))
: Lemma
  (requires (List.Tot.length x1 == List.Tot.length x2))
  (ensures (cbor_compare_map x1 x2 == lex_compare cbor_compare_key_value x1 x2))
  (decreases x1)
= match x1, x2 with
  | [], [] -> ()
  | a1 :: q1, a2 :: q2 ->
    let c = cbor_compare_key_value a1 a2 in
    if c = 0
    then cbor_compare_map_eq q1 q2
    else ()

inline_for_extraction
let cbor_compare_t =
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#p1: perm) ->
  (#p2: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
      (cbor_match p1 x1 v1 ** cbor_match p2 x2 v2)
      (fun res -> cbor_match p1 x1 v1 ** cbor_match p2 x2 v2 **
        pure (
          same_sign (I16.v res) (cbor_compare v1 v2)
        )
      )

inline_for_extraction
fn cbor_compare_of_impl_compare
  (ih: A.impl_compare_t (vmatch_with_perm cbor_match) cbor_compare)
: cbor_compare_t
=
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
{
  let px1 = Mkwith_perm x1 p1;
  Trade.rewrite_with_trade
    (cbor_match p1 x1 v1)
    (vmatch_with_perm cbor_match px1 v1);
  let px2 = Mkwith_perm x2 p2;
  Trade.rewrite_with_trade
    (cbor_match p2 x2 v2)
    (vmatch_with_perm cbor_match px2 v2);
  let res = ih px1 px2;
  Trade.elim _ (cbor_match p1 x1 v1);
  Trade.elim _ (cbor_match p2 x2 v2);
  res
}

inline_for_extraction
fn impl_compare_of_cbor_compare
  (ih: cbor_compare_t)
: A.impl_compare_t u#0 u#0 #_ #_ (vmatch_with_perm cbor_match) cbor_compare
=
  (x1: with_perm cbor_raw)
  (x2: with_perm cbor_raw)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
{
  unfold (vmatch_with_perm cbor_match x1 v1);
  unfold (vmatch_with_perm cbor_match x2 v2);
  let res = ih x1.v x2.v;
  fold (vmatch_with_perm cbor_match x1 v1);
  fold (vmatch_with_perm cbor_match x2 v2);
  res
}

inline_for_extraction
fn impl_cbor_compare_key_value
  (ih: cbor_compare_t)
: A.impl_compare_t u#0 u#0 #_ #_
    (vmatch_with_perm cbor_match_map_entry)
    cbor_compare_key_value
= (x1: _)
  (x2: _)
  (#v1: _)
  (#v2: _)
{
  unfold (vmatch_with_perm cbor_match_map_entry x1 v1);
  unfold (vmatch_with_perm cbor_match_map_entry x2 v2);
  unfold (cbor_match_map_entry x1.p x1.v v1);
  unfold (cbor_match_map_entry x2.p x2.v v2);
  let c = ih x1.v.cbor_map_entry_key x2.v.cbor_map_entry_key;
  if (c = 0s) {
    let c = ih x1.v.cbor_map_entry_value x2.v.cbor_map_entry_value;
    fold (cbor_match_map_entry x1.p x1.v v1);
    fold (cbor_match_map_entry x2.p x2.v v2);
    fold (vmatch_with_perm cbor_match_map_entry x1 v1);
    fold (vmatch_with_perm cbor_match_map_entry x2 v2);
    c
  } else {
    fold (cbor_match_map_entry x1.p x1.v v1);
    fold (cbor_match_map_entry x2.p x2.v v2);
    fold (vmatch_with_perm cbor_match_map_entry x1 v1);
    fold (vmatch_with_perm cbor_match_map_entry x2 v2);
    c
  }
}

fn impl_major_type
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p x v
returns t: major_type_t
ensures
  cbor_match p x v ** pure (t == get_major_type v)
{
  cbor_match_cases x;
  match x {
    norewrite
    CBOR_Case_Simple _ -> {
      cbor_major_type_simple_value
    }
    norewrite
    CBOR_Case_Int _ -> {
      let res = cbor_match_int_elim_type x;
      res
    }
    norewrite
    CBOR_Case_String _ -> {
      let res = cbor_match_string_elim_type x;
      res
    }
    norewrite
    CBOR_Case_Tagged _ -> {
      cbor_major_type_tagged
    }
    norewrite
    CBOR_Case_Serialized_Tagged _ -> {
      cbor_major_type_tagged
    }
    norewrite
    CBOR_Case_Array _ -> {
      cbor_major_type_array
    }
    norewrite
    CBOR_Case_Serialized_Array _ -> {
      cbor_major_type_array
    }
    norewrite
    CBOR_Case_Map _ -> {
      cbor_major_type_map
    }
    norewrite
    CBOR_Case_Serialized_Map _ -> {
      cbor_major_type_map
    }
    norewrite
    CBOR_Case_Array_Gen _ -> {
      cbor_major_type_array
    }
    norewrite
    CBOR_Case_Map_Gen _ -> {
      cbor_major_type_map
    }
  }
}

let uint64_compare (x1 x2: U64.t) : Tot I16.t =
  if U64.lt x1 x2
  then (-1s)
  else if U64.gt x1 x2
  then 1s
  else 0s

fn impl_raw_uint64_compare (_: unit) : impl_compare_scalar_t u#0 #_ raw_uint64_compare
= (x1: _)
  (x2: _)
{
  let c = impl_uint8_compare () x1.size x2.size;
  if (c = 0s) {
    uint64_compare x1.value x2.value
  } else {
    c
  }
}

#push-options "--z3rlimit 32"

// ===================================================================
// Depth-indexed lexicographic comparison (proves termination).
// Thin public wrapper [impl_cbor_compare] over a depth-indexed driver
// [cbor_compare_with_depth]; mirrors CBOR.Pulse.Raw.Nondet.Compare.
// ===================================================================

// Convert a non-inline-composite (leaf or serialized) [cbor_match_with_depth]
// to a plain [cbor_match], with a trade to restore the depth predicate.
ghost
fn cbor_match_with_depth_to_match
  (depth: Ghost.erased nat)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p x v **
  pure (~ (CBOR_Case_Array? x \/ CBOR_Case_Map? x \/ CBOR_Case_Tagged? x \/
           CBOR_Case_Array_Gen? x \/ CBOR_Case_Map_Gen? x))
ensures
  cbor_match p x v **
  Trade.trade (cbor_match p x v) (cbor_match_with_depth depth p x v)
{
  cbor_match_with_depth_cases depth p x v;
  match x {
    norewrite
    CBOR_Case_Int ct -> {
      cbor_match_with_depth_eq_match_int depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Simple ct -> {
      cbor_match_with_depth_eq_match_simple depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_String ct -> {
      cbor_match_with_depth_eq_match_string depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Array ct -> {
      cbor_match_with_depth_eq_match_ser_array depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Map ct -> {
      cbor_match_with_depth_eq_match_ser_map depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Tagged ct -> {
      cbor_match_with_depth_eq_match_ser_tagged depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Array ct -> {
      unreachable ()
    }
    norewrite
    CBOR_Case_Map ct -> {
      unreachable ()
    }
    norewrite
    CBOR_Case_Tagged ct -> {
      unreachable ()
    }
    norewrite
    CBOR_Case_Array_Gen ct -> {
      unreachable ()
    }
    norewrite
    CBOR_Case_Map_Gen ct -> {
      unreachable ()
    }
  }
}

// A tagged at [cbor_match_with_depth depth] forces depth >= 1.
ghost
fn cbor_match_with_depth_tagged_pos
  (depth: Ghost.erased nat) (p: perm) (a: cbor_tagged) (v: raw_data_item { Tagged? v })
  requires cbor_match_with_depth depth p (CBOR_Case_Tagged a) v
  ensures cbor_match_with_depth depth p (CBOR_Case_Tagged a) v ** pure (Ghost.reveal depth >= 1)
{
  cbor_match_with_depth_tagged_elim depth p a v;
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
}

ghost
fn cbor_match_with_depth_tagged_pos_raw
  (depth: Ghost.erased nat) (p: perm) (x: cbor_raw) (v: raw_data_item { Tagged? v })
  requires cbor_match_with_depth depth p x v ** pure (CBOR_Case_Tagged? x)
  ensures cbor_match_with_depth depth p x v ** pure (Ghost.reveal depth >= 1)
{
  let a = CBOR_Case_Tagged?.v x;
  rewrite (cbor_match_with_depth depth p x v) as (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
  cbor_match_with_depth_tagged_pos depth p a v;
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v) as (cbor_match_with_depth depth p x v);
}

ghost
fn tagged_pos2
  (depth: Ghost.erased nat)
  (p1: perm) (x1: cbor_raw) (v1: raw_data_item { Tagged? v1 })
  (p2: perm) (x2: cbor_raw) (v2: raw_data_item { Tagged? v2 })
requires
  cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
  pure (CBOR_Case_Tagged? x1 \/ CBOR_Case_Tagged? x2)
ensures
  cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
  pure (Ghost.reveal depth >= 1)
{
  if (CBOR_Case_Tagged? x1) {
    cbor_match_with_depth_tagged_pos_raw depth p1 x1 v1;
  } else {
    cbor_match_with_depth_tagged_pos_raw depth p2 x2 v2;
  }
}

// Depth-preserving major-type reader.
fn impl_major_type_with_depth
  (depth: Ghost.erased nat)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p x v
returns t: major_type_t
ensures
  cbor_match_with_depth depth p x v ** pure (t == get_major_type v)
{
  cbor_match_with_depth_cases depth p x v;
  match x {
    norewrite
    CBOR_Case_Simple _ -> { cbor_major_type_simple_value }
    norewrite
    CBOR_Case_Int ct -> {
      cbor_match_with_depth_to_match depth x;
      let res = cbor_match_int_elim_type x;
      Trade.elim (cbor_match p x v) (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_String ct -> {
      cbor_match_with_depth_to_match depth x;
      let res = cbor_match_string_elim_type x;
      Trade.elim (cbor_match p x v) (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_Tagged _ -> { cbor_major_type_tagged }
    norewrite
    CBOR_Case_Serialized_Tagged _ -> { cbor_major_type_tagged }
    norewrite
    CBOR_Case_Array _ -> { cbor_major_type_array }
    norewrite
    CBOR_Case_Serialized_Array _ -> { cbor_major_type_array }
    norewrite
    CBOR_Case_Map _ -> { cbor_major_type_map }
    norewrite
    CBOR_Case_Serialized_Map _ -> { cbor_major_type_map }
    norewrite
    CBOR_Case_Array_Gen _ -> { cbor_major_type_array }
    norewrite
    CBOR_Case_Map_Gen _ -> { cbor_major_type_map }
  }
}

// Depth-preserving array length reader (inline and serialized).
fn cbor_match_array_get_length_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p c v ** pure (Array? v)
returns res: raw_uint64
ensures
  cbor_match_with_depth depth p c v ** pure (Array? v /\ res == Array?.len v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Array a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
      cbor_match_with_depth_array_elim depth p a v;
      let res : raw_uint64 = { size = a.cbor_array_length_size; value = SZ.sizet_to_uint64 (Sl.len a.cbor_array_ptr) };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Array a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Array a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_array_get_length c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Array_Gen a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Array_Gen a) v);
      cbor_match_with_depth_array_gen_elim depth p a v;
      cbor_match_mixed_list_array_length p a v (depth_cb depth v);
      let res : raw_uint64 = { size = a.cbor_array_gen_length_size; value = ML.cbor_raw_mixed_list_length a.cbor_array_gen_ptr };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Array_Gen a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Array_Gen a) v) as (cbor_match_with_depth depth p c v);
      res
    }
  }
}

// Depth-preserving map length reader (inline and serialized).
fn cbor_match_map_get_length_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p c v ** pure (Map? v)
returns res: raw_uint64
ensures
  cbor_match_with_depth depth p c v ** pure (Map? v /\ res == Map?.len v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Map a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
      cbor_match_with_depth_map_elim depth p a v;
      let res : raw_uint64 = { size = a.cbor_map_length_size; value = SZ.sizet_to_uint64 (Sl.len a.cbor_map_ptr) };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Map a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Map a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_map_get_length c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Map_Gen a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Map_Gen a) v);
      cbor_match_with_depth_map_gen_elim depth p a v;
      cbor_match_mixed_list_map_length p a v (depth_cb depth v);
      let res : raw_uint64 = { size = a.cbor_map_gen_length_size; value = ML.cbor_raw_mixed_list_length a.cbor_map_gen_ptr };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Map_Gen a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Map_Gen a) v) as (cbor_match_with_depth depth p c v);
      res
    }
  }
}

// Depth-preserving tag reader (inline and serialized).
fn cbor_match_tagged_get_tag_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p c v ** pure (Tagged? v)
returns res: raw_uint64
ensures
  cbor_match_with_depth depth p c v ** pure (Tagged? v /\ res == Tagged?.tag v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Tagged a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
      cbor_match_with_depth_tagged_elim depth p a v;
      let res = a.cbor_tagged_tag;
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Tagged a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_tagged_get_tag c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
  }
}

// Two serialized arrays / maps (the only shapes that are depth-agnostic and so
// may occur at depth 0): dedicated serialized comparison, no recursion needed.
inline_for_extraction
let cbor_compare_with_depth_t (depth: Ghost.erased nat) =
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#p1: perm) ->
  (#p2: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
    (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
      pure (raw_data_item_size v1 <= Ghost.reveal depth /\ raw_data_item_size v2 <= Ghost.reveal depth))
    (fun res -> cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
      pure (
        same_sign (I16.v res) (cbor_compare v1 v2)
      )
    )

// Lexicographic comparison of two array iterators at [nat_pred depth], reusing
// the recursive comparator [ih] on elements. The [for_all size_lt] preconditions
// give, for each yielded element, [size elt < depth] hence [size elt <= nat_pred depth]
// (so [ih (nat_pred depth)] applies) and [depth >= 1] (so [nat_pred depth < depth]).
// Handles inline, serialized, and _Gen arrays uniformly (via the depth iterators).
inline_for_extraction
fn lex_compare_array_iterator_with_depth
  (depth: Ghost.erased nat)
  (ih: (depth': Ghost.erased nat { depth' < depth }) -> cbor_compare_with_depth_t depth')
  (i1: cbor_array_iterator)
  (i2: cbor_array_iterator)
  (#p1: perm)
  (#p2: perm)
  (#l1: Ghost.erased (list raw_data_item))
  (#l2: Ghost.erased (list raw_data_item))
requires
  cbor_array_iterator_match_with_depth (nat_pred depth) p1 i1 l1 **
  cbor_array_iterator_match_with_depth (nat_pred depth) p2 i2 l2 **
  pure (
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.for_all (size_lt depth) l1 /\
    List.Tot.for_all (size_lt depth) l2
  )
returns res: I16.t
ensures
  cbor_array_iterator_match_with_depth (nat_pred depth) p1 i1 l1 **
  cbor_array_iterator_match_with_depth (nat_pred depth) p2 i2 l2 **
  pure (same_sign (I16.v res) (lex_compare cbor_compare l1 l2))
{
  let mut pi1 = i1;
  let mut pi2 = i2;
  let mut pres = 0s;
  Trade.refl (cbor_array_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
  Trade.refl (cbor_array_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
  while (
    let res = !pres;
    let ci1 = !pi1;
    (res = 0s && not (cbor_array_iterator_is_empty_with_depth (nat_pred depth) ci1))
  ) invariant exists* gi1 gi2 res m1 m2 pj1 pj2 . (
    pts_to pi1 gi1 **
    pts_to pi2 gi2 **
    pts_to pres res **
    cbor_array_iterator_match_with_depth (nat_pred depth) pj1 gi1 m1 **
    cbor_array_iterator_match_with_depth (nat_pred depth) pj2 gi2 m2 **
    Trade.trade
      (cbor_array_iterator_match_with_depth (nat_pred depth) pj1 gi1 m1)
      (cbor_array_iterator_match_with_depth (nat_pred depth) p1 i1 l1) **
    Trade.trade
      (cbor_array_iterator_match_with_depth (nat_pred depth) pj2 gi2 m2)
      (cbor_array_iterator_match_with_depth (nat_pred depth) p2 i2 l2) **
    pure (
      List.Tot.length m1 == List.Tot.length m2 /\
      List.Tot.for_all (size_lt depth) m1 /\
      List.Tot.for_all (size_lt depth) m2 /\
      same_sign (lex_compare cbor_compare l1 l2)
        (if res = 0s then lex_compare cbor_compare m1 m2 else I16.v res)
    )
  ) {
    let y1 = cbor_array_iterator_next_with_depth (nat_pred depth) pi1;
    Trade.trans _ _ (cbor_array_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
    let y2 = cbor_array_iterator_next_with_depth (nat_pred depth) pi2;
    Trade.trans _ _ (cbor_array_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
    let c = ih (nat_pred depth) y1 y2;
    Trade.elim_hyp_l _ _ (cbor_array_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
    Trade.elim_hyp_l _ _ (cbor_array_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
    pres := c;
  };
  Trade.elim _ (cbor_array_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
  Trade.elim _ (cbor_array_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
  !pres
}

// Lexicographic comparison of two map iterators at [nat_pred depth]. Each entry
// is compared key-first then value ([cbor_compare_key_value]); the [map_size_lt]
// preconditions bound both key and value sizes below depth.
inline_for_extraction
fn lex_compare_map_iterator_with_depth
  (depth: Ghost.erased nat)
  (ih: (depth': Ghost.erased nat { depth' < depth }) -> cbor_compare_with_depth_t depth')
  (i1: cbor_map_iterator)
  (i2: cbor_map_iterator)
  (#p1: perm)
  (#p2: perm)
  (#l1: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#l2: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 l1 **
  cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 l2 **
  pure (
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.for_all (map_size_lt depth) l1 /\
    List.Tot.for_all (map_size_lt depth) l2
  )
returns res: I16.t
ensures
  cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 l1 **
  cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 l2 **
  pure (same_sign (I16.v res) (lex_compare cbor_compare_key_value l1 l2))
{
  let mut pi1 = i1;
  let mut pi2 = i2;
  let mut pres = 0s;
  Trade.refl (cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
  Trade.refl (cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
  while (
    let res = !pres;
    let ci1 = !pi1;
    (res = 0s && not (cbor_map_iterator_is_empty_with_depth (nat_pred depth) ci1))
  ) invariant exists* gi1 gi2 res m1 m2 pj1 pj2 . (
    pts_to pi1 gi1 **
    pts_to pi2 gi2 **
    pts_to pres res **
    cbor_map_iterator_match_with_depth (nat_pred depth) pj1 gi1 m1 **
    cbor_map_iterator_match_with_depth (nat_pred depth) pj2 gi2 m2 **
    Trade.trade
      (cbor_map_iterator_match_with_depth (nat_pred depth) pj1 gi1 m1)
      (cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 l1) **
    Trade.trade
      (cbor_map_iterator_match_with_depth (nat_pred depth) pj2 gi2 m2)
      (cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 l2) **
    pure (
      List.Tot.length m1 == List.Tot.length m2 /\
      List.Tot.for_all (map_size_lt depth) m1 /\
      List.Tot.for_all (map_size_lt depth) m2 /\
      same_sign (lex_compare cbor_compare_key_value l1 l2)
        (if res = 0s then lex_compare cbor_compare_key_value m1 m2 else I16.v res)
    )
  ) {
    let y1 = cbor_map_iterator_next_with_depth (nat_pred depth) pi1;
    Trade.trans _ _ (cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
    let y2 = cbor_map_iterator_next_with_depth (nat_pred depth) pi2;
    Trade.trans _ _ (cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
    with pe1 e1. assert (cbor_match_map_entry_with_depth (nat_pred depth) pe1 y1 e1);
    with pe2 e2. assert (cbor_match_map_entry_with_depth (nat_pred depth) pe2 y2 e2);
    unfold (cbor_match_map_entry_with_depth (nat_pred depth) pe1 y1 e1);
    unfold (cbor_match_map_entry_with_depth (nat_pred depth) pe2 y2 e2);
    let ck = ih (nat_pred depth) y1.cbor_map_entry_key y2.cbor_map_entry_key;
    if (ck = 0s) {
      let cv = ih (nat_pred depth) y1.cbor_map_entry_value y2.cbor_map_entry_value;
      fold (cbor_match_map_entry_with_depth (nat_pred depth) pe1 y1 e1);
      fold (cbor_match_map_entry_with_depth (nat_pred depth) pe2 y2 e2);
      Trade.elim_hyp_l _ _ (cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
      Trade.elim_hyp_l _ _ (cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
      pres := cv;
    } else {
      fold (cbor_match_map_entry_with_depth (nat_pred depth) pe1 y1 e1);
      fold (cbor_match_map_entry_with_depth (nat_pred depth) pe2 y2 e2);
      Trade.elim_hyp_l _ _ (cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
      Trade.elim_hyp_l _ _ (cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
      pres := ck;
    }
  };
  Trade.elim _ (cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 l1);
  Trade.elim _ (cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 l2);
  !pres
}

#restart-solver
inline_for_extraction
fn cbor_compare_body_d
  (depth: Ghost.erased nat)
  (ih: (depth': Ghost.erased nat { depth' < depth }) -> cbor_compare_with_depth_t depth')
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
requires
  (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
    pure (raw_data_item_size v1 <= Ghost.reveal depth /\ raw_data_item_size v2 <= Ghost.reveal depth))
returns res: I16.t
ensures
  (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
    pure (
      same_sign (I16.v res) (cbor_compare v1 v2)
    )
  )
{
  cbor_match_with_depth_cases depth p1 x1 v1;
  cbor_match_with_depth_cases depth p2 x2 v2;
  let ty1 = impl_major_type_with_depth depth x1;
  let ty2 = impl_major_type_with_depth depth x2;
  let c = impl_uint8_compare () ty1 ty2;
  if (c = 0s) {
    if (ty1 = cbor_major_type_uint64 || ty1 = cbor_major_type_neg_int64) {
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      let i1 = cbor_match_int_elim_value x1;
      let i2 = cbor_match_int_elim_value x2;
      let res = impl_raw_uint64_compare () i1 i2;
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      res
    } else if (ty1 = cbor_major_type_byte_string || ty1 = cbor_major_type_text_string) {
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      let i1 = cbor_match_string_elim_length x1;
      let i2 = cbor_match_string_elim_length x2;
      let c : I16.t = impl_raw_uint64_compare () i1 i2;
      if (c = 0s) {
        let pl1 = cbor_match_string_elim_payload x1;
        let pl2 = cbor_match_string_elim_payload x2;
        let res = lex_compare_bytes pl1 pl2;
        Trade.elim _ (cbor_match p1 x1 v1);
        Trade.elim _ (cbor_match p2 x2 v2);
        Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
        Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
        res
      } else {
        Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
        Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
        c
      }
    } else if (ty1 = cbor_major_type_tagged) {
      let tag1 = cbor_match_tagged_get_tag_with_depth depth x1;
      let tag2 = cbor_match_tagged_get_tag_with_depth depth x2;
      let c = impl_raw_uint64_compare () tag1 tag2;
      if (c = 0s) {
        if (match x1, x2 with CBOR_Case_Serialized_Tagged _, CBOR_Case_Serialized_Tagged _ -> true | _ -> false) {
          cbor_match_with_depth_to_match depth x1;
          cbor_match_with_depth_to_match depth x2;
          norewrite let CBOR_Case_Serialized_Tagged cs1 = x1;
          norewrite let CBOR_Case_Serialized_Tagged cs2 = x2;
          Trade.rewrite_with_trade
            (cbor_match p1 x1 v1)
            (cbor_match_serialized_tagged cs1 p1 v1);
          Trade.rewrite_with_trade
            (cbor_match p2 x2 v2)
            (cbor_match_serialized_tagged cs2 p2 v2);
          let res = Ser.cbor_match_compare_serialized_tagged cs1 cs2;
          Trade.elim _ (cbor_match p2 x2 v2);
          Trade.elim _ (cbor_match p1 x1 v1);
          Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
          res
        } else {
          tagged_pos2 depth p1 x1 v1 p2 x2 v2;
          size_tagged_child v1;
          size_tagged_child v2;
          let pl1 = cbor_match_tagged_get_payload_with_depth depth x1;
          let pl2 = cbor_match_tagged_get_payload_with_depth depth x2;
          let res = ih (nat_pred depth) pl1 pl2;
          Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
          res
        }
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_array) {
      let len1 = cbor_match_array_get_length_with_depth depth x1;
      let len2 = cbor_match_array_get_length_with_depth depth x2;
      let c = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        if (match x1, x2 with CBOR_Case_Serialized_Array _, CBOR_Case_Serialized_Array _ -> true | _ -> false) {
          cbor_match_with_depth_to_match depth x1;
          cbor_match_with_depth_to_match depth x2;
          norewrite let CBOR_Case_Serialized_Array cs1 = x1;
          norewrite let CBOR_Case_Serialized_Array cs2 = x2;
          Trade.rewrite_with_trade
            (cbor_match p1 x1 v1)
            (cbor_match_serialized_array cs1 p1 v1);
          Trade.rewrite_with_trade
            (cbor_match p2 x2 v2)
            (cbor_match_serialized_array cs2 p2 v2);
          let res = Ser.cbor_match_compare_serialized_array cs1 cs2;
          Trade.elim _ (cbor_match p2 x2 v2);
          Trade.elim _ (cbor_match p1 x1 v1);
          Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
          res
        } else {
          cbor_compare_array_eq (Array?.v v1) (Array?.v v2);
          array_elts_size_bound v1 depth;
          array_elts_size_bound v2 depth;
          let i1 = cbor_array_iterator_init_with_depth depth x1;
          let i2 = cbor_array_iterator_init_with_depth depth x2;
          let res = lex_compare_array_iterator_with_depth depth ih i1 i2;
          Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
          res
        }
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_map) {
      let len1 = cbor_match_map_get_length_with_depth depth x1;
      let len2 = cbor_match_map_get_length_with_depth depth x2;
      let c = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        if (match x1, x2 with CBOR_Case_Serialized_Map _, CBOR_Case_Serialized_Map _ -> true | _ -> false) {
          cbor_match_with_depth_to_match depth x1;
          cbor_match_with_depth_to_match depth x2;
          norewrite let CBOR_Case_Serialized_Map cs1 = x1;
          norewrite let CBOR_Case_Serialized_Map cs2 = x2;
          Trade.rewrite_with_trade
            (cbor_match p1 x1 v1)
            (cbor_match_serialized_map cs1 p1 v1);
          Trade.rewrite_with_trade
            (cbor_match p2 x2 v2)
            (cbor_match_serialized_map cs2 p2 v2);
          let res = Ser.cbor_match_compare_serialized_map cs1 cs2;
          Trade.elim _ (cbor_match p2 x2 v2);
          Trade.elim _ (cbor_match p1 x1 v1);
          Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
          res
        } else {
          cbor_compare_map_eq (Map?.v v1) (Map?.v v2);
          map_entries_size_bound v1 depth;
          map_entries_size_bound v2 depth;
          let i1 = cbor_map_iterator_init_with_depth depth x1;
          let i2 = cbor_map_iterator_init_with_depth depth x2;
          let res = lex_compare_map_iterator_with_depth depth ih i1 i2;
          Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
          res
        }
      } else {
        c
      }
    } else {
      assert (pure (ty1 == cbor_major_type_simple_value));
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      let val1 = cbor_match_simple_elim x1;
      let val2 = cbor_match_simple_elim x2;
      let res = impl_uint8_compare () val1 val2;
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      res
    }
  } else {
    c
  }
}

#pop-options

let common_depth (n1 n2: Ghost.erased nat) : Ghost.erased nat =
  Ghost.hide (if Ghost.reveal n1 >= Ghost.reveal n2 then Ghost.reveal n1 else Ghost.reveal n2)

#push-options "--z3rlimit 32"

fn rec cbor_compare_with_depth
  (depth: Ghost.erased nat)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
requires
  (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
    pure (raw_data_item_size v1 <= Ghost.reveal depth /\ raw_data_item_size v2 <= Ghost.reveal depth))
returns res: I16.t
ensures
  (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
    pure (
      same_sign (I16.v res) (cbor_compare v1 v2)
    )
  )
decreases (Ghost.reveal depth)
{
  cbor_compare_body_d depth (fun (depth': Ghost.erased nat { depth' < depth }) -> cbor_compare_with_depth depth') x1 x2
}

fn impl_cbor_compare
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
requires
  (cbor_match p1 x1 v1 ** cbor_match p2 x2 v2)
returns res: I16.t
ensures
      (cbor_match p1 x1 v1 ** cbor_match p2 x2 v2 **
        pure (
          same_sign (I16.v res) (cbor_compare v1 v2)
        )
      )
{
  let m = common_depth (Ghost.hide (raw_data_item_size v1)) (Ghost.hide (raw_data_item_size v2));
  cbor_match_to_depth m p1 x1 v1;
  cbor_match_to_depth m p2 x2 v2;
  let res = cbor_compare_with_depth m x1 x2;
  cbor_match_with_depth_forget m p1 x1 v1;
  cbor_match_with_depth_forget m p2 x2 v2;
  res
}

#pop-options
