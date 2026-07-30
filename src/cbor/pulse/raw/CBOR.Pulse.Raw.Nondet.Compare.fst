module CBOR.Pulse.Raw.Nondet.Compare
#lang-pulse
open CBOR.Pulse.Raw.Match
open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Base

module Spec = CBOR.Spec.API.Format
module Raw = CBOR.Pulse.Raw.Match
module SpecRaw = CBOR.Spec.Raw
module Read = CBOR.Pulse.Raw.Read
module U64 = FStar.UInt64
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module ML = CBOR.Pulse.Raw.Format.MixedList

// ===== Size-invariant helpers (mirror of CBOR.Pulse.Raw.Compare) =====
// [size_lt depth e] holds when element [e]'s recursive size is strictly below
// [depth], hence [<= nat_pred depth] once [depth >= 1]. Threaded through the
// recursion so the depth destructors need not force [depth >= 1] for _Gen.
let size_lt (depth: nat) (e: SpecRaw.raw_data_item) : bool =
  SpecRaw.raw_data_item_size e < depth

let map_size_lt (depth: nat) (e: (SpecRaw.raw_data_item & SpecRaw.raw_data_item)) : bool =
  SpecRaw.raw_data_item_size (fst e) < depth &&
  SpecRaw.raw_data_item_size (snd e) < depth

let rec list_elts_size_bound (l: list SpecRaw.raw_data_item) (depth: nat)
  : Lemma (requires CBOR.Spec.Util.list_sum SpecRaw.raw_data_item_size l + 2 <= depth)
          (ensures List.Tot.for_all (size_lt depth) l)
          (decreases l)
  = match l with
    | [] -> ()
    | a :: q -> list_elts_size_bound q depth

let array_elts_size_bound (v: SpecRaw.raw_data_item {SpecRaw.Array? v}) (depth: nat)
  : Lemma (requires SpecRaw.raw_data_item_size v <= depth)
          (ensures List.Tot.for_all (size_lt depth) (SpecRaw.Array?.v v))
  = SpecRaw.raw_data_item_size_eq v;
    list_elts_size_bound (SpecRaw.Array?.v v) depth

let rec map_entries_size_bound_aux
  (l: list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)) (depth: nat)
  : Lemma (requires
      CBOR.Spec.Util.list_sum
        (CBOR.Spec.Util.pair_sum SpecRaw.raw_data_item_size SpecRaw.raw_data_item_size) l + 2 <= depth)
          (ensures List.Tot.for_all (map_size_lt depth) l)
          (decreases l)
  = match l with
    | [] -> ()
    | a :: q -> map_entries_size_bound_aux q depth

let map_entries_size_bound (v: SpecRaw.raw_data_item {SpecRaw.Map? v}) (depth: nat)
  : Lemma (requires SpecRaw.raw_data_item_size v <= depth)
          (ensures List.Tot.for_all (map_size_lt depth) (SpecRaw.Map?.v v))
  = SpecRaw.raw_data_item_size_eq v;
    map_entries_size_bound_aux (SpecRaw.Map?.v v) depth

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_equiv_t =
  (x1: Raw.cbor_raw) ->
  (#p1: perm) ->
  (#v1: Ghost.erased SpecRaw.raw_data_item) ->
  (x2: Raw.cbor_raw) ->
  (#p2: perm) ->
  (#v2: Ghost.erased SpecRaw.raw_data_item) ->
  stt bool
  (Raw.cbor_match p1 x1 v1 **
    Raw.cbor_match p2 x2 v2 **
    pure (SpecRaw.valid_raw_data_item v1 /\
      SpecRaw.valid_raw_data_item v2
    )
  )
  (fun res ->
    Raw.cbor_match p1 x1 v1 **
    Raw.cbor_match p2 x2 v2 **
    pure (res == SpecRaw.raw_equiv v1 v2)
  )

// Convert a non-inline-composite (leaf or serialized) [cbor_match_with_depth]
// to a plain [cbor_match], with a trade to restore the depth predicate.
ghost
fn cbor_match_with_depth_to_match
  (depth: Ghost.erased nat)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased SpecRaw.raw_data_item)
requires
  cbor_match_with_depth depth p x v **
  pure (~ (CBOR_Case_Array? x \/ CBOR_Case_Map? x \/ CBOR_Case_Tagged? x \/ CBOR_Case_Array_Gen? x \/ CBOR_Case_Map_Gen? x))
ensures
  cbor_match p x v **
  Trade.trade (cbor_match p x v) (cbor_match_with_depth depth p x v)
{
  Read.cbor_match_with_depth_cases depth p x v;
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

module Sl = Pulse.Lib.Slice

// A tagged at [cbor_match_with_depth depth] forces depth >= 1 (mirror of array_pos/map_pos).
ghost
fn cbor_match_with_depth_tagged_pos
  (depth: Ghost.erased nat) (p: perm) (a: cbor_tagged) (v: SpecRaw.raw_data_item { SpecRaw.Tagged? v })
  requires cbor_match_with_depth depth p (CBOR_Case_Tagged a) v
  ensures cbor_match_with_depth depth p (CBOR_Case_Tagged a) v ** pure (Ghost.reveal depth >= 1)
{
  cbor_match_with_depth_tagged_elim depth p a v;
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
}

// Depth-preserving major-type reader.
fn impl_major_type_with_depth
  (depth: Ghost.erased nat)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased SpecRaw.raw_data_item)
requires
  cbor_match_with_depth depth p x v
returns t: Spec.major_type_t
ensures
  cbor_match_with_depth depth p x v ** pure (t == SpecRaw.get_major_type v)
{
  Read.cbor_match_with_depth_cases depth p x v;
  match x {
    norewrite
    CBOR_Case_Simple _ -> { Spec.cbor_major_type_simple_value }
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
    CBOR_Case_Tagged _ -> { Spec.cbor_major_type_tagged }
    norewrite
    CBOR_Case_Serialized_Tagged _ -> { Spec.cbor_major_type_tagged }
    norewrite
    CBOR_Case_Array _ -> { Spec.cbor_major_type_array }
    norewrite
    CBOR_Case_Serialized_Array _ -> { Spec.cbor_major_type_array }
    norewrite
    CBOR_Case_Map _ -> { Spec.cbor_major_type_map }
    norewrite
    CBOR_Case_Serialized_Map _ -> { Spec.cbor_major_type_map }
    norewrite
    CBOR_Case_Array_Gen _ -> { Spec.cbor_major_type_array }
    norewrite
    CBOR_Case_Map_Gen _ -> { Spec.cbor_major_type_map }
  }
}

// Depth-preserving array length reader (handles inline and serialized).
fn cbor_match_array_get_length_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased SpecRaw.raw_data_item)
requires
  cbor_match_with_depth depth p c v ** pure (SpecRaw.Array? v)
returns res: SpecRaw.raw_uint64
ensures
  cbor_match_with_depth depth p c v ** pure (SpecRaw.Array? v /\ res == SpecRaw.Array?.len v)
{
  Read.cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Array a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
      cbor_match_with_depth_array_elim depth p a v;
      let res : SpecRaw.raw_uint64 = { size = a.cbor_array_length_size; value = SZ.sizet_to_uint64 (Sl.len a.cbor_array_ptr) };
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
      let res : SpecRaw.raw_uint64 = { size = a.cbor_array_gen_length_size; value = SZ.sizet_to_uint64 (ML.cbor_raw_mixed_list_length a.cbor_array_gen_ptr) };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Array_Gen a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Array_Gen a) v) as (cbor_match_with_depth depth p c v);
      res
    }
  }
}

// Depth-preserving tag reader (handles inline and serialized).
fn cbor_match_tagged_get_tag_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased SpecRaw.raw_data_item)
requires
  cbor_match_with_depth depth p c v ** pure (SpecRaw.Tagged? v)
returns res: SpecRaw.raw_uint64
ensures
  cbor_match_with_depth depth p c v ** pure (SpecRaw.Tagged? v /\ res == SpecRaw.Tagged?.tag v)
{
  Read.cbor_match_with_depth_cases depth p c v;
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

ghost
fn cbor_match_with_depth_tagged_pos_raw
  (depth: Ghost.erased nat) (p: perm) (x: cbor_raw) (v: SpecRaw.raw_data_item { SpecRaw.Tagged? v })
  requires cbor_match_with_depth depth p x v ** pure (CBOR_Case_Tagged? x)
  ensures cbor_match_with_depth depth p x v ** pure (Ghost.reveal depth >= 1)
{
  let a = CBOR_Case_Tagged?.v x;
  rewrite (cbor_match_with_depth depth p x v) as (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
  cbor_match_with_depth_tagged_pos depth p a v;
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v) as (cbor_match_with_depth depth p x v);
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_equiv_with_depth_t (depth: Ghost.erased nat) =
  (x1: cbor_raw) ->
  (#p1: perm) ->
  (#v1: Ghost.erased SpecRaw.raw_data_item) ->
  (x2: cbor_raw) ->
  (#p2: perm) ->
  (#v2: Ghost.erased SpecRaw.raw_data_item) ->
  stt bool
  (cbor_match_with_depth depth p1 x1 v1 **
    cbor_match_with_depth depth p2 x2 v2 **
    pure (SpecRaw.valid_raw_data_item v1 /\ SpecRaw.valid_raw_data_item v2 /\
      SpecRaw.raw_data_item_size v1 <= Ghost.reveal depth /\ SpecRaw.raw_data_item_size v2 <= Ghost.reveal depth))
  (fun res ->
    cbor_match_with_depth depth p1 x1 v1 **
    cbor_match_with_depth depth p2 x2 v2 **
    pure (res == SpecRaw.raw_equiv v1 v2))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_setoid_assoc_eq_with_depth
  (depth: Ghost.erased nat)
  (req: (depth': Ghost.erased nat { depth' < depth }) -> cbor_nondet_equiv_with_depth_t depth')
  (i1: cbor_map_iterator)
  (#p1: perm)
  (#v1: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
  (x2: cbor_map_entry)
  (#p2: perm)
  (#v2: Ghost.erased (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
requires
  Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 v1 **
  cbor_match_map_entry_with_depth (nat_pred depth) p2 x2 v2 **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v1) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v1) /\
    SpecRaw.valid_raw_data_item (fst v2) /\
    SpecRaw.valid_raw_data_item (snd v2) /\
    List.Tot.for_all (map_size_lt depth) v1 /\
    map_size_lt depth v2
  )
returns res: bool
ensures
  Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 v1 **
  cbor_match_map_entry_with_depth (nat_pred depth) p2 x2 v2 **
  pure (res == CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1 v2)
{
  Trade.refl (Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 v1);
  let mut pi1 = i1;
  let mut pres = (None #bool);
  while (
    let res = !pres;
    let i1 = !pi1;
    (None? res && not (Read.cbor_map_iterator_is_empty_with_depth (nat_pred depth) i1))
  ) invariant exists* gi1 l1 res . (
    pts_to pi1 gi1 **
    Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 gi1 l1 **
    Trade.trade
      (Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 gi1 l1)
      (Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 v1) **
    pts_to pres res **
    cbor_match_map_entry_with_depth (nat_pred depth) p2 x2 v2 **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l1) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd l1) /\
      List.Tot.for_all (map_size_lt depth) l1 /\
      map_size_lt depth v2 /\
      CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1 v2 == (match res with Some r -> r | _ -> CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv l1 v2)
    )
  ) {
    let x1 = Read.cbor_map_iterator_next_with_depth (nat_pred depth) pi1;
    Trade.trans _ _ (Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 v1);
    with px1 vx1 . assert (cbor_match_map_entry_with_depth (nat_pred depth) px1 x1 vx1);
    unfold (cbor_match_map_entry_with_depth (nat_pred depth) px1 x1 vx1);
    unfold (cbor_match_map_entry_with_depth (nat_pred depth) p2 x2 v2);
    if (req (nat_pred depth) x2.cbor_map_entry_key x1.cbor_map_entry_key) {
      pres := Some (req (nat_pred depth) x2.cbor_map_entry_value x1.cbor_map_entry_value);
      fold (cbor_match_map_entry_with_depth (nat_pred depth) px1 x1 vx1);
      fold (cbor_match_map_entry_with_depth (nat_pred depth) p2 x2 v2);
      Trade.elim_hyp_l _ _ _
    } else {
      fold (cbor_match_map_entry_with_depth (nat_pred depth) px1 x1 vx1);
      fold (cbor_match_map_entry_with_depth (nat_pred depth) p2 x2 v2);
      Trade.elim_hyp_l _ _ _
    }
  };
  Trade.elim _ _;
  CBOR.Pulse.Raw.Util.eq_Some_true !pres
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_list_for_all_setoid_assoc_eq_with_depth
  (depth: Ghost.erased nat)
  (req: (depth': Ghost.erased nat { depth' < depth }) -> cbor_nondet_equiv_with_depth_t depth')
  (i1: cbor_map_iterator)
  (#p1: perm)
  (#v1: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
  (i2: cbor_map_iterator)
  (#p2: perm)
  (#v2: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
requires
  Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 v1 **
  Read.cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 v2 **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v1) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v1) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v2) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v2) /\
    List.Tot.for_all (map_size_lt depth) v1 /\
    List.Tot.for_all (map_size_lt depth) v2
  )
returns res: bool
ensures
  Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 v1 **
  Read.cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 v2 **
  pure (res == List.Tot.for_all (CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1) v2)
{
  let mut pi2 = i2;
  Trade.refl (Read.cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 v2);
  let mut pres = true;
  while (
    let res = !pres;
    let i2 = !pi2;
    (res && not (Read.cbor_map_iterator_is_empty_with_depth (nat_pred depth) i2))
  ) invariant exists* gi2 l2 res . (
    Read.cbor_map_iterator_match_with_depth (nat_pred depth) p1 i1 v1 **
    pts_to pi2 gi2 **
    Read.cbor_map_iterator_match_with_depth (nat_pred depth) p2 gi2 l2 **
    pts_to pres res **
    Trade.trade
      (Read.cbor_map_iterator_match_with_depth (nat_pred depth) p2 gi2 l2)
      (Read.cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 v2) **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l2) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd l2) /\
      List.Tot.for_all (map_size_lt depth) v1 /\
      List.Tot.for_all (map_size_lt depth) l2 /\
      List.Tot.for_all (CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1) v2 == (res && List.Tot.for_all (CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1) l2)
    )
  ) {
    let x2 = Read.cbor_map_iterator_next_with_depth (nat_pred depth) pi2;
    Trade.trans _ _ (Read.cbor_map_iterator_match_with_depth (nat_pred depth) p2 i2 v2);
    pres := cbor_nondet_setoid_assoc_eq_with_depth depth req i1 x2;
    Trade.elim_hyp_l _ _ _
  };
  Trade.elim _ _;
  !pres
}

#push-options "--z3rlimit 32 --print_implicits"

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_equiv_body_d
  (depth: Ghost.erased nat)
  (req: (depth': Ghost.erased nat { depth' < depth }) -> cbor_nondet_equiv_with_depth_t depth')
  (x1: cbor_raw)
  (#p1: perm)
  (#v1: Ghost.erased SpecRaw.raw_data_item)
  (x2: cbor_raw)
  (#p2: perm)
  (#v2: Ghost.erased SpecRaw.raw_data_item)
requires
  cbor_match_with_depth depth p1 x1 v1 **
  cbor_match_with_depth depth p2 x2 v2 **
  pure (SpecRaw.valid_raw_data_item v1 /\ SpecRaw.valid_raw_data_item v2 /\
    SpecRaw.raw_data_item_size v1 <= Ghost.reveal depth /\ SpecRaw.raw_data_item_size v2 <= Ghost.reveal depth)
returns res: bool
ensures
  cbor_match_with_depth depth p1 x1 v1 **
  cbor_match_with_depth depth p2 x2 v2 **
  pure (res == SpecRaw.raw_equiv v1 v2)
{
  Read.cbor_match_with_depth_cases depth p1 x1 v1;
  Read.cbor_match_with_depth_cases depth p2 x2 v2;
  SpecRaw.valid_eq SpecRaw.basic_data_model v1;
  SpecRaw.valid_eq SpecRaw.basic_data_model v2;
  SpecRaw.raw_equiv_eq_valid v1 v2;
  let mt1 = impl_major_type_with_depth depth x1;
  let mt2 = impl_major_type_with_depth depth x2;
  if (mt1 <> mt2) {
    false
  } else if (mt1 = Spec.cbor_major_type_simple_value) {
    cbor_match_with_depth_to_match depth x1;
    cbor_match_with_depth_to_match depth x2;
    let w1 = Raw.cbor_match_simple_elim x1;
    let w2 = Raw.cbor_match_simple_elim x2;
    Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
    Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
    (w1 = w2)
  } else if (mt1 = Spec.cbor_major_type_uint64 || mt1 = Spec.cbor_major_type_neg_int64) {
    cbor_match_with_depth_to_match depth x1;
    cbor_match_with_depth_to_match depth x2;
    let w1 = Raw.cbor_match_int_elim_value x1;
    let w2 = Raw.cbor_match_int_elim_value x2;
    Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
    Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
    ((w1.value <: U64.t) = w2.value)
  } else if (mt1 = Spec.cbor_major_type_byte_string || mt1 = Spec.cbor_major_type_text_string) {
    cbor_match_with_depth_to_match depth x1;
    cbor_match_with_depth_to_match depth x2;
    let len1 = Raw.cbor_match_string_elim_length x1;
    let len2 = Raw.cbor_match_string_elim_length x2;
    if ((len1.value <: U64.t) <> len2.value) {
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      false
    } else {
      let w1 = Raw.cbor_match_string_elim_payload x1;
      let w2 = Raw.cbor_match_string_elim_payload x2;
      let res = CBOR.Pulse.Raw.Compare.Bytes.lex_compare_bytes w1 w2;
      CBOR.Spec.Raw.Format.bytes_lex_compare_equal (SpecRaw.String?.v v1) (SpecRaw.String?.v v2);
      Trade.elim _ (cbor_match p1 x1 v1);
      Trade.elim _ (cbor_match p2 x2 v2);
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      (res = 0s)
    }
  } else if (mt1 = Spec.cbor_major_type_tagged) {
    if (match x1, x2 with Raw.CBOR_Case_Serialized_Tagged _, Raw.CBOR_Case_Serialized_Tagged _ -> true | _ -> false) {
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      norewrite let Raw.CBOR_Case_Serialized_Tagged cs1 = x1;
      norewrite let Raw.CBOR_Case_Serialized_Tagged cs2 = x2;
      Trade.rewrite_with_trade
        (cbor_match p1 x1 v1)
        (cbor_match_serialized_tagged cs1 p1 v1);
      Trade.rewrite_with_trade
        (cbor_match p2 x2 v2)
        (cbor_match_serialized_tagged cs2 p2 v2);
      let res = CBOR.Pulse.Raw.Format.Nondet.Compare.cbor_match_equal_serialized_tagged cs1 cs2;
      Trade.elim _ (cbor_match p1 x1 v1);
      Trade.elim _ (cbor_match p2 x2 v2);
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      res
    } else {
      let tag1 = cbor_match_tagged_get_tag_with_depth depth x1;
      let tag2 = cbor_match_tagged_get_tag_with_depth depth x2;
      if ((tag1.value <: U64.t) <> tag2.value) {
        false
      } else {
        if (match x1 with Raw.CBOR_Case_Tagged _ -> true | _ -> false) {
          cbor_match_with_depth_tagged_pos_raw depth p1 x1 v1;
        } else {
          cbor_match_with_depth_tagged_pos_raw depth p2 x2 v2;
        };
        size_tagged_child v1;
        size_tagged_child v2;
        let w1 = Read.cbor_match_tagged_get_payload_with_depth depth x1;
        let w2 = Read.cbor_match_tagged_get_payload_with_depth depth x2;
        let res = req (nat_pred depth) w1 w2;
        Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
        Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
        res
      }
    }
  } else if (mt1 = Spec.cbor_major_type_array) {
    if (match x1, x2 with Raw.CBOR_Case_Serialized_Array _, Raw.CBOR_Case_Serialized_Array _ -> true | _ -> false) {
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      norewrite let Raw.CBOR_Case_Serialized_Array cs1 = x1;
      norewrite let Raw.CBOR_Case_Serialized_Array cs2 = x2;
      Trade.rewrite_with_trade
        (cbor_match p1 x1 v1)
        (cbor_match_serialized_array cs1 p1 v1);
      Trade.rewrite_with_trade
        (cbor_match p2 x2 v2)
        (cbor_match_serialized_array cs2 p2 v2);
      let res = CBOR.Pulse.Raw.Format.Nondet.Compare.cbor_match_compare_serialized_array cs1 cs2;
      Trade.elim _ (cbor_match p1 x1 v1);
      Trade.elim _ (cbor_match p2 x2 v2);
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      res
    } else {
      let len1 = cbor_match_array_get_length_with_depth depth x1;
      let len2 = cbor_match_array_get_length_with_depth depth x2;
      Classical.move_requires (CBOR.Spec.Util.list_for_all2_length SpecRaw.raw_equiv (SpecRaw.Array?.v v1)) (SpecRaw.Array?.v v2);
      if ((len1.value <: U64.t) <> len2.value) {
        false
      } else {
        array_elts_size_bound v1 depth;
        array_elts_size_bound v2 depth;
        let i1 = Read.cbor_array_iterator_init_with_depth depth x1;
        let i2 = Read.cbor_array_iterator_init_with_depth depth x2;
        let mut pi1 = i1;
        let mut pi2 = i2;
        let mut pres = true;
        while (
          let res = !pres;
          let i1 = !pi1;
          (res && not (Read.cbor_array_iterator_is_empty_with_depth (nat_pred depth) i1))
        ) invariant exists* i1 i2 res l1 l2 pj1 pj2 . (
          pts_to pi1 i1 **
          pts_to pi2 i2 **
          pts_to pres res **
          Read.cbor_array_iterator_match_with_depth (nat_pred depth) pj1 i1 l1 **
          Read.cbor_array_iterator_match_with_depth (nat_pred depth) pj2 i2 l2 **
          Trade.trade
            (Read.cbor_array_iterator_match_with_depth (nat_pred depth) pj1 i1 l1)
            (cbor_match_with_depth depth p1 x1 v1) **
          Trade.trade
            (Read.cbor_array_iterator_match_with_depth (nat_pred depth) pj2 i2 l2)
            (cbor_match_with_depth depth p2 x2 v2) **
          pure (
            List.Tot.length l1 == List.Tot.length l2 /\
            List.Tot.for_all SpecRaw.valid_raw_data_item l1 /\
            List.Tot.for_all SpecRaw.valid_raw_data_item l2 /\
            List.Tot.for_all (size_lt depth) l1 /\
            List.Tot.for_all (size_lt depth) l2 /\
            (SpecRaw.raw_equiv v1 v2 == (res && CBOR.Spec.Util.list_for_all2 SpecRaw.raw_equiv l1 l2))
          )
        ) {
          let y1 = Read.cbor_array_iterator_next_with_depth (nat_pred depth) pi1;
          Trade.trans _ _ (cbor_match_with_depth depth p1 x1 v1);
          let y2 = Read.cbor_array_iterator_next_with_depth (nat_pred depth) pi2;
          Trade.trans _ _ (cbor_match_with_depth depth p2 x2 v2);
          pres := req (nat_pred depth) y1 y2;
          Trade.elim_hyp_l _ _ (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim_hyp_l _ _ (cbor_match_with_depth depth p2 x2 v2);
        };
        Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
        Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
        !pres
      }
    }
  } else {
    assert (pure (mt1 == Spec.cbor_major_type_map));
    if (match x1, x2 with Raw.CBOR_Case_Serialized_Map _, Raw.CBOR_Case_Serialized_Map _ -> true | _ -> false) {
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      norewrite let Raw.CBOR_Case_Serialized_Map cs1 = x1;
      norewrite let Raw.CBOR_Case_Serialized_Map cs2 = x2;
      Trade.rewrite_with_trade
        (cbor_match p1 x1 v1)
        (cbor_match_serialized_map cs1 p1 v1);
      Trade.rewrite_with_trade
        (cbor_match p2 x2 v2)
        (cbor_match_serialized_map cs2 p2 v2);
      let res = CBOR.Pulse.Raw.Format.Nondet.Compare.cbor_match_compare_serialized_map cs1 cs2;
      Trade.elim _ (cbor_match p1 x1 v1);
      Trade.elim _ (cbor_match p2 x2 v2);
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      res
    } else {
      map_entries_size_bound v1 depth;
      map_entries_size_bound v2 depth;
      let i1 = Read.cbor_map_iterator_init_with_depth depth x1;
      let i2 = Read.cbor_map_iterator_init_with_depth depth x2;
      if (not (cbor_nondet_list_for_all_setoid_assoc_eq_with_depth depth req i2 i1)) {
        Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
        Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
        false
      } else {
        let res = cbor_nondet_list_for_all_setoid_assoc_eq_with_depth depth req i1 i2;
        Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
        Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
        res
      }
    }
  }
}

#pop-options

let common_depth (n1 n2: Ghost.erased nat) : Ghost.erased nat =
  Ghost.hide (if Ghost.reveal n1 >= Ghost.reveal n2 then Ghost.reveal n1 else Ghost.reveal n2)

fn rec cbor_nondet_equiv_with_depth
  (depth: Ghost.erased nat)
  (x1: cbor_raw)
  (#p1: perm)
  (#v1: Ghost.erased SpecRaw.raw_data_item)
  (x2: cbor_raw)
  (#p2: perm)
  (#v2: Ghost.erased SpecRaw.raw_data_item)
requires
  cbor_match_with_depth depth p1 x1 v1 **
  cbor_match_with_depth depth p2 x2 v2 **
  pure (SpecRaw.valid_raw_data_item v1 /\ SpecRaw.valid_raw_data_item v2 /\
    SpecRaw.raw_data_item_size v1 <= Ghost.reveal depth /\ SpecRaw.raw_data_item_size v2 <= Ghost.reveal depth)
returns res: bool
ensures
  cbor_match_with_depth depth p1 x1 v1 **
  cbor_match_with_depth depth p2 x2 v2 **
  pure (res == SpecRaw.raw_equiv v1 v2)
decreases (Ghost.reveal depth)
{
  cbor_nondet_equiv_body_d depth (fun (depth': Ghost.erased nat { depth' < depth }) -> cbor_nondet_equiv_with_depth depth') x1 x2
}

fn cbor_nondet_equiv
  (x1: cbor_raw)
  (#p1: perm)
  (#v1: Ghost.erased SpecRaw.raw_data_item)
  (x2: cbor_raw)
  (#p2: perm)
  (#v2: Ghost.erased SpecRaw.raw_data_item)
requires
  Raw.cbor_match p1 x1 v1 **
  Raw.cbor_match p2 x2 v2 **
  pure (SpecRaw.valid_raw_data_item v1 /\ SpecRaw.valid_raw_data_item v2)
returns res: bool
ensures
  Raw.cbor_match p1 x1 v1 **
  Raw.cbor_match p2 x2 v2 **
  pure (res == SpecRaw.raw_equiv v1 v2)
{
  let m = common_depth (Ghost.hide (SpecRaw.raw_data_item_size v1)) (Ghost.hide (SpecRaw.raw_data_item_size v2));
  cbor_match_to_depth m p1 x1 v1;
  cbor_match_to_depth m p2 x2 v2;
  let res = cbor_nondet_equiv_with_depth m x1 x2;
  cbor_match_with_depth_forget m p1 x1 v1;
  cbor_match_with_depth_forget m p2 x2 v2;
  res
}

module S = Pulse.Lib.Slice.Util
module SM = Pulse.Lib.SeqMatch.Util

fn cbor_nondet_no_setoid_repeats
  (x: S.slice cbor_map_entry)
  (#px: perm)
  (#s: Ghost.erased (Seq.seq cbor_map_entry))
  (#ps: perm)
  (#l: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
requires
  pts_to x #px s **
  SM.seq_list_match s l (Raw.cbor_match_map_entry ps) **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l)
  )
returns res: bool
ensures
  pts_to x #px s **
  SM.seq_list_match s l (Raw.cbor_match_map_entry ps) **
  pure (res == CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l))
{
  S.pts_to_len x;
  let mut pn1 = 0sz;
  let mut pres = true;
  Trade.refl (SM.seq_list_match s l (Raw.cbor_match_map_entry ps));
  while (
    let res = !pres;
    SM.seq_list_match_length (Raw.cbor_match_map_entry ps) _ _;
    (res && SZ.lt !pn1 (S.len x))
  ) invariant exists* n1 res s1 l1 . (
    pts_to x #px s **
    pts_to pn1 n1 **
    pts_to pres res **
    SM.seq_list_match s1 l1 (Raw.cbor_match_map_entry ps) **
    Trade.trade
      (SM.seq_list_match s1 l1 (Raw.cbor_match_map_entry ps))
      (SM.seq_list_match s l (Raw.cbor_match_map_entry ps)) **
    pure (
      SZ.v n1 <= Seq.length s /\
      Seq.equal s1 (Seq.slice s (SZ.v n1) (Seq.length s)) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l1) /\
      CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l) == (res && CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l1))
    )
  ) {
    SM.seq_list_match_length (Raw.cbor_match_map_entry ps) _ _;
    let n1 = !pn1;
    let x1 = S.op_Array_Access x n1;
    SM.seq_list_match_cons_elim_trade _ _ (Raw.cbor_match_map_entry ps);
    Trade.trans _ _ (SM.seq_list_match s l (Raw.cbor_match_map_entry ps));
    with gx1 y1 . assert Raw.cbor_match_map_entry ps gx1 y1;
    rewrite each gx1 as x1;
    let n2 : SZ.t = SZ.add n1 1sz;
    pn1 := n2;
    let mut pn2 = n2;
    with s1' l1' . assert (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps));
    Trade.refl (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps));
    while (
      let res = !pres;
      SM.seq_list_match_length (Raw.cbor_match_map_entry ps) _ _;
      (res && SZ.lt !pn2 (S.len x))
    ) invariant exists* n2 res s2 l2 . (
      pts_to x #px s **
      Raw.cbor_match_map_entry ps x1 y1 **
      pts_to pn2 n2 **
      pts_to pres res **
      SM.seq_list_match s2 l2 (Raw.cbor_match_map_entry ps) **
      Trade.trade
        (SM.seq_list_match s2 l2 (Raw.cbor_match_map_entry ps))
        (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps)) **
      pure (
        SZ.v n2 <= Seq.length s /\
        Seq.equal s2 (Seq.slice s (SZ.v n2) (Seq.length s)) /\
        List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l2) /\
        CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l) == (res && (not (List.Tot.existsb (SpecRaw.raw_equiv (fst y1)) (List.Tot.map fst l2))) && CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l1'))
      )
    ) {
      SM.seq_list_match_length (Raw.cbor_match_map_entry ps) _ _;
      let n2 = !pn2;
      let x2 = S.op_Array_Access x n2;
      SM.seq_list_match_cons_elim_trade _ _ (Raw.cbor_match_map_entry ps);
      with gx2 y2 . assert (Raw.cbor_match_map_entry ps x1 y1 ** Raw.cbor_match_map_entry ps gx2 y2);
      rewrite each gx2 as x2;
      unfold (Raw.cbor_match_map_entry ps x1 y1);
      unfold (Raw.cbor_match_map_entry ps x2 y2);
      pres := not (cbor_nondet_equiv x1.cbor_map_entry_key x2.cbor_map_entry_key);
      fold (Raw.cbor_match_map_entry ps x1 y1);
      fold (Raw.cbor_match_map_entry ps x2 y2);
      Trade.elim_hyp_l (Raw.cbor_match_map_entry ps x2 y2) _ _;
      Trade.trans _ _ (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps));
      pn2 := SZ.add n2 1sz;
    };
    Trade.elim_hyp_l _ _ _;
    Trade.elim _ (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps));
    ()
  };
  Trade.elim _ _;
  !pres
}
