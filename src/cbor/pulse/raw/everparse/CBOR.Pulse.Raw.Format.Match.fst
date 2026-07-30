module CBOR.Pulse.Raw.Format.Match
friend CBOR.Pulse.Raw.Format.MixedList
#lang-pulse
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.VCList
open LowParse.Pulse.Base

module U64 = FStar.UInt64

let cbor_match_serialized_payload_array
  c p r
= exists* n (r': nlist n raw_data_item) .
    pts_to_serialized (serialize_nlist n serialize_raw_data_item) c #p r' **
    pure (r == r')

let cbor_match_serialized_payload_map
  c p r
= exists* n (r' : nlist n (raw_data_item & raw_data_item)) .
    pts_to_serialized (serialize_nlist n (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item)) c #p r' **
    pure (r == r')

let cbor_match_serialized_payload_tagged
  c p r
= pts_to_serialized serialize_raw_data_item c #p r

ghost
fn cbor_match_serialized_payload_array_share
  (c: slice U8.t)
  (p: perm)
  (r: list raw_data_item)
requires
    (cbor_match_serialized_payload_array c p r)
ensures
    (
      cbor_match_serialized_payload_array c (p /. 2.0R) r **
      cbor_match_serialized_payload_array c (p /. 2.0R) r
    )
{
  unfold (cbor_match_serialized_payload_array c p r);
  with n (r': nlist n raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n serialize_raw_data_item) c #p r');
  pts_to_serialized_share (serialize_nlist n serialize_raw_data_item) c;
  fold (cbor_match_serialized_payload_array c (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_array c (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_array_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: list raw_data_item)
  (p2: perm)
  (r2: list raw_data_item)
requires
    (cbor_match_serialized_payload_array c p1 r1 **
      cbor_match_serialized_payload_array c p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_array c (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_array c p1 r1);
  with n1 (r1': nlist n1 raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) c #p1 r1');
  unfold (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) c #p1 r1');
  serialize_nlist_serialize_list n1 serialize_raw_data_item r1';
  unfold (cbor_match_serialized_payload_array c p2 r2);
  with n2 (r2': nlist n2 raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) c #p2 r2');
  unfold (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) c #p2 r2');
  serialize_nlist_serialize_list n2 serialize_raw_data_item r2';
  Pulse.Lib.Slice.gather c;
  serializer_injective _ (serialize_list _ serialize_raw_data_item) r1' r2';
  fold (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) c #(p1 +. p2) r1');
  fold (cbor_match_serialized_payload_array c (p1 +. p2) r1);
}

ghost
fn cbor_match_serialized_payload_map_share
  (c: slice U8.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
requires
    (cbor_match_serialized_payload_map c p r)
ensures
    (
      cbor_match_serialized_payload_map c (p /. 2.0R) r **
      cbor_match_serialized_payload_map c (p /. 2.0R) r
    )
{
  unfold (cbor_match_serialized_payload_map c p r);
  with n (r': nlist n (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p r');
  pts_to_serialized_share (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c;
  fold (cbor_match_serialized_payload_map c (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_map c (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_map_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: list (raw_data_item & raw_data_item))
  (p2: perm)
  (r2: list (raw_data_item & raw_data_item))
requires
    (cbor_match_serialized_payload_map c p1 r1 **
      cbor_match_serialized_payload_map c p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_map c (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_map c p1 r1);
  with n1 (r1': nlist n1 (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p1 r1');
  unfold (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p1 r1');
  serialize_nlist_serialize_list n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) r1';
  unfold (cbor_match_serialized_payload_map c p2 r2);
  with n2 (r2': nlist n2 (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p2 r2');
  unfold (pts_to_serialized (serialize_nlist n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p2 r2');
  serialize_nlist_serialize_list n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) r2';
  Pulse.Lib.Slice.gather c;
  serializer_injective _ (serialize_list _ (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) r1' r2';
  fold (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #(p1 +. p2) r1');
  fold (cbor_match_serialized_payload_map c (p1 +. p2) r1);
}

ghost
fn cbor_match_serialized_payload_tagged_share
  (c: slice U8.t)
  (p: perm)
  (r: raw_data_item)
requires
    (cbor_match_serialized_payload_tagged c p r)
ensures
    (
      cbor_match_serialized_payload_tagged c (p /. 2.0R) r **
      cbor_match_serialized_payload_tagged c (p /. 2.0R) r
    )
{
  unfold (cbor_match_serialized_payload_tagged c p r);
  pts_to_serialized_share serialize_raw_data_item c;
  fold (cbor_match_serialized_payload_tagged c (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_tagged c (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_tagged_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
requires
    (cbor_match_serialized_payload_tagged c p1 r1 **
      cbor_match_serialized_payload_tagged c p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_tagged c (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_tagged c p1 r1);
  unfold (cbor_match_serialized_payload_tagged c p2 r2);
  pts_to_serialized_gather serialize_raw_data_item c;
  fold (cbor_match_serialized_payload_tagged c (p1 +. p2) r1);
}

#set-options "--print_implicits"

fn cbor_match_serialized_payload_array_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list raw_data_item))
  (c': slice U8.t)
norewrite
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_array c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_array c p r **
      cbor_match_serialized_payload_array c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_array c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_array c p r);
  with n r' . assert (
    pts_to_serialized (serialize_nlist n serialize_raw_data_item) c #p r'
  );
  pts_to_serialized_copy #(nlist n raw_data_item) #(parse_nlist_kind n parse_raw_data_item_kind) #(coerce_eq () (parse_nlist n parse_raw_data_item)) (coerce_eq () (serialize_nlist n serialize_raw_data_item <: serializer (parse_nlist n parse_raw_data_item))) c c';
  fold (cbor_match_serialized_payload_array c p r);
  fold (cbor_match_serialized_payload_array c' 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_array c' 1.0R r)
      (exists* v' . pts_to c' v')
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_array c' 1.0R r);
    with n r' . assert (
      pts_to_serialized (serialize_nlist n serialize_raw_data_item) c' r'
    );
    unfold (pts_to_serialized (serialize_nlist n serialize_raw_data_item) c' r')
  };
}

fn cbor_match_serialized_payload_map_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list (raw_data_item & raw_data_item)))
  (c': slice U8.t)
norewrite
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_map c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_map c p r **
      cbor_match_serialized_payload_map c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_map c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_map c p r);
  with n r' . assert (
    pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p r'
  );
  pts_to_serialized_copy #(nlist n (raw_data_item & raw_data_item)) #(parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) #(coerce_eq () (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item))) (coerce_eq () (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) <: serializer (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item)))) c c';
  fold (cbor_match_serialized_payload_map c p r);
  fold (cbor_match_serialized_payload_map c' 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_map c' 1.0R r)
      (exists* v' . pts_to c' v')
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_map c' 1.0R r);
    with n r' . assert (
      pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c' r'
    );
    unfold (pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c' r')
  };
}

fn cbor_match_serialized_payload_tagged_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (raw_data_item))
  (c': slice U8.t)
norewrite
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_tagged c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_tagged c p r **
      cbor_match_serialized_payload_tagged c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_tagged c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_tagged c p r);
  with r' . assert (
    pts_to_serialized (serialize_raw_data_item) c #p r'
  );
  pts_to_serialized_copy serialize_raw_data_item c c';
  fold (cbor_match_serialized_payload_tagged c p r);
  fold (cbor_match_serialized_payload_tagged c' 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_tagged c' 1.0R r)
      (exists* v' . pts_to c' v')
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_tagged c' 1.0R r);
    with r' . assert (
      pts_to_serialized (serialize_raw_data_item) c' r'
    );
    unfold (pts_to_serialized (serialize_raw_data_item) c' r')
  };
}

let cbor_match_bounded
    (#t: Type0)
    (r0: t)
    (cbor_match: perm -> cbor_raw -> (r: raw_data_item { r << r0 }) -> slprop)
    (p: perm)
    (c: cbor_raw)
    (r: raw_data_item)
: Tot slprop
= if FStar.IndefiniteDescription.strong_excluded_middle (r << r0)
  then cbor_match p c r
  else pure False

let cbor_match_map_entry_bounded
  (#t: Type0)
  (r0: t)
  (cbor_match: perm -> (cbor_raw -> (v': raw_data_item { v' << r0 }) -> slprop))
  (p: perm)
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item))
: Tot slprop
= if FStar.IndefiniteDescription.strong_excluded_middle (r << r0)
  then cbor_match p c.cbor_map_entry_key (fst r) **
    cbor_match p c.cbor_map_entry_value (snd r)
  else pure False

let cbor_match_mixed_list_array p c r cbor_match =
    LowParse.PulseParse.Iterator.mixed_list_match (cbor_match_bounded r cbor_match) parse_raw_data_item (p *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) **
    pure (c.cbor_array_gen_length_size == (Array?.len r).size)

let cbor_match_mixed_list_map p c r cbor_match =
    LowParse.PulseParse.Iterator.mixed_list_match (cbor_match_map_entry_bounded r cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) (p *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) **
    pure (c.cbor_map_gen_length_size == (Map?.len r).size)

(* ==== Phase B: abstract mixed-list operations for the _Gen cases ==== *)

module I = LowParse.PulseParse.Iterator
module SZ = FStar.SizeT

let array_elem_precedes
  (r0: raw_data_item { Array? r0 })
  (y: raw_data_item)
: Lemma
  (requires (List.Tot.memP y (Array?.v r0)))
  (ensures (y << r0))
= FStar.List.Tot.Properties.memP_precedes y (Array?.v r0)

let map_elem_precedes
  (r0: raw_data_item { Map? r0 })
  (y: (raw_data_item & raw_data_item))
: Lemma
  (requires (List.Tot.memP y (Map?.v r0)))
  (ensures (y << r0 /\ fst y << r0 /\ snd y << r0))
= FStar.List.Tot.Properties.memP_precedes y (Map?.v r0)

let cbor_match_bounded_eq
  (#t: Type0)
  (r0: t)
  (cbor_match: perm -> cbor_raw -> (r: raw_data_item { r << r0 }) -> slprop)
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
: Lemma
  (requires (r << r0))
  (ensures (cbor_match_bounded r0 cbor_match p c r == cbor_match p c r))
= let b = FStar.IndefiniteDescription.strong_excluded_middle (r << r0) in
  assert (b == true)

let cbor_match_map_entry_bounded_eq
  (#t: Type0)
  (r0: t)
  (cbor_match: perm -> cbor_raw -> (r: raw_data_item { r << r0 }) -> slprop)
  (p: perm)
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item))
: Lemma
  (requires (r << r0))
  (ensures (cbor_match_map_entry_bounded r0 cbor_match p c r ==
    (cbor_match p c.cbor_map_entry_key (fst r) ** cbor_match p c.cbor_map_entry_value (snd r))))
= let b = FStar.IndefiniteDescription.strong_excluded_middle (r << r0) in
  assert (b == true)

ghost
fn cbor_match_mixed_list_array_length
  (p: perm)
  (c: cbor_mixed_list_array)
  (r: raw_data_item { Array? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
requires
  cbor_match_mixed_list_array p c r cbor_match
ensures
  cbor_match_mixed_list_array p c r cbor_match ** pure (
    c.cbor_array_gen_length_size == (Array?.len r).size /\
    (SZ.v (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length c.cbor_array_gen_ptr) <: (x: Prims.int { FStar.UInt.size x FStar.UInt64.n \/ x >= 0 })) == U64.v (Array?.len r).value
  )
{
  unfold (cbor_match_mixed_list_array p c r cbor_match);
  I.mixed_list_match_length (cbor_match_bounded r cbor_match) parse_raw_data_item (p *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r);
  fold (cbor_match_mixed_list_array p c r cbor_match);
}

ghost
fn cbor_match_mixed_list_map_length
  (p: perm)
  (c: cbor_mixed_list_map)
  (r: raw_data_item { Map? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
requires
  cbor_match_mixed_list_map p c r cbor_match
ensures
  cbor_match_mixed_list_map p c r cbor_match ** pure (
    c.cbor_map_gen_length_size == (Map?.len r).size /\
    (SZ.v (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length c.cbor_map_gen_ptr) <: (x: Prims.int { FStar.UInt.size x FStar.UInt64.n \/ x >= 0 })) == U64.v (Map?.len r).value
  )
{
  unfold (cbor_match_mixed_list_map p c r cbor_match);
  I.mixed_list_match_length (cbor_match_map_entry_bounded r cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) (p *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r);
  fold (cbor_match_mixed_list_map p c r cbor_match);
}

ghost
fn cbor_match_mixed_list_array_weaken
  (p: perm)
  (c: cbor_mixed_list_array)
  (r: raw_data_item { Array? r })
  (cm1 cm2: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (prf: (
    (p': perm) ->
    (c': cbor_raw) ->
    (v': raw_data_item { List.Tot.memP v' (Array?.v r) /\ v' << r }) ->
    stt_ghost unit emp_inames (cm1 p' c' v') (fun _ -> cm2 p' c' v')
  ))
requires
  cbor_match_mixed_list_array p c r cm1
ensures
  cbor_match_mixed_list_array p c r cm2
{
  unfold (cbor_match_mixed_list_array p c r cm1);
  ghost
  fn prf'
    (x: cbor_raw)
    (pm0: perm)
    (y: raw_data_item { List.Tot.memP y (Array?.v r) })
  requires cbor_match_bounded r cm1 pm0 x y
  ensures cbor_match_bounded r cm2 pm0 x y
  {
    array_elem_precedes r y;
    cbor_match_bounded_eq r cm1 pm0 x y;
    rewrite (cbor_match_bounded r cm1 pm0 x y) as (cm1 pm0 x y);
    prf pm0 x y;
    cbor_match_bounded_eq r cm2 pm0 x y;
    rewrite (cm2 pm0 x y) as (cbor_match_bounded r cm2 pm0 x y);
  };
  I.mixed_list_match_weaken (cbor_match_bounded r cm1) (cbor_match_bounded r cm2) parse_raw_data_item (p *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) prf';
  fold (cbor_match_mixed_list_array p c r cm2);
}

ghost
fn cbor_match_mixed_list_map_weaken
  (p: perm)
  (c: cbor_mixed_list_map)
  (r: raw_data_item { Map? r })
  (cm1 cm2: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (prf: (
    (p': perm) ->
    (x: cbor_map_entry) ->
    (pair: (raw_data_item & raw_data_item) { List.Tot.memP pair (Map?.v r) /\ fst pair << r /\ snd pair << r }) ->
    stt_ghost unit emp_inames
      (cm1 p' x.cbor_map_entry_key (fst pair) ** cm1 p' x.cbor_map_entry_value (snd pair))
      (fun _ -> cm2 p' x.cbor_map_entry_key (fst pair) ** cm2 p' x.cbor_map_entry_value (snd pair))
  ))
requires
  cbor_match_mixed_list_map p c r cm1
ensures
  cbor_match_mixed_list_map p c r cm2
{
  unfold (cbor_match_mixed_list_map p c r cm1);
  ghost
  fn prf'
    (x: cbor_map_entry)
    (pm0: perm)
    (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r) })
  requires cbor_match_map_entry_bounded r cm1 pm0 x y
  ensures cbor_match_map_entry_bounded r cm2 pm0 x y
  {
    map_elem_precedes r y;
    cbor_match_map_entry_bounded_eq r cm1 pm0 x y;
    rewrite (cbor_match_map_entry_bounded r cm1 pm0 x y)
      as (cm1 pm0 x.cbor_map_entry_key (fst y) ** cm1 pm0 x.cbor_map_entry_value (snd y));
    prf pm0 x y;
    cbor_match_map_entry_bounded_eq r cm2 pm0 x y;
    rewrite (cm2 pm0 x.cbor_map_entry_key (fst y) ** cm2 pm0 x.cbor_map_entry_value (snd y))
      as (cbor_match_map_entry_bounded r cm2 pm0 x y);
  };
  I.mixed_list_match_weaken (cbor_match_map_entry_bounded r cm1) (cbor_match_map_entry_bounded r cm2) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) (p *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) prf';
  fold (cbor_match_mixed_list_map p c r cm2);
}

let cbor_match_mixed_list_array_perm_eq
  p1 p2 c1 c2 r cbor_match
= ()

let cbor_match_mixed_list_map_perm_eq
  p1 p2 c1 c2 r cbor_match
= ()

(* ==== Phase B (cont.): share / gather for the _Gen cases ==== *)

let perm_half_mul (p q: perm) : Lemma ((p *. q) /. 2.0R == (p /. 2.0R) *. q) = ()

let perm_add_mul (p1 p2 q: perm) : Lemma ((p2 *. q) +. (p1 *. q) == (p1 +. p2) *. q) = ()

let array_v_len_eq (r1 r2: raw_data_item)
: Lemma
  (requires (Array? r1 /\ Array? r2 /\
    (Array?.v r1 <: list raw_data_item) == (Array?.v r2 <: list raw_data_item) /\
    (Array?.len r1).size == (Array?.len r2).size))
  (ensures (r1 == r2))
= ()

let map_v_len_eq (r1 r2: raw_data_item)
: Lemma
  (requires (Map? r1 /\ Map? r2 /\
    (Map?.v r1 <: list (raw_data_item & raw_data_item)) == (Map?.v r2 <: list (raw_data_item & raw_data_item)) /\
    (Map?.len r1).size == (Map?.len r2).size))
  (ensures (r1 == r2))
= ()

let cbor_match_bounded_eq_false
  (#t: Type0)
  (r0: t)
  (cbor_match: perm -> cbor_raw -> (r: raw_data_item { r << r0 }) -> slprop)
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
: Lemma
  (requires (~(r << r0)))
  (ensures (cbor_match_bounded r0 cbor_match p c r == pure False))
= let b = FStar.IndefiniteDescription.strong_excluded_middle (r << r0) in
  assert (b == false)

let cbor_match_map_entry_bounded_eq_false
  (#t: Type0)
  (r0: t)
  (cbor_match: perm -> cbor_raw -> (r: raw_data_item { r << r0 }) -> slprop)
  (p: perm)
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item))
: Lemma
  (requires (~(r << r0)))
  (ensures (cbor_match_map_entry_bounded r0 cbor_match p c r == pure False))
= let b = FStar.IndefiniteDescription.strong_excluded_middle (r << r0) in
  assert (b == false)

let cbor_match_map_entry_unbounded
  (cbor_match: perm -> cbor_raw -> raw_data_item -> slprop)
  (p: perm)
  (c: cbor_map_entry)
  (pair: (raw_data_item & raw_data_item))
: Tot slprop
= cbor_match p c.cbor_map_entry_key (fst pair) ** cbor_match p c.cbor_map_entry_value (snd pair)

(* ---- share ---- *)

ghost
fn vmatch_share_array
  (r: raw_data_item { Array? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (cbor_match_share: (
    (p': perm) ->
    (c': cbor_raw) ->
    (v': raw_data_item { v' << r }) ->
    stt_ghost unit emp_inames (cbor_match p' c' v') (fun _ -> cbor_match (p' /. 2.0R) c' v' ** cbor_match (p' /. 2.0R) c' v')
  ))
  (x1: cbor_raw)
  (#pm: perm)
  (#x2: raw_data_item)
requires cbor_match_bounded r cbor_match pm x1 x2
ensures cbor_match_bounded r cbor_match (pm /. 2.0R) x1 x2 ** cbor_match_bounded r cbor_match (pm /. 2.0R) x1 x2
{
  let b : (b: bool { b == true <==> (x2 << r) }) = FStar.IndefiniteDescription.strong_excluded_middle (x2 << r);
  if b {
    cbor_match_bounded_eq r cbor_match pm x1 x2;
    rewrite (cbor_match_bounded r cbor_match pm x1 x2) as (cbor_match pm x1 x2);
    cbor_match_share pm x1 x2;
    cbor_match_bounded_eq r cbor_match (pm /. 2.0R) x1 x2;
    rewrite (cbor_match (pm /. 2.0R) x1 x2) as (cbor_match_bounded r cbor_match (pm /. 2.0R) x1 x2);
    rewrite (cbor_match (pm /. 2.0R) x1 x2) as (cbor_match_bounded r cbor_match (pm /. 2.0R) x1 x2);
  } else {
    cbor_match_bounded_eq_false r cbor_match pm x1 x2;
    rewrite (cbor_match_bounded r cbor_match pm x1 x2) as (pure False);
    rewrite emp as (cbor_match_bounded r cbor_match (pm /. 2.0R) x1 x2 ** cbor_match_bounded r cbor_match (pm /. 2.0R) x1 x2);
  }
}

ghost
fn cbor_match_mixed_list_array_share
  (p: perm)
  (c: cbor_mixed_list_array)
  (r: raw_data_item { Array? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (cbor_match_share: (
    (p': perm) ->
    (c': cbor_raw) ->
    (v': raw_data_item { v' << r }) ->
    stt_ghost unit emp_inames (cbor_match p' c' v') (fun _ -> cbor_match (p' /. 2.0R) c' v' ** cbor_match (p' /. 2.0R) c' v')
  ))
requires
  cbor_match_mixed_list_array p c r cbor_match
ensures
  cbor_match_mixed_list_array (p /. 2.0R) c r cbor_match ** cbor_match_mixed_list_array (p /. 2.0R) c r cbor_match
{
  unfold (cbor_match_mixed_list_array p c r cbor_match);
  I.mixed_list_match_share (cbor_match_bounded r cbor_match) parse_raw_data_item (p *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) (vmatch_share_array r cbor_match cbor_match_share);
  perm_half_mul p c.cbor_array_gen_perm;
  rewrite (I.mixed_list_match (cbor_match_bounded r cbor_match) parse_raw_data_item ((p *. c.cbor_array_gen_perm) /. 2.0R) c.cbor_array_gen_ptr (Array?.v r))
       as (I.mixed_list_match (cbor_match_bounded r cbor_match) parse_raw_data_item ((p /. 2.0R) *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r));
  rewrite (I.mixed_list_match (cbor_match_bounded r cbor_match) parse_raw_data_item ((p *. c.cbor_array_gen_perm) /. 2.0R) c.cbor_array_gen_ptr (Array?.v r))
       as (I.mixed_list_match (cbor_match_bounded r cbor_match) parse_raw_data_item ((p /. 2.0R) *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r));
  fold (cbor_match_mixed_list_array (p /. 2.0R) c r cbor_match);
  fold (cbor_match_mixed_list_array (p /. 2.0R) c r cbor_match);
}

ghost
fn vmatch_share_map
  (r: raw_data_item { Map? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (cbor_match_share: (
    (p': perm) ->
    (c': cbor_raw) ->
    (v': raw_data_item { v' << r }) ->
    stt_ghost unit emp_inames (cbor_match p' c' v') (fun _ -> cbor_match (p' /. 2.0R) c' v' ** cbor_match (p' /. 2.0R) c' v')
  ))
  (x1: cbor_map_entry)
  (#pm: perm)
  (#x2: (raw_data_item & raw_data_item))
requires cbor_match_map_entry_bounded r cbor_match pm x1 x2
ensures cbor_match_map_entry_bounded r cbor_match (pm /. 2.0R) x1 x2 ** cbor_match_map_entry_bounded r cbor_match (pm /. 2.0R) x1 x2
{
  let b : (b: bool { b == true <==> (x2 << r) }) = FStar.IndefiniteDescription.strong_excluded_middle (x2 << r);
  if b {
    cbor_match_map_entry_bounded_eq r cbor_match pm x1 x2;
    rewrite (cbor_match_map_entry_bounded r cbor_match pm x1 x2)
      as (cbor_match pm x1.cbor_map_entry_key (fst x2) ** cbor_match pm x1.cbor_map_entry_value (snd x2));
    cbor_match_share pm x1.cbor_map_entry_key (fst x2);
    cbor_match_share pm x1.cbor_map_entry_value (snd x2);
    cbor_match_map_entry_bounded_eq r cbor_match (pm /. 2.0R) x1 x2;
    rewrite (cbor_match (pm /. 2.0R) x1.cbor_map_entry_key (fst x2) ** cbor_match (pm /. 2.0R) x1.cbor_map_entry_value (snd x2))
      as (cbor_match_map_entry_bounded r cbor_match (pm /. 2.0R) x1 x2);
    rewrite (cbor_match (pm /. 2.0R) x1.cbor_map_entry_key (fst x2) ** cbor_match (pm /. 2.0R) x1.cbor_map_entry_value (snd x2))
      as (cbor_match_map_entry_bounded r cbor_match (pm /. 2.0R) x1 x2);
  } else {
    cbor_match_map_entry_bounded_eq_false r cbor_match pm x1 x2;
    rewrite (cbor_match_map_entry_bounded r cbor_match pm x1 x2) as (pure False);
    rewrite emp as (cbor_match_map_entry_bounded r cbor_match (pm /. 2.0R) x1 x2 ** cbor_match_map_entry_bounded r cbor_match (pm /. 2.0R) x1 x2);
  }
}

ghost
fn cbor_match_mixed_list_map_share
  (p: perm)
  (c: cbor_mixed_list_map)
  (r: raw_data_item { Map? r })
  (cbor_match: perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop)
  (cbor_match_share: (
    (p': perm) ->
    (c': cbor_raw) ->
    (v': raw_data_item { v' << r }) ->
    stt_ghost unit emp_inames (cbor_match p' c' v') (fun _ -> cbor_match (p' /. 2.0R) c' v' ** cbor_match (p' /. 2.0R) c' v')
  ))
requires
  cbor_match_mixed_list_map p c r cbor_match
ensures
  cbor_match_mixed_list_map (p /. 2.0R) c r cbor_match ** cbor_match_mixed_list_map (p /. 2.0R) c r cbor_match
{
  unfold (cbor_match_mixed_list_map p c r cbor_match);
  I.mixed_list_match_share (cbor_match_map_entry_bounded r cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) (p *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) (vmatch_share_map r cbor_match cbor_match_share);
  perm_half_mul p c.cbor_map_gen_perm;
  rewrite (I.mixed_list_match (cbor_match_map_entry_bounded r cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) ((p *. c.cbor_map_gen_perm) /. 2.0R) c.cbor_map_gen_ptr (Map?.v r))
       as (I.mixed_list_match (cbor_match_map_entry_bounded r cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) ((p /. 2.0R) *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r));
  rewrite (I.mixed_list_match (cbor_match_map_entry_bounded r cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) ((p *. c.cbor_map_gen_perm) /. 2.0R) c.cbor_map_gen_ptr (Map?.v r))
       as (I.mixed_list_match (cbor_match_map_entry_bounded r cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) ((p /. 2.0R) *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r));
  fold (cbor_match_mixed_list_map (p /. 2.0R) c r cbor_match);
  fold (cbor_match_mixed_list_map (p /. 2.0R) c r cbor_match);
}

(* ---- gather ---- *)

ghost
fn cbor_match_mixed_list_array_gather
  (p1 p2: perm)
  (c: cbor_mixed_list_array)
  (r1: raw_data_item { Array? r1 })
  (r2: raw_data_item { Array? r2 })
  (cbor_match: perm -> cbor_raw -> raw_data_item -> slprop)
  (cbor_match_gather: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (v1': raw_data_item { v1' << r1 }) ->
    (p2': perm) ->
    (v2': raw_data_item) ->
    stt_ghost unit emp_inames (cbor_match p1' c' v1' ** cbor_match p2' c' v2') (fun _ -> cbor_match (p1' +. p2') c' v1' ** pure (eq2 #raw_data_item v1' v2'))
  ))
requires
  cbor_match_mixed_list_array p1 c r1 cbor_match ** cbor_match_mixed_list_array p2 c r2 cbor_match
ensures
  cbor_match_mixed_list_array (p1 +. p2) c r1 cbor_match ** pure (eq2 #(x: raw_data_item { Array? x \/ Array? x }) r1 r2)
{
  unfold (cbor_match_mixed_list_array p1 c r1 cbor_match);
  unfold (cbor_match_mixed_list_array p2 c r2 cbor_match);
  ghost
  fn prf1
    (x: cbor_raw)
    (pm0: perm)
    (y: raw_data_item { List.Tot.memP y (Array?.v r1) })
  requires cbor_match_bounded r1 cbor_match pm0 x y
  ensures cbor_match pm0 x y
  {
    array_elem_precedes r1 y;
    cbor_match_bounded_eq r1 cbor_match pm0 x y;
    rewrite (cbor_match_bounded r1 cbor_match pm0 x y) as (cbor_match pm0 x y);
  };
  I.mixed_list_match_weaken (cbor_match_bounded r1 cbor_match) cbor_match parse_raw_data_item (p1 *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r1) prf1;
  ghost
  fn prf2
    (x: cbor_raw)
    (pm0: perm)
    (y: raw_data_item { List.Tot.memP y (Array?.v r2) })
  requires cbor_match_bounded r2 cbor_match pm0 x y
  ensures cbor_match pm0 x y
  {
    array_elem_precedes r2 y;
    cbor_match_bounded_eq r2 cbor_match pm0 x y;
    rewrite (cbor_match_bounded r2 cbor_match pm0 x y) as (cbor_match pm0 x y);
  };
  I.mixed_list_match_weaken (cbor_match_bounded r2 cbor_match) cbor_match parse_raw_data_item (p2 *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r2) prf2;
  ghost
  fn vmatch_gather
    (x1: cbor_raw)
    (#pm0: perm)
    (#x2: raw_data_item)
    (#pm0': perm)
    (x2': raw_data_item { List.Tot.memP x2' (Array?.v r1) })
  requires cbor_match pm0 x1 x2 ** cbor_match pm0' x1 x2'
  ensures cbor_match (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
  {
    array_elem_precedes r1 x2';
    cbor_match_gather pm0' x1 x2' pm0 x2;
    rewrite (cbor_match (pm0' +. pm0) x1 x2') as (cbor_match (pm0 +. pm0') x1 x2);
  };
  I.mixed_list_match_gather_bound cbor_match parse_raw_data_item (p2 *. c.cbor_array_gen_perm) (p1 *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r2) (Array?.v r1) vmatch_gather;
  array_v_len_eq r1 r2;
  perm_add_mul p1 p2 c.cbor_array_gen_perm;
  rewrite (I.mixed_list_match cbor_match parse_raw_data_item ((p2 *. c.cbor_array_gen_perm) +. (p1 *. c.cbor_array_gen_perm)) c.cbor_array_gen_ptr (Array?.v r2))
       as (I.mixed_list_match cbor_match parse_raw_data_item ((p1 +. p2) *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r1));
  ghost
  fn prf3
    (x: cbor_raw)
    (pm0: perm)
    (y: raw_data_item { List.Tot.memP y (Array?.v r1) })
  requires cbor_match pm0 x y
  ensures cbor_match_bounded r1 cbor_match pm0 x y
  {
    array_elem_precedes r1 y;
    cbor_match_bounded_eq r1 cbor_match pm0 x y;
    rewrite (cbor_match pm0 x y) as (cbor_match_bounded r1 cbor_match pm0 x y);
  };
  I.mixed_list_match_weaken cbor_match (cbor_match_bounded r1 cbor_match) parse_raw_data_item ((p1 +. p2) *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r1) prf3;
  fold (cbor_match_mixed_list_array (p1 +. p2) c r1 cbor_match);
}

ghost
fn cbor_match_mixed_list_map_gather
  (p1 p2: perm)
  (c: cbor_mixed_list_map)
  (r1: raw_data_item { Map? r1 })
  (r2: raw_data_item { Map? r2 })
  (cbor_match: perm -> cbor_raw -> raw_data_item -> slprop)
  (cbor_match_gather: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (v1': raw_data_item { v1' << r1 }) ->
    (p2': perm) ->
    (v2': raw_data_item) ->
    stt_ghost unit emp_inames (cbor_match p1' c' v1' ** cbor_match p2' c' v2') (fun _ -> cbor_match (p1' +. p2') c' v1' ** pure (eq2 #raw_data_item v1' v2'))
  ))
requires
  cbor_match_mixed_list_map p1 c r1 cbor_match ** cbor_match_mixed_list_map p2 c r2 cbor_match
ensures
  cbor_match_mixed_list_map (p1 +. p2) c r1 cbor_match ** pure (eq2 #(x: raw_data_item { Map? x \/ Map? x }) r1 r2)
{
  unfold (cbor_match_mixed_list_map p1 c r1 cbor_match);
  unfold (cbor_match_mixed_list_map p2 c r2 cbor_match);
  ghost
  fn prf1
    (x: cbor_map_entry)
    (pm0: perm)
    (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r1) })
  requires cbor_match_map_entry_bounded r1 cbor_match pm0 x y
  ensures cbor_match_map_entry_unbounded cbor_match pm0 x y
  {
    map_elem_precedes r1 y;
    cbor_match_map_entry_bounded_eq r1 cbor_match pm0 x y;
    rewrite (cbor_match_map_entry_bounded r1 cbor_match pm0 x y) as (cbor_match_map_entry_unbounded cbor_match pm0 x y);
  };
  I.mixed_list_match_weaken (cbor_match_map_entry_bounded r1 cbor_match) (cbor_match_map_entry_unbounded cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) (p1 *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r1) prf1;
  ghost
  fn prf2
    (x: cbor_map_entry)
    (pm0: perm)
    (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r2) })
  requires cbor_match_map_entry_bounded r2 cbor_match pm0 x y
  ensures cbor_match_map_entry_unbounded cbor_match pm0 x y
  {
    map_elem_precedes r2 y;
    cbor_match_map_entry_bounded_eq r2 cbor_match pm0 x y;
    rewrite (cbor_match_map_entry_bounded r2 cbor_match pm0 x y) as (cbor_match_map_entry_unbounded cbor_match pm0 x y);
  };
  I.mixed_list_match_weaken (cbor_match_map_entry_bounded r2 cbor_match) (cbor_match_map_entry_unbounded cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) (p2 *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r2) prf2;
  ghost
  fn vmatch_gather
    (x1: cbor_map_entry)
    (#pm0: perm)
    (#x2: (raw_data_item & raw_data_item))
    (#pm0': perm)
    (x2': (raw_data_item & raw_data_item) { List.Tot.memP x2' (Map?.v r1) })
  requires cbor_match_map_entry_unbounded cbor_match pm0 x1 x2 ** cbor_match_map_entry_unbounded cbor_match pm0' x1 x2'
  ensures cbor_match_map_entry_unbounded cbor_match (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
  {
    unfold (cbor_match_map_entry_unbounded cbor_match pm0 x1 x2);
    unfold (cbor_match_map_entry_unbounded cbor_match pm0' x1 x2');
    map_elem_precedes r1 x2';
    cbor_match_gather pm0' x1.cbor_map_entry_key (fst x2') pm0 (fst x2);
    cbor_match_gather pm0' x1.cbor_map_entry_value (snd x2') pm0 (snd x2);
    rewrite (cbor_match (pm0' +. pm0) x1.cbor_map_entry_key (fst x2')) as (cbor_match (pm0 +. pm0') x1.cbor_map_entry_key (fst x2));
    rewrite (cbor_match (pm0' +. pm0) x1.cbor_map_entry_value (snd x2')) as (cbor_match (pm0 +. pm0') x1.cbor_map_entry_value (snd x2));
    fold (cbor_match_map_entry_unbounded cbor_match (pm0 +. pm0') x1 x2);
  };
  I.mixed_list_match_gather_bound (cbor_match_map_entry_unbounded cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) (p2 *. c.cbor_map_gen_perm) (p1 *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r2) (Map?.v r1) vmatch_gather;
  map_v_len_eq r1 r2;
  perm_add_mul p1 p2 c.cbor_map_gen_perm;
  rewrite (I.mixed_list_match (cbor_match_map_entry_unbounded cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) ((p2 *. c.cbor_map_gen_perm) +. (p1 *. c.cbor_map_gen_perm)) c.cbor_map_gen_ptr (Map?.v r2))
       as (I.mixed_list_match (cbor_match_map_entry_unbounded cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) ((p1 +. p2) *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r1));
  ghost
  fn prf3
    (x: cbor_map_entry)
    (pm0: perm)
    (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r1) })
  requires cbor_match_map_entry_unbounded cbor_match pm0 x y
  ensures cbor_match_map_entry_bounded r1 cbor_match pm0 x y
  {
    map_elem_precedes r1 y;
    cbor_match_map_entry_bounded_eq r1 cbor_match pm0 x y;
    rewrite (cbor_match_map_entry_unbounded cbor_match pm0 x y) as (cbor_match_map_entry_bounded r1 cbor_match pm0 x y);
  };
  I.mixed_list_match_weaken (cbor_match_map_entry_unbounded cbor_match) (cbor_match_map_entry_bounded r1 cbor_match) (LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item) ((p1 +. p2) *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r1) prf3;
  fold (cbor_match_mixed_list_map (p1 +. p2) c r1 cbor_match);
}
