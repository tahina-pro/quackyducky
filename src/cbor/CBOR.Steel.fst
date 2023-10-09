module CBOR.Steel
open Steel.ST.OnRange
open Steel.ST.GenElim

module Cbor = CBOR.SteelST
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module LPA = LowParse.SteelST.ArrayPtr
module LPS = LowParse.SteelST.SeqMatch
module R = Steel.ST.Reference
module A = Steel.ST.Array

noeq
type cbor_int = {
  typ: Cbor.major_type_uint64_or_neg_int64;
  value: U64.t;
}

noeq
type cbor_string = {
  typ: Cbor.major_type_byte_string_or_text_string;
  byte_length: U64.t;
  payload: LPS.byte_array;
  footprint: LPA.array LPS.byte;
}

noeq
type cbor_serialized = {
  byte_size: SZ.t;
  payload: LPS.byte_array;
  footprint: LPA.array LPS.byte; // ghost
}

noeq
type cbor_tagged = {
  tag: U64.t;
  payload: R.ref cbor;
}

and cbor_array = {
  count: U64.t;
  payload: A.array cbor;
  footprint: Ghost.erased (Seq.seq cbor);
}

and cbor_map_entry = {
  key: cbor;
  value: cbor;
}

and cbor_map = {
  entry_count: U64.t;
  payload: A.array cbor_map_entry;
}

and cbor =
| CBOR_Case_Int64 of cbor_int
| CBOR_Case_String of cbor_string
| CBOR_Case_Tagged of cbor_tagged
| CBOR_Case_Array of cbor_array
| CBOR_Case_Map of cbor_map
| CBOR_Case_Simple_value of Cbor.simple_value
| CBOR_Case_Serialized of cbor_serialized

let dummy_cbor : cbor = CBOR_Case_Simple_value 0uy

let raw_data_item_match_serialized_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: LPS.byte_array)
  (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Serialized c ->
    c.byte_size == LPA.len (LPS.array_of w) /\
    c.payload == a /\
    c.footprint == LPS.array_of w /\
    w.LPS.contents == v
  | _ -> False

[@@__reduce__]
let raw_data_item_match_serialized0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun (a: LPS.byte_array) -> exists_ (fun (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) ->
    LPS.aparse Cbor.parse_raw_data_item a w `star`
    pure (
      raw_data_item_match_serialized_prop c v a w
    )
  ))

let raw_data_item_match_simple_value_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Simple_value c -> v == Cbor.Simple c
  | _ -> False

[@@__reduce__]
let raw_data_item_match_simple_value0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= pure (raw_data_item_match_simple_value_prop c v)

let raw_data_item_match_int_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Int64 c -> v == Cbor.Int64 c.typ c.value
  | _ -> False

[@@__reduce__]
let raw_data_item_match_int0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= pure (raw_data_item_match_int_prop c v)

let raw_data_item_match_string_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: LPS.byte_array)
  (w: LPA.v LPS.byte)
: Tot prop
= match c with
  | CBOR_Case_String c ->
    U64.v c.byte_length == LPA.length (LPA.array_of w) /\
    v == Cbor.String c.typ (LPA.contents_of w) /\
    c.footprint == LPA.array_of w /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_string0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun a -> exists_ (fun w ->
    LPA.arrayptr a w `star`
    pure (raw_data_item_match_string_prop c v a w)
  ))

let raw_data_item_match_tagged_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: R.ref cbor)
: Tot prop
= match v, c with
  | Cbor.Tagged tag _, CBOR_Case_Tagged c ->
    c.tag == tag /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_tagged0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Tagged? v })
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun a -> exists_ (fun c' ->
    R.pts_to a full_perm c' `star`
    raw_data_item_match c' (Cbor.Tagged?.v v) `star`
    pure (raw_data_item_match_tagged_prop c v a)
  ))

let raw_data_item_match_array_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (s: Seq.seq cbor)
  (a: A.array cbor)
: GTot prop
= match c, v with
  | CBOR_Case_Array c, Cbor.Array l ->
    U64.v c.count == List.Tot.length l /\
    Ghost.reveal c.footprint == s /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_array0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Array? v })
  (raw_data_item_array_match: (Seq.seq cbor -> (v': list Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: A.array cbor) -> exists_ (fun (c': Seq.seq cbor) ->
    A.pts_to a full_perm c' `star`
    raw_data_item_array_match c' (Cbor.Array?.v v) `star`
    pure (
      raw_data_item_match_array_prop c v c' a
    )
  ))

let raw_data_item_match_map_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: A.array cbor_map_entry)
: GTot prop
= match c, v with
  | CBOR_Case_Map c, Cbor.Map l ->
    U64.v c.entry_count == List.Tot.length l /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_map0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Map? v })
  (raw_data_item_map_match: (Seq.seq cbor_map_entry -> (v': list (Cbor.raw_data_item & Cbor.raw_data_item) { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: A.array cbor_map_entry) -> exists_ (fun (c': Seq.seq cbor_map_entry) ->
    A.pts_to a full_perm c' `star`
    raw_data_item_map_match c' (Cbor.Map?.v v) `star`
    pure (
      raw_data_item_match_map_prop c v a
    )
  ))

noextract
let fstp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a1 = fst x

noextract
let sndp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a2 = snd x

[@@__reduce__]
let raw_data_item_map_entry_match1
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v1 }) -> vprop))
: Tot vprop
= raw_data_item_match c1.key (fstp v1) `star`
  raw_data_item_match c1.value (sndp v1)

let raw_data_item_map_entry_match0
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << l }) -> vprop))
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item) { v1 << l })
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 raw_data_item_match

let rec raw_data_item_match
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= match c, v with
  | CBOR_Case_Serialized _, _ -> raw_data_item_match_serialized0 c v
  | CBOR_Case_Simple_value _, Cbor.Simple _ -> raw_data_item_match_simple_value0 c v
  | CBOR_Case_Int64 _, Cbor.Int64 _ _ -> raw_data_item_match_int0 c v
  | CBOR_Case_String _, Cbor.String _ _ -> raw_data_item_match_string0 c v
  | CBOR_Case_Array _, Cbor.Array _ -> raw_data_item_match_array0 c v raw_data_item_array_match
  | CBOR_Case_Map _, Cbor.Map _ -> raw_data_item_match_map0 c v raw_data_item_map_match
  | CBOR_Case_Tagged _, Cbor.Tagged _ _ -> raw_data_item_match_tagged0 c v raw_data_item_match
  | _ -> pure False

and raw_data_item_array_match
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= LPS.seq_list_match c v raw_data_item_match

and raw_data_item_map_match
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= LPS.seq_list_match c v (raw_data_item_map_entry_match0 v raw_data_item_match)

#set-options "--ide_id_info_off"

let raw_data_item_match_get_case
  (#opened: _)
  (#v: Cbor.raw_data_item)
  (c: cbor)
: STGhost unit opened
    (raw_data_item_match c v)
    (fun _ -> raw_data_item_match c v)
    True
    (fun _ -> match c, v with
    | CBOR_Case_Serialized _, _
    | CBOR_Case_Array _, Cbor.Array _
    | CBOR_Case_Int64 _, Cbor.Int64 _ _
    | CBOR_Case_Map _, Cbor.Map _
    | CBOR_Case_Simple_value _, Cbor.Simple _
    | CBOR_Case_String _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> True
    | _ -> False
    )
= match c, v with
    | CBOR_Case_Serialized _, _
    | CBOR_Case_Array _, Cbor.Array _
    | CBOR_Case_Int64 _, Cbor.Int64 _ _
    | CBOR_Case_Map _, Cbor.Map _
    | CBOR_Case_Simple_value _, Cbor.Simple _
    | CBOR_Case_String _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> noop ()
    | _ ->
      rewrite (raw_data_item_match c v) (pure False);
      let _ = gen_elim () in
      rewrite emp (raw_data_item_match c v)

let raw_data_item_match_array_intro
  (#opened: _)
  (#c': Seq.seq cbor)
  (#v': list Cbor.raw_data_item)
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: STGhostT unit opened
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v')
    (fun _ ->
      raw_data_item_match
        (CBOR_Case_Array ({
          count = len;
          payload = a;
          footprint = c';
        }))
        (Cbor.Array v')
    )
= noop ();
  rewrite_with_tactic
    (raw_data_item_match_array0
      (CBOR_Case_Array ({
        count = len;
        payload = a;
        footprint = c';
      }))
      (Cbor.Array v')
      raw_data_item_array_match
    )
    (raw_data_item_match _ _)

let raw_data_item_match_array_elim
  (#opened: _)
  (a: cbor_array)
  (v: Cbor.raw_data_item)
: STGhost (squash (Cbor.Array? v)) opened
    (raw_data_item_match (CBOR_Case_Array a) v)
    (fun _ ->
      A.pts_to a.payload full_perm a.footprint `star`
      raw_data_item_array_match a.footprint (Cbor.Array?.v v)
    )
    True
    (fun _ -> U64.v a.count == List.Tot.length (Cbor.Array?.v v))
= raw_data_item_match_get_case _;
  let sq : squash (Cbor.Array? v) = () in
  let Cbor.Array v' = v in
  vpattern_rewrite (raw_data_item_match _) (Cbor.Array v');
  rewrite_with_tactic
    (raw_data_item_match _ _)
    (raw_data_item_match_array0 (CBOR_Case_Array a) (Cbor.Array v') raw_data_item_array_match);
  let _ = gen_elim () in
  rewrite (A.pts_to _ _ _) (A.pts_to a.payload full_perm a.footprint);
  rewrite (raw_data_item_array_match _ _) (raw_data_item_array_match a.footprint (Cbor.Array?.v v));
  sq

let constr_cbor_array
  (#c': Ghost.erased (Seq.seq cbor))
  (#v': Ghost.erased (list Cbor.raw_data_item))
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: ST cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v')
    (fun res ->
      raw_data_item_match res (Cbor.Array v') `star`
      (raw_data_item_match res (Cbor.Array v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_array_match c' v')
      )
    )
    True
    (fun res ->
      res == CBOR_Case_Array ({
        payload = a;
        count = len;
        footprint = c';
      })
    )
= [@@inline_let]
  let ares : cbor_array = {
    count = len;
    payload = a;
    footprint = c';
  }
  in
  [@@inline_let]
  let res = CBOR_Case_Array ares in
  raw_data_item_match_array_intro a len;
  rewrite (raw_data_item_match _ _) (raw_data_item_match res (Cbor.Array v'));
  intro_implies
    (raw_data_item_match res (Cbor.Array v'))
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v'
    )
    emp
    (fun _ ->
      rewrite (raw_data_item_match _ _) (raw_data_item_match (CBOR_Case_Array ares) (Cbor.Array v'));
      let _ = raw_data_item_match_array_elim _ _ in
      rewrite (A.pts_to _ _ _) (A.pts_to a full_perm c');
      rewrite (raw_data_item_array_match _ _) (raw_data_item_array_match c' v')
    );
  return res

[@@__reduce__]
let maybe_cbor_array
  (v: Cbor.raw_data_item)
: GTot (list Cbor.raw_data_item)
= match v with
  | Cbor.Array l -> l
  | _ -> []

let destr_cbor_array
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_array
    (raw_data_item_match a v)
    (fun res ->
      A.pts_to res.payload full_perm res.footprint `star`
      raw_data_item_array_match res.footprint (maybe_cbor_array v) `star`
      ((A.pts_to res.payload full_perm res.footprint `star`
        raw_data_item_array_match res.footprint (maybe_cbor_array v)) `implies_`
        raw_data_item_match a v
      )
    )
    (CBOR_Case_Array? a)
    (fun res ->
      a == CBOR_Case_Array res /\
      Cbor.Array? v /\
      U64.v res.count == List.Tot.length (Cbor.Array?.v v)
    )
= raw_data_item_match_get_case _;
  let CBOR_Case_Array res = a in
  vpattern_rewrite
    (fun a -> raw_data_item_match a _)
    (CBOR_Case_Array res);
  let _ = raw_data_item_match_array_elim _ _ in
  vpattern_rewrite (raw_data_item_array_match _) (maybe_cbor_array v);
  intro_implies
    (A.pts_to res.payload full_perm res.footprint `star`
      raw_data_item_array_match res.footprint (maybe_cbor_array v))
    (raw_data_item_match a v)
    emp
    (fun _ ->
      raw_data_item_match_array_intro _ res.count;
      rewrite (raw_data_item_match _ _) (raw_data_item_match _ _)
    );
  return res

let read_valid_cbor_from_buffer_with_size_strong
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
  (alen: SZ.t)
: ST cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents `star`
      (raw_data_item_match c' va.contents `implies_` LPS.aparse Cbor.parse_raw_data_item a va)
    )
    (alen == LPA.len (LPS.array_of va))
    (fun c' -> CBOR_Case_Serialized? c')
= [@@inline_let]
  let c_pl : cbor_serialized = ({
    byte_size = alen;
    payload = a;
    footprint = LPS.array_of va;
  })
  in
  [@@inline_let]
  let c' = CBOR_Case_Serialized c_pl in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (raw_data_item_match c' va.contents);
  intro_implies
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (LPS.aparse Cbor.parse_raw_data_item a va)
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite (LPS.aparse Cbor.parse_raw_data_item _ _) (LPS.aparse Cbor.parse_raw_data_item a va) // works thanks to c_pl.footprint
    );
  implies_trans
    (raw_data_item_match c' va.contents)
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (LPS.aparse Cbor.parse_raw_data_item a va);
  return c'

let read_valid_cbor_from_buffer_with_size
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
  (alen: SZ.t)
: ST cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents
    )
    (alen == LPA.len (LPS.array_of va))
    (fun c' -> CBOR_Case_Serialized? c')
= let c' = read_valid_cbor_from_buffer_with_size_strong a alen in
  drop (_ `implies_` _);
  return c'

let read_valid_cbor_from_buffer
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
: STT cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents
    )
= let alen = LPS.get_parsed_size Cbor.jump_raw_data_item a in
  read_valid_cbor_from_buffer_with_size a alen

let read_cbor_int64
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> raw_data_item_match c (Ghost.reveal va))
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.typ c'.value
    )
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_int0 c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_int0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let typ = Cbor.read_major_type cs.payload in
    let value = Cbor.read_int64 cs.payload in
    let c' : cbor_int = {
      typ = typ;
      value = value;
    }
    in
    noop ();
    elim_implies
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_int64
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.typ c'.value
    )
= let c' = read_cbor_int64 c in
  rewrite
    (raw_data_item_match_int0 (CBOR_Case_Int64 c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va));
  intro_implies
    (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> drop (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va)));
  return c'

let constr_cbor_int64
  (ty: Cbor.major_type_uint64_or_neg_int64)
  (value: U64.t)
: ST cbor
    emp
    (fun c -> raw_data_item_match c (Cbor.Int64 ty value))
    True
    (fun c -> c == CBOR_Case_Int64 ({ typ = ty; value = value }))
= [@@inline_let]
  let c = CBOR_Case_Int64 ({ typ = ty; value = value }) in
  noop ();
  rewrite
    (raw_data_item_match_int0 c (Cbor.Int64 ty value))
    (raw_data_item_match c (Cbor.Int64 ty value));
  return c

let read_cbor_simple_value
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match c (Ghost.reveal va)
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' -> Ghost.reveal va == Cbor.Simple c')
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Simple_value c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_simple_value0 c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_simple_value0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let c' = Cbor.read_simple_value cs.payload in
    elim_implies
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_simple_value
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' -> Ghost.reveal va == Cbor.Simple c')
= let c' = read_cbor_simple_value c in
  rewrite
    (raw_data_item_match_simple_value0 (CBOR_Case_Simple_value c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va));
  intro_implies
    (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> drop (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va)));
  return c'

let constr_cbor_simple_value
  (value: Cbor.simple_value)
: ST cbor
    emp
    (fun c -> raw_data_item_match c (Cbor.Simple value))
    True
    (fun c -> c == CBOR_Case_Simple_value value)
= [@@inline_let]
  let c = CBOR_Case_Simple_value value in
  noop ();
  rewrite
    (raw_data_item_match_simple_value0 c (Cbor.Simple value))
    (raw_data_item_match c (Cbor.Simple value));
  return c

let destr_cbor_string'
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_string
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.String? (Ghost.reveal va))
    (fun _ -> True)
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_String c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let va' = vpattern_replace (LPS.aparse Cbor.parse_raw_data_item _) in
    let typ = Cbor.read_major_type cs.payload in
    let len = Cbor.read_argument_as_uint64 cs.payload in
    let payload = Cbor.focus_string cs.payload in
    let _ = gen_elim () in
    let vpl : LPA.v LPS.byte = vpattern_replace (fun vpl -> LPA.arrayptr payload vpl `star` (LPA.arrayptr payload vpl `implies_` LPS.aparse Cbor.parse_raw_data_item cs.payload va')) in
    let c' : cbor_string = {
      typ = typ;
      byte_length = len;
      payload = payload;
      footprint = LPA.array_of vpl;
    }
    in
    noop ();
    intro_implies
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (LPA.arrayptr payload vpl `implies_` LPS.aparse Cbor.parse_raw_data_item cs.payload va')
      (fun _ ->
        let _ = gen_elim () in
        rewrite (LPA.arrayptr _ _) (LPA.arrayptr payload vpl);
        elim_implies
          (LPA.arrayptr payload vpl)
          (LPS.aparse Cbor.parse_raw_data_item cs.payload va');
        noop ()
      );
    rewrite_with_implies
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
    implies_trans
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    implies_trans
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_string
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: STT cbor_string
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' -> exists_ (fun vc' ->
      LPA.arrayptr c'.payload vc' `star`
      (LPA.arrayptr c'.payload vc' `implies_` raw_data_item_match c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.byte_length == Seq.length (LPA.contents_of' vc') /\
        Ghost.reveal va == Cbor.String c'.typ (LPA.contents_of vc')
    )))
= let c' = destr_cbor_string' c in
  rewrite_with_implies
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va));
  let _ = gen_elim () in
  vpattern_rewrite (fun a -> LPA.arrayptr a _) c'.payload;
  let vc' = vpattern_replace (LPA.arrayptr _) in
  intro_implies
    (LPA.arrayptr c'.payload vc')
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
    (pure (raw_data_item_match_string_prop (CBOR_Case_String c') (Ghost.reveal va) c'.payload vc')) // FIXME: WHY WHY WHY?
    (fun _ ->
      noop ()
    );
  implies_trans
    (LPA.arrayptr c'.payload vc')
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
  implies_trans
    (LPA.arrayptr c'.payload vc')
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va));
  intro_exists vc' (fun vc' -> // FIXME: WHY WHY WHY?
    LPA.arrayptr c'.payload vc' `star`
      (LPA.arrayptr c'.payload vc' `implies_` raw_data_item_match c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.byte_length == Seq.length (LPA.contents_of' vc') /\
        Ghost.reveal va == Cbor.String c'.typ (LPA.contents_of vc')
    )  
  );
  return c'

let constr_cbor_string
  (#va: LPA.v LPS.byte)
  (typ: Cbor.major_type_byte_string_or_text_string)
  (a: LPS.byte_array)
  (len: U64.t {
    U64.v len == Seq.length (LPA.contents_of va)
  })
: STT cbor
    (LPA.arrayptr a va)
    (fun c' ->
      raw_data_item_match c' (Cbor.String typ (LPA.contents_of va)) `star`
      (raw_data_item_match c' (Cbor.String typ (LPA.contents_of va)) `implies_`
        LPA.arrayptr a va
      )
    )
= [@@inline_let]
  let c' = CBOR_Case_String ({
    typ = typ;
    payload = a;
    byte_length = len;
    footprint = LPA.array_of va;
  })
  in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_string0 c' (Cbor.String typ (LPA.contents_of va)))
    (raw_data_item_match c' (Cbor.String typ (LPA.contents_of va)));
  intro_implies
    (raw_data_item_match_string0 c' (Cbor.String typ (LPA.contents_of va)))
    (LPA.arrayptr a va)
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite (LPA.arrayptr _ _) (LPA.arrayptr a va)
    );
  implies_trans
    (raw_data_item_match c' (Cbor.String typ (LPA.contents_of va)))
    (raw_data_item_match_string0 c' (Cbor.String typ (LPA.contents_of va)))
    (LPA.arrayptr a va);
  return c'

inline_for_extraction
noextract
let read_cbor_array_payload
  (n0: U64.t)
  (vl0: LPS.v (LowParse.Spec.VCList.parse_nlist_kind (U64.v n0) Cbor.parse_raw_data_item_kind) (LowParse.Spec.VCList.nlist (U64.v n0) Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (#va0: Ghost.erased (Seq.seq cbor))
  (a0: A.array cbor)
: ST (Ghost.erased (Seq.seq cbor))
    (A.pts_to a0 full_perm va0 `star`
      LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0
    )
    (fun res ->
      A.pts_to a0 full_perm res `star`
      raw_data_item_array_match res vl0.contents `star`
      (raw_data_item_array_match res vl0.contents `implies_`
        LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0
      )
    )
    (A.length a0 == U64.v n0 /\
      SZ.fits_u64
    )
    (fun _ -> True)
=
  let n0_as_sz = SZ.uint64_to_sizet n0 in
  let vl = LPS.rewrite_aparse_with_implies l0 (LPS.parse_nlist (SZ.v n0_as_sz) Cbor.parse_raw_data_item) in
  let res = LPS.read_array_payload_from_nlist Cbor.jump_raw_data_item raw_data_item_match (fun a alen -> read_valid_cbor_from_buffer_with_size_strong a alen) n0_as_sz l0 a0 in
  implies_trans
    (LPS.seq_list_match res vl.contents raw_data_item_match)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (SZ.v n0_as_sz) Cbor.parse_raw_data_item) l0 vl)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0);
  rewrite_with_implies_with_tactic
    (LPS.seq_list_match res vl.contents raw_data_item_match)
    (raw_data_item_array_match res vl.contents);
  implies_trans
    (raw_data_item_array_match res vl.contents)
    (LPS.seq_list_match res vl.contents raw_data_item_match)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0);
  rewrite_with_implies
    (raw_data_item_array_match res vl.contents)
    (raw_data_item_array_match res vl0.contents);
  implies_trans
    (raw_data_item_array_match res vl0.contents)
    (raw_data_item_array_match res vl.contents)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0);
  return res

[@@__reduce__]
let read_cbor_array_post_success
  (c: cbor_array)
: Tot vprop
= exists_ (A.pts_to c.payload full_perm) `star`
  pure (
    A.is_full_array c.payload
  )

let read_cbor_array_post
  (input: cbor)
  (res: cbor)
: Tot vprop
= if CBOR_Case_Serialized? input && CBOR_Case_Array? res
  then read_cbor_array_post_success (CBOR_Case_Array?._0 res)
  else emp

inline_for_extraction
noextract
let read_cbor_array_noop
  (#obj: Ghost.erased Cbor.raw_data_item)
  (input: cbor)
: STT cbor
    (raw_data_item_match input obj)
    (fun res ->
      raw_data_item_match res obj `star`
      (raw_data_item_match res obj `implies_`
        (raw_data_item_match input obj `star` read_cbor_array_post input res)
      )
    )
= implies_with_tactic (raw_data_item_match input obj) (raw_data_item_match input obj);
  rewrite emp (read_cbor_array_post input input);
  implies_concl_r (raw_data_item_match input obj) (raw_data_item_match input obj) (read_cbor_array_post input input);
  return input

let array_pts_to_or_null
  (#t: Type)
  (a: A.array t)
  (v: Seq.seq t)
: Tot vprop
= if A.is_null a
  then emp
  else A.pts_to a full_perm v

inline_for_extraction
noextract
let array_alloc
  (#t: Type)
  (init: t)
  (n: SZ.t)
: ST (A.array t)
    emp
    (fun res -> array_pts_to_or_null res (Seq.create (SZ.v n) init))
    True
    (fun res ->
      if A.is_null res
      then True
      else A.length res == SZ.v n /\ A.is_full_array res
    )
= let res = A.alloc init n in
  A.pts_to_not_null res _;
  rewrite
    (A.pts_to res full_perm (Seq.create (SZ.v n) init))
    (array_pts_to_or_null res (Seq.create (SZ.v n) init));
  return res

let read_cbor_array
  (#obj: Ghost.erased Cbor.raw_data_item)
  (input: cbor)
: ST cbor
    (raw_data_item_match input obj)
    (fun res ->
      raw_data_item_match res obj `star`
      (raw_data_item_match res obj `implies_`
        (raw_data_item_match input obj `star` read_cbor_array_post input res)
      )
    )
    (Cbor.Array? obj)
    (fun _ -> True)
= raw_data_item_match_get_case input;
  match input with
  | CBOR_Case_Array _ -> read_cbor_array_noop input
  | CBOR_Case_Serialized s ->
      rewrite_with_implies
        (raw_data_item_match input obj)
        (raw_data_item_match_serialized0 input obj);
      let _ = gen_elim () in
      vpattern_rewrite_with_implies
        (fun a -> LPS.aparse Cbor.parse_raw_data_item a _)
        s.payload;
      intro_implies
        (LPS.aparse Cbor.parse_raw_data_item s.payload _)
        (raw_data_item_match_serialized0 input obj)
        (LPS.aparse Cbor.parse_raw_data_item s.payload _ `implies_`
          LPS.aparse Cbor.parse_raw_data_item _ _
        )
        (fun _ ->
          elim_implies
            (LPS.aparse Cbor.parse_raw_data_item s.payload _)
            (LPS.aparse Cbor.parse_raw_data_item _ _);
          noop ()
        );
      implies_trans
        (LPS.aparse Cbor.parse_raw_data_item s.payload _)
        (raw_data_item_match_serialized0 input obj)
        (raw_data_item_match input obj);
      R.with_local 0uL (fun plen ->
      R.with_local s.payload (fun pa ->
        let w = CBOR.SteelST.Array.focus_array plen pa s.payload in
        implies_trans
          (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.a _)
          (LPS.aparse Cbor.parse_raw_data_item s.payload _)
          (raw_data_item_match input obj);
        let len = R.read plen in
        let _ = A.intro_fits_u64 () in
        let a0 = array_alloc dummy_cbor (SZ.uint64_to_sizet len) in
        if (A.is_null a0)
        then begin
          noop ();
          rewrite
            (array_pts_to_or_null a0 _)
            emp;
          elim_implies
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.a _)
            (raw_data_item_match input obj);
          let res = read_cbor_array_noop input in
          return res
        end else begin
          noop ();
          rewrite
            (array_pts_to_or_null a0 _)
            (A.pts_to a0 full_perm (Seq.create (U64.v len) dummy_cbor));
          let vl = LPS.rewrite_aparse_with_implies
            w.a
            (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item)
          in
          let a = R.read pa in
          vpattern_rewrite_with_implies
            (fun a -> LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            a;
          implies_trans
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) _ _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) _ _);
          implies_trans
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) _ _)
            (raw_data_item_match input obj);
          let va = read_cbor_array_payload len vl a a0 in
          implies_trans
            (raw_data_item_array_match va vl.contents)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (raw_data_item_match input obj);
          let res = constr_cbor_array a0 len in
          vpattern_rewrite
            (fun ar -> raw_data_item_match _ ar `star` (raw_data_item_match _ ar `implies_` (A.pts_to _ _ _ `star` raw_data_item_array_match _ _)))
            obj;
          intro_implies
            (A.pts_to a0 full_perm va `star` raw_data_item_array_match va vl.contents)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res)
            emp
            (fun _ ->
              vpattern_rewrite (fun a0 -> A.pts_to a0 _ _) (CBOR_Case_Array?._0 res).payload;
              rewrite (read_cbor_array_post_success (CBOR_Case_Array?._0 res)) (read_cbor_array_post input res)
            );
          implies_reg_r
            (raw_data_item_array_match va vl.contents)
            (raw_data_item_match input obj)
            (read_cbor_array_post input res);
          implies_trans
            (raw_data_item_match res obj)
            (A.pts_to a0 full_perm va `star` raw_data_item_array_match va vl.contents)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res);
          implies_trans
            (raw_data_item_match res obj)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res)
            (raw_data_item_match input obj `star` read_cbor_array_post input res);
          return res
        end
      ))
