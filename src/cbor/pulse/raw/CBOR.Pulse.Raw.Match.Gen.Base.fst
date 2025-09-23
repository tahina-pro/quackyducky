module CBOR.Pulse.Raw.Match.Gen.Base
#lang-pulse
open CBOR.Pulse.Raw.Util
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util

// not reusing raw_uint64, for packing purposes
inline_for_extraction
noeq
type cbor_int = {
  cbor_int_type: major_type_uint64_or_neg_int64;
  cbor_int_size: integer_size;
  cbor_int_value: (value: U64.t { raw_uint64_size_prop cbor_int_size value });
}

let cbor_match_int
  (c: cbor_int)
  (r: raw_data_item)
: Tot slprop
= pure (
    r == Int64 c.cbor_int_type ({ size = c.cbor_int_size; value = c.cbor_int_value })
  )

let cbor_match_simple
  (c: simple_value)
  (r: raw_data_item)
: Tot slprop
= pure (
    r == Simple c
  )

[@@no_auto_projectors]
noeq
type cbor_tagged
  ([@@@strictly_positive] cbor_raw: Type0)
: Type0
 = {
  cbor_tagged_tag: raw_uint64;
  cbor_tagged_ptr: ref cbor_raw;
  cbor_tagged_ref_perm: perm;
  cbor_tagged_payload_perm: perm;
}

let cbor_match_tagged
  (#cbor_raw: Type0)
  (c: cbor_tagged cbor_raw)
  (p: perm)
  (r: raw_data_item { Tagged? r })
  (cbor_match: (perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop))
: Tot slprop
= exists* c' . R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
    cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r) **
    pure (c.cbor_tagged_tag == Tagged?.tag r)

noeq
type cbor_raw
  (cbor_string: Type0)
  (cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (cbor_serialized: Type0)
: Type0
=
| CBOR_Case_Int: v: cbor_int -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized
| CBOR_Case_Simple: v: simple_value -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized
| CBOR_Case_String: v: cbor_string -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized
| CBOR_Case_Tagged: v: cbor_tagged (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized
| CBOR_Case_Array: v: cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized
| CBOR_Case_Map: v: cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized
| CBOR_Case_Serialized_Tagged: v: cbor_serialized -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized
| CBOR_Case_Serialized_Array: v: cbor_serialized -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized
| CBOR_Case_Serialized_Map: v: cbor_serialized -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized

and cbor_raw_map_entry
  (cbor_string: Type0)
  (cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (cbor_serialized: Type0)
= {
  cbor_raw_map_entry_key_perm: perm;
  cbor_raw_map_entry_key: cbor_raw cbor_string cbor_array cbor_map cbor_serialized;
  cbor_raw_map_entry_value_perm: perm;
  cbor_raw_map_entry_value: cbor_raw cbor_string cbor_array cbor_map cbor_serialized;
}

let rec cbor_match
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (p: perm)
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (r: raw_data_item)
: Tot slprop
  (decreases r)
= match c, r with
  | CBOR_Case_Array v, Array _ _ -> cbor_match_array v p r (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  | CBOR_Case_Map v, Map _ _ -> cbor_match_map0 v p r (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  | CBOR_Case_Simple v, Simple _ -> cbor_match_simple v r
  | CBOR_Case_Int v, Int64 _ _ -> cbor_match_int v r
  | CBOR_Case_String v, String _ _ _ -> cbor_match_string v p r
  | CBOR_Case_Tagged v, Tagged _ _ -> cbor_match_tagged v p r (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  | CBOR_Case_Serialized_Array v, Array _ _ -> cbor_match_serialized_array v p r
  | CBOR_Case_Serialized_Map v, Map _ _ -> cbor_match_serialized_map v p r
  | CBOR_Case_Serialized_Tagged v, Tagged _ _ -> cbor_match_serialized_tagged v p r
  | _ -> pure False

and cbor_match_map_entry
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (p: perm)
  (c: cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized)
  (r: (raw_data_item & raw_data_item))
: Tot slprop
  (decreases r)
= cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged (p *. c.cbor_raw_map_entry_key_perm) c.cbor_raw_map_entry_key (fst r) **
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged (p *. c.cbor_raw_map_entry_value_perm) c.cbor_raw_map_entry_value (snd r)

let cbor_match_cases_pred
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (r: raw_data_item)
: Tot bool
= 
    match c, r with
    | CBOR_Case_Array _, Array _ _
    | CBOR_Case_Map _, Map _ _
    | CBOR_Case_Simple _, Simple _
    | CBOR_Case_Int _, Int64 _ _
    | CBOR_Case_String _, String _ _ _
    | CBOR_Case_Tagged _, Tagged _ _
    | CBOR_Case_Serialized_Array _, Array _ _
    | CBOR_Case_Serialized_Map _, Map _ _
    | CBOR_Case_Serialized_Tagged _, Tagged _ _ ->
      true
    | _ -> false

ghost
fn cbor_match_cases
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#pm: perm)
  (#r: raw_data_item)
  requires cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm c r
  ensures cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm c r ** pure (cbor_match_cases_pred c r)
{
  if cbor_match_cases_pred c r {
    ()
  } else {
    rewrite (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm c r) as (pure False);
    rewrite emp as (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm c r)
  }
}

ghost
fn cbor_match_int_intro_trade_aux
  (q: slprop)
  (res: cbor_int)
  (v: raw_data_item)
  requires
    q
  ensures
    trade (cbor_match_int res v) q
{ 
  intro
    (Trade.trade
      (cbor_match_int res v)
      q
    )
    #q
    fn _
  {
    unfold (cbor_match_int res v)
  };
}

inline_for_extraction
fn cbor_match_int_intro_aux
  (typ: major_type_uint64_or_neg_int64)
  (i: raw_uint64)
  requires emp
  returns res: cbor_int
  ensures cbor_match_int res (Int64 typ i)
{
  let res = { cbor_int_type = typ; cbor_int_size = i.size; cbor_int_value = i.value };
  fold (cbor_match_int res (Int64 typ i));
  res
}

inline_for_extraction
fn cbor_match_int_intro
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (typ: major_type_uint64_or_neg_int64)
  (i: raw_uint64)
  requires emp
  returns res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Int64 typ i)
{
  let resi = cbor_match_int_intro_aux typ i;
  let res : cbor_raw cbor_string cbor_array cbor_map cbor_serialized = CBOR_Case_Int resi;
  fold (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R (CBOR_Case_Int resi) (Int64 typ i));
  res
}

inline_for_extraction
fn cbor_match_int_intro_trade
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (q: slprop)
  (typ: major_type_uint64_or_neg_int64)
  (i: raw_uint64)
  requires q
  returns res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Int64 typ i) ** trade (cbor_match  cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Int64 typ i)) q
{
  let resi = cbor_match_int_intro_aux typ i;
  cbor_match_int_intro_trade_aux q resi (Int64 typ i);
  let res : cbor_raw cbor_string cbor_array cbor_map cbor_serialized = CBOR_Case_Int resi;
  Trade.rewrite_with_trade (cbor_match_int resi (Int64 typ i)) (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Int64 typ i));
  Trade.trans _ _ q;
  res
}

inline_for_extraction
fn cbor_match_int_elim_type
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Int64? v)
returns res: major_type_uint64_or_neg_int64
ensures
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Int64? v /\ res == Int64?.typ v)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  let CBOR_Case_Int c' = c;
  Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_int c' v);
  unfold (cbor_match_int c' v);
  fold (cbor_match_int c' v);
  Trade.elim _ _;
  c'.cbor_int_type
}

inline_for_extraction
fn cbor_match_int_elim_value
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Int64? v)
returns res: raw_uint64
ensures
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Int64? v /\ res == Int64?.v v)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  let CBOR_Case_Int c' = c;
  Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_int c' v);
  unfold (cbor_match_int c' v);
  fold (cbor_match_int c' v);
  Trade.elim _ _;
  let res = {
    size = c'.cbor_int_size;
    value = c'.cbor_int_value;
  };
  res
}

ghost
fn cbor_match_int_free
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Int64? v)
ensures
  emp
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  let CBOR_Case_Int c' = c;
  rewrite (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) as (cbor_match_int c' v);
  unfold (cbor_match_int c' v)
}

ghost
fn cbor_match_simple_intro_trade_aux
  (q: slprop)
  (res: simple_value)
  (v: raw_data_item)
  requires
    q
  ensures
    trade (cbor_match_simple res v) q
{ 
  intro
    (Trade.trade
      (cbor_match_simple res v)
      q
    )
    #q
    fn _
  {
    unfold (cbor_match_simple res v)
  };
}

inline_for_extraction
fn cbor_match_simple_intro
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (i: simple_value)
  requires emp
  returns res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Simple i)
{
  fold (cbor_match_simple i (Simple i));
  let res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized = CBOR_Case_Simple i;
  fold (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R (CBOR_Case_Simple i) (Simple i));
  res
}

inline_for_extraction
fn cbor_match_simple_intro_trade
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (q: slprop)
  (i: simple_value)
  requires q
  returns res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Simple i) ** trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Simple i)) q
{
  cbor_match_simple_intro_trade_aux q i (Simple i);
  fold (cbor_match_simple i (Simple i));
  let res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized = CBOR_Case_Simple i;
  Trade.rewrite_with_trade (cbor_match_simple i (Simple i)) (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Simple i));
  Trade.trans _ _ q;
  res
}

inline_for_extraction
fn cbor_match_simple_elim
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Simple? v)
returns res: simple_value
ensures
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (v == Simple res)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  let CBOR_Case_Simple res = c;
  Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_simple res v);
  unfold (cbor_match_simple res v);
  fold (cbor_match_simple res v);
  Trade.elim _ _;
  res
}

ghost
fn cbor_match_simple_free
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Simple? v)
ensures
  emp
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  let CBOR_Case_Simple res = c;
  rewrite (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) as (cbor_match_simple res v);
  unfold (cbor_match_simple res v)
}

module S = Pulse.Lib.Slice

inline_for_extraction
let cbor_match_string_intro_aux_t
  (#cbor_string: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
=
  (typ: major_type_byte_string_or_text_string) ->
  (len: raw_uint64) ->
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_string
  (requires
    pts_to input #pm v ** pure (
      (typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) /\
      Seq.length v == U64.v len.value
    )
  )
  (ensures fun c -> exists* r .
    cbor_match_string c 1.0R r **
    trade (cbor_match_string c 1.0R r) (pts_to input #pm v) **
    pure (
      Seq.length v == U64.v len.value /\
      (typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) /\
      r == String typ len (Ghost.reveal v)
    )
  )

inline_for_extraction
fn cbor_match_string_intro
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (#cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_string_intro_aux: cbor_match_string_intro_aux_t cbor_match_string)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (typ: major_type_byte_string_or_text_string)
  (len: raw_uint64)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  requires
    pts_to input #pm v ** pure (
      (typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) /\
      Seq.length v == U64.v len.value
    )
  returns c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures exists* r .
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R c r **
    trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R c r) (pts_to input #pm v) **
    pure (
      Seq.length v == U64.v len.value /\
      (typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) /\
      r == String typ len (Ghost.reveal v)
    )
{
  S.pts_to_len input;
  let ress = cbor_match_string_intro_aux typ len input;
  with r . assert (cbor_match_string ress 1.0R (Ghost.reveal r));
  let res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized = CBOR_Case_String ress;
  Trade.rewrite_with_trade
    (cbor_match_string ress 1.0R r)
    (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res r);
  Trade.trans _ _ (pts_to input #pm v);
  res
}

inline_for_extraction
let cbor_match_string_elim_type_aux_t
  (#cbor_string: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
=
  (c: cbor_string) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item {String? v}) ->
  stt major_type_byte_string_or_text_string
  (requires
    cbor_match_string c p v
  )
  (ensures fun res ->
    cbor_match_string c p v ** pure (res == String?.typ v)
  )

inline_for_extraction
fn cbor_match_string_elim_type
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (#cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_string_elim_type_aux: cbor_match_string_elim_type_aux_t cbor_match_string)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (String? v)
returns res: major_type_byte_string_or_text_string
ensures
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (String? v /\ res == String?.typ v)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  let CBOR_Case_String c' = c;
  Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_string c' p v);
  let res = cbor_match_string_elim_type_aux c';
  Trade.elim _ _;
  res
}

inline_for_extraction
let cbor_match_string_elim_length_aux_t
  (#cbor_string: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
=
  (c: cbor_string) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item {String? v}) ->
  stt raw_uint64
  (requires
    cbor_match_string c p v
  )
  (ensures fun res ->
    cbor_match_string c p v ** pure (res == String?.len v)
  )

inline_for_extraction
fn cbor_match_string_elim_length
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (#cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_string_elim_length_aux: cbor_match_string_elim_length_aux_t cbor_match_string)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (String? v)
returns res: raw_uint64
ensures
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (String? v /\ res == String?.len v)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  let CBOR_Case_String c' = c;
  Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_string c' p v);
  let res = cbor_match_string_elim_length_aux c';
  Trade.elim _ _;
  res
}

inline_for_extraction
let cbor_match_string_elim_payload_aux_t
  (#cbor_string: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
=
  (c: cbor_string) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item {String? v}) ->
  stt (S.slice U8.t)
  (requires
    cbor_match_string c p v
  )
  (ensures fun res -> exists* p' v' .
    S.pts_to res #p' v' **
    trade
      (pts_to res #p' v')
      (cbor_match_string c p v) **
    pure (v' == String?.v v)
  )

inline_for_extraction
fn cbor_match_string_elim_payload
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (#cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_string_elim_payload_aux: cbor_match_string_elim_payload_aux_t cbor_match_string)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (String? v)
returns res: S.slice U8.t
ensures exists* p' (v': Seq.seq U8.t) .
  pts_to res #p' v' **
  trade (pts_to res #p' v') (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) **
  pure (String? v /\ v' == String?.v v)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  let CBOR_Case_String c' = c;
  Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_string c' p v);
  let res = cbor_match_string_elim_payload_aux c';
  Trade.trans _ (cbor_match_string _ _ _) _;
  res
}

let cbor_match_eq_tagged
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (pm: perm)
  (ct: cbor_tagged (cbor_raw cbor_string cbor_array cbor_map cbor_serialized))
  (r: raw_data_item)
: Lemma
  (requires (Tagged? r))
  (ensures 
    (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm (CBOR_Case_Tagged ct) r ==
    cbor_match_tagged ct pm r (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  ))
=
  let Tagged tag v = r in
  assert_norm (
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm (CBOR_Case_Tagged ct) (Tagged tag v) ==
      cbor_match_tagged ct pm (Tagged tag v) (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  )

inline_for_extraction
let cbor_match_serialized_tagged_get_tag_t
  (#cbor_serialized: Type0)
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
=
  (c: cbor_serialized) ->
  (#p: perm) ->
  (#r: Ghost.erased raw_data_item { Tagged? r }) ->
  stt raw_uint64
  (requires cbor_match_serialized_tagged c p r)
  (ensures fun res -> cbor_match_serialized_tagged c p r **
    pure (Tagged? r /\ res == Tagged?.tag r)
  )

inline_for_extraction
fn cbor_match_tagged_get_tag
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (#cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (cbor_match_serialized_tagged_get_tag: cbor_match_serialized_tagged_get_tag_t cbor_match_serialized_tagged)
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Tagged? v)
returns res: raw_uint64
ensures
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v ** pure (Tagged? v /\ res == Tagged?.tag v)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  match c {
    CBOR_Case_Tagged c' -> {
      cbor_match_eq_tagged cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c' v;
      Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_tagged c' p v (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
      unfold (cbor_match_tagged c' p v (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
      fold (cbor_match_tagged c' p v (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
      Trade.elim _ _;
      c'.cbor_tagged_tag
    }
    CBOR_Case_Serialized_Tagged c' -> {
      Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_serialized_tagged c' p v);
      let res = cbor_match_serialized_tagged_get_tag c';
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction
let cbor_match_serialized_tagged_get_payload_t
  (#cbor_serialized: Type0)
  (#cbor_raw: Type0)
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (cbor_match: (perm -> cbor_raw -> (raw_data_item) -> slprop))
=
  (c: cbor_serialized) ->
  (#p: perm) ->
  (#r: Ghost.erased raw_data_item { Tagged? r }) ->
  stt cbor_raw
  (requires cbor_match_serialized_tagged c p r)
  (ensures fun res -> exists* p' v .
    cbor_match p' res v **
    trade
      (cbor_match p' res v)
      (cbor_match_serialized_tagged c p r) **
    pure (Tagged? r /\ v == Tagged?.v r)
  )

ghost
fn cbor_match_tagged_elim_tagged
  (#cbor_raw: Type0)
  (cbor_match: (perm -> cbor_raw -> (raw_data_item) -> slprop))
  (c: cbor_tagged cbor_raw)
  (p: perm)
  (r: raw_data_item { Tagged? r })
  requires
    cbor_match_tagged c p r cbor_match
  ensures exists* c' . R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
    cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r) **
    trade
      (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
        cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r))
      (cbor_match_tagged c p r cbor_match)
{
  unfold (cbor_match_tagged c p r cbor_match);
  with c' . assert (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
    cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r));
  intro
    (Trade.trade
      (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
        cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r)
      )
      (cbor_match_tagged c p r cbor_match)
    )
    #emp
    fn _
  {
    fold (cbor_match_tagged c p r cbor_match)
  };
}

inline_for_extraction
fn cbor_match_tagged_elim
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (#cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (cbor_match_serialized_tagged_get_payload: cbor_match_serialized_tagged_get_payload_t cbor_match_serialized_tagged (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (p: perm)
  (r: raw_data_item { Tagged? r })
  requires
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c r
  returns res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures exists* p' v' .
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p' res v' **
    trade
      (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p' res v')
      (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c r) **
    pure (Tagged? r /\ v' == Tagged?.v r)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  match c {
    CBOR_Case_Tagged c' -> {
      cbor_match_eq_tagged cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c' r;
      Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c r) (cbor_match_tagged c' p r (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
      cbor_match_tagged_elim_tagged (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged) c' p r;
      Trade.trans _ _ (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c r);
      let res = ! c'.cbor_tagged_ptr;
      Trade.elim_hyp_l _ _ _;
      res
    }
    CBOR_Case_Serialized_Tagged c' -> {
      Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c r) (cbor_match_serialized_tagged c' p r);
      let res = cbor_match_serialized_tagged_get_payload c';
      Trade.trans _ _ (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c r);
      res
    }
  }
}

inline_for_extraction
fn cbor_match_tagged_intro
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (tag: raw_uint64)
  (pc: R.ref (cbor_raw cbor_string cbor_array cbor_map cbor_serialized))
  (#pr: perm)
  (#c: Ghost.erased (cbor_raw cbor_string cbor_array cbor_map cbor_serialized))
  (#pm: perm)
  (#r: Ghost.erased raw_data_item)
  requires R.pts_to pc #pr c ** cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm c r
  returns res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Tagged tag r) **
    trade
      (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Tagged tag r))
      (R.pts_to pc #pr c ** cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm c r)
{
  let res' = {
    cbor_tagged_tag = tag;
    cbor_tagged_ptr = pc;
    cbor_tagged_ref_perm = pr /. 2.0R;
    cbor_tagged_payload_perm = pm;
  };
  R.share pc;
  rewrite (R.pts_to pc #(pr /. 2.0R) c)
    as (R.pts_to res'.cbor_tagged_ptr #res'.cbor_tagged_ref_perm c);
  fold (cbor_match_tagged res' 1.0R (Tagged tag r) (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
  intro
    (Trade.trade
      (cbor_match_tagged res' 1.0R (Tagged tag r) (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
      (R.pts_to pc #pr c ** cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm c r)
    )
    #(R.pts_to pc #(pr /. 2.0R) c)
    fn _
  {
    unfold (cbor_match_tagged res' 1.0R (Tagged tag r) (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
    with c' . assert (R.pts_to res'.cbor_tagged_ptr #res'.cbor_tagged_ref_perm c');
    rewrite (R.pts_to res'.cbor_tagged_ptr #res'.cbor_tagged_ref_perm c')
      as (R.pts_to pc #(pr /. 2.0R) c');
    R.gather pc
  };
  cbor_match_eq_tagged cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res' (Tagged tag r);
  let res = CBOR_Case_Tagged res';
  Trade.rewrite_with_trade
    (cbor_match_tagged res' 1.0R (Tagged tag r) (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
    (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Tagged tag r));
  Trade.trans (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Tagged tag r)) _ _;
  res
}

let cbor_match_eq_array
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (pm: perm)
  (ct: cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized))
  (r: raw_data_item)
: Lemma
  (requires (Array? r))
  (ensures 
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm (CBOR_Case_Array ct) r ==
    cbor_match_array ct pm r (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  )
=
  assert_norm (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm (CBOR_Case_Array ct) (Array (Array?.len r) (Array?.v r)) ==
    cbor_match_array ct pm (Array (Array?.len r) (Array?.v r)) (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  )

inline_for_extraction
let cbor_match_serialized_array_get_length_t
  (#cbor_serialized: Type0)
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
=
  (c: cbor_serialized) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item {Array? v}) ->
  stt raw_uint64
  (requires
    cbor_match_serialized_array c p v
  )
  (ensures fun res ->
    cbor_match_serialized_array c p v ** pure (Array? v /\ res == Array?.len v)
  )

inline_for_extraction
let cbor_match_array_get_array_length_t
  (#cbor_array: Type0)
  (#cbor_raw: Type0)
  (cbor_match_array: (cbor_array -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match: (perm -> cbor_raw -> raw_data_item -> slprop))
=
  (c: cbor_array) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item {Array? v}) ->
  stt raw_uint64
  (requires
    cbor_match_array c p v cbor_match
  )
  (ensures fun res ->
    cbor_match_array c p v cbor_match ** pure (Array? v /\ res == Array?.len v)
  )

inline_for_extraction
fn cbor_match_array_get_length
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (#cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_array_get_length: cbor_match_serialized_array_get_length_t cbor_match_serialized_array)
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (cbor_match_array_get_array_length: cbor_match_array_get_array_length_t cbor_match_array (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item {Array? v})
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v
returns res: raw_uint64
ensures
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v **
  pure (Array? v /\ res == Array?.len v)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  match c {
    CBOR_Case_Array c' -> {
      cbor_match_eq_array cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c' v;
      Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_array c' p v (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
      let res = cbor_match_array_get_array_length c';
      Trade.elim _ _;
      res
    }
    CBOR_Case_Serialized_Array c' -> {
      Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_serialized_array c' p v);
      let res = cbor_match_serialized_array_get_length c';
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction
let cbor_match_array_intro_array_t
  (#cbor_array: Type0)
  (#cbor_raw: Type0)
  (cbor_match_array: (cbor_array -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match: (perm -> cbor_raw -> raw_data_item -> slprop))
=
  (len: raw_uint64) ->
  (pc: S.slice cbor_raw) ->
  (#pr: perm) ->
  (#c: Ghost.erased (Seq.seq cbor_raw)) ->
  (#pm: perm) ->
  (#r: Ghost.erased (list raw_data_item)) ->
  stt cbor_array
  (requires pts_to pc #pr c ** PM.seq_list_match c r (cbor_match pm) ** pure (Seq.length c == U64.v len.value))
  (ensures fun res -> exists* r' .
    cbor_match_array res 1.0R (Array len r') cbor_match **
    trade
      (cbor_match_array res 1.0R (Array len r') cbor_match)
      (pts_to pc #pr c ** PM.seq_list_match c r (cbor_match pm)) **
    pure (Ghost.reveal r == r')
  )

inline_for_extraction
fn cbor_match_array_intro
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (cbor_match_array_intro_array: cbor_match_array_intro_array_t cbor_match_array (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
  (len: raw_uint64)
  (pc: S.slice (cbor_raw cbor_string cbor_array cbor_map cbor_serialized))
  (#pr: perm)
  (#c: Ghost.erased (Seq.seq (cbor_raw cbor_string cbor_array cbor_map cbor_serialized)))
  (#pm: perm)
  (#r: Ghost.erased (list raw_data_item))
  requires pts_to pc #pr c ** PM.seq_list_match c r (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm) ** pure (Seq.length c == U64.v len.value)
  returns res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures exists* r' .
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Array len r') **
    trade
      (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Array len r'))
      (pts_to pc #pr c ** PM.seq_list_match c r (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm)) **
    pure (Ghost.reveal r == r')
{
  S.pts_to_len pc;
  PM.seq_list_match_length (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm) c r;
  let res' = cbor_match_array_intro_array len pc;
  with r' .  assert (cbor_match_array res' 1.0R (Array len r') (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
  let res : cbor_raw cbor_string cbor_array cbor_map cbor_serialized = CBOR_Case_Array res';
  cbor_match_eq_array cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res' (Array len r');
  Trade.rewrite_with_trade
    (cbor_match_array res' 1.0R (Array len r') (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
    (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Array len r));
  Trade.trans (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Array len r)) _ _;
  res
}

let cbor_match_eq_map0
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (pm: perm)
  (ct: cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized))
  (r: raw_data_item)
: Lemma
  (requires (Map? r))
  (ensures 
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm (CBOR_Case_Map ct) r ==
    cbor_match_map0 ct pm r (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  )
=
  assert_norm (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm (CBOR_Case_Map ct) (Map (Map?.len r) (Map?.v r)) ==
    cbor_match_map0 ct pm (Map (Map?.len r) (Map?.v r)) (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged)
  )

inline_for_extraction
let cbor_match_serialized_map_get_length_t
  (#cbor_serialized: Type0)
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
=
  (c: cbor_serialized) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item {Map? v}) ->
  stt raw_uint64
  (requires
    cbor_match_serialized_map c p v
  )
  (ensures fun res ->
    cbor_match_serialized_map c p v ** pure (Map? v /\ res == Map?.len v)
  )

inline_for_extraction
let cbor_match_map_get_map_length_t
  (#cbor_map: Type0)
  (#cbor_raw_map_entry: Type0)
  (cbor_match_map0: (cbor_map -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_map_entry: (perm -> cbor_raw_map_entry -> (raw_data_item & raw_data_item) -> slprop))
=
  (c: cbor_map) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item {Map? v}) ->
  stt raw_uint64
  (requires
    cbor_match_map0 c p v cbor_match_map_entry
  )
  (ensures fun res ->
    cbor_match_map0 c p v cbor_match_map_entry ** pure (Map? v /\ res == Map?.len v)
  )

inline_for_extraction
fn cbor_match_map_get_length
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (#cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_map_get_length: cbor_match_serialized_map_get_length_t cbor_match_serialized_map)
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (cbor_match_map_get_map_length: cbor_match_map_get_map_length_t cbor_match_map0 (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
  (c: cbor_raw cbor_string cbor_array cbor_map cbor_serialized)
  (#p: perm)
  (#v: Ghost.erased raw_data_item {Map? v})
requires
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v
returns res: raw_uint64
ensures
  cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v **
  pure (Map? v /\ res == Map?.len v)
{
  cbor_match_cases cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged c;
  match c {
    CBOR_Case_Map c' -> {
      cbor_match_eq_map0 cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c' v;
      Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_map0 c' p v (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
      let res = cbor_match_map_get_map_length c';
      Trade.elim _ _;
      res
    }
    CBOR_Case_Serialized_Map c' -> {
      Trade.rewrite_with_trade (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged p c v) (cbor_match_serialized_map c' p v);
      let res = cbor_match_serialized_map_get_length c';
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction
let cbor_match_map_intro_map_t
  (#cbor_map: Type0)
  (#cbor_raw_map_entry: Type0)
  (cbor_match_map0: (cbor_map -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_map_entry: (perm -> cbor_raw_map_entry -> (raw_data_item & raw_data_item) -> slprop))
=
  (len: raw_uint64) ->
  (pc: S.slice cbor_raw_map_entry) ->
  (#pr: perm) ->
  (#c: Ghost.erased (Seq.seq cbor_raw_map_entry)) ->
  (#pm: perm) ->
  (#r: Ghost.erased (list (raw_data_item & raw_data_item))) ->
  stt cbor_map
  (requires pts_to pc #pr c ** PM.seq_list_match c r (cbor_match_map_entry pm) ** pure (Seq.length c == U64.v len.value))
  (ensures fun res -> exists* r' .
    cbor_match_map0 res 1.0R (Map len r') cbor_match_map_entry **
    trade
      (cbor_match_map0 res 1.0R (Map len r') cbor_match_map_entry)
      (pts_to pc #pr c ** PM.seq_list_match c r (cbor_match_map_entry pm)) **
    pure (Ghost.reveal r == r')
  )

inline_for_extraction
fn cbor_match_map_intro
  (#cbor_string: Type0)
  (#cbor_array: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_map: (([@@@strictly_positive] t: Type0) -> Type0))
  (#cbor_serialized: Type0)
  (cbor_match_string: cbor_string -> perm -> (r: raw_data_item { String? r}) -> slprop)
  (cbor_match_array: (cbor_array (cbor_raw cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item {Array? r}) -> (perm -> cbor_raw cbor_string cbor_array cbor_map cbor_serialized -> (r': raw_data_item {r' << r}) -> slprop) -> slprop))
  (cbor_match_map0: (cbor_map (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized) -> perm -> (r: raw_data_item { Map? r}) -> (perm -> cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized -> (r': (raw_data_item & raw_data_item) {r' << r}) -> slprop) -> slprop))
  (cbor_match_serialized_array: (cbor_serialized -> perm -> (r: raw_data_item { Array? r}) -> slprop))
  (cbor_match_serialized_map: (cbor_serialized -> perm -> (r: raw_data_item { Map? r}) -> slprop))
  (cbor_match_serialized_tagged: (cbor_serialized -> perm -> (r: raw_data_item { Tagged? r}) -> slprop))
  (cbor_match_map_intro_map: cbor_match_map_intro_map_t cbor_match_map0 (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
  (len: raw_uint64)
  (pc: S.slice (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized))
  (#pr: perm)
  (#c: Ghost.erased (Seq.seq (cbor_raw_map_entry cbor_string cbor_array cbor_map cbor_serialized)))
  (#pm: perm)
  (#r: Ghost.erased (list (raw_data_item & raw_data_item)))
  requires pts_to pc #pr c ** PM.seq_list_match c r (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm) ** pure (Seq.length c == U64.v len.value)
  returns res: cbor_raw cbor_string cbor_array cbor_map cbor_serialized
  ensures exists* r' .
    cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Map len r') **
    trade
      #emp_inames // FIXME: WHY WHY WHY?
      (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Map len r'))
      (S.pts_to pc #pr c ** PM.seq_list_match c r (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm)) **
    pure (Ghost.reveal r == r')
{
  S.pts_to_len pc;
  PM.seq_list_match_length (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged pm) c r;
  let res' = cbor_match_map_intro_map len pc;
  with r' .  assert (cbor_match_map0 res' 1.0R (Map len r') (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged));
  let res : cbor_raw cbor_string cbor_array cbor_map cbor_serialized = CBOR_Case_Map res';
  cbor_match_eq_map0 cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res' (Map len r');
  Trade.rewrite_with_trade
    (cbor_match_map0 res' 1.0R (Map len r') (cbor_match_map_entry cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged))
    (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Map len r));
  Trade.trans (cbor_match cbor_match_string cbor_match_array cbor_match_map0 cbor_match_serialized_array cbor_match_serialized_map cbor_match_serialized_tagged 1.0R res (Map len r)) _ _;
  res
}
