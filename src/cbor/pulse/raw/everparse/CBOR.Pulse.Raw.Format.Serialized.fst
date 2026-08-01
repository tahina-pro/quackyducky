module CBOR.Pulse.Raw.Format.Serialized
friend CBOR.Pulse.Raw.Format.Match
friend CBOR.Pulse.Raw.Format.MixedList
#lang-pulse
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.Iterator
open CBOR.Pulse.Raw.EverParse.Iterator
open CBOR.Pulse.Raw.EverParse.Iterator.Mixed
open Pulse.Lib.Slice open Pulse.Lib.Pervasives open Pulse.Lib.Trade
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Format
open LowParse.Pulse.Combinators
open CBOR.Pulse.Raw.EverParse.Serialized.Base

module Trade = Pulse.Lib.Trade.Util
module Iter = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module PP = LowParse.PulseParse.Base
module ML = CBOR.Pulse.Raw.Format.MixedList
module Perm = CBOR.Pulse.Raw.Match.Perm
module MD = CBOR.Pulse.Raw.Format.Match.Depth

ghost
fn cbor_match_serialized_tagged_elim
  (c: cbor_serialized)
  (pm: perm)
  (r: raw_data_item { Tagged? r })
  requires
    cbor_match_serialized_tagged c pm r
  ensures exists* pm' .
    pts_to_serialized serialize_raw_data_item (to_slice c.cbor_serialized_payload) #pm' (Tagged?.v r) **
    trade
      (pts_to_serialized serialize_raw_data_item (to_slice c.cbor_serialized_payload) #pm' (Tagged?.v r))
      (cbor_match_serialized_tagged c pm r)
{
  unfold (cbor_match_serialized_tagged c pm r);
  unfold (cbor_match_serialized_payload_tagged (to_slice c.cbor_serialized_payload) (pm `perm_mul` c.cbor_serialized_perm) (Tagged?.v r));
  with pm' . assert (pts_to_serialized serialize_raw_data_item (to_slice c.cbor_serialized_payload) #pm' (Tagged?.v r));
  intro
    (Trade.trade
      (pts_to_serialized serialize_raw_data_item (to_slice c.cbor_serialized_payload) #pm' (Tagged?.v r))
      (cbor_match_serialized_tagged c pm r)
    )
    #emp
    fn _
  {
    fold (cbor_match_serialized_payload_tagged (to_slice c.cbor_serialized_payload) (pm `perm_mul` c.cbor_serialized_perm) (Tagged?.v r));
    fold (cbor_match_serialized_tagged c pm r);
  };
}

fn cbor_match_serialized_tagged_get_payload
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Tagged? r })
  requires cbor_match_serialized_tagged c pm r
  returns res: cbor_raw
  ensures
    cbor_match 1.0R res (Tagged?.v r) **
    trade
      (cbor_match 1.0R res (Tagged?.v r))
      (cbor_match_serialized_tagged c pm r) **
    pure (~ (CBOR_Case_Array? res \/ CBOR_Case_Map? res \/ CBOR_Case_Tagged? res \/ CBOR_Case_Array_Gen? res \/ CBOR_Case_Map_Gen? res))
{
  cbor_match_serialized_tagged_elim c pm r;
  let res = cbor_read (to_slice c.cbor_serialized_payload);
  Trade.trans _ _ (cbor_match_serialized_tagged c pm r);
  res
}

module LP = LowParse.Pulse.VCList

ghost
fn cbor_match_serialized_array_elim
  (c: cbor_serialized)
  (pm: perm)
  (r: raw_data_item { Array? r })
  requires
    cbor_match_serialized_array c pm r
  ensures exists* pm' .
    pts_to_serialized (LP.serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item) (to_slice c.cbor_serialized_payload) #pm' (Array?.v r) **
    trade
      (pts_to_serialized (LP.serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item) (to_slice c.cbor_serialized_payload) #pm' (Array?.v r))
      (cbor_match_serialized_array c pm r) **
    pure (c.cbor_serialized_header == Array?.len r)
{
  unfold (cbor_match_serialized_array c pm r);
  unfold (cbor_match_serialized_payload_array (to_slice c.cbor_serialized_payload) (pm `perm_mul` c.cbor_serialized_perm) (Array?.v r));
  with pm' . assert (pts_to_serialized (LP.serialize_nlist (U64.v (Array?.len r).value)  serialize_raw_data_item) (to_slice c.cbor_serialized_payload) #pm' (Array?.v r));
  intro
    (Trade.trade
      (pts_to_serialized (LP.serialize_nlist (U64.v (Array?.len r).value)  serialize_raw_data_item) (to_slice c.cbor_serialized_payload) #pm' (Array?.v r))
      (cbor_match_serialized_array c pm r)
    )
    #emp
    fn _
  {
    fold (cbor_match_serialized_payload_array (to_slice c.cbor_serialized_payload) (pm `perm_mul` c.cbor_serialized_perm) (Array?.v r));
    fold (cbor_match_serialized_array c pm r);
  };
}

fn cbor_serialized_array_item
  (c: cbor_serialized)
  (i: U64.t)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
    (cbor_match_serialized_array c pm r **
      pure (U64.v i < List.Tot.length (Array?.v r))
    )
returns res: cbor_raw
ensures exists* y .
      cbor_match 1.0R res y **
      trade
        (cbor_match 1.0R res y)
        (cbor_match_serialized_array c pm r) **
      pure (
        U64.v i < List.Tot.length (Array?.v r) /\
        List.Tot.index (Array?.v r) (U64.v i) == y
      )
{
  cbor_match_serialized_array_elim c pm r;
  with pm' . assert (pts_to_serialized (LowParse.Pulse.VCList.serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item) (to_slice c.cbor_serialized_payload) #pm' (Array?.v r));
  LowParse.Pulse.Base.pts_to_serialized_length (LowParse.Pulse.VCList.serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item) (to_slice c.cbor_serialized_payload);
  LowParse.Spec.VCList.parse_nlist_kind_low (U64.v (Array?.len r).value) parse_raw_data_item_kind;
  assert_norm (parse_raw_data_item_kind.parser_kind_low == 1);
  SZ.fits_lte (U64.v i) (SZ.v (len (to_slice c.cbor_serialized_payload)));
  let j : SZ.t = SZ.uint64_to_sizet i;
  let elt = LowParse.Pulse.VCList.nlist_nth _ (jump_raw_data_item ()) (U64.v (Array?.len r).value) (to_slice c.cbor_serialized_payload) j;
  Trade.trans _ _ (cbor_match_serialized_array c pm r);
  let res = cbor_read elt;
  Trade.trans _ _ (cbor_match_serialized_array c pm r);
  res
}

let cbor_serialized_array_iterator_match = cbor_raw_serialized_iterator_match serialize_raw_data_item


fn cbor_serialized_array_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
    (cbor_match_serialized_array c pm r)
returns res: cbor_raw_serialized_iterator
ensures
    (exists* p .
      cbor_serialized_array_iterator_match p res (Array?.v r) **
      trade
        (cbor_serialized_array_iterator_match p res (Array?.v r))
        (cbor_match_serialized_array c pm r)
    )
{
  cbor_match_serialized_array_elim c pm r;
  with p . assert (
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (U64.v (Array?.len (Ghost.reveal r)).value)
          serialize_raw_data_item)
      (to_slice c.cbor_serialized_payload)
      #p
      (Array?.v (Ghost.reveal r)))
  );
  let res : cbor_raw_serialized_iterator = {
    s = c.cbor_serialized_payload;
    p = 1.0R;
    glen = Ghost.hide (U64.v (Array?.len r).value);
    len = c.cbor_serialized_header.value;
  };
  Trade.rewrite_with_trade
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (U64.v (Array?.len (Ghost.reveal r)).value)
          serialize_raw_data_item)
      (to_slice c.cbor_serialized_payload)
      #p
      (Array?.v (Ghost.reveal r)))
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (Ghost.reveal res.glen)
          serialize_raw_data_item)
      (to_slice res.s)
      #p
      (Array?.v (Ghost.reveal r))      
  )
  ;
  Trade.trans _ _ (cbor_match_serialized_array c pm r);
  cbor_raw_serialized_iterator_fold serialize_raw_data_item p res (Array?.v r);
  LowParse.Pulse.VCList.trade_trans_nounify _ _ _ (cbor_match_serialized_array c pm r);
  fold (cbor_serialized_array_iterator_match p res (Array?.v r));
  with _pm' . rewrite
    trade (cbor_raw_serialized_iterator_match serialize_raw_data_item
          _pm'
          res
          (Array?.v r))
      (cbor_match_serialized_array c pm r)
    as trade (cbor_serialized_array_iterator_match _pm' res (Array?.v r))
      (cbor_match_serialized_array c pm r)
    ;
  res
}

let cbor_serialized_array_iterator_is_empty = cbor_raw_serialized_iterator_is_empty _

let cbor_serialized_array_iterator_length = cbor_raw_serialized_iterator_length _

inline_for_extraction
fn cbor_serialized_array_iterator_next_cont (_: unit)
: cbor_raw_serialized_iterator_next_cont #cbor_raw #raw_data_item #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item cbor_match
= (x: _) (#pm: _) (#v: _) {
  cbor_read x
}

let cbor_serialized_array_iterator_next _ = cbor_raw_serialized_iterator_next _ (jump_raw_data_item ()) cbor_match (cbor_serialized_array_iterator_next_cont ())

inline_for_extraction
fn cbor_serialized_array_iterator_next_cont_with_depth (n: Ghost.erased nat) (_: unit)
: cbor_raw_serialized_iterator_next_cont #cbor_raw #raw_data_item #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item (cbor_match_with_depth n)
= (x: _) (#pm: _) (#v: _) {
  let res = cbor_read x;
  cbor_match_with_depth_intro_noninline n 1.0R res v;
  Trade.trans _ _ (pts_to_serialized serialize_raw_data_item x #pm v);
  res
}

let cbor_serialized_array_iterator_next_with_depth (n: Ghost.erased nat) = cbor_raw_serialized_iterator_next _ (jump_raw_data_item ()) (cbor_match_with_depth n) (cbor_serialized_array_iterator_next_cont_with_depth n ())

let cbor_serialized_array_iterator_truncate = cbor_raw_serialized_iterator_truncate serialize_raw_data_item

let cbor_serialized_array_iterator_share = cbor_raw_serialized_iterator_share serialize_raw_data_item

let cbor_serialized_array_iterator_gather = cbor_raw_serialized_iterator_gather serialize_raw_data_item

let cbor_serialized_map_iterator_match = cbor_raw_serialized_iterator_match (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)

module LP = LowParse.Pulse.VCList

ghost
fn cbor_match_serialized_map_elim
  (c: cbor_serialized)
  (pm: perm)
  (r: raw_data_item { Map? r })
  requires
    cbor_match_serialized_map c pm r
  ensures exists* pm' .
    pts_to_serialized (LP.serialize_nlist (U64.v (Map?.len r).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (to_slice c.cbor_serialized_payload) #pm' (Map?.v r) **
    trade
      (pts_to_serialized (LP.serialize_nlist (U64.v (Map?.len r).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (to_slice c.cbor_serialized_payload) #pm' (Map?.v r))
      (cbor_match_serialized_map c pm r) **
    pure (c.cbor_serialized_header == Map?.len r)
{
  unfold (cbor_match_serialized_map c pm r);
  unfold (cbor_match_serialized_payload_map (to_slice c.cbor_serialized_payload) (pm `perm_mul` c.cbor_serialized_perm) (Map?.v r));
  with pm' . assert (pts_to_serialized (LP.serialize_nlist (U64.v (Map?.len r).value)  (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (to_slice c.cbor_serialized_payload) #pm' (Map?.v r));
  intro
    (Trade.trade
      (pts_to_serialized (LP.serialize_nlist (U64.v (Map?.len r).value)  (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (to_slice c.cbor_serialized_payload) #pm' (Map?.v r))
      (cbor_match_serialized_map c pm r)
    )
    #emp
    fn _
  {
    fold (cbor_match_serialized_payload_map (to_slice c.cbor_serialized_payload) (pm `perm_mul` c.cbor_serialized_perm) (Map?.v r));
    fold (cbor_match_serialized_map c pm r);
  };
}

fn cbor_serialized_map_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
requires
    (cbor_match_serialized_map c pm r)
returns res: cbor_raw_serialized_iterator
ensures
    (exists* p .
      cbor_serialized_map_iterator_match p res (Map?.v r) **
      trade
        (cbor_serialized_map_iterator_match p res (Map?.v r))
        (cbor_match_serialized_map c pm r)
    )
{
  cbor_match_serialized_map_elim c pm r;
  with p . assert (
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (U64.v (Map?.len (Ghost.reveal r)).value)
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      (to_slice c.cbor_serialized_payload)
      #p
      (Map?.v (Ghost.reveal r)))
  );
  let res : cbor_raw_serialized_iterator = {
    s = c.cbor_serialized_payload;
    p = 1.0R;
    glen = Ghost.hide (U64.v (Map?.len r).value);
    len = c.cbor_serialized_header.value;
  };
  Trade.rewrite_with_trade
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (U64.v (Map?.len (Ghost.reveal r)).value)
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      (to_slice c.cbor_serialized_payload)
      #p
      (Map?.v (Ghost.reveal r)))
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (Ghost.reveal res.glen)
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      (to_slice res.s)
      #p
      (Map?.v (Ghost.reveal r))      
  )
  ;
  Trade.trans _ _ (cbor_match_serialized_map c pm r);
  cbor_raw_serialized_iterator_fold (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) p res (Map?.v r);
  LowParse.Pulse.VCList.trade_trans_nounify _ _ _ (cbor_match_serialized_map c pm r);
  fold (cbor_serialized_map_iterator_match p res (Map?.v r));
  with _pm' . rewrite
    trade (cbor_raw_serialized_iterator_match (serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item)
          _pm'
          res
          (Map?.v r))
      (cbor_match_serialized_map c pm r)
    as trade (cbor_serialized_map_iterator_match _pm' res (Map?.v r))
      (cbor_match_serialized_map c pm r)
    ;
  res
}

let cbor_serialized_map_iterator_is_empty = cbor_raw_serialized_iterator_is_empty _

module LPC = LowParse.Pulse.Combinators

inline_for_extraction
fn cbor_serialized_map_iterator_next_cont (_: unit)
: cbor_raw_serialized_iterator_next_cont #cbor_map_entry #(raw_data_item & raw_data_item) #(and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind) #(nondep_then parse_raw_data_item parse_raw_data_item) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) cbor_match_map_entry
= (x: _) (#pm: _) (#v: _) {
  let s1, s2 = LPC.split_nondep_then
    serialize_raw_data_item
    (jump_raw_data_item ())
    serialize_raw_data_item
    x;
  unfold (LPC.split_nondep_then_post serialize_raw_data_item serialize_raw_data_item x pm v (s1, s2));
  unfold (LPC.split_nondep_then_post' serialize_raw_data_item serialize_raw_data_item x pm v s1 s2);
  with v1 . assert (pts_to_serialized serialize_raw_data_item s1 #pm v1);
  with v2 . assert (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  let res1 = cbor_read s1;
  let res2 = cbor_read s2;
  Trade.prod _ (pts_to_serialized serialize_raw_data_item s1 #pm v1) _ (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) x #pm v);
  let res : cbor_map_entry = {
    cbor_map_entry_key = res1;
    cbor_map_entry_value = res2;
  };
  Trade.rewrite_with_trade
    (cbor_match 1.0R res1 v1 ** cbor_match 1.0R res2 v2)
    (cbor_match_map_entry 1.0R res v);
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) x #pm v);
  res
}

let cbor_serialized_map_iterator_next _ = cbor_raw_serialized_iterator_next _ (jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ())) cbor_match_map_entry (cbor_serialized_map_iterator_next_cont ())

inline_for_extraction
fn cbor_serialized_map_iterator_next_cont_with_depth (n: Ghost.erased nat) (_: unit)
: cbor_raw_serialized_iterator_next_cont #cbor_map_entry #(raw_data_item & raw_data_item) #(and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind) #(nondep_then parse_raw_data_item parse_raw_data_item) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) (cbor_match_map_entry_with_depth n)
= (x: _) (#pm: _) (#v: _) {
  let s1, s2 = LPC.split_nondep_then
    serialize_raw_data_item
    (jump_raw_data_item ())
    serialize_raw_data_item
    x;
  unfold (LPC.split_nondep_then_post serialize_raw_data_item serialize_raw_data_item x pm v (s1, s2));
  unfold (LPC.split_nondep_then_post' serialize_raw_data_item serialize_raw_data_item x pm v s1 s2);
  with v1 . assert (pts_to_serialized serialize_raw_data_item s1 #pm v1);
  with v2 . assert (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  let res1 = cbor_read s1;
  let res2 = cbor_read s2;
  cbor_match_with_depth_intro_noninline n 1.0R res1 v1;
  Trade.trans _ _ (pts_to_serialized serialize_raw_data_item s1 #pm v1);
  cbor_match_with_depth_intro_noninline n 1.0R res2 v2;
  Trade.trans _ _ (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  Trade.prod _ (pts_to_serialized serialize_raw_data_item s1 #pm v1) _ (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) x #pm v);
  let res : cbor_map_entry = {
    cbor_map_entry_key = res1;
    cbor_map_entry_value = res2;
  };
  Trade.rewrite_with_trade
    (cbor_match_with_depth n 1.0R res1 v1 ** cbor_match_with_depth n 1.0R res2 v2)
    (cbor_match_map_entry_with_depth n 1.0R res v);
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) x #pm v);
  res
}

let cbor_serialized_map_iterator_next_with_depth (n: Ghost.erased nat) = cbor_raw_serialized_iterator_next _ (jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ())) (cbor_match_map_entry_with_depth n) (cbor_serialized_map_iterator_next_cont_with_depth n ())

let cbor_serialized_map_iterator_share = cbor_raw_serialized_iterator_share (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)

let cbor_serialized_map_iterator_gather = cbor_raw_serialized_iterator_gather (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)

////////////////////////////////////////////////////////////////////////////////
// Mixed-list ("_Gen") iterators (Layer 2), built on the lowparse mixed-list
// iterator API (LowParse.PulseParse.Iterator) and the generic Layer-1
// operations in CBOR.Pulse.Raw.EverParse.Iterator.Mixed.
////////////////////////////////////////////////////////////////////////////////

// ---- element-vmatch share/gather wrappers (share_t / gather_t shape) ----

ghost
fn cbor_match_share_ (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires cbor_match p x1 x2
ensures cbor_match (p /. 2.0R) x1 x2 ** cbor_match (p /. 2.0R) x1 x2
{
  Perm.cbor_raw_share p x1 x2;
}

ghost
fn cbor_match_gather_ (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires cbor_match p x1 x2 ** cbor_match p' x1 x2'
ensures cbor_match (p +. p') x1 x2 ** pure (x2 == x2')
{
  Perm.cbor_raw_gather p x1 x2 p' x2';
}

ghost
fn cbor_match_map_entry_share_ (x1: cbor_map_entry) (#p: perm) (#x2: (raw_data_item & raw_data_item))
requires cbor_match_map_entry p x1 x2
ensures cbor_match_map_entry (p /. 2.0R) x1 x2 ** cbor_match_map_entry (p /. 2.0R) x1 x2
{
  unfold (cbor_match_map_entry p x1 x2);
  Perm.cbor_raw_share p x1.cbor_map_entry_key (fst x2);
  Perm.cbor_raw_share p x1.cbor_map_entry_value (snd x2);
  fold (cbor_match_map_entry (p /. 2.0R) x1 x2);
  fold (cbor_match_map_entry (p /. 2.0R) x1 x2);
}

ghost
fn cbor_match_map_entry_gather_ (x1: cbor_map_entry) (#p: perm) (#x2: (raw_data_item & raw_data_item)) (#p': perm) (#x2': (raw_data_item & raw_data_item))
requires cbor_match_map_entry p x1 x2 ** cbor_match_map_entry p' x1 x2'
ensures cbor_match_map_entry (p +. p') x1 x2 ** pure (x2 == x2')
{
  unfold (cbor_match_map_entry p x1 x2);
  unfold (cbor_match_map_entry p' x1 x2');
  Perm.cbor_raw_gather p x1.cbor_map_entry_key (fst x2) p' (fst x2');
  Perm.cbor_raw_gather p x1.cbor_map_entry_value (snd x2) p' (snd x2');
  fold (cbor_match_map_entry (p +. p') x1 x2);
}

// ---- zero_copy_parse readers (for iterator_next) ----

inline_for_extraction
fn cbor_read_zcp (input: S.slice byte) (#pm: perm) (#v: Ghost.erased raw_data_item)
requires PP.pts_to_parsed parse_raw_data_item input #pm v
returns res: cbor_raw
ensures
  cbor_match 1.0R res v **
  Trade.trade (cbor_match 1.0R res v) (PP.pts_to_parsed parse_raw_data_item input #pm v)
{
  PP.pts_to_parsed_serialized serialize_raw_data_item input;
  let res = cbor_read input;
  Trade.trans _ _ (PP.pts_to_parsed parse_raw_data_item input #pm v);
  res
}

inline_for_extraction
fn cbor_read_map_entry_zcp (input: S.slice byte) (#pm: perm) (#v: Ghost.erased (raw_data_item & raw_data_item))
requires PP.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v
returns res: cbor_map_entry
ensures
  cbor_match_map_entry 1.0R res v **
  Trade.trade (cbor_match_map_entry 1.0R res v) (PP.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
{
  PP.pts_to_parsed_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input;
  let s1, s2 = LowParse.Pulse.Combinators.split_nondep_then
    serialize_raw_data_item
    (jump_raw_data_item ())
    serialize_raw_data_item
    input;
  unfold (LowParse.Pulse.Combinators.split_nondep_then_post serialize_raw_data_item serialize_raw_data_item input pm v (s1, s2));
  unfold (LowParse.Pulse.Combinators.split_nondep_then_post' serialize_raw_data_item serialize_raw_data_item input pm v s1 s2);
  with v1 . assert (pts_to_serialized serialize_raw_data_item s1 #pm v1);
  with v2 . assert (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  let res1 = cbor_read s1;
  let res2 = cbor_read s2;
  Trade.prod _ (pts_to_serialized serialize_raw_data_item s1 #pm v1) _ (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input #pm v);
  let res : cbor_map_entry = {
    cbor_map_entry_key = res1;
    cbor_map_entry_value = res2;
  };
  Trade.rewrite_with_trade
    (cbor_match 1.0R res1 v1 ** cbor_match 1.0R res2 v2)
    (cbor_match_map_entry 1.0R res v);
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input #pm v);
  Trade.trans _ _ (PP.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v);
  res
}

// ---- depth-aware zero_copy_parse readers (for depth iterator_next) ----

inline_for_extraction
fn cbor_read_zcp_with_depth (n: Ghost.erased nat) (input: S.slice byte) (#pm: perm) (#v: Ghost.erased raw_data_item)
requires PP.pts_to_parsed parse_raw_data_item input #pm v
returns res: cbor_raw
ensures
  cbor_match_with_depth n 1.0R res v **
  Trade.trade (cbor_match_with_depth n 1.0R res v) (PP.pts_to_parsed parse_raw_data_item input #pm v)
{
  PP.pts_to_parsed_serialized serialize_raw_data_item input;
  let res = cbor_read input;
  Trade.trans _ _ (PP.pts_to_parsed parse_raw_data_item input #pm v);
  cbor_match_with_depth_intro_noninline n 1.0R res v;
  Trade.trans _ _ (PP.pts_to_parsed parse_raw_data_item input #pm v);
  res
}

inline_for_extraction
fn cbor_read_map_entry_zcp_with_depth (n: Ghost.erased nat) (input: S.slice byte) (#pm: perm) (#v: Ghost.erased (raw_data_item & raw_data_item))
requires PP.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v
returns res: cbor_map_entry
ensures
  cbor_match_map_entry_with_depth n 1.0R res v **
  Trade.trade (cbor_match_map_entry_with_depth n 1.0R res v) (PP.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
{
  PP.pts_to_parsed_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input;
  let s1, s2 = LowParse.Pulse.Combinators.split_nondep_then
    serialize_raw_data_item
    (jump_raw_data_item ())
    serialize_raw_data_item
    input;
  unfold (LowParse.Pulse.Combinators.split_nondep_then_post serialize_raw_data_item serialize_raw_data_item input pm v (s1, s2));
  unfold (LowParse.Pulse.Combinators.split_nondep_then_post' serialize_raw_data_item serialize_raw_data_item input pm v s1 s2);
  with v1 . assert (pts_to_serialized serialize_raw_data_item s1 #pm v1);
  with v2 . assert (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  let res1 = cbor_read s1;
  cbor_match_with_depth_intro_noninline n 1.0R res1 v1;
  Trade.trans (cbor_match_with_depth n 1.0R res1 v1) (cbor_match 1.0R res1 v1) (pts_to_serialized serialize_raw_data_item s1 #pm v1);
  let res2 = cbor_read s2;
  cbor_match_with_depth_intro_noninline n 1.0R res2 v2;
  Trade.trans (cbor_match_with_depth n 1.0R res2 v2) (cbor_match 1.0R res2 v2) (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  Trade.prod _ (pts_to_serialized serialize_raw_data_item s1 #pm v1) _ (pts_to_serialized serialize_raw_data_item s2 #pm v2);
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input #pm v);
  let res : cbor_map_entry = {
    cbor_map_entry_key = res1;
    cbor_map_entry_value = res2;
  };
  Trade.rewrite_with_trade
    (cbor_match_with_depth n 1.0R res1 v1 ** cbor_match_with_depth n 1.0R res2 v2)
    (cbor_match_map_entry_with_depth n 1.0R res v);
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) input #pm v);
  Trade.trans _ _ (PP.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v);
  res
}

// ---- depth-aware share/gather callbacks ----

ghost
fn cbor_match_with_depth_share_ (n: Ghost.erased nat) (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires cbor_match_with_depth n p x1 x2
ensures cbor_match_with_depth n (p /. 2.0R) x1 x2 ** cbor_match_with_depth n (p /. 2.0R) x1 x2
{
  MD.cbor_match_with_depth_share n p x1 x2
}

ghost
fn cbor_match_with_depth_gather_ (n: Ghost.erased nat) (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires cbor_match_with_depth n p x1 x2 ** cbor_match_with_depth n p' x1 x2'
ensures cbor_match_with_depth n (p +. p') x1 x2 ** pure (x2 == x2')
{
  MD.cbor_match_with_depth_gather n p x1 x2 p' x2'
}

ghost
fn cbor_match_map_entry_with_depth_share_ (n: Ghost.erased nat) (x1: cbor_map_entry) (#p: perm) (#x2: (raw_data_item & raw_data_item))
requires cbor_match_map_entry_with_depth n p x1 x2
ensures cbor_match_map_entry_with_depth n (p /. 2.0R) x1 x2 ** cbor_match_map_entry_with_depth n (p /. 2.0R) x1 x2
{
  unfold (cbor_match_map_entry_with_depth n p x1 x2);
  MD.cbor_match_with_depth_share n p x1.cbor_map_entry_key (fst x2);
  MD.cbor_match_with_depth_share n p x1.cbor_map_entry_value (snd x2);
  fold (cbor_match_map_entry_with_depth n (p /. 2.0R) x1 x2);
  fold (cbor_match_map_entry_with_depth n (p /. 2.0R) x1 x2);
}

ghost
fn cbor_match_map_entry_with_depth_gather_ (n: Ghost.erased nat) (x1: cbor_map_entry) (#p: perm) (#x2: (raw_data_item & raw_data_item)) (#p': perm) (#x2': (raw_data_item & raw_data_item))
requires cbor_match_map_entry_with_depth n p x1 x2 ** cbor_match_map_entry_with_depth n p' x1 x2'
ensures cbor_match_map_entry_with_depth n (p +. p') x1 x2 ** pure (x2 == x2')
{
  unfold (cbor_match_map_entry_with_depth n p x1 x2);
  unfold (cbor_match_map_entry_with_depth n p' x1 x2');
  MD.cbor_match_with_depth_gather n p x1.cbor_map_entry_key (fst x2) p' (fst x2');
  MD.cbor_match_with_depth_gather n p x1.cbor_map_entry_value (snd x2) p' (snd x2');
  fold (cbor_match_map_entry_with_depth n (p +. p') x1 x2);
}

// ---- generic record-wrapped mixed match + operations ----

let mixed_iter_match
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pp: perm) (c: ML.cbor_raw_mixed_iterator t) (l: list u)
: slprop
= Iter.iterator_match vmatch p (pp *. c.mi_perm) c.mi_iterator l **
  pure (SZ.fits (List.Tot.length l) /\ FStar.UInt.fits (List.Tot.length l) 64)

inline_for_extraction
fn mixed_iter_is_empty
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
: cbor_raw_mixed_iterator_is_empty_t #t #u (mixed_iter_match vmatch p)
= (c: _) (#pm: _) (#r: _) {
    unfold (mixed_iter_match vmatch p pm c r);
    let res = iter_is_empty vmatch p c.mi_iterator;
    fold (mixed_iter_match vmatch p pm c r);
    res
  }

inline_for_extraction
fn mixed_iter_length
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
: cbor_raw_mixed_iterator_length_t #t #u (mixed_iter_match vmatch p)
= (c: _) (#pm: _) (#r: _) {
    unfold (mixed_iter_match vmatch p pm c r);
    let res_sz = iter_length vmatch p c.mi_iterator;
    let res = SZ.sizet_to_uint64 res_sz;
    fold (mixed_iter_match vmatch p pm c r);
    res
  }

ghost
fn mixed_iter_share
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (vmatch_share: PP.share_t vmatch)
: cbor_raw_mixed_iterator_share_t #t #u (mixed_iter_match vmatch p)
= (c: _) (#pm: _) (#r: _) {
    unfold (mixed_iter_match vmatch p pm c r);
    iter_share vmatch p vmatch_share c.mi_iterator;
    rewrite (Iter.iterator_match vmatch p ((pm *. c.mi_perm) /. 2.0R) c.mi_iterator r)
      as (Iter.iterator_match vmatch p ((pm /. 2.0R) *. c.mi_perm) c.mi_iterator r);
    rewrite (Iter.iterator_match vmatch p ((pm *. c.mi_perm) /. 2.0R) c.mi_iterator r)
      as (Iter.iterator_match vmatch p ((pm /. 2.0R) *. c.mi_perm) c.mi_iterator r);
    fold (mixed_iter_match vmatch p (pm /. 2.0R) c r);
    fold (mixed_iter_match vmatch p (pm /. 2.0R) c r);
  }

ghost
fn mixed_iter_gather
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (vmatch_gather: PP.gather_t vmatch)
: cbor_raw_mixed_iterator_gather_t #t #u (mixed_iter_match vmatch p)
= (c: _) (#pm1: _) (#r1: _) (#pm2: _) (#r2: _) {
    unfold (mixed_iter_match vmatch p pm1 c r1);
    unfold (mixed_iter_match vmatch p pm2 c r2);
    iter_gather vmatch p vmatch_gather c.mi_iterator #(pm1 *. c.mi_perm) #r1 #(pm2 *. c.mi_perm) #r2;
    rewrite (Iter.iterator_match vmatch p ((pm1 *. c.mi_perm) +. (pm2 *. c.mi_perm)) c.mi_iterator r1)
      as (Iter.iterator_match vmatch p ((pm1 +. pm2) *. c.mi_perm) c.mi_iterator r1);
    fold (mixed_iter_match vmatch p (pm1 +. pm2) c r1);
  }

#push-options "--z3rlimit 40"
inline_for_extraction
fn mixed_iter_truncate
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LowParse.Pulse.Base.jumper p)
  (vmatch_share: PP.share_t vmatch) (vmatch_gather: PP.gather_t vmatch)
: cbor_raw_mixed_iterator_truncate_t #t #u (mixed_iter_match vmatch p)
= (c: _) (len: U64.t) (#pm: _) (#r: _) {
    unfold (mixed_iter_match vmatch p pm c r);
    SZ.fits_lte (U64.v len) (List.Tot.length r);
    let len_sz = SZ.uint64_to_sizet len;
    let res0 = iter_truncate vmatch p j vmatch_share vmatch_gather c.mi_iterator len_sz;
    with pm' . assert (Iter.iterator_match vmatch p pm' res0 (fst (List.Tot.splitAt (SZ.v len_sz) r)));
    let res : ML.cbor_raw_mixed_iterator t = { mi_iterator = res0; mi_perm = pm' };
    FStar.List.Pure.Properties.splitAt_length (U64.v len) r;
    rewrite (Iter.iterator_match vmatch p pm' res0 (fst (List.Tot.splitAt (SZ.v len_sz) r)))
      as (Iter.iterator_match vmatch p (1.0R *. res.mi_perm) res.mi_iterator (fst (List.Tot.splitAt (U64.v len) r)));
    fold (mixed_iter_match vmatch p 1.0R res (fst (List.Tot.splitAt (U64.v len) r)));
    intro (mixed_iter_match vmatch p 1.0R res (fst (List.Tot.splitAt (U64.v len) r)) @==>
           mixed_iter_match vmatch p pm c r)
      #(Trade.trade (Iter.iterator_match vmatch p pm' res0 (fst (List.Tot.splitAt (SZ.v len_sz) r)))
                    (Iter.iterator_match vmatch p (pm *. c.mi_perm) c.mi_iterator r))
      fn _ {
        unfold (mixed_iter_match vmatch p 1.0R res (fst (List.Tot.splitAt (U64.v len) r)));
        rewrite (Iter.iterator_match vmatch p (1.0R *. res.mi_perm) res.mi_iterator (fst (List.Tot.splitAt (U64.v len) r)))
          as (Iter.iterator_match vmatch p pm' res0 (fst (List.Tot.splitAt (SZ.v len_sz) r)));
        elim_trade _ _;
        fold (mixed_iter_match vmatch p pm c r);
      };
    res
  }
#pop-options

inline_for_extraction
fn mixed_iter_init
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LowParse.Pulse.Base.jumper p)
  (vmatch_share: PP.share_t vmatch) (vmatch_gather: PP.gather_t vmatch)
  (ml: IT.mixed_list t)
  (#pm: perm) (#l: Ghost.erased (list u))
requires
  Iter.mixed_list_match vmatch p pm ml l **
  pure (SZ.fits (List.Tot.length l) /\ FStar.UInt.fits (List.Tot.length l) 64)
returns res: ML.cbor_raw_mixed_iterator t
ensures
  mixed_iter_match vmatch p 1.0R res l **
  Trade.trade
    (mixed_iter_match vmatch p 1.0R res l)
    (Iter.mixed_list_match vmatch p pm ml l)
{
  let it = Iter.iterator_start vmatch p j pm ml l vmatch_share vmatch_gather;
  with pm' . assert (Iter.iterator_match vmatch p pm' it l);
  let res : ML.cbor_raw_mixed_iterator t = { mi_iterator = it; mi_perm = pm' };
  rewrite (Iter.iterator_match vmatch p pm' it l)
    as (Iter.iterator_match vmatch p (1.0R *. res.mi_perm) res.mi_iterator l);
  fold (mixed_iter_match vmatch p 1.0R res l);
  intro (mixed_iter_match vmatch p 1.0R res l @==> Iter.mixed_list_match vmatch p pm ml l)
    #(Trade.trade (Iter.iterator_match vmatch p pm' it l) (Iter.mixed_list_match vmatch p pm ml l))
    fn _ {
      unfold (mixed_iter_match vmatch p 1.0R res l);
      rewrite (Iter.iterator_match vmatch p (1.0R *. res.mi_perm) res.mi_iterator l)
        as (Iter.iterator_match vmatch p pm' it l);
      elim_trade _ _;
    };
  res
}

#push-options "--z3rlimit 40"
inline_for_extraction
fn mixed_iter_next
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LowParse.Pulse.Base.jumper p)
  (vmatch_share: PP.share_t vmatch) (vmatch_gather: PP.gather_t vmatch)
  (zcp: PP.zero_copy_parse (vmatch 1.0R) p)
: cbor_raw_mixed_iterator_next_t #t #u vmatch (mixed_iter_match vmatch p)
= (pi: _) (#pm: _) (i: _) (#l: _) {
    unfold (mixed_iter_match vmatch p pm i l);
    let mut rr = i.mi_iterator;
    let res = Iter.iterator_next vmatch p j (pm *. i.mi_perm) rr i.mi_iterator l vmatch_share vmatch_gather zcp;
    unfold (Iter.iterator_next_post vmatch p (pm *. i.mi_perm) rr i.mi_iterator l res);
    with pm_v hd tl it' pm' . assert (
      vmatch pm_v res hd **
      R.pts_to rr it' **
      Iter.iterator_match vmatch p pm' it' tl **
      Trade.trade (vmatch pm_v res hd ** Iter.iterator_match vmatch p pm' it' tl)
            (Iter.iterator_match vmatch p (pm *. i.mi_perm) i.mi_iterator l) **
      pure (Ghost.reveal l == hd :: tl)
    );
    let it2 = !rr;
    let res_it : ML.cbor_raw_mixed_iterator t = { mi_iterator = it2; mi_perm = pm' /. pm };
    pi := CBOR_Raw_Iterator_Mixed res_it;
    SZ.fits_lte (List.Tot.length tl) (List.Tot.length l);
    assert (pure (pm *. res_it.mi_perm == pm'));
    rewrite (Iter.iterator_match vmatch p pm' it' tl)
      as (Iter.iterator_match vmatch p (pm *. res_it.mi_perm) res_it.mi_iterator tl);
    fold (mixed_iter_match vmatch p pm res_it tl);
    intro (vmatch pm_v res hd ** mixed_iter_match vmatch p pm res_it tl @==> mixed_iter_match vmatch p pm i l)
      #(Trade.trade (vmatch pm_v res hd ** Iter.iterator_match vmatch p pm' it' tl)
                    (Iter.iterator_match vmatch p (pm *. i.mi_perm) i.mi_iterator l))
      fn _ {
        unfold (mixed_iter_match vmatch p pm res_it tl);
        rewrite (Iter.iterator_match vmatch p (pm *. res_it.mi_perm) res_it.mi_iterator tl)
          as (Iter.iterator_match vmatch p pm' it' tl);
        elim_trade _ _;
        fold (mixed_iter_match vmatch p pm i l);
      };
    res
  }
#pop-options

////////////////////////////////////////////////////////////////////////////////
// ARRAY (non-depth) instantiations
////////////////////////////////////////////////////////////////////////////////

let cbor_mixed_array_iterator_match = mixed_iter_match cbor_match parse_raw_data_item

ghost
fn mixed_array_length_facts
  (pm: perm) (c: cbor_mixed_list_array) (r: raw_data_item { Array? r })
requires
  cbor_match_mixed_list_array pm c r cbor_match
ensures
  cbor_match_mixed_list_array pm c r cbor_match **
  pure (List.Tot.length (Array?.v r) == U64.v (Array?.len r).value /\
        FStar.SizeT.fits (List.Tot.length (Array?.v r)) /\
        FStar.UInt.fits (List.Tot.length (Array?.v r)) 64)
{
  cbor_match_mixed_list_array_length pm c r cbor_match;
  unfold (cbor_match_mixed_list_array pm c r cbor_match);
  Iter.mixed_list_match_length (cbor_match_bounded r cbor_match) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r);
  assert (pure (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length c.cbor_array_gen_ptr == LowParse.PulseParse.Iterator.Type.mixed_list_length c.cbor_array_gen_ptr));
  fold (cbor_match_mixed_list_array pm c r cbor_match);
}

ghost
fn array_to_unbounded
  (pm: perm) (c: cbor_mixed_list_array) (r: raw_data_item { Array? r })
requires
  cbor_match_mixed_list_array pm c r cbor_match
ensures
  Iter.mixed_list_match cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) **
  Trade.trade
    (Iter.mixed_list_match cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
    (cbor_match_mixed_list_array pm c r cbor_match) **
  pure (FStar.SizeT.fits (List.Tot.length (Array?.v r)) /\ FStar.UInt.fits (List.Tot.length (Array?.v r)) 64)
{
  mixed_array_length_facts pm c r;
  unfold (cbor_match_mixed_list_array pm c r cbor_match);
  ghost
  fn prf_fwd
    (x: cbor_raw)
    (pm0: perm)
    (y: raw_data_item { List.Tot.memP y (Array?.v r) })
  requires cbor_match_bounded r cbor_match pm0 x y
  ensures cbor_match pm0 x y
  {
    array_elem_precedes r y;
    cbor_match_bounded_eq r cbor_match pm0 x y;
    rewrite (cbor_match_bounded r cbor_match pm0 x y) as (cbor_match pm0 x y);
  };
  Iter.mixed_list_match_weaken
    (cbor_match_bounded r cbor_match) cbor_match parse_raw_data_item
    (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) prf_fwd;
  intro
    (Iter.mixed_list_match cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) @==>
     Iter.mixed_list_match (cbor_match_bounded r cbor_match) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
    #emp
    fn _
  {
    ghost
    fn prf_bwd
      (x: cbor_raw)
      (pm0: perm)
      (y: raw_data_item { List.Tot.memP y (Array?.v r) })
    requires cbor_match pm0 x y
    ensures cbor_match_bounded r cbor_match pm0 x y
    {
      array_elem_precedes r y;
        cbor_match_bounded_eq r cbor_match pm0 x y;
      rewrite (cbor_match pm0 x y) as (cbor_match_bounded r cbor_match pm0 x y);
    };
    Iter.mixed_list_match_weaken
      cbor_match (cbor_match_bounded r cbor_match) parse_raw_data_item
      (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) prf_bwd;
  };
  intro
    (Iter.mixed_list_match (cbor_match_bounded r cbor_match) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) @==>
     cbor_match_mixed_list_array pm c r cbor_match)
    #emp
    fn _
  {
    fold (cbor_match_mixed_list_array pm c r cbor_match);
  };
  Trade.trans
    (Iter.mixed_list_match cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
    (Iter.mixed_list_match (cbor_match_bounded r cbor_match) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
    (cbor_match_mixed_list_array pm c r cbor_match);
}

fn cbor_mixed_array_iterator_init
  (c: cbor_mixed_list_array)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
  cbor_match_mixed_list_array pm c r cbor_match
returns res: ML.cbor_raw_mixed_iterator cbor_raw
ensures exists* p .
  cbor_mixed_array_iterator_match p res (Array?.v r) **
  Trade.trade
    (cbor_mixed_array_iterator_match p res (Array?.v r))
    (cbor_match_mixed_list_array pm c r cbor_match)
{
  array_to_unbounded pm c r;
  let res = mixed_iter_init cbor_match parse_raw_data_item (jump_raw_data_item ())
    cbor_match_share_ cbor_match_gather_ c.cbor_array_gen_ptr
    #(pm *. c.cbor_array_gen_perm) #(Array?.v r);
  Trade.trans
    (mixed_iter_match cbor_match parse_raw_data_item 1.0R res (Array?.v r))
    (Iter.mixed_list_match cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
    (cbor_match_mixed_list_array pm c r cbor_match);
  rewrite (mixed_iter_match cbor_match parse_raw_data_item 1.0R res (Array?.v r))
    as (cbor_mixed_array_iterator_match 1.0R res (Array?.v r));
  rewrite
    (Trade.trade (mixed_iter_match cbor_match parse_raw_data_item 1.0R res (Array?.v r)) (cbor_match_mixed_list_array pm c r cbor_match))
    as (Trade.trade (cbor_mixed_array_iterator_match 1.0R res (Array?.v r)) (cbor_match_mixed_list_array pm c r cbor_match));
  res
}

let cbor_mixed_array_iterator_is_empty = mixed_iter_is_empty cbor_match parse_raw_data_item

let cbor_mixed_array_iterator_length = mixed_iter_length cbor_match parse_raw_data_item

let cbor_mixed_array_iterator_next _ = mixed_iter_next cbor_match parse_raw_data_item (jump_raw_data_item ()) cbor_match_share_ cbor_match_gather_ cbor_read_zcp

let cbor_mixed_array_iterator_truncate = mixed_iter_truncate cbor_match parse_raw_data_item (jump_raw_data_item ()) cbor_match_share_ cbor_match_gather_

let cbor_mixed_array_iterator_share = mixed_iter_share cbor_match parse_raw_data_item cbor_match_share_

let cbor_mixed_array_iterator_gather = mixed_iter_gather cbor_match parse_raw_data_item cbor_match_gather_

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let list_narrow_index_hd (#a: Type) (l: list a) (k: nat)
  : Lemma (requires k < List.Tot.length l)
          (ensures Cons? (Iter.list_narrow l k 1) /\ List.Tot.hd (Iter.list_narrow l k 1) == List.Tot.index l k)
= FStar.List.Pure.Properties.lemma_splitAt_index_hd k l;
  FStar.List.Tot.Base.lemma_splitAt_snd_length k l;
  let tl = snd (List.Tot.splitAt k l) in
  assert (fst (List.Tot.splitAt 1 tl) == [List.Tot.hd tl])

let singleton_of_len1 (#a:Type) (xs:list a)
  : Lemma (requires List.Tot.length xs == 1) (ensures xs == [List.Tot.hd xs])
= ()
#pop-options

#push-options "--z3rlimit 40"
fn cbor_mixed_array_item
  (c: cbor_mixed_list_array)
  (i: U64.t)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
    (cbor_match_mixed_list_array pm c r cbor_match **
      pure (U64.v i < List.Tot.length (Array?.v r))
    )
returns res: cbor_raw
ensures exists* p' y .
      cbor_match p' res y **
      trade
        (cbor_match p' res y)
        (cbor_match_mixed_list_array pm c r cbor_match) **
      pure (
        U64.v i < List.Tot.length (Array?.v r) /\
        List.Tot.index (Array?.v r) (U64.v i) == y
      )
{
  array_to_unbounded pm c r;
  Iter.mixed_list_match_length cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r);
  SZ.fits_lte (U64.v i) (List.Tot.length (Array?.v r));
  let iu : SZ.t = SZ.uint64_to_sizet i;
  assert_norm (SZ.v 1sz == 1);
  unfold (Iter.mixed_list_match cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r));
  let ml_i = Iter.mixed_list_narrow_n cbor_match parse_raw_data_item (jump_raw_data_item ())
    0 (SZ.v (IT.mixed_list_length c.cbor_array_gen_ptr)) (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r)
    iu 1sz cbor_match_share_ cbor_match_gather_;
  Iter.list_narrow_length (Array?.v r) (U64.v i) 1;
  list_narrow_index_hd (Array?.v r) (U64.v i);
  singleton_of_len1 (Iter.list_narrow (Array?.v r) (U64.v i) 1);
  rewrite (Iter.mixed_list_match cbor_match parse_raw_data_item ((pm *. c.cbor_array_gen_perm) /. 2.0R) ml_i (Iter.list_narrow (Array?.v r) (SZ.v iu - 0) (SZ.v 1sz)))
    as (Iter.mixed_list_match cbor_match parse_raw_data_item ((pm *. c.cbor_array_gen_perm) /. 2.0R) ml_i [List.Tot.index (Array?.v r) (U64.v i)]);
  rewrite (Trade.trade
             (Iter.mixed_list_match cbor_match parse_raw_data_item ((pm *. c.cbor_array_gen_perm) /. 2.0R) ml_i (Iter.list_narrow (Array?.v r) (SZ.v iu - 0) (SZ.v 1sz)))
             (Iter.mixed_list_match_n cbor_match parse_raw_data_item 0 (SZ.v (IT.mixed_list_length c.cbor_array_gen_ptr)) (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r)))
    as (Trade.trade
             (Iter.mixed_list_match cbor_match parse_raw_data_item ((pm *. c.cbor_array_gen_perm) /. 2.0R) ml_i [List.Tot.index (Array?.v r) (U64.v i)])
             (Iter.mixed_list_match_n cbor_match parse_raw_data_item 0 (SZ.v (IT.mixed_list_length c.cbor_array_gen_ptr)) (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r)));
  let it = mixed_iter_init cbor_match parse_raw_data_item (jump_raw_data_item ())
    cbor_match_share_ cbor_match_gather_ ml_i;
  let mut pi = CBOR_Raw_Iterator_Mixed it;
  let res = mixed_iter_next cbor_match parse_raw_data_item (jump_raw_data_item ())
    cbor_match_share_ cbor_match_gather_ cbor_read_zcp pi it;
  with a_v p_v i_v q_v. assert (
    cbor_match p_v res a_v **
    mixed_iter_match cbor_match parse_raw_data_item 1.0R i_v q_v **
    Trade.trade
      (cbor_match p_v res a_v ** mixed_iter_match cbor_match parse_raw_data_item 1.0R i_v q_v)
      (mixed_iter_match cbor_match parse_raw_data_item 1.0R it [List.Tot.index (Array?.v r) (U64.v i)]) **
    pure ([List.Tot.index (Array?.v r) (U64.v i)] == a_v :: q_v)
  );
  Trade.elim_hyp_r
    (cbor_match p_v res a_v)
    (mixed_iter_match cbor_match parse_raw_data_item 1.0R i_v q_v)
    (mixed_iter_match cbor_match parse_raw_data_item 1.0R it [List.Tot.index (Array?.v r) (U64.v i)]);
  Trade.trans
    (cbor_match p_v res a_v)
    (mixed_iter_match cbor_match parse_raw_data_item 1.0R it [List.Tot.index (Array?.v r) (U64.v i)])
    (Iter.mixed_list_match cbor_match parse_raw_data_item ((pm *. c.cbor_array_gen_perm) /. 2.0R) ml_i [List.Tot.index (Array?.v r) (U64.v i)]);
  Trade.trans
    (cbor_match p_v res a_v)
    (Iter.mixed_list_match cbor_match parse_raw_data_item ((pm *. c.cbor_array_gen_perm) /. 2.0R) ml_i [List.Tot.index (Array?.v r) (U64.v i)])
    (Iter.mixed_list_match_n cbor_match parse_raw_data_item 0 (SZ.v (IT.mixed_list_length c.cbor_array_gen_ptr)) (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r));
  rewrite (Trade.trade
             (cbor_match p_v res a_v)
             (Iter.mixed_list_match_n cbor_match parse_raw_data_item 0 (SZ.v (IT.mixed_list_length c.cbor_array_gen_ptr)) (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r)))
    as (Trade.trade
             (cbor_match p_v res a_v)
             (Iter.mixed_list_match cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r)));
  Trade.trans
    (cbor_match p_v res a_v)
    (Iter.mixed_list_match cbor_match parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
    (cbor_match_mixed_list_array pm c r cbor_match);
  res
}
#pop-options

////////////////////////////////////////////////////////////////////////////////
// MAP (non-depth) instantiations
////////////////////////////////////////////////////////////////////////////////

let cbor_mixed_map_iterator_match = mixed_iter_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item)

ghost
fn mixed_map_length_facts
  (pm: perm) (c: cbor_mixed_list_map) (r: raw_data_item { Map? r })
requires
  cbor_match_mixed_list_map pm c r cbor_match
ensures
  cbor_match_mixed_list_map pm c r cbor_match **
  pure (List.Tot.length (Map?.v r) == U64.v (Map?.len r).value /\
        FStar.SizeT.fits (List.Tot.length (Map?.v r)) /\
        FStar.UInt.fits (List.Tot.length (Map?.v r)) 64)
{
  cbor_match_mixed_list_map_length pm c r cbor_match;
  unfold (cbor_match_mixed_list_map pm c r cbor_match);
  Iter.mixed_list_match_length (cbor_match_map_entry_bounded r cbor_match) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r);
  assert (pure (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length c.cbor_map_gen_ptr == LowParse.PulseParse.Iterator.Type.mixed_list_length c.cbor_map_gen_ptr));
  fold (cbor_match_mixed_list_map pm c r cbor_match);
}

ghost
fn map_to_unbounded
  (pm: perm) (c: cbor_mixed_list_map) (r: raw_data_item { Map? r })
requires
  cbor_match_mixed_list_map pm c r cbor_match
ensures
  Iter.mixed_list_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) **
  Trade.trade
    (Iter.mixed_list_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r))
    (cbor_match_mixed_list_map pm c r cbor_match) **
  pure (FStar.SizeT.fits (List.Tot.length (Map?.v r)) /\ FStar.UInt.fits (List.Tot.length (Map?.v r)) 64)
{
  mixed_map_length_facts pm c r;
  unfold (cbor_match_mixed_list_map pm c r cbor_match);
  ghost
  fn prf_fwd
    (x: cbor_map_entry)
    (pm0: perm)
    (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r) })
  requires cbor_match_map_entry_bounded r cbor_match pm0 x y
  ensures cbor_match_map_entry pm0 x y
  {
    map_elem_precedes r y;
    cbor_match_map_entry_bounded_eq r cbor_match pm0 x y;
    rewrite (cbor_match_map_entry_bounded r cbor_match pm0 x y)
      as (cbor_match pm0 x.cbor_map_entry_key (fst y) ** cbor_match pm0 x.cbor_map_entry_value (snd y));
    fold (cbor_match_map_entry pm0 x y);
  };
  Iter.mixed_list_match_weaken
    (cbor_match_map_entry_bounded r cbor_match) cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item)
    (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) prf_fwd;
  intro
    (Iter.mixed_list_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) @==>
     Iter.mixed_list_match (cbor_match_map_entry_bounded r cbor_match) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r))
    #emp
    fn _
  {
    ghost
    fn prf_bwd
      (x: cbor_map_entry)
      (pm0: perm)
      (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r) })
    requires cbor_match_map_entry pm0 x y
    ensures cbor_match_map_entry_bounded r cbor_match pm0 x y
    {
      map_elem_precedes r y;
      unfold (cbor_match_map_entry pm0 x y);
        cbor_match_map_entry_bounded_eq r cbor_match pm0 x y;
      rewrite (cbor_match pm0 x.cbor_map_entry_key (fst y) ** cbor_match pm0 x.cbor_map_entry_value (snd y))
        as (cbor_match_map_entry_bounded r cbor_match pm0 x y);
    };
    Iter.mixed_list_match_weaken
      cbor_match_map_entry (cbor_match_map_entry_bounded r cbor_match) (nondep_then parse_raw_data_item parse_raw_data_item)
      (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) prf_bwd;
  };
  intro
    (Iter.mixed_list_match (cbor_match_map_entry_bounded r cbor_match) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) @==>
     cbor_match_mixed_list_map pm c r cbor_match)
    #emp
    fn _
  {
    fold (cbor_match_mixed_list_map pm c r cbor_match);
  };
  Trade.trans
    (Iter.mixed_list_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r))
    (Iter.mixed_list_match (cbor_match_map_entry_bounded r cbor_match) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r))
    (cbor_match_mixed_list_map pm c r cbor_match);
}

fn cbor_mixed_map_iterator_init
  (c: cbor_mixed_list_map)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
requires
  cbor_match_mixed_list_map pm c r cbor_match
returns res: ML.cbor_raw_mixed_iterator cbor_map_entry
ensures exists* p .
  cbor_mixed_map_iterator_match p res (Map?.v r) **
  Trade.trade
    (cbor_mixed_map_iterator_match p res (Map?.v r))
    (cbor_match_mixed_list_map pm c r cbor_match)
{
  map_to_unbounded pm c r;
  let res = mixed_iter_init cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item)
    (jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ()))
    cbor_match_map_entry_share_ cbor_match_map_entry_gather_ c.cbor_map_gen_ptr
    #(pm *. c.cbor_map_gen_perm) #(Map?.v r);
  Trade.trans
    (mixed_iter_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) 1.0R res (Map?.v r))
    (Iter.mixed_list_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r))
    (cbor_match_mixed_list_map pm c r cbor_match);
  rewrite (mixed_iter_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) 1.0R res (Map?.v r))
    as (cbor_mixed_map_iterator_match 1.0R res (Map?.v r));
  rewrite
    (Trade.trade (mixed_iter_match cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) 1.0R res (Map?.v r)) (cbor_match_mixed_list_map pm c r cbor_match))
    as (Trade.trade (cbor_mixed_map_iterator_match 1.0R res (Map?.v r)) (cbor_match_mixed_list_map pm c r cbor_match));
  res
}

let cbor_mixed_map_iterator_is_empty = mixed_iter_is_empty cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item)

let cbor_mixed_map_iterator_next _ = mixed_iter_next cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) (jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ())) cbor_match_map_entry_share_ cbor_match_map_entry_gather_ cbor_read_map_entry_zcp

let cbor_mixed_map_iterator_share = mixed_iter_share cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) cbor_match_map_entry_share_

let cbor_mixed_map_iterator_gather = mixed_iter_gather cbor_match_map_entry (nondep_then parse_raw_data_item parse_raw_data_item) cbor_match_map_entry_gather_

////////////////////////////////////////////////////////////////////////////////
// Depth-aware mixed-list ("_Gen") iterators.
//
// The element predicate is [cbor_match_with_depth (nat_pred depth)] (array) or
// [cbor_match_map_entry_with_depth (nat_pred depth)] (map). Init converts the
// bounded element predicate [cbor_match_bounded r (depth_cb depth r)] of the
// [cbor_match_mixed_list_array/map] representation into that unbounded
// depth-indexed predicate, with a trade back.
//
// At depth >= 1 the two predicates coincide per element (depth_cb succ), so a
// pair of forward/backward [mixed_list_match_weaken] does the job. At depth = 0
// the source predicate [cbor_match_bounded r (depth_cb 0 r)] is constantly
// [pure False]; there the forward pass is ex-falso and the reverse trade is
// built one-shot by [mixed_list_detonating_iso].
////////////////////////////////////////////////////////////////////////////////

// Generic "detonating" isomorphism: when every element of the source mixed list
// satisfies a vmatch1 that is unsatisfiable (implies [pure False]), convert to
// ANY vmatch2 (forward: ex-falso for inline positions, structural for the
// vmatch-free positions) and provide the reverse trade.
let slprop_rw : (p:slprop -> q:slprop -> slprop_equiv p q -> stt_ghost unit emp_inames p (fun _ -> q)) =
  _ by (FStar.Tactics.V2.exact (FStar.Tactics.V2.pack (FStar.Tactics.V2.Tv_FVar (FStar.Tactics.V2.pack_fv ["Pulse"; "Lib"; "Core"; "rewrite"]))))

// Ground-fact perm-arithmetic lemmas: these nonlinear real identities are proven
// once here in a minimal context, then injected as ground equalities before the
// (otherwise flaky under large-context pressure) perm rewrites in the helpers.
let perm_mul_half (pm sp: perm) : Lemma ((pm *. sp) /. 2.0R == (pm /. 2.0R) *. sp) = ()
let perm_mul_half2 (pm sp: perm) : Lemma ((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp == pm *. sp) = ()

ghost
fn rec seq_list_detonating_iso
  (#t #u: Type0)
  (im1 im2: (t -> u -> slprop))
  (c: Seq.seq t)
  (l: list u)
  (prf: (
    (x: t) ->
    (y: u { y << l /\ List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (im1 x y)
      (fun _ -> im2 x y ** Trade.trade (im2 x y) (im1 x y))
  ))
requires PM.seq_list_match c l im1
ensures
  PM.seq_list_match c l im2 **
  Trade.trade (PM.seq_list_match c l im2) (PM.seq_list_match c l im1)
decreases l
{
  if (Nil? l) {
    PM.seq_list_match_nil_elim c l im1;
    PM.seq_list_match_nil_intro c l im2;
    intro (PM.seq_list_match c l im2 @==> PM.seq_list_match c l im1)
      #(pure (c `Seq.equal` Seq.empty /\ Nil? l))
      fn _ {
        PM.seq_list_match_nil_elim c l im2;
        PM.seq_list_match_nil_intro c l im1;
      };
  } else {
    PM.list_cons_precedes (List.Tot.hd l) (List.Tot.tl l);
    PM.seq_list_match_cons_elim c l im1;
    prf (Seq.head c) (List.Tot.hd l);
    ghost fn prf'
      (x: t) (y: u { y << List.Tot.tl l /\ List.Tot.memP y (List.Tot.tl l) })
    requires im1 x y
    ensures im2 x y ** Trade.trade (im2 x y) (im1 x y)
    {
      prf x y
    };
    seq_list_detonating_iso im1 im2 (Seq.tail c) (List.Tot.tl l) prf';
    PM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd l) (Seq.tail c) (List.Tot.tl l) im2;
    Seq.cons_head_tail c;
    rewrite (PM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd l :: List.Tot.tl l) im2)
      as (PM.seq_list_match c l im2);
    intro (PM.seq_list_match c l im2 @==> PM.seq_list_match c l im1)
      #(pure (Cons? l) **
        Trade.trade (im2 (Seq.head c) (List.Tot.hd l)) (im1 (Seq.head c) (List.Tot.hd l)) **
        Trade.trade (PM.seq_list_match (Seq.tail c) (List.Tot.tl l) im2) (PM.seq_list_match (Seq.tail c) (List.Tot.tl l) im1))
      fn _ {
        PM.seq_list_match_cons_elim c l im2;
        elim_trade (im2 (Seq.head c) (List.Tot.hd l)) (im1 (Seq.head c) (List.Tot.hd l));
        elim_trade (PM.seq_list_match (Seq.tail c) (List.Tot.tl l) im2) (PM.seq_list_match (Seq.tail c) (List.Tot.tl l) im1);
        PM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd l) (Seq.tail c) (List.Tot.tl l) im1;
        Seq.cons_head_tail c;
        rewrite (PM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd l :: List.Tot.tl l) im1)
          as (PM.seq_list_match c l im1);
      };
  }
}

ghost
fn base_mixed_list_detonating_iso_n
  (#t #u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: IT.base_mixed_list t)
  (l: list u)
  (prf: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch1 pm0 x y)
      (fun _ -> vmatch2 (pm0 /. 2.0R) x y ** Trade.trade (vmatch2 (pm0 /. 2.0R) x y) (vmatch1 pm0 x y))
  ))
requires Iter.base_mixed_list_match_n vmatch1 p off n pm i l
ensures
  Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) i l **
  Trade.trade (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) i l) (Iter.base_mixed_list_match_n vmatch1 p off n pm i l)
{
  match i {
    IT.Empty -> {
      unfold (Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Empty #t) l);
      fold (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Empty #t) l);
      intro (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Empty #t) l @==>
             Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Empty #t) l)
        #(pure (Nil? l /\ n == 0 /\ off == 0))
        fn _ {
          unfold (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Empty #t) l);
          fold (Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Empty #t) l);
        };
      rewrite each (IT.Empty #t) as i;
    }
    IT.Singleton sp sv s -> {
      if (n = 0) {
        Iter.base_mixed_list_match_n_singleton_unfold_0 vmatch1 p off n pm sp sv s l ();
        Iter.base_mixed_list_match_n_singleton_fold_0 vmatch2 p off n (pm /. 2.0R) sp sv s l ();
        intro (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Singleton #t sp sv s) l @==>
               Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Singleton #t sp sv s) l)
          #emp
          fn _ {
            Iter.base_mixed_list_match_n_singleton_unfold_0 vmatch2 p off n (pm /. 2.0R) sp sv s l ();
            Iter.base_mixed_list_match_n_singleton_fold_0 vmatch1 p off n pm sp sv s l ();
          };
        rewrite each (IT.Singleton #t sp sv s) as i;
      } else {
        Iter.base_mixed_list_match_n_singleton_unfold_pos vmatch1 p off n pm sp sv s l ();
        with x y. assert (R.pts_to s #(pm *. sp) x ** vmatch1 (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1));
        R.share s;
        rewrite (R.pts_to s #((pm *. sp) /. 2.0R) x) as (R.pts_to s #((pm /. 2.0R) *. sp) x);
        rewrite (R.pts_to s #((pm *. sp) /. 2.0R) x) as (R.pts_to s #((pm /. 2.0R) *. sp) x);
        prf x (pm *. sv) y;
        rewrite (vmatch2 ((pm *. sv) /. 2.0R) x y) as (vmatch2 ((pm /. 2.0R) *. sv) x y);
        Iter.base_mixed_list_match_n_singleton_fold_pos vmatch2 p off n (pm /. 2.0R) sp sv s l ();
        intro (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Singleton #t sp sv s) l @==>
               Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Singleton #t sp sv s) l)
          #(R.pts_to s #((pm /. 2.0R) *. sp) x **
            Trade.trade (vmatch2 ((pm *. sv) /. 2.0R) x y) (vmatch1 (pm *. sv) x y))
          fn _ {
            Iter.base_mixed_list_match_n_singleton_unfold_pos vmatch2 p off n (pm /. 2.0R) sp sv s l ();
            with x2 y2. assert (R.pts_to s #((pm /. 2.0R) *. sp) x2 ** vmatch2 ((pm /. 2.0R) *. sv) x2 y2 ** pure (l == [y2] /\ off == 0 /\ n == 1));
            R.gather s;
            with xg. assert (R.pts_to s #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) xg);
            rewrite (R.pts_to s #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) xg) as (R.pts_to s #(pm *. sp) x);
            rewrite (vmatch2 ((pm /. 2.0R) *. sv) x2 y2) as (vmatch2 ((pm *. sv) /. 2.0R) x y);
            Trade.elim_trade (vmatch2 ((pm *. sv) /. 2.0R) x y) (vmatch1 (pm *. sv) x y);
            Iter.base_mixed_list_match_n_singleton_fold_pos vmatch1 p off n pm sp sv s l ();
          };
        rewrite each (IT.Singleton #t sp sv s) as i;
      }
    }
    IT.Slice sp sv s -> {
      unfold (Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Slice #t sp sv s) l);
      with l' l1. assert (S.pts_to s #(pm *. sp) l' ** PM.seq_list_match l1 l (vmatch1 (pm *. sv)) ** pure (off + n <= Seq.length l' /\ l1 == Seq.slice l' off (off + n)));
      S.share s;
      rewrite (S.pts_to s #((pm *. sp) /. 2.0R) l') as (S.pts_to s #((pm /. 2.0R) *. sp) l');
      rewrite (S.pts_to s #((pm *. sp) /. 2.0R) l') as (S.pts_to s #((pm /. 2.0R) *. sp) l');
      ghost fn prf'
        (x: t) (y: u { y << l /\ List.Tot.memP y l })
      requires vmatch1 (pm *. sv) x y
      ensures vmatch2 ((pm /. 2.0R) *. sv) x y ** Trade.trade (vmatch2 ((pm /. 2.0R) *. sv) x y) (vmatch1 (pm *. sv) x y)
      {
        prf x (pm *. sv) y;
        rewrite (vmatch2 ((pm *. sv) /. 2.0R) x y) as (vmatch2 ((pm /. 2.0R) *. sv) x y);
        rewrite (Trade.trade (vmatch2 ((pm *. sv) /. 2.0R) x y) (vmatch1 (pm *. sv) x y))
             as (Trade.trade (vmatch2 ((pm /. 2.0R) *. sv) x y) (vmatch1 (pm *. sv) x y));
      };
      seq_list_detonating_iso (vmatch1 (pm *. sv)) (vmatch2 ((pm /. 2.0R) *. sv)) l1 l prf';
      fold (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Slice #t sp sv s) l);
      intro (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Slice #t sp sv s) l @==>
             Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Slice #t sp sv s) l)
        #(S.pts_to s #((pm /. 2.0R) *. sp) l' **
          Trade.trade (PM.seq_list_match l1 l (vmatch2 ((pm /. 2.0R) *. sv))) (PM.seq_list_match l1 l (vmatch1 (pm *. sv))) **
          pure (off + n <= Seq.length l' /\ l1 == Seq.slice l' off (off + n)))
        fn _ {
          unfold (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Slice #t sp sv s) l);
          with l1_2. assert (PM.seq_list_match l1_2 l (vmatch2 ((pm /. 2.0R) *. sv)));
          S.gather s;
          with lg. assert (S.pts_to s #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) lg);
          rewrite (S.pts_to s #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) lg) as (S.pts_to s #(pm *. sp) l');
          rewrite (PM.seq_list_match l1_2 l (vmatch2 ((pm /. 2.0R) *. sv))) as (PM.seq_list_match l1 l (vmatch2 ((pm /. 2.0R) *. sv)));
          Trade.elim_trade (PM.seq_list_match l1 l (vmatch2 ((pm /. 2.0R) *. sv))) (PM.seq_list_match l1 l (vmatch1 (pm *. sv)));
          fold (Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Slice #t sp sv s) l);
        };
      rewrite each (IT.Slice #t sp sv s) as i;
    }
    IT.Serialized sp count pl -> {
      unfold (Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Serialized #t sp count pl) l);
      with l_all. assert (Iter.pts_to_parsed_strong_prefix (Iter.parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      unfold (Iter.pts_to_parsed_strong_prefix (Iter.parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      with v'. assert (S.pts_to pl #(pm *. sp) v');
      S.share pl;
      perm_mul_half pm sp;
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      fold (Iter.pts_to_parsed_strong_prefix (Iter.parse_nlist (off + n) p) pl #((pm /. 2.0R) *. sp) l_all);
      fold (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Serialized #t sp count pl) l);
      intro (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Serialized #t sp count pl) l @==>
             Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Serialized #t sp count pl) l)
        #(S.pts_to pl #((pm /. 2.0R) *. sp) v' **
          pure (PP.pts_to_parsed_strong_prefix_prop (Iter.parse_nlist (off + n) p) (reveal v') l_all /\
                l == snd (List.Tot.splitAt off l_all) /\ off + n <= SZ.v count))
        fn _ {
          unfold (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Serialized #t sp count pl) l);
          with lv2. assert (Iter.pts_to_parsed_strong_prefix (Iter.parse_nlist (off + n) p) pl #((pm /. 2.0R) *. sp) lv2);
          unfold (Iter.pts_to_parsed_strong_prefix (Iter.parse_nlist (off + n) p) pl #((pm /. 2.0R) *. sp) lv2);
          S.gather pl;
          perm_mul_half2 pm sp;
          with v'2. assert (S.pts_to pl #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) v'2);
          rewrite (S.pts_to pl #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) v'2) as (S.pts_to pl #(pm *. sp) v');
          fold (Iter.pts_to_parsed_strong_prefix (Iter.parse_nlist (off + n) p) pl #(pm *. sp) l_all);
          fold (Iter.base_mixed_list_match_n vmatch1 p off n pm (IT.Serialized #t sp count pl) l);
        };
      rewrite each (IT.Serialized #t sp count pl) as i;
    }
  }
}

#push-options "--z3rlimit 40"

ghost
fn rec mixed_list_detonating_iso_n
  (#t #u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: IT.mixed_list t)
  (l: list u)
  (prf: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch1 pm0 x y)
      (fun _ -> vmatch2 (pm0 /. 2.0R) x y ** Trade.trade (vmatch2 (pm0 /. 2.0R) x y) (vmatch1 pm0 x y))
  ))
requires Iter.mixed_list_match_n vmatch1 p off n pm i l
ensures
  Iter.mixed_list_match_n vmatch2 p off n (pm /. 2.0R) i l **
  Trade.trade (Iter.mixed_list_match_n vmatch2 p off n (pm /. 2.0R) i l) (Iter.mixed_list_match_n vmatch1 p off n pm i l)
decreases (Iter.mixed_list_depth i)
{
  match i {
    IT.Base bi -> {
      unfold (Iter.mixed_list_match_n vmatch1 p off n pm (IT.Base #t bi) l);
      base_mixed_list_detonating_iso_n vmatch1 vmatch2 p off n pm bi l prf;
      fold (Iter.mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Base #t bi) l);
      intro (Iter.mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Base #t bi) l @==>
             Iter.mixed_list_match_n vmatch1 p off n pm (IT.Base #t bi) l)
        #(Trade.trade (Iter.base_mixed_list_match_n vmatch2 p off n (pm /. 2.0R) bi l)
                      (Iter.base_mixed_list_match_n vmatch1 p off n pm bi l))
        fn _ {
          unfold (Iter.mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Base #t bi) l);
          Trade.elim_trade _ _;
          fold (Iter.mixed_list_match_n vmatch1 p off n pm (IT.Base #t bi) l);
        };
      rewrite each (IT.Base #t bi) as i;
    }
    IT.Append depth cb ca ob bp before oa ap after sc -> {
      unfold (Iter.mixed_list_match_n vmatch1 p off n pm (IT.Append #t depth cb ca ob bp before oa ap after sc) l);
      with i_before i_after l1 l2 . assert (
        R.pts_to before #(pm *. bp) i_before **
        Iter.mixed_list_match_n vmatch1 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) (pm *. sc) i_before l1 **
        R.pts_to after #(pm *. ap) i_after **
        Iter.mixed_list_match_n vmatch1 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) (pm *. sc) i_after l2
      );
      let off_b = Iter.append_off_before off (SZ.v ob) (SZ.v cb);
      let n1 = Iter.append_n_before off n (SZ.v cb);
      let off_a = Iter.append_off_after off (SZ.v oa) (SZ.v cb);
      let na = Iter.append_n_after off n (SZ.v cb);
      rewrite (Iter.mixed_list_match_n vmatch1 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) (pm *. sc) i_before l1)
        as (Iter.mixed_list_match_n vmatch1 p off_b n1 (pm *. sc) i_before l1);
      rewrite (Iter.mixed_list_match_n vmatch1 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) (pm *. sc) i_after l2)
        as (Iter.mixed_list_match_n vmatch1 p off_a na (pm *. sc) i_after l2);
      List.Tot.Properties.append_memP_forall l1 l2;
      ghost fn prf1
        (x: t) (pm0: perm) (y: u { List.Tot.memP y l1 })
      requires vmatch1 pm0 x y
      ensures vmatch2 (pm0 /. 2.0R) x y ** Trade.trade (vmatch2 (pm0 /. 2.0R) x y) (vmatch1 pm0 x y)
      {
        prf x pm0 y
      };
      ghost fn prf2
        (x: t) (pm0: perm) (y: u { List.Tot.memP y l2 })
      requires vmatch1 pm0 x y
      ensures vmatch2 (pm0 /. 2.0R) x y ** Trade.trade (vmatch2 (pm0 /. 2.0R) x y) (vmatch1 pm0 x y)
      {
        prf x pm0 y
      };
      mixed_list_detonating_iso_n vmatch1 vmatch2 p off_b n1 (pm *. sc) i_before l1 prf1;
      R.share before;
      perm_mul_half pm bp;
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      mixed_list_detonating_iso_n vmatch1 vmatch2 p off_a na (pm *. sc) i_after l2 prf2;
      R.share after;
      perm_mul_half pm ap;
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      perm_mul_half pm sc;
      rewrite (Iter.mixed_list_match_n vmatch2 p off_b n1 ((pm *. sc) /. 2.0R) i_before l1)
        as (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_before l1);
      rewrite (Iter.mixed_list_match_n vmatch2 p off_a na ((pm *. sc) /. 2.0R) i_after l2)
        as (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_after l2);
      rewrite (Trade.trade (Iter.mixed_list_match_n vmatch2 p off_b n1 ((pm *. sc) /. 2.0R) i_before l1)
                           (Iter.mixed_list_match_n vmatch1 p off_b n1 (pm *. sc) i_before l1))
        as (Trade.trade (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_before l1)
                        (Iter.mixed_list_match_n vmatch1 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) (pm *. sc) i_before l1));
      rewrite (Trade.trade (Iter.mixed_list_match_n vmatch2 p off_a na ((pm *. sc) /. 2.0R) i_after l2)
                           (Iter.mixed_list_match_n vmatch1 p off_a na (pm *. sc) i_after l2))
        as (Trade.trade (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_after l2)
                        (Iter.mixed_list_match_n vmatch1 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) (pm *. sc) i_after l2));
      fold (Iter.mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Append #t depth cb ca ob bp before oa ap after sc) l);
      intro (Iter.mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Append #t depth cb ca ob bp before oa ap after sc) l @==>
             Iter.mixed_list_match_n vmatch1 p off n pm (IT.Append #t depth cb ca ob bp before oa ap after sc) l)
        #(Trade.trade (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_before l1)
                      (Iter.mixed_list_match_n vmatch1 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) (pm *. sc) i_before l1) **
          R.pts_to before #((pm /. 2.0R) *. bp) i_before **
          Trade.trade (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_after l2)
                      (Iter.mixed_list_match_n vmatch1 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) (pm *. sc) i_after l2) **
          R.pts_to after #((pm /. 2.0R) *. ap) i_after **
          pure (
            off + n <= SZ.v cb + SZ.v ca /\
            SZ.v ob + SZ.v cb <= SZ.v (IT.mixed_list_length i_before) /\
            SZ.v oa + SZ.v ca <= SZ.v (IT.mixed_list_length i_after) /\
            List.Tot.length l1 == n1 /\
            List.Tot.length l2 == na /\
            l == List.Tot.append l1 l2 /\
            Iter.mixed_list_depth i_before < Ghost.reveal depth /\
            Iter.mixed_list_depth i_after < Ghost.reveal depth
          ))
        fn _ {
          unfold (Iter.mixed_list_match_n vmatch2 p off n (pm /. 2.0R) (IT.Append #t depth cb ca ob bp before oa ap after sc) l);
          with ib_u ia_u l1_u l2_u . assert (
            R.pts_to before #((pm /. 2.0R) *. bp) ib_u **
            Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ib_u l1_u **
            R.pts_to after #((pm /. 2.0R) *. ap) ia_u **
            Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ia_u l2_u
          );
          R.gather before;
          perm_mul_half2 pm bp;
          drop_ (pure (reveal i_before == reveal ib_u));
          rewrite (R.pts_to before #((pm /. 2.0R) *. bp +. (pm /. 2.0R) *. bp) i_before)
            as (R.pts_to before #(pm *. bp) i_before);
          R.gather after;
          perm_mul_half2 pm ap;
          drop_ (pure (reveal i_after == reveal ia_u));
          rewrite (R.pts_to after #((pm /. 2.0R) *. ap +. (pm /. 2.0R) *. ap) i_after)
            as (R.pts_to after #(pm *. ap) i_after);
          Iter.mixed_list_match_n_length vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ib_u l1_u;
          Iter.mixed_list_match_n_length vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ia_u l2_u;
          List.Tot.Properties.append_injective l1_u l1 l2_u l2;
          with ib_x . assert (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ib_x l1_u);
          slprop_rw
            (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ib_x l1_u)
            (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_before l1)
            (Pulse.Lib.Core.slprop_equiv_ext'
              (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ib_x l1_u)
              (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_before l1)
              ());
          Trade.elim_trade
            (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_before l1)
            (Iter.mixed_list_match_n vmatch1 p (Iter.append_off_before off (SZ.v ob) (SZ.v cb)) (Iter.append_n_before off n (SZ.v cb)) (pm *. sc) i_before l1);
          with ia_x . assert (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ia_x l2_u);
          slprop_rw
            (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ia_x l2_u)
            (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_after l2)
            (Pulse.Lib.Core.slprop_equiv_ext'
              (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) ia_x l2_u)
              (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_after l2)
              ());
          Trade.elim_trade
            (Iter.mixed_list_match_n vmatch2 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) ((pm /. 2.0R) *. sc) i_after l2)
            (Iter.mixed_list_match_n vmatch1 p (Iter.append_off_after off (SZ.v oa) (SZ.v cb)) (Iter.append_n_after off n (SZ.v cb)) (pm *. sc) i_after l2);
          fold (Iter.mixed_list_match_n vmatch1 p off n pm (IT.Append #t depth cb ca ob bp before oa ap after sc) l);
        };
      rewrite each (IT.Append #t depth cb ca ob bp before oa ap after sc) as i;
    }
  }
}

#pop-options

ghost
fn mixed_list_detonating_iso
  (#t #u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pm: perm) (i: IT.mixed_list t) (l: list u)
  (prf_false: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames (vmatch1 pm0 x y) (fun _ -> pure False)
  ))
requires Iter.mixed_list_match vmatch1 p pm i l
ensures exists* pm'.
  Iter.mixed_list_match vmatch2 p pm' i l **
  Trade.trade (Iter.mixed_list_match vmatch2 p pm' i l) (Iter.mixed_list_match vmatch1 p pm i l)
{
  ghost fn prf
    (x: t) (pm0: perm) (y: u { List.Tot.memP y l })
  requires vmatch1 pm0 x y
  ensures vmatch2 (pm0 /. 2.0R) x y ** Trade.trade (vmatch2 (pm0 /. 2.0R) x y) (vmatch1 pm0 x y)
  {
    prf_false x pm0 y;
    unreachable ()
  };
  unfold (Iter.mixed_list_match vmatch1 p pm i l);
  mixed_list_detonating_iso_n vmatch1 vmatch2 p 0 (SZ.v (IT.mixed_list_length i)) pm i l prf;
  fold (Iter.mixed_list_match vmatch2 p (pm /. 2.0R) i l);
  rewrite (Trade.trade (Iter.mixed_list_match_n vmatch2 p 0 (SZ.v (IT.mixed_list_length i)) (pm /. 2.0R) i l)
                       (Iter.mixed_list_match_n vmatch1 p 0 (SZ.v (IT.mixed_list_length i)) pm i l))
    as (Trade.trade (Iter.mixed_list_match vmatch2 p (pm /. 2.0R) i l)
                    (Iter.mixed_list_match vmatch1 p pm i l));
}

////////////////////////////////////////////////////////////////////////////////
// ARRAY (depth) instantiations
////////////////////////////////////////////////////////////////////////////////

let cbor_mixed_array_iterator_match_with_depth d = mixed_iter_match (cbor_match_with_depth d) parse_raw_data_item

ghost
fn mixed_array_length_facts_depth
  (depth: nat) (pm: perm) (c: cbor_mixed_list_array) (r: raw_data_item { Array? r })
requires
  cbor_match_mixed_list_array pm c r (depth_cb depth r)
ensures
  cbor_match_mixed_list_array pm c r (depth_cb depth r) **
  pure (List.Tot.length (Array?.v r) == U64.v (Array?.len r).value /\
        FStar.SizeT.fits (List.Tot.length (Array?.v r)) /\
        FStar.UInt.fits (List.Tot.length (Array?.v r)) 64)
{
  cbor_match_mixed_list_array_length pm c r (depth_cb depth r);
  unfold (cbor_match_mixed_list_array pm c r (depth_cb depth r));
  Iter.mixed_list_match_length (cbor_match_bounded r (depth_cb depth r)) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r);
  assert (pure (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length c.cbor_array_gen_ptr == LowParse.PulseParse.Iterator.Type.mixed_list_length c.cbor_array_gen_ptr));
  fold (cbor_match_mixed_list_array pm c r (depth_cb depth r));
}

// Convert the bounded element predicate of an array _Gen representation into
// the unbounded depth-indexed one, with a reverse trade. Factored out (with an
// explicit [ensures]) so the depth=0 / depth>=1 case split has a known join
// postcondition.
ghost
fn array_convert_element_vmatch
  (depth: nat) (pm: perm) (c: cbor_mixed_list_array) (r: raw_data_item { Array? r })
requires
  Iter.mixed_list_match (cbor_match_bounded r (depth_cb depth r)) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r)
ensures exists* p'.
  Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item p' c.cbor_array_gen_ptr (Array?.v r) **
  Trade.trade
    (Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item p' c.cbor_array_gen_ptr (Array?.v r))
    (Iter.mixed_list_match (cbor_match_bounded r (depth_cb depth r)) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
{
  if (depth = 0) {
    ghost
    fn prf_false
      (x: cbor_raw)
      (pm0: perm)
      (y: raw_data_item { List.Tot.memP y (Array?.v r) })
    requires cbor_match_bounded r (depth_cb depth r) pm0 x y
    ensures pure False
    {
      array_elem_precedes r y;
      cbor_match_bounded_eq r (depth_cb depth r) pm0 x y;
      rewrite (cbor_match_bounded r (depth_cb depth r) pm0 x y) as (depth_cb depth r pm0 x y);
      depth_cb_zero r pm0 x y;
      rewrite (depth_cb depth r pm0 x y) as (pure False);
    };
    mixed_list_detonating_iso
      (cbor_match_bounded r (depth_cb depth r)) (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item
      (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) prf_false;
  } else {
    ghost
    fn prf_fwd
      (x: cbor_raw)
      (pm0: perm)
      (y: raw_data_item { List.Tot.memP y (Array?.v r) })
    requires cbor_match_bounded r (depth_cb depth r) pm0 x y
    ensures cbor_match_with_depth (nat_pred depth) pm0 x y
    {
      array_elem_precedes r y;
      cbor_match_bounded_eq r (depth_cb depth r) pm0 x y;
      rewrite (cbor_match_bounded r (depth_cb depth r) pm0 x y) as (depth_cb depth r pm0 x y);
      depth_cb_succ depth r pm0 x y;
      nat_pred_succ depth;
      rewrite (depth_cb depth r pm0 x y) as (cbor_match_with_depth (nat_pred depth) pm0 x y);
    };
    Iter.mixed_list_match_weaken
      (cbor_match_bounded r (depth_cb depth r)) (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item
      (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) prf_fwd;
    intro
      (Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) @==>
       Iter.mixed_list_match (cbor_match_bounded r (depth_cb depth r)) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
      #emp
      fn _
    {
      ghost
      fn prf_bwd
        (x: cbor_raw)
        (pm0: perm)
        (y: raw_data_item { List.Tot.memP y (Array?.v r) })
      requires cbor_match_with_depth (nat_pred depth) pm0 x y
      ensures cbor_match_bounded r (depth_cb depth r) pm0 x y
      {
        array_elem_precedes r y;
        cbor_match_bounded_eq r (depth_cb depth r) pm0 x y;
        depth_cb_succ depth r pm0 x y;
        nat_pred_succ depth;
        rewrite (cbor_match_with_depth (nat_pred depth) pm0 x y) as (depth_cb depth r pm0 x y);
        rewrite (depth_cb depth r pm0 x y) as (cbor_match_bounded r (depth_cb depth r) pm0 x y);
      };
      Iter.mixed_list_match_weaken
        (cbor_match_with_depth (nat_pred depth)) (cbor_match_bounded r (depth_cb depth r)) parse_raw_data_item
        (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) prf_bwd;
    };
  }
}

ghost
fn array_to_unbounded_with_depth
  (depth: nat) (pm: perm) (c: cbor_mixed_list_array) (r: raw_data_item { Array? r })
requires
  cbor_match_mixed_list_array pm c r (depth_cb depth r)
ensures exists* p'.
  Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item p' c.cbor_array_gen_ptr (Array?.v r) **
  Trade.trade
    (Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item p' c.cbor_array_gen_ptr (Array?.v r))
    (cbor_match_mixed_list_array pm c r (depth_cb depth r)) **
  pure (FStar.SizeT.fits (List.Tot.length (Array?.v r)) /\ FStar.UInt.fits (List.Tot.length (Array?.v r)) 64)
{
  mixed_array_length_facts_depth depth pm c r;
  unfold (cbor_match_mixed_list_array pm c r (depth_cb depth r));
  array_convert_element_vmatch depth pm c r;
  with p'. assert (Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item p' c.cbor_array_gen_ptr (Array?.v r));
  intro
    (Iter.mixed_list_match (cbor_match_bounded r (depth_cb depth r)) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r) @==>
     cbor_match_mixed_list_array pm c r (depth_cb depth r))
    #emp
    fn _
  {
    fold (cbor_match_mixed_list_array pm c r (depth_cb depth r));
  };
  Trade.trans
    (Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item p' c.cbor_array_gen_ptr (Array?.v r))
    (Iter.mixed_list_match (cbor_match_bounded r (depth_cb depth r)) parse_raw_data_item (pm *. c.cbor_array_gen_perm) c.cbor_array_gen_ptr (Array?.v r))
    (cbor_match_mixed_list_array pm c r (depth_cb depth r));
}

fn cbor_mixed_array_iterator_init_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_mixed_list_array)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
  cbor_match_with_depth depth pm (CBOR_Case_Array_Gen c) r
returns res: ML.cbor_raw_mixed_iterator cbor_raw
ensures exists* p .
  cbor_mixed_array_iterator_match_with_depth (nat_pred depth) p res (Array?.v r) **
  Trade.trade
    (cbor_mixed_array_iterator_match_with_depth (nat_pred depth) p res (Array?.v r))
    (cbor_match_with_depth depth pm (CBOR_Case_Array_Gen c) r)
{
  cbor_match_with_depth_array_gen_elim depth pm c r;
  array_to_unbounded_with_depth depth pm c r;
  with p'. assert (Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item p' c.cbor_array_gen_ptr (Array?.v r));
  let res = mixed_iter_init (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item (jump_raw_data_item ())
    (cbor_match_with_depth_share_ (nat_pred depth)) (cbor_match_with_depth_gather_ (nat_pred depth)) c.cbor_array_gen_ptr
    #p' #(Array?.v r);
  Trade.trans
    (mixed_iter_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item 1.0R res (Array?.v r))
    (Iter.mixed_list_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item p' c.cbor_array_gen_ptr (Array?.v r))
    (cbor_match_mixed_list_array pm c r (depth_cb depth r));
  Trade.trans
    (mixed_iter_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item 1.0R res (Array?.v r))
    (cbor_match_mixed_list_array pm c r (depth_cb depth r))
    (cbor_match_with_depth depth pm (CBOR_Case_Array_Gen c) r);
  rewrite (mixed_iter_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item 1.0R res (Array?.v r))
    as (cbor_mixed_array_iterator_match_with_depth (nat_pred depth) 1.0R res (Array?.v r));
  rewrite
    (Trade.trade (mixed_iter_match (cbor_match_with_depth (nat_pred depth)) parse_raw_data_item 1.0R res (Array?.v r)) (cbor_match_with_depth depth pm (CBOR_Case_Array_Gen c) r))
    as (Trade.trade (cbor_mixed_array_iterator_match_with_depth (nat_pred depth) 1.0R res (Array?.v r)) (cbor_match_with_depth depth pm (CBOR_Case_Array_Gen c) r));
  res
}

let cbor_mixed_array_iterator_is_empty_with_depth d = mixed_iter_is_empty (cbor_match_with_depth d) parse_raw_data_item

let cbor_mixed_array_iterator_next_with_depth d = mixed_iter_next (cbor_match_with_depth d) parse_raw_data_item (jump_raw_data_item ()) (cbor_match_with_depth_share_ d) (cbor_match_with_depth_gather_ d) (cbor_read_zcp_with_depth d)

////////////////////////////////////////////////////////////////////////////////
// MAP (depth) instantiations
////////////////////////////////////////////////////////////////////////////////

let cbor_mixed_map_iterator_match_with_depth d = mixed_iter_match (cbor_match_map_entry_with_depth d) (nondep_then parse_raw_data_item parse_raw_data_item)

ghost
fn mixed_map_length_facts_depth
  (depth: nat) (pm: perm) (c: cbor_mixed_list_map) (r: raw_data_item { Map? r })
requires
  cbor_match_mixed_list_map pm c r (depth_cb depth r)
ensures
  cbor_match_mixed_list_map pm c r (depth_cb depth r) **
  pure (List.Tot.length (Map?.v r) == U64.v (Map?.len r).value /\
        FStar.SizeT.fits (List.Tot.length (Map?.v r)) /\
        FStar.UInt.fits (List.Tot.length (Map?.v r)) 64)
{
  cbor_match_mixed_list_map_length pm c r (depth_cb depth r);
  unfold (cbor_match_mixed_list_map pm c r (depth_cb depth r));
  Iter.mixed_list_match_length (cbor_match_map_entry_bounded r (depth_cb depth r)) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r);
  assert (pure (CBOR.Pulse.Raw.Format.MixedList.cbor_raw_mixed_list_length c.cbor_map_gen_ptr == LowParse.PulseParse.Iterator.Type.mixed_list_length c.cbor_map_gen_ptr));
  fold (cbor_match_mixed_list_map pm c r (depth_cb depth r));
}

ghost
fn map_convert_element_vmatch
  (depth: nat) (pm: perm) (c: cbor_mixed_list_map) (r: raw_data_item { Map? r })
requires
  Iter.mixed_list_match (cbor_match_map_entry_bounded r (depth_cb depth r)) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r)
ensures exists* p'.
  Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) p' c.cbor_map_gen_ptr (Map?.v r) **
  Trade.trade
    (Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) p' c.cbor_map_gen_ptr (Map?.v r))
    (Iter.mixed_list_match (cbor_match_map_entry_bounded r (depth_cb depth r)) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r))
{
  if (depth = 0) {
    ghost
    fn prf_false
      (x: cbor_map_entry)
      (pm0: perm)
      (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r) })
    requires cbor_match_map_entry_bounded r (depth_cb depth r) pm0 x y
    ensures pure False
    {
      map_elem_precedes r y;
      cbor_match_map_entry_bounded_eq r (depth_cb depth r) pm0 x y;
      rewrite (cbor_match_map_entry_bounded r (depth_cb depth r) pm0 x y)
        as (depth_cb depth r pm0 x.cbor_map_entry_key (fst y) ** depth_cb depth r pm0 x.cbor_map_entry_value (snd y));
      depth_cb_zero r pm0 x.cbor_map_entry_key (fst y);
      rewrite (depth_cb depth r pm0 x.cbor_map_entry_key (fst y)) as (pure False);
      rewrite (depth_cb depth r pm0 x.cbor_map_entry_value (snd y)) as emp;
    };
    mixed_list_detonating_iso
      (cbor_match_map_entry_bounded r (depth_cb depth r)) (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item)
      (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) prf_false;
  } else {
    ghost
    fn prf_fwd
      (x: cbor_map_entry)
      (pm0: perm)
      (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r) })
    requires cbor_match_map_entry_bounded r (depth_cb depth r) pm0 x y
    ensures cbor_match_map_entry_with_depth (nat_pred depth) pm0 x y
    {
      map_elem_precedes r y;
      cbor_match_map_entry_bounded_eq r (depth_cb depth r) pm0 x y;
      rewrite (cbor_match_map_entry_bounded r (depth_cb depth r) pm0 x y)
        as (depth_cb depth r pm0 x.cbor_map_entry_key (fst y) ** depth_cb depth r pm0 x.cbor_map_entry_value (snd y));
      depth_cb_succ depth r pm0 x.cbor_map_entry_key (fst y);
      depth_cb_succ depth r pm0 x.cbor_map_entry_value (snd y);
      nat_pred_succ depth;
      rewrite (depth_cb depth r pm0 x.cbor_map_entry_key (fst y)) as (cbor_match_with_depth (nat_pred depth) pm0 x.cbor_map_entry_key (fst y));
      rewrite (depth_cb depth r pm0 x.cbor_map_entry_value (snd y)) as (cbor_match_with_depth (nat_pred depth) pm0 x.cbor_map_entry_value (snd y));
      fold (cbor_match_map_entry_with_depth (nat_pred depth) pm0 x y);
    };
    Iter.mixed_list_match_weaken
      (cbor_match_map_entry_bounded r (depth_cb depth r)) (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item)
      (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) prf_fwd;
    intro
      (Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) @==>
       Iter.mixed_list_match (cbor_match_map_entry_bounded r (depth_cb depth r)) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r))
      #emp
      fn _
    {
      ghost
      fn prf_bwd
        (x: cbor_map_entry)
        (pm0: perm)
        (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v r) })
      requires cbor_match_map_entry_with_depth (nat_pred depth) pm0 x y
      ensures cbor_match_map_entry_bounded r (depth_cb depth r) pm0 x y
      {
        map_elem_precedes r y;
        cbor_match_map_entry_bounded_eq r (depth_cb depth r) pm0 x y;
        depth_cb_succ depth r pm0 x.cbor_map_entry_key (fst y);
        depth_cb_succ depth r pm0 x.cbor_map_entry_value (snd y);
        nat_pred_succ depth;
        unfold (cbor_match_map_entry_with_depth (nat_pred depth) pm0 x y);
        rewrite (cbor_match_with_depth (nat_pred depth) pm0 x.cbor_map_entry_key (fst y)) as (depth_cb depth r pm0 x.cbor_map_entry_key (fst y));
        rewrite (cbor_match_with_depth (nat_pred depth) pm0 x.cbor_map_entry_value (snd y)) as (depth_cb depth r pm0 x.cbor_map_entry_value (snd y));
        rewrite (depth_cb depth r pm0 x.cbor_map_entry_key (fst y) ** depth_cb depth r pm0 x.cbor_map_entry_value (snd y))
          as (cbor_match_map_entry_bounded r (depth_cb depth r) pm0 x y);
      };
      Iter.mixed_list_match_weaken
        (cbor_match_map_entry_with_depth (nat_pred depth)) (cbor_match_map_entry_bounded r (depth_cb depth r)) (nondep_then parse_raw_data_item parse_raw_data_item)
        (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) prf_bwd;
    };
  }
}

ghost
fn map_to_unbounded_with_depth
  (depth: nat) (pm: perm) (c: cbor_mixed_list_map) (r: raw_data_item { Map? r })
requires
  cbor_match_mixed_list_map pm c r (depth_cb depth r)
ensures exists* p'.
  Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) p' c.cbor_map_gen_ptr (Map?.v r) **
  Trade.trade
    (Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) p' c.cbor_map_gen_ptr (Map?.v r))
    (cbor_match_mixed_list_map pm c r (depth_cb depth r)) **
  pure (FStar.SizeT.fits (List.Tot.length (Map?.v r)) /\ FStar.UInt.fits (List.Tot.length (Map?.v r)) 64)
{
  mixed_map_length_facts_depth depth pm c r;
  unfold (cbor_match_mixed_list_map pm c r (depth_cb depth r));
  map_convert_element_vmatch depth pm c r;
  with p'. assert (Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) p' c.cbor_map_gen_ptr (Map?.v r));
  intro
    (Iter.mixed_list_match (cbor_match_map_entry_bounded r (depth_cb depth r)) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r) @==>
     cbor_match_mixed_list_map pm c r (depth_cb depth r))
    #emp
    fn _
  {
    fold (cbor_match_mixed_list_map pm c r (depth_cb depth r));
  };
  Trade.trans
    (Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) p' c.cbor_map_gen_ptr (Map?.v r))
    (Iter.mixed_list_match (cbor_match_map_entry_bounded r (depth_cb depth r)) (nondep_then parse_raw_data_item parse_raw_data_item) (pm *. c.cbor_map_gen_perm) c.cbor_map_gen_ptr (Map?.v r))
    (cbor_match_mixed_list_map pm c r (depth_cb depth r));
}

fn cbor_mixed_map_iterator_init_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_mixed_list_map)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
requires
  cbor_match_with_depth depth pm (CBOR_Case_Map_Gen c) r
returns res: ML.cbor_raw_mixed_iterator cbor_map_entry
ensures exists* p .
  cbor_mixed_map_iterator_match_with_depth (nat_pred depth) p res (Map?.v r) **
  Trade.trade
    (cbor_mixed_map_iterator_match_with_depth (nat_pred depth) p res (Map?.v r))
    (cbor_match_with_depth depth pm (CBOR_Case_Map_Gen c) r)
{
  cbor_match_with_depth_map_gen_elim depth pm c r;
  map_to_unbounded_with_depth depth pm c r;
  with p'. assert (Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) p' c.cbor_map_gen_ptr (Map?.v r));
  let res = mixed_iter_init (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item)
    (jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ()))
    (cbor_match_map_entry_with_depth_share_ (nat_pred depth)) (cbor_match_map_entry_with_depth_gather_ (nat_pred depth)) c.cbor_map_gen_ptr
    #p' #(Map?.v r);
  Trade.trans
    (mixed_iter_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) 1.0R res (Map?.v r))
    (Iter.mixed_list_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) p' c.cbor_map_gen_ptr (Map?.v r))
    (cbor_match_mixed_list_map pm c r (depth_cb depth r));
  Trade.trans
    (mixed_iter_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) 1.0R res (Map?.v r))
    (cbor_match_mixed_list_map pm c r (depth_cb depth r))
    (cbor_match_with_depth depth pm (CBOR_Case_Map_Gen c) r);
  rewrite (mixed_iter_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) 1.0R res (Map?.v r))
    as (cbor_mixed_map_iterator_match_with_depth (nat_pred depth) 1.0R res (Map?.v r));
  rewrite
    (Trade.trade (mixed_iter_match (cbor_match_map_entry_with_depth (nat_pred depth)) (nondep_then parse_raw_data_item parse_raw_data_item) 1.0R res (Map?.v r)) (cbor_match_with_depth depth pm (CBOR_Case_Map_Gen c) r))
    as (Trade.trade (cbor_mixed_map_iterator_match_with_depth (nat_pred depth) 1.0R res (Map?.v r)) (cbor_match_with_depth depth pm (CBOR_Case_Map_Gen c) r));
  res
}

let cbor_mixed_map_iterator_is_empty_with_depth d = mixed_iter_is_empty (cbor_match_map_entry_with_depth d) (nondep_then parse_raw_data_item parse_raw_data_item)

let cbor_mixed_map_iterator_next_with_depth d = mixed_iter_next (cbor_match_map_entry_with_depth d) (nondep_then parse_raw_data_item parse_raw_data_item) (jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ())) (cbor_match_map_entry_with_depth_share_ d) (cbor_match_map_entry_with_depth_gather_ d) (cbor_read_map_entry_zcp_with_depth d)
