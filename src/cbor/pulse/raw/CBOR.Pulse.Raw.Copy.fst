module CBOR.Pulse.Raw.Copy
#lang-pulse
include CBOR.Pulse.Raw.Type
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open Pulse { pts_to }

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module IT = LowParse.PulseParse.Iterator.Type

[@@erasable]
noeq
type freeable_tree = // this is necessary to define the freeable slprop by structural recursion, because cbor_freeable0 is not structurally recursive because V.vec and B.box may introduce cycles
| FTBytes
| FTBox: (b: freeable_tree) -> freeable_tree
| FTArray: (a: list freeable_tree) -> freeable_tree
| FTMap: (m: list (freeable_tree & freeable_tree)) -> freeable_tree
| FTArrayGen: (a: list freeable_tree) -> freeable_tree
| FTMapGen: (m: list (freeable_tree & freeable_tree)) -> freeable_tree
| FTUnit

noeq
type cbor_freeable0 =
| CBOR_Copy_Bytes: (v: V.vec U8.t) -> cbor_freeable0
| CBOR_Copy_Box: (b: cbor_freeable_box) -> cbor_freeable0
| CBOR_Copy_Array: (a: cbor_freeable_array) -> cbor_freeable0
| CBOR_Copy_Map: (m: cbor_freeable_map) -> cbor_freeable0
| CBOR_Copy_ArrayGen: (a: option (B.box arraygen_node)) -> cbor_freeable0
| CBOR_Copy_MapGen: (m: option (B.box mapgen_node)) -> cbor_freeable0
| CBOR_Copy_Unit

// A heap node in the spine (box-chain) of a structurally-copied (_Gen) array
// footprint. Recursion goes through [B.box] (which is [strictly_positive]), so
// the mutual inductive [cbor_freeable0] is accepted; a [Prims.list] here would
// leak (its cons cells are pure values with no [pts_to]) and is rejected by
// KaRaMeL's C backend as a garbage-collected type.
and arraygen_node = {
  ag_hd: cbor_freeable_arraygen_elt;
  ag_tl: option (B.box arraygen_node);
}

// A heap node in the spine (box-chain) of a structurally-copied (_Gen) MAP
// footprint.  Mirrors [arraygen_node]; recursion goes through [B.box]
// ([strictly_positive]) so the mutual inductive is accepted.
and mapgen_node = {
  mg_hd: cbor_freeable_mapgen_elt;
  mg_tl: option (B.box mapgen_node);
}

and cbor_freeable_box = {
  box_cbor: B.box cbor_raw; // the box turned into ref in cbor_tagged
  box_footprint: B.box cbor_freeable0; // the cbor_freeable associated to the contents of box_cbor
}

and cbor_freeable_array = {
  array_cbor: V.vec cbor_raw; // the vec turned into slice in cbor_array
  array_footprint: V.vec cbor_freeable0; // the cbor_freeable objects associated to each element of array_cbor
  array_len: (array_len: SZ.t { SZ.v array_len == V.length array_footprint });
}

and cbor_freeable_map_entry = {
  map_entry_key: cbor_freeable0;
  map_entry_value: cbor_freeable0;
}

and cbor_freeable_map = {
  map_cbor: V.vec cbor_map_entry; // the vec turned into slice in cbor_map
  map_footprint: V.vec cbor_freeable_map_entry; // the cbor_freeable objects associated to each map entry key and value of map_cbor
  map_len: (map_len: SZ.t { SZ.v map_len == V.length map_footprint });
}

// One element of a structurally-copied (_Gen) array: the element's own
// footprint, plus the three O(1) heap boxes used to build the singleton and
// the enclosing Append node (the singleton slot [age_box_elt] and the Append
// node's before/after sublist refs [age_box_before]/[age_box_after]).
and cbor_freeable_arraygen_elt = {
  age_footprint: cbor_freeable0;
  age_box_elt: B.box cbor_raw;
  age_box_before: B.box (IT.mixed_list U64.t cbor_raw);
  age_box_after: B.box (IT.mixed_list U64.t cbor_raw);
}

// One entry of a structurally-copied (_Gen) map: the key's and value's own
// footprints (like [cbor_freeable_map_entry]), plus the three O(1) heap boxes
// used to build the singleton entry and the enclosing Append node (the
// singleton slot [mge_box_elt] and the Append node's before/after sublist refs
// [mge_box_before]/[mge_box_after]).
and cbor_freeable_mapgen_elt = {
  mge_key_footprint: cbor_freeable0;
  mge_val_footprint: cbor_freeable0;
  mge_box_elt: B.box cbor_map_entry;
  mge_box_before: B.box (IT.mixed_list U64.t cbor_map_entry);
  mge_box_after: B.box (IT.mixed_list U64.t cbor_map_entry);
}

module SM = Pulse.Lib.SeqMatch.Util

// ===== spine of a structurally-copied (_Gen) array footprint =====
// A heap linked list (box-chain) of per-element footprints.  Modeled faithfully
// on [Pulse.Lib.LinkedList.is_list] and its case-analysis lemmas; hand-rolled
// rather than reusing [llist] because [llist] is not marked [strictly_positive]
// (so it cannot occur in the [cbor_freeable0] inductive), whereas [B.box] is.
// [arraygen_spine x l] owns ONLY the spine node boxes and pins the element
// sequence to the ghost list [l]; the per-element runtime resources live in a
// companion [seq_list_match] indexed by that same [l].

let rec arraygen_spine
  ([@@@mkey] x: option (B.box arraygen_node))
  (l: list cbor_freeable_arraygen_elt)
: Tot slprop
  (decreases l)
= match l with
  | [] -> pure (x == None)
  | hd :: tl -> exists* (v: B.box arraygen_node) (tail: option (B.box arraygen_node)) .
      pure (x == Some v) **
      B.pts_to v ({ ag_hd = hd; ag_tl = tail }) **
      arraygen_spine tail tl

let arraygen_spine_cases
  ([@@@mkey] x: option (B.box arraygen_node))
  (l: list cbor_freeable_arraygen_elt)
: Tot slprop
= match x with
  | None -> pure (l == [])
  | Some v -> exists* (node: arraygen_node) (tl: list cbor_freeable_arraygen_elt) .
      B.pts_to v node **
      pure (l == node.ag_hd :: tl) **
      arraygen_spine node.ag_tl tl

ghost
fn arraygen_intro_cons
  (x: option (B.box arraygen_node))
  (v: B.box arraygen_node)
  (#node: arraygen_node)
  (#tl: list cbor_freeable_arraygen_elt)
requires
  B.pts_to v node ** arraygen_spine node.ag_tl tl ** pure (x == Some v)
ensures
  arraygen_spine x (node.ag_hd :: tl)
{
  fold (arraygen_spine x (node.ag_hd :: tl));
}

ghost
fn arraygen_cases_of_spine
  (x: option (B.box arraygen_node))
  (l: list cbor_freeable_arraygen_elt)
requires
  arraygen_spine x l
ensures
  arraygen_spine_cases x l
{
  match l {
    [] -> {
      unfold (arraygen_spine x ([] <: list cbor_freeable_arraygen_elt));
      fold (arraygen_spine_cases (None #(B.box arraygen_node)) l);
      rewrite (arraygen_spine_cases (None #(B.box arraygen_node)) l)
           as (arraygen_spine_cases x l);
    }
    hd :: tl -> {
      unfold (arraygen_spine x (hd :: tl));
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      rewrite each tail as (({ ag_hd = hd; ag_tl = tail }).ag_tl) in (arraygen_spine tail tl);
      fold (arraygen_spine_cases (Some v) l);
      rewrite (arraygen_spine_cases (Some v) l)
           as (arraygen_spine_cases x l);
    }
  }
}

ghost
fn arraygen_spine_cases_none
  (x: option (B.box arraygen_node))
  (#l: list cbor_freeable_arraygen_elt)
requires
  arraygen_spine x l ** pure (x == None)
ensures
  arraygen_spine x l ** pure (l == [])
{
  match l {
    [] -> { () }
    hd :: tl -> {
      unfold (arraygen_spine x (hd :: tl));
      unreachable ()
    }
  }
}

ghost
fn arraygen_spine_cases_some
  (x: option (B.box arraygen_node))
  (v: B.box arraygen_node)
  (#l: list cbor_freeable_arraygen_elt)
requires
  arraygen_spine x l ** pure (x == Some v)
ensures
  exists* (node: arraygen_node) (tl: list cbor_freeable_arraygen_elt) .
    B.pts_to v node **
    pure (l == node.ag_hd :: tl) **
    arraygen_spine node.ag_tl tl
{
  arraygen_cases_of_spine x l;
  rewrite (arraygen_spine_cases x l) as (arraygen_spine_cases (Some v) l);
  unfold (arraygen_spine_cases (Some v) l);
}

// Allocate one spine node (O(1), no total-count allocation) and prepend it.
fn arraygen_cons
  (new_elt: cbor_freeable_arraygen_elt)
  (x: option (B.box arraygen_node))
  (#l: Ghost.erased (list cbor_freeable_arraygen_elt))
requires
  arraygen_spine x l
returns y: option (B.box arraygen_node)
ensures
  arraygen_spine y (new_elt :: l)
{
  let node : arraygen_node = { ag_hd = new_elt; ag_tl = x };
  let np = B.alloc node;
  rewrite each x as node.ag_tl in (arraygen_spine x l);
  arraygen_intro_cons (Some np) np;
  Some np
}

// [Some?] written as a [match] so C/Rust extraction compiles a tag-switch
// rather than referencing the [uu___is_Some] discriminator; the refinement
// keeps the [while]-guard fact available for the proof.
inline_for_extraction
let option_box_is_some (x: option (B.box arraygen_node))
: (b: bool { b == Some? x })
= match x with
  | None -> false
  | Some _ -> true

// ===== spine of a structurally-copied (_Gen) MAP footprint =====
// Exact mirror of [arraygen_spine] and its case-analysis helpers, for the map
// entry element type [cbor_freeable_mapgen_elt] and spine node [mapgen_node].

let rec mapgen_spine
  ([@@@mkey] x: option (B.box mapgen_node))
  (l: list cbor_freeable_mapgen_elt)
: Tot slprop
  (decreases l)
= match l with
  | [] -> pure (x == None)
  | hd :: tl -> exists* (v: B.box mapgen_node) (tail: option (B.box mapgen_node)) .
      pure (x == Some v) **
      B.pts_to v ({ mg_hd = hd; mg_tl = tail }) **
      mapgen_spine tail tl

let mapgen_spine_cases
  ([@@@mkey] x: option (B.box mapgen_node))
  (l: list cbor_freeable_mapgen_elt)
: Tot slprop
= match x with
  | None -> pure (l == [])
  | Some v -> exists* (node: mapgen_node) (tl: list cbor_freeable_mapgen_elt) .
      B.pts_to v node **
      pure (l == node.mg_hd :: tl) **
      mapgen_spine node.mg_tl tl

ghost
fn mapgen_intro_cons
  (x: option (B.box mapgen_node))
  (v: B.box mapgen_node)
  (#node: mapgen_node)
  (#tl: list cbor_freeable_mapgen_elt)
requires
  B.pts_to v node ** mapgen_spine node.mg_tl tl ** pure (x == Some v)
ensures
  mapgen_spine x (node.mg_hd :: tl)
{
  fold (mapgen_spine x (node.mg_hd :: tl));
}

ghost
fn mapgen_cases_of_spine
  (x: option (B.box mapgen_node))
  (l: list cbor_freeable_mapgen_elt)
requires
  mapgen_spine x l
ensures
  mapgen_spine_cases x l
{
  match l {
    [] -> {
      unfold (mapgen_spine x ([] <: list cbor_freeable_mapgen_elt));
      fold (mapgen_spine_cases (None #(B.box mapgen_node)) l);
      rewrite (mapgen_spine_cases (None #(B.box mapgen_node)) l)
           as (mapgen_spine_cases x l);
    }
    hd :: tl -> {
      unfold (mapgen_spine x (hd :: tl));
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      rewrite each tail as (({ mg_hd = hd; mg_tl = tail }).mg_tl) in (mapgen_spine tail tl);
      fold (mapgen_spine_cases (Some v) l);
      rewrite (mapgen_spine_cases (Some v) l)
           as (mapgen_spine_cases x l);
    }
  }
}

ghost
fn mapgen_spine_cases_none
  (x: option (B.box mapgen_node))
  (#l: list cbor_freeable_mapgen_elt)
requires
  mapgen_spine x l ** pure (x == None)
ensures
  mapgen_spine x l ** pure (l == [])
{
  match l {
    [] -> { () }
    hd :: tl -> {
      unfold (mapgen_spine x (hd :: tl));
      unreachable ()
    }
  }
}

ghost
fn mapgen_spine_cases_some
  (x: option (B.box mapgen_node))
  (v: B.box mapgen_node)
  (#l: list cbor_freeable_mapgen_elt)
requires
  mapgen_spine x l ** pure (x == Some v)
ensures
  exists* (node: mapgen_node) (tl: list cbor_freeable_mapgen_elt) .
    B.pts_to v node **
    pure (l == node.mg_hd :: tl) **
    mapgen_spine node.mg_tl tl
{
  mapgen_cases_of_spine x l;
  rewrite (mapgen_spine_cases x l) as (mapgen_spine_cases (Some v) l);
  unfold (mapgen_spine_cases (Some v) l);
}

// Allocate one spine node (O(1), no total-count allocation) and prepend it.
fn mapgen_cons
  (new_elt: cbor_freeable_mapgen_elt)
  (x: option (B.box mapgen_node))
  (#l: Ghost.erased (list cbor_freeable_mapgen_elt))
requires
  mapgen_spine x l
returns y: option (B.box mapgen_node)
ensures
  mapgen_spine y (new_elt :: l)
{
  let node : mapgen_node = { mg_hd = new_elt; mg_tl = x };
  let np = B.alloc node;
  rewrite each x as node.mg_tl in (mapgen_spine x l);
  mapgen_intro_cons (Some np) np;
  Some np
}

inline_for_extraction
let option_mapbox_is_some (x: option (B.box mapgen_node))
: (b: bool { b == Some? x })
= match x with
  | None -> false
  | Some _ -> true

let rec freeable_match'
  (x: cbor_freeable0)
  (ft: freeable_tree)
: Tot slprop
  (decreases ft)
= match x, ft with
  | CBOR_Copy_Bytes ve, FTBytes -> exists* (v: Seq.seq U8.t) . pts_to ve v ** pure (V.is_full_vec ve)
  | CBOR_Copy_Box bx, FTBox ft' -> exists* (v: cbor_raw) (x': cbor_freeable0) . pts_to bx.box_cbor v ** pts_to bx.box_footprint x' ** freeable_match' x' ft'
  | CBOR_Copy_Array ar, FTArray ft' -> exists* (v: Seq.seq cbor_raw) (x': Seq.seq cbor_freeable0) . pts_to ar.array_cbor v ** pts_to ar.array_footprint x' ** SM.seq_list_match x' ft' freeable_match' ** pure (V.is_full_vec ar.array_cbor /\ V.is_full_vec ar.array_footprint)
  | CBOR_Copy_Map m, FTMap ft' -> exists* (v: Seq.seq cbor_map_entry) (x': Seq.seq cbor_freeable_map_entry) . pts_to m.map_cbor v ** pts_to m.map_footprint x' ** SM.seq_list_match x' ft' (freeable_match_map_entry' ft freeable_match') ** pure (V.is_full_vec m.map_cbor /\ V.is_full_vec m.map_footprint)
  | CBOR_Copy_ArrayGen ag, FTArrayGen ft' -> exists* (agl: list cbor_freeable_arraygen_elt) . arraygen_spine ag agl ** SM.seq_list_match (Seq.seq_of_list agl) ft' (freeable_match_arraygen_elt' ft freeable_match')
  | CBOR_Copy_MapGen mg, FTMapGen ft' -> exists* (mgl: list cbor_freeable_mapgen_elt) . mapgen_spine mg mgl ** SM.seq_list_match (Seq.seq_of_list mgl) ft' (freeable_match_mapgen_elt' ft freeable_match')
  | CBOR_Copy_Unit, FTUnit -> emp
  | _ -> pure False
    
and freeable_match_map_entry'
  (r0: freeable_tree)
  (freeable_match: (cbor_freeable0 -> (v': freeable_tree { v' << r0 }) -> slprop))
  (c: cbor_freeable_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
: Tot slprop
  (decreases r)
= freeable_match' c.map_entry_key (fst r) **
  freeable_match' c.map_entry_value (snd r)

and freeable_match_arraygen_elt'
  (r0: freeable_tree)
  (freeable_match: (cbor_freeable0 -> (v': freeable_tree { v' << r0 }) -> slprop))
  (c: cbor_freeable_arraygen_elt)
  (r: freeable_tree { r << r0 })
: Tot slprop
  (decreases r)
= freeable_match c.age_footprint r **
  (exists* (w: cbor_raw) . R.pts_to (B.box_to_ref c.age_box_elt) w) **
  (exists* (wb wa: IT.mixed_list U64.t cbor_raw) . R.pts_to (B.box_to_ref c.age_box_before) wb ** R.pts_to (B.box_to_ref c.age_box_after) wa) **
  pure (R.is_full_ref (B.box_to_ref c.age_box_elt) /\ R.is_full_ref (B.box_to_ref c.age_box_before) /\ R.is_full_ref (B.box_to_ref c.age_box_after))

and freeable_match_mapgen_elt'
  (r0: freeable_tree)
  (freeable_match: (cbor_freeable0 -> (v': freeable_tree { v' << r0 }) -> slprop))
  (c: cbor_freeable_mapgen_elt)
  (r: (freeable_tree & freeable_tree) { r << r0 })
: Tot slprop
  (decreases r)
= freeable_match' c.mge_key_footprint (fst r) **
  freeable_match' c.mge_val_footprint (snd r) **
  (exists* (w: cbor_map_entry) . R.pts_to (B.box_to_ref c.mge_box_elt) w) **
  (exists* (wb wa: IT.mixed_list U64.t cbor_map_entry) . R.pts_to (B.box_to_ref c.mge_box_before) wb ** R.pts_to (B.box_to_ref c.mge_box_after) wa) **
  pure (R.is_full_ref (B.box_to_ref c.mge_box_elt) /\ R.is_full_ref (B.box_to_ref c.mge_box_before) /\ R.is_full_ref (B.box_to_ref c.mge_box_after))

let freeable_match_box
  (bx: cbor_freeable_box)
  (ft': freeable_tree)
: Tot slprop
= exists* (v: cbor_raw) (x': cbor_freeable0) . pts_to bx.box_cbor v ** pts_to bx.box_footprint x' ** freeable_match' x' ft'

let freeable_match_box_eq
  (bx: cbor_freeable_box)
  (ft': freeable_tree)
: Lemma
  (freeable_match' (CBOR_Copy_Box bx) (FTBox ft') == freeable_match_box bx ft')
= assert_norm (freeable_match' (CBOR_Copy_Box bx) (FTBox ft') == freeable_match_box bx ft')

let freeable_match_map_entry
  (c: cbor_freeable_map_entry)
  (r: (freeable_tree & freeable_tree))
: Tot slprop
  (decreases r)
= freeable_match' c.map_entry_key (fst r) **
  freeable_match' c.map_entry_value (snd r)

ghost
fn freeable_match_map_entry_weaken
  (r0: freeable_tree)
  (c: cbor_freeable_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
requires
  freeable_match_map_entry' r0 freeable_match' c r
ensures
  freeable_match_map_entry c r
{
  unfold (freeable_match_map_entry' r0 freeable_match' c r);
  fold (freeable_match_map_entry c r)
}

let ftmap_precedes'
  (r: freeable_tree { FTMap? r })
: Lemma
  (FTMap?.m r << r)
= ()

let ftmap_precedes
  (r0: list (freeable_tree & freeable_tree))
: Lemma
  (ensures (r0 << FTMap r0))
  [SMTPat (FTMap r0)]
= ftmap_precedes' (FTMap r0)

let ftbox_precedes'
  (r: freeable_tree { FTBox? r })
: Lemma
  (FTBox?.b r << r)
= ()

let ftbox_precedes
  (r0: freeable_tree)
: Lemma
  (ensures (r0 << FTBox r0))
  [SMTPat (FTBox r0)]
= ftbox_precedes' (FTBox r0)

let ftarray_precedes'
  (r: freeable_tree { FTArray? r })
: Lemma
  (FTArray?.a r << r)
= ()

let ftarray_precedes
  (r0: list freeable_tree)
: Lemma
  (ensures (r0 << FTArray r0))
  [SMTPat (FTArray r0)]
= ftarray_precedes' (FTArray r0)

// ===== structural (_Gen) array element footprint helpers =====

// Standalone element match (unrefined tree arg): used by the build loop (as a
// fixed item_match for [seq_list_match], independent of the whole tree) and by
// the recursive free.  Mirrors [freeable_match_arraygen_elt'] with the
// recursive knot instantiated to [freeable_match'].
let freeable_match_arraygen_elt
  (c: cbor_freeable_arraygen_elt)
  (r: freeable_tree)
: Tot slprop
= freeable_match' c.age_footprint r **
  (exists* (w: cbor_raw) . R.pts_to (B.box_to_ref c.age_box_elt) w) **
  (exists* (wb wa: IT.mixed_list U64.t cbor_raw) . R.pts_to (B.box_to_ref c.age_box_before) wb ** R.pts_to (B.box_to_ref c.age_box_after) wa) **
  pure (R.is_full_ref (B.box_to_ref c.age_box_elt) /\ R.is_full_ref (B.box_to_ref c.age_box_before) /\ R.is_full_ref (B.box_to_ref c.age_box_after))

ghost
fn freeable_match_arraygen_elt_weaken
  (r0: freeable_tree)
  (c: cbor_freeable_arraygen_elt)
  (r: freeable_tree { r << r0 })
requires
  freeable_match_arraygen_elt' r0 freeable_match' c r
ensures
  freeable_match_arraygen_elt c r
{
  unfold (freeable_match_arraygen_elt' r0 freeable_match' c r);
  fold (freeable_match_arraygen_elt c r)
}

let ftarraygen_precedes'
  (r: freeable_tree { FTArrayGen? r })
: Lemma
  (FTArrayGen?.a r << r)
= ()

let ftarraygen_precedes
  (r0: list freeable_tree)
: Lemma
  (ensures (r0 << FTArrayGen r0))
  [SMTPat (FTArrayGen r0)]
= ftarraygen_precedes' (FTArrayGen r0)

ghost
fn freeable_match_arraygen_elt_weaken_recip
  (r0: list freeable_tree)
  (c: cbor_freeable_arraygen_elt)
  (r: freeable_tree { r << r0 })
requires
  freeable_match_arraygen_elt c r
ensures
  freeable_match_arraygen_elt' (FTArrayGen r0) freeable_match' c r
{
  unfold (freeable_match_arraygen_elt c r);
  fold (freeable_match_arraygen_elt' (FTArrayGen r0) freeable_match' c r);
}

ghost
fn freeable_match_map_entry_weaken_recip
  (r0: list (freeable_tree & freeable_tree))
  (c: cbor_freeable_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
requires
  freeable_match_map_entry c r
ensures
  freeable_match_map_entry' (FTMap r0) freeable_match' c r
{
  unfold (freeable_match_map_entry c r);
  fold (freeable_match_map_entry' (FTMap r0) freeable_match' c r);
}

// ===== structural (_Gen) map entry footprint helpers =====

// Standalone entry match (unrefined tree arg): mirrors
// [freeable_match_mapgen_elt'] with the recursive knot instantiated to
// [freeable_match'].  Owns BOTH the key and value footprints plus the three
// O(1) build boxes.
let freeable_match_mapgen_elt
  (c: cbor_freeable_mapgen_elt)
  (r: (freeable_tree & freeable_tree))
: Tot slprop
= freeable_match' c.mge_key_footprint (fst r) **
  freeable_match' c.mge_val_footprint (snd r) **
  (exists* (w: cbor_map_entry) . R.pts_to (B.box_to_ref c.mge_box_elt) w) **
  (exists* (wb wa: IT.mixed_list U64.t cbor_map_entry) . R.pts_to (B.box_to_ref c.mge_box_before) wb ** R.pts_to (B.box_to_ref c.mge_box_after) wa) **
  pure (R.is_full_ref (B.box_to_ref c.mge_box_elt) /\ R.is_full_ref (B.box_to_ref c.mge_box_before) /\ R.is_full_ref (B.box_to_ref c.mge_box_after))

ghost
fn freeable_match_mapgen_elt_weaken
  (r0: freeable_tree)
  (c: cbor_freeable_mapgen_elt)
  (r: (freeable_tree & freeable_tree) { r << r0 })
requires
  freeable_match_mapgen_elt' r0 freeable_match' c r
ensures
  freeable_match_mapgen_elt c r
{
  unfold (freeable_match_mapgen_elt' r0 freeable_match' c r);
  fold (freeable_match_mapgen_elt c r)
}

let ftmapgen_precedes'
  (r: freeable_tree { FTMapGen? r })
: Lemma
  (FTMapGen?.m r << r)
= ()

let ftmapgen_precedes
  (r0: list (freeable_tree & freeable_tree))
: Lemma
  (ensures (r0 << FTMapGen r0))
  [SMTPat (FTMapGen r0)]
= ftmapgen_precedes' (FTMapGen r0)

ghost
fn freeable_match_mapgen_elt_weaken_recip
  (r0: list (freeable_tree & freeable_tree))
  (c: cbor_freeable_mapgen_elt)
  (r: (freeable_tree & freeable_tree) { r << r0 })
requires
  freeable_match_mapgen_elt c r
ensures
  freeable_match_mapgen_elt' (FTMapGen r0) freeable_match' c r
{
  unfold (freeable_match_mapgen_elt c r);
  fold (freeable_match_mapgen_elt' (FTMapGen r0) freeable_match' c r);
}

// [hd]/[tl] and the two component trees of the head entry all strictly precede
// the whole [(tree & tree)] list, so the per-entry [cbor_free'] calls (on the
// key and value footprints) terminate against [bound == ft].
let mapgen_hd_tree_precedes
  (l: list (freeable_tree & freeable_tree) { Cons? l })
: Lemma
  (List.Tot.hd l << l /\ List.Tot.tl l << l /\
   fst (List.Tot.hd l) << l /\ snd (List.Tot.hd l) << l)
= ()

let freeable_match'_cases_pred
  (x: cbor_freeable0)
  (ft: freeable_tree)
: GTot bool
  (decreases ft)
= match x, ft with
  | CBOR_Copy_Bytes _, FTBytes
  | CBOR_Copy_Box _, FTBox _
  | CBOR_Copy_Array _, FTArray _
  | CBOR_Copy_Map _, FTMap _
  | CBOR_Copy_ArrayGen _, FTArrayGen _
  | CBOR_Copy_MapGen _, FTMapGen _
  | CBOR_Copy_Unit, FTUnit
   -> true
  | _ -> false

ghost
fn freeable_match'_cases
  (x: cbor_freeable0)
  (ft: freeable_tree)
requires
  freeable_match' x ft
ensures
  freeable_match' x ft ** pure (freeable_match'_cases_pred x ft)
{
  let test = freeable_match'_cases_pred x ft;
  if test {
    ()
  } else {
    rewrite (freeable_match' x ft) as (pure False);
    rewrite emp as (freeable_match' x ft); //  by contradiction
  }
}

inline_for_extraction
let cbor_free'_t (bound: freeable_tree) =
  (x: cbor_freeable0) ->
  (ft: freeable_tree { ft << bound }) ->
  stt unit
    (freeable_match' x ft)
    (fun _ -> emp)

inline_for_extraction
fn cbor_free_map_entry
  (bound: freeable_tree)
  (cbor_free': cbor_free'_t bound)
  (x: cbor_freeable_map_entry)
  (ft: Ghost.erased (freeable_tree & freeable_tree) { fst (Ghost.reveal ft) << bound /\ snd (Ghost.reveal ft) << bound })
requires
    (freeable_match_map_entry x ft)
ensures
    (emp)
{
  unfold (freeable_match_map_entry x ft);
  cbor_free' x.map_entry_key (fst (Ghost.reveal ft));
  cbor_free' x.map_entry_value (snd (Ghost.reveal ft));
}

inline_for_extraction
fn free_arraygen_box
  (#t: Type0)
  (b: B.box t)
requires
  (exists* (w: t) . R.pts_to (B.box_to_ref b) w) ** pure (R.is_full_ref (B.box_to_ref b))
ensures
  emp
{
  with w. assert (R.pts_to (B.box_to_ref b) w);
  B.to_box_pts_to b;
  B.free b;
}

let arraygen_hd_precedes
  (l: list freeable_tree { Cons? l })
: Lemma
  (List.Tot.hd l << l /\ List.Tot.tl l << l)
= ()

// NOTE: the per-element free walk over a [CBOR_Copy_ArrayGen] footprint spine is
// inlined as a [while]-loop directly inside the [CBOR_Copy_ArrayGen] arm of
// [cbor_free'] below (mirroring the [CBOR_Copy_Array]/[CBOR_Copy_Map] arms).
// A recursive higher-order helper taking [cbor_free'] as a partially-applied
// argument does NOT extract (KaRaMeL Warning 16: cannot enforce arity at the
// call-site for a partial application of a recursive function).

fn rec cbor_free'
  (bound: freeable_tree)
  (x: cbor_freeable0)
  (ft: freeable_tree { ft << bound })
requires
  freeable_match' x ft
ensures
  emp
decreases bound
{
  freeable_match'_cases x ft;
  match x {
    CBOR_Copy_Unit -> {
      rewrite each ft as FTUnit;
      unfold (freeable_match' CBOR_Copy_Unit FTUnit);
      ()
    }
    CBOR_Copy_Bytes v -> {
      rewrite each ft as FTBytes;
      unfold (freeable_match' (CBOR_Copy_Bytes v) FTBytes);
      V.free v
    }
    CBOR_Copy_Box b -> {
      let ft' = Ghost.hide (FTBox?.b ft);
      rewrite each ft as (FTBox ft');
      unfold (freeable_match' (CBOR_Copy_Box b) (FTBox ft'));
      B.free b.box_cbor;
      let b' = ((let open Pulse.Lib.Box in ( ! )) b.box_footprint);
      cbor_free' ft b' _;
      B.free b.box_footprint
    }
    CBOR_Copy_Array a -> {
      let ft' = Ghost.hide (FTArray?.a ft);
      rewrite each ft as (FTArray ft');
      unfold (freeable_match' (CBOR_Copy_Array a) (FTArray ft'));
      V.free a.array_cbor;
      with s . assert (pts_to a.array_footprint s ** SM.seq_list_match s ft' freeable_match');
      V.pts_to_len a.array_footprint;
      SM.seq_list_match_length freeable_match' s ft';
      SM.seq_list_match_seq_seq_match freeable_match' s ft';
      let len = a.array_len;
      let mut pi = 0sz;
      while (
        let i = !pi;
        (SZ.lt i len)
      ) invariant exists* i . (
        pts_to a.array_footprint s **
        pts_to pi i **
        SM.seq_seq_match freeable_match' s (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v i) (SZ.v len) **
        pure (
          SZ.v i <= SZ.v len /\
          SZ.v len == List.Tot.length (Ghost.reveal ft') /\
          Ghost.reveal ft == FTArray (Ghost.reveal ft')
        )
      ) {
        let i = !pi;
        SM.seq_seq_match_dequeue_left freeable_match' s (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v i) (SZ.v len);
        let x' = V.op_Array_Access a.array_footprint i;
        rewrite (freeable_match' (Seq.index s (SZ.v i)) (Seq.index (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v i)))
             as (freeable_match' x' (Seq.index (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v i)));
        FStar.List.Tot.Properties.memP_precedes (List.Tot.index (Ghost.reveal ft') (SZ.v i)) (Ghost.reveal ft');
        cbor_free' ft x' _;
        pi := (SZ.add i 1sz);
      };
      SM.seq_seq_match_empty_elim freeable_match' s (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v len);
      V.free a.array_footprint
    }
    CBOR_Copy_Map a -> {
      let ft' = Ghost.hide (FTMap?.m ft);
      rewrite each ft as (FTMap ft');
      unfold (freeable_match' (CBOR_Copy_Map a) (FTMap ft'));
      V.free a.map_cbor;
      with s . assert (pts_to a.map_footprint s ** SM.seq_list_match s ft' (freeable_match_map_entry' ft freeable_match'));
      SM.seq_list_match_weaken s ft' (freeable_match_map_entry' ft freeable_match') freeable_match_map_entry (freeable_match_map_entry_weaken ft);
      V.pts_to_len a.map_footprint;
      SM.seq_list_match_length freeable_match_map_entry s ft';
      SM.seq_list_match_seq_seq_match freeable_match_map_entry s ft';
      let len = a.map_len;
      let mut pi = 0sz;
      while (
        let i = !pi;
        (SZ.lt i len)
      ) invariant exists* i . (
        pts_to a.map_footprint s **
        pts_to pi i **
        SM.seq_seq_match freeable_match_map_entry s (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v i) (SZ.v len) **
        pure (
          SZ.v i <= SZ.v len /\
          SZ.v len == List.Tot.length (Ghost.reveal ft') /\
          Ghost.reveal ft == FTMap (Ghost.reveal ft')
        )
      ) {
        let i = !pi;
        SM.seq_seq_match_dequeue_left freeable_match_map_entry s (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v i) (SZ.v len);
        let x' = V.op_Array_Access a.map_footprint i;
        rewrite (freeable_match_map_entry (Seq.index s (SZ.v i)) (Seq.index (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v i)))
             as (freeable_match_map_entry x' (Seq.index (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v i)));
        FStar.List.Tot.Properties.memP_precedes (List.Tot.index (Ghost.reveal ft') (SZ.v i)) (Ghost.reveal ft');
        cbor_free_map_entry ft (cbor_free' ft) x' _;
        pi := (SZ.add i 1sz);
      };
      SM.seq_seq_match_empty_elim freeable_match_map_entry s (Seq.seq_of_list (Ghost.reveal ft')) (SZ.v len);
      V.free a.map_footprint
    }
    CBOR_Copy_ArrayGen ag -> {
      let ft' = Ghost.hide (FTArrayGen?.a ft);
      rewrite each ft as (FTArrayGen ft');
      unfold (freeable_match' (CBOR_Copy_ArrayGen ag) (FTArrayGen ft'));
      with agl. assert (
        arraygen_spine ag agl **
        SM.seq_list_match (Seq.seq_of_list agl) (Ghost.reveal ft') (freeable_match_arraygen_elt' ft freeable_match')
      );
      SM.seq_list_match_weaken (Seq.seq_of_list agl) (Ghost.reveal ft') (freeable_match_arraygen_elt' ft freeable_match') freeable_match_arraygen_elt (freeable_match_arraygen_elt_weaken ft);
      // Walk the spine box-chain, synchronized (via the shared ghost element
      // list) with the companion [seq_list_match] carrying the per-element
      // resources.  Each iteration frees one element (via a FULLY-APPLIED
      // [cbor_free']), its three scratch boxes and its spine node box.
      // No recursive higher-order helper => extraction is happy (no Warning 16).
      ftarraygen_precedes (Ghost.reveal ft');
      let mut phead = ag;
      while (
        let h = !phead;
        option_box_is_some h
      )
      invariant exists* (h: option (B.box arraygen_node)) (r_ag: list cbor_freeable_arraygen_elt) (r_ft: list freeable_tree).
        pts_to phead h **
        arraygen_spine h r_ag **
        SM.seq_list_match (Seq.seq_of_list r_ag) r_ft freeable_match_arraygen_elt **
        pure (r_ft << ft)
      {
        with h0 r_ag0 r_ft0. assert (
          pts_to phead h0 **
          arraygen_spine h0 r_ag0 **
          SM.seq_list_match (Seq.seq_of_list r_ag0) r_ft0 freeable_match_arraygen_elt **
          pure (r_ft0 << ft)
        );
        let h = !phead;
        match h {
          None -> {
            unreachable ()
          }
          Some v -> {
            // [h == Some v] (branch) and [h == h0] (read) => [h0 == Some v]
            arraygen_spine_cases_some h v;
            with gnode gtl. assert (
              B.pts_to v gnode **
              arraygen_spine gnode.ag_tl gtl **
              pure (r_ag0 == gnode.ag_hd :: gtl)
            );
            let node_v = ((let open Pulse.Lib.Box in ( ! )) v); // node_v == gnode
            rewrite (SM.seq_list_match (Seq.seq_of_list r_ag0) r_ft0 freeable_match_arraygen_elt)
                 as (SM.seq_list_match (Seq.seq_of_list (gnode.ag_hd :: gtl)) r_ft0 freeable_match_arraygen_elt);
            Seq.lemma_seq_of_list_induction (gnode.ag_hd :: gtl);
            let _sq = SM.seq_list_match_cons_elim (Seq.seq_of_list (gnode.ag_hd :: gtl)) r_ft0 freeable_match_arraygen_elt;
            arraygen_hd_precedes r_ft0;
            rewrite (freeable_match_arraygen_elt (Seq.head (Seq.seq_of_list (gnode.ag_hd :: gtl))) (List.Tot.hd r_ft0))
                 as (freeable_match_arraygen_elt node_v.ag_hd (List.Tot.hd r_ft0));
            unfold (freeable_match_arraygen_elt node_v.ag_hd (List.Tot.hd r_ft0));
            cbor_free' ft node_v.ag_hd.age_footprint (List.Tot.hd r_ft0);
            free_arraygen_box node_v.ag_hd.age_box_elt;
            free_arraygen_box node_v.ag_hd.age_box_before;
            free_arraygen_box node_v.ag_hd.age_box_after;
            B.free v;
            rewrite (SM.seq_list_match (Seq.tail (Seq.seq_of_list (gnode.ag_hd :: gtl))) (List.Tot.tl r_ft0) freeable_match_arraygen_elt)
                 as (SM.seq_list_match (Seq.seq_of_list gtl) (List.Tot.tl r_ft0) freeable_match_arraygen_elt);
            rewrite each gnode.ag_tl as node_v.ag_tl in (arraygen_spine gnode.ag_tl gtl);
            phead := node_v.ag_tl;
          }
        }
      };
      // loop exit: [h == None], so the spine and its element list are empty
      with hlast r_ag1 r_ft1. assert (
        pts_to phead hlast **
        arraygen_spine hlast r_ag1 **
        SM.seq_list_match (Seq.seq_of_list r_ag1) r_ft1 freeable_match_arraygen_elt
      );
      arraygen_spine_cases_none hlast;
      rewrite (SM.seq_list_match (Seq.seq_of_list r_ag1) r_ft1 freeable_match_arraygen_elt)
           as (SM.seq_list_match (Seq.seq_of_list []) r_ft1 freeable_match_arraygen_elt);
      SM.seq_list_match_nil_elim (Seq.seq_of_list []) r_ft1 freeable_match_arraygen_elt;
      rewrite (arraygen_spine hlast r_ag1) as (arraygen_spine hlast ([] <: list cbor_freeable_arraygen_elt));
      unfold (arraygen_spine hlast ([] <: list cbor_freeable_arraygen_elt));
    }
    CBOR_Copy_MapGen mg -> {
      let ft' = Ghost.hide (FTMapGen?.m ft);
      rewrite each ft as (FTMapGen ft');
      unfold (freeable_match' (CBOR_Copy_MapGen mg) (FTMapGen ft'));
      with mgl. assert (
        mapgen_spine mg mgl **
        SM.seq_list_match (Seq.seq_of_list mgl) (Ghost.reveal ft') (freeable_match_mapgen_elt' ft freeable_match')
      );
      SM.seq_list_match_weaken (Seq.seq_of_list mgl) (Ghost.reveal ft') (freeable_match_mapgen_elt' ft freeable_match') freeable_match_mapgen_elt (freeable_match_mapgen_elt_weaken ft);
      // Walk the spine box-chain, freeing per entry the key and value footprints
      // (two FULLY-APPLIED [cbor_free'] calls), the three scratch boxes and the
      // spine node box.  No higher-order recursive helper => no Warning 16.
      ftmapgen_precedes (Ghost.reveal ft');
      let mut phead = mg;
      while (
        let h = !phead;
        option_mapbox_is_some h
      )
      invariant exists* (h: option (B.box mapgen_node)) (r_mg: list cbor_freeable_mapgen_elt) (r_ft: list (freeable_tree & freeable_tree)).
        pts_to phead h **
        mapgen_spine h r_mg **
        SM.seq_list_match (Seq.seq_of_list r_mg) r_ft freeable_match_mapgen_elt **
        pure (r_ft << ft)
      {
        with h0 r_mg0 r_ft0. assert (
          pts_to phead h0 **
          mapgen_spine h0 r_mg0 **
          SM.seq_list_match (Seq.seq_of_list r_mg0) r_ft0 freeable_match_mapgen_elt **
          pure (r_ft0 << ft)
        );
        let h = !phead;
        match h {
          None -> {
            unreachable ()
          }
          Some v -> {
            mapgen_spine_cases_some h v;
            with gnode gtl. assert (
              B.pts_to v gnode **
              mapgen_spine gnode.mg_tl gtl **
              pure (r_mg0 == gnode.mg_hd :: gtl)
            );
            let node_v = ((let open Pulse.Lib.Box in ( ! )) v); // node_v == gnode
            rewrite (SM.seq_list_match (Seq.seq_of_list r_mg0) r_ft0 freeable_match_mapgen_elt)
                 as (SM.seq_list_match (Seq.seq_of_list (gnode.mg_hd :: gtl)) r_ft0 freeable_match_mapgen_elt);
            Seq.lemma_seq_of_list_induction (gnode.mg_hd :: gtl);
            let _sq = SM.seq_list_match_cons_elim (Seq.seq_of_list (gnode.mg_hd :: gtl)) r_ft0 freeable_match_mapgen_elt;
            mapgen_hd_tree_precedes r_ft0;
            rewrite (freeable_match_mapgen_elt (Seq.head (Seq.seq_of_list (gnode.mg_hd :: gtl))) (List.Tot.hd r_ft0))
                 as (freeable_match_mapgen_elt node_v.mg_hd (List.Tot.hd r_ft0));
            unfold (freeable_match_mapgen_elt node_v.mg_hd (List.Tot.hd r_ft0));
            cbor_free' ft node_v.mg_hd.mge_key_footprint (fst (List.Tot.hd r_ft0));
            cbor_free' ft node_v.mg_hd.mge_val_footprint (snd (List.Tot.hd r_ft0));
            free_arraygen_box node_v.mg_hd.mge_box_elt;
            free_arraygen_box node_v.mg_hd.mge_box_before;
            free_arraygen_box node_v.mg_hd.mge_box_after;
            B.free v;
            rewrite (SM.seq_list_match (Seq.tail (Seq.seq_of_list (gnode.mg_hd :: gtl))) (List.Tot.tl r_ft0) freeable_match_mapgen_elt)
                 as (SM.seq_list_match (Seq.seq_of_list gtl) (List.Tot.tl r_ft0) freeable_match_mapgen_elt);
            rewrite each gnode.mg_tl as node_v.mg_tl in (mapgen_spine gnode.mg_tl gtl);
            phead := node_v.mg_tl;
          }
        }
      };
      with hlast r_mg1 r_ft1. assert (
        pts_to phead hlast **
        mapgen_spine hlast r_mg1 **
        SM.seq_list_match (Seq.seq_of_list r_mg1) r_ft1 freeable_match_mapgen_elt
      );
      mapgen_spine_cases_none hlast;
      rewrite (SM.seq_list_match (Seq.seq_of_list r_mg1) r_ft1 freeable_match_mapgen_elt)
           as (SM.seq_list_match (Seq.seq_of_list []) r_ft1 freeable_match_mapgen_elt);
      SM.seq_list_match_nil_elim (Seq.seq_of_list []) r_ft1 freeable_match_mapgen_elt;
      rewrite (mapgen_spine hlast r_mg1) as (mapgen_spine hlast ([] <: list cbor_freeable_mapgen_elt));
      unfold (mapgen_spine hlast ([] <: list cbor_freeable_mapgen_elt));
    }
  }
}

noeq
type cbor_freeable = {
  cbor: cbor_raw;
  footprint: cbor_freeable0;
  tree: freeable_tree;
}

let freeable (f: cbor_freeable) : Tot slprop = freeable_match' f.footprint f.tree

fn cbor_free0
  (x: cbor_freeable)
requires
  freeable x
ensures
  emp
{
  unfold (freeable x);
  cbor_free' (FTBox x.tree) x.footprint _
}

open CBOR.Pulse.Raw.Read
module Trade = Pulse.Lib.Trade.Util
module ML = CBOR.Pulse.Raw.Format.MixedList
module IO = LowParse.PulseParse.Iterator.IntOps
module Match = CBOR.Pulse.Raw.Match
module AB = CBOR.Pulse.Raw.EverParse.ArrayBuilder
module I = LowParse.PulseParse.Iterator
module Append = LowParse.PulseParse.Iterator.Append
module MB = CBOR.Pulse.Raw.EverParse.MapBuilder
module MP = CBOR.Pulse.Raw.Match.Perm
module LPC = LowParse.Spec.Combinators
module Cbor = CBOR.Spec.Raw.EverParse

// The element parser for map entries (a key/value pair).  Kept as an [unfold]
// abbreviation so it reduces to the literal application that the MapBuilder /
// Append signatures spell out, and hence unifies with them.
unfold let map_entry_parser = LPC.nondep_then Cbor.parse_raw_data_item Cbor.parse_raw_data_item

// Bridge the lowparse dictionary views [IO.u64_ops.v]/[IO.u64_ops.fits] to
// their concrete [U64] meaning (mirrors MapBuilder.fst), so the [io.fits]
// precondition of [mixed_list_append] discharges from the [U64.v count] bound.
let u64_ops_v_eq (x: U64.t) : Lemma (IO.u64_ops.v x == U64.v x) [SMTPat (IO.u64_ops.v x)] = ()
let u64_ops_fits_eq (n: nat) : Lemma (IO.u64_ops.fits n == (n < pow2 64 <: prop)) [SMTPat (IO.u64_ops.fits n)] = ()


// ===== PURE size-bound helpers (mirror CBOR.Pulse.Raw.Compare) =====
// A [size]-bound threaded as a precondition keeps [decreases depth] working
// for the open recursion: a non-empty container of size <= depth forces
// depth >= 1, so its elements copy at [nat_pred depth < depth].
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

// Ordering helper for the streaming (iterator-based) _Gen copy loops.
// The loop tracks [m == snd (splitAt i l)] (the suffix of the spec list at
// position i), recovering [m] from the iterator slprop. This single lemma
// exposes the head (== index l i) and the one-step advance in one shot, and
// its statement is always well-typed (no hd/tl refinement obligation).
let rec splitAt_snd_cons (#t: Type) (n: nat) (l: list t)
  : Lemma (requires n < List.Tot.length l)
          (ensures snd (List.Tot.splitAt n l) == List.Tot.index l n :: snd (List.Tot.splitAt (n + 1) l))
          (decreases n)
  = if n = 0 then ()
    else (match l with | _ :: q -> splitAt_snd_cons (n - 1) q)

// A raw_data_item node always has [raw_data_item_size >= 1] (leaves are 1;
// Array/Map/Tagged are >= 2), so each child's [raw_data_item_size] is strictly
// less than its parent's.  Combined with [raw_data_item_size v <= depth], this
// discharges the [raw_data_item_size child <= nat_pred depth] precondition of
// the recursive [copy (nat_pred depth)] call, keeping [decreases depth]
// well-founded for the open recursion.
let rec length_le_list_sum_size (l: list raw_data_item)
  : Lemma (ensures List.Tot.length l <= CBOR.Spec.Util.list_sum raw_data_item_size l)
          (decreases l)
  = match l with
    | [] -> ()
    | a :: q -> raw_data_item_size_eq a; length_le_list_sum_size q

let array_length_le_size (v: raw_data_item { Array? v })
  : Lemma (ensures List.Tot.length (Array?.v v) <= raw_data_item_size v)
  = raw_data_item_size_eq v;
    length_le_list_sum_size (Array?.v v)

let rec length_le_pair_list_sum_size (l: list (raw_data_item & raw_data_item))
  : Lemma (ensures List.Tot.length l <= CBOR.Spec.Util.list_sum (CBOR.Spec.Util.pair_sum raw_data_item_size raw_data_item_size) l)
          (decreases l)
  = match l with
    | [] -> ()
    | a :: q -> raw_data_item_size_eq (fst a); length_le_pair_list_sum_size q

let map_length_le_size (v: raw_data_item { Map? v })
  : Lemma (ensures List.Tot.length (Map?.v v) <= raw_data_item_size v)
  = raw_data_item_size_eq v;
    length_le_pair_list_sum_size (Map?.v v)

// Depth-indexed copy type for open recursion: the INPUT is preserved at
// [cbor_match_with_depth depth]; the freshly-built OUTPUT copy is plain
// [cbor_match 1.0R] (a full copy carries no depth obligation).
// The [pure (raw_data_item_size v <= depth)] precondition threads the size
// bound needed to keep [decreases depth] valid across the recursion.
inline_for_extraction
let cbor_copy_with_depth_t (depth: Ghost.erased nat) =
  (x: cbor_raw) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item) ->
  stt cbor_freeable
    (cbor_match_with_depth depth p x v ** pure (raw_data_item_size v <= Ghost.reveal depth))
    (fun res ->
      cbor_match_with_depth depth p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )

// Expose the constructor/case relationship while preserving the depth predicate.
ghost
fn cbor_match_with_depth_cases (n: nat) (p: perm) (c: cbor_raw) (r: raw_data_item)
  requires cbor_match_with_depth n p c r
  ensures cbor_match_with_depth n p c r ** pure (cbor_match_cases_pred c r)
{
  cbor_match_with_depth_eq0 n p c r;
  rewrite (cbor_match_with_depth n p c r) as (cbor_match0 p c r (depth_cb n r));
  cbor_match0_cases p c r (depth_cb n r);
  rewrite (cbor_match0 p c r (depth_cb n r)) as (cbor_match_with_depth n p c r);
}

// Unrefined depth-indexed map-entry predicate (mirrors cbor_match_map_entry
// but at a fixed depth; carries no [<<] refinement, so a seq_list_match using
// it can be indexed by seq_list_match_index_trade).
let cbor_match_map_entry_with_depth
  (n: nat)
  (p: perm)
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item))
: Tot slprop
= cbor_match_with_depth n p c.cbor_map_entry_key (fst r) **
  cbor_match_with_depth n p c.cbor_map_entry_value (snd r)

// ===== array element-predicate conversions =====
// The depth-array elim yields a seq_list_match whose element predicate is the
// REFINED depth callback [(depth_cb depth parent) pl : cbor_raw -> (v'{v'<<parent}) -> slprop].
// To index it (seq_list_match_index_trade needs an UNREFINED predicate) we
// convert it to [cbor_match_with_depth (nat_pred depth) pl], run the loop, then
// convert back so the elim's trade can restore the parent.

// Peek the head (if any) to learn that a non-empty container forces depth >= 1.
ghost
fn array_peek
  (depth: Ghost.erased nat)
  (parent: raw_data_item { Array? parent })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    SM.seq_list_match s (Array?.v parent) ((depth_cb (Ghost.reveal depth) parent) pl)
ensures
    SM.seq_list_match s (Array?.v parent) ((depth_cb (Ghost.reveal depth) parent) pl) **
    pure (Cons? (Array?.v parent) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  if (Cons? (Array?.v parent)) {
    SM.seq_list_match_cons_elim_trade s (Array?.v parent) ((depth_cb d parent) pl);
    depth_cb_pos d parent pl (Seq.head s) (List.Tot.hd (Array?.v parent));
    Trade.elim _ (SM.seq_list_match s (Array?.v parent) ((depth_cb d parent) pl));
  } else {
    ()
  }
}

ghost
fn array_to_unref
  (depth: Ghost.erased nat)
  (parent: raw_data_item { Array? parent })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    SM.seq_list_match s (Array?.v parent) ((depth_cb (Ghost.reveal depth) parent) pl)
ensures
    SM.seq_list_match s (Array?.v parent) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Array?.v parent) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  array_peek depth parent pl s;
  ghost fn prf
    (c': cbor_raw)
    (v': raw_data_item { v' << Array?.v parent /\ List.Tot.memP v' (Array?.v parent) })
    requires (depth_cb d parent) pl c' v'
    ensures cbor_match_with_depth (nat_pred d) pl c' v'
  {
    depth_cb_pos d parent pl c' v';
    depth_cb_succ d parent pl c' v';
    nat_pred_succ d;
    rewrite ((depth_cb d parent) pl c' v')
      as (cbor_match_with_depth (nat_pred d) pl c' v');
  };
  seq_list_match_conv s (Array?.v parent)
    ((depth_cb d parent) pl)
    (cbor_match_with_depth (nat_pred d) pl)
    prf;
}

ghost
fn array_to_ref
  (depth: Ghost.erased nat)
  (parent: raw_data_item { Array? parent })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    SM.seq_list_match s (Array?.v parent) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Array?.v parent) ==> Ghost.reveal depth >= 1)
ensures
    SM.seq_list_match s (Array?.v parent) ((depth_cb (Ghost.reveal depth) parent) pl)
{
  let d = Ghost.reveal depth;
  if (d = 0) {
    SM.seq_list_match_nil_elim s (Array?.v parent) (cbor_match_with_depth (nat_pred d) pl);
    SM.seq_list_match_nil_intro s (Array?.v parent) ((depth_cb d parent) pl);
  } else {
    ghost fn prf
      (c': cbor_raw)
      (v': raw_data_item { v' << Array?.v parent /\ List.Tot.memP v' (Array?.v parent) })
      requires cbor_match_with_depth (nat_pred d) pl c' v'
      ensures (depth_cb d parent) pl c' v'
    {
      depth_cb_succ d parent pl c' v';
      nat_pred_succ d;
      rewrite (cbor_match_with_depth (nat_pred d) pl c' v')
        as ((depth_cb d parent) pl c' v');
    };
    seq_list_match_conv s (Array?.v parent)
      (cbor_match_with_depth (nat_pred d) pl)
      ((depth_cb d parent) pl)
      prf;
  }
}

// ===== map element-predicate conversions (entry-level) =====
ghost
fn map_peek
  (depth: Ghost.erased nat)
  (parent: raw_data_item { Map? parent })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    SM.seq_list_match s (Map?.v parent) (cbor_match_map_entry0 parent ((depth_cb (Ghost.reveal depth) parent) pl))
ensures
    SM.seq_list_match s (Map?.v parent) (cbor_match_map_entry0 parent ((depth_cb (Ghost.reveal depth) parent) pl)) **
    pure (Cons? (Map?.v parent) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  if (Cons? (Map?.v parent)) {
    SM.seq_list_match_cons_elim_trade s (Map?.v parent) (cbor_match_map_entry0 parent ((depth_cb d parent) pl));
    unfold (cbor_match_map_entry0 parent ((depth_cb d parent) pl) (Seq.head s) (List.Tot.hd (Map?.v parent)));
    depth_cb_pos d parent pl (Seq.head s).cbor_map_entry_key (fst (List.Tot.hd (Map?.v parent)));
    fold (cbor_match_map_entry0 parent ((depth_cb d parent) pl) (Seq.head s) (List.Tot.hd (Map?.v parent)));
    Trade.elim _ (SM.seq_list_match s (Map?.v parent) (cbor_match_map_entry0 parent ((depth_cb d parent) pl)));
  } else {
    ()
  }
}

ghost
fn map_to_unref
  (depth: Ghost.erased nat)
  (parent: raw_data_item { Map? parent })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    SM.seq_list_match s (Map?.v parent) (cbor_match_map_entry0 parent ((depth_cb (Ghost.reveal depth) parent) pl))
ensures
    SM.seq_list_match s (Map?.v parent) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Map?.v parent) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  map_peek depth parent pl s;
  ghost fn prf
    (c': cbor_map_entry)
    (pr: (raw_data_item & raw_data_item) { pr << Map?.v parent /\ List.Tot.memP pr (Map?.v parent) })
    requires cbor_match_map_entry0 parent ((depth_cb d parent) pl) c' pr
    ensures cbor_match_map_entry_with_depth (nat_pred d) pl c' pr
  {
    unfold (cbor_match_map_entry0 parent ((depth_cb d parent) pl) c' pr);
    depth_cb_pos d parent pl c'.cbor_map_entry_key (fst pr);
    depth_cb_succ d parent pl c'.cbor_map_entry_key (fst pr);
    nat_pred_succ d;
    rewrite ((depth_cb d parent) pl c'.cbor_map_entry_key (fst pr))
      as (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_key (fst pr));
    depth_cb_succ d parent pl c'.cbor_map_entry_value (snd pr);
    rewrite ((depth_cb d parent) pl c'.cbor_map_entry_value (snd pr))
      as (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_value (snd pr));
    fold (cbor_match_map_entry_with_depth (nat_pred d) pl c' pr);
  };
  seq_list_match_conv s (Map?.v parent)
    (cbor_match_map_entry0 parent ((depth_cb d parent) pl))
    (cbor_match_map_entry_with_depth (nat_pred d) pl)
    prf;
}

ghost
fn map_to_ref
  (depth: Ghost.erased nat)
  (parent: raw_data_item { Map? parent })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    SM.seq_list_match s (Map?.v parent) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Map?.v parent) ==> Ghost.reveal depth >= 1)
ensures
    SM.seq_list_match s (Map?.v parent) (cbor_match_map_entry0 parent ((depth_cb (Ghost.reveal depth) parent) pl))
{
  let d = Ghost.reveal depth;
  if (d = 0) {
    SM.seq_list_match_nil_elim s (Map?.v parent) (cbor_match_map_entry_with_depth (nat_pred d) pl);
    SM.seq_list_match_nil_intro s (Map?.v parent) (cbor_match_map_entry0 parent ((depth_cb d parent) pl));
  } else {
    ghost fn prf
      (c': cbor_map_entry)
      (pr: (raw_data_item & raw_data_item) { pr << Map?.v parent /\ List.Tot.memP pr (Map?.v parent) })
      requires cbor_match_map_entry_with_depth (nat_pred d) pl c' pr
      ensures cbor_match_map_entry0 parent ((depth_cb d parent) pl) c' pr
    {
      unfold (cbor_match_map_entry_with_depth (nat_pred d) pl c' pr);
      depth_cb_succ d parent pl c'.cbor_map_entry_key (fst pr);
      nat_pred_succ d;
      rewrite (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_key (fst pr))
        as ((depth_cb d parent) pl c'.cbor_map_entry_key (fst pr));
      depth_cb_succ d parent pl c'.cbor_map_entry_value (snd pr);
      rewrite (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_value (snd pr))
        as ((depth_cb d parent) pl c'.cbor_map_entry_value (snd pr));
      fold (cbor_match_map_entry0 parent ((depth_cb d parent) pl) c' pr);
    };
    seq_list_match_conv s (Map?.v parent)
      (cbor_match_map_entry_with_depth (nat_pred d) pl)
      (cbor_match_map_entry0 parent ((depth_cb d parent) pl))
      prf;
  }
}

// Copy a single map entry one depth level down, from the UNREFINED entry
// predicate. The depth bookkeeping is done at the seq_list_match level by the
// caller (map_to_unref / map_to_ref); here we just unfold, copy key & value
// with the depth-d' copier, and refold.
inline_for_extraction
fn cbor_copy_map_entry_d
  (d': Ghost.erased nat)
  (copyd': cbor_copy_with_depth_t d')
  (pl: perm)
  (x: cbor_map_entry)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
requires
    cbor_match_map_entry_with_depth d' pl x v **
    pure (raw_data_item_size (fst v) <= Ghost.reveal d' /\ raw_data_item_size (snd v) <= Ghost.reveal d')
returns res: (cbor_freeable & cbor_freeable)
ensures
    cbor_match_map_entry_with_depth d' pl x v **
    cbor_match 1.0R (fst res).cbor (fst v) **
    cbor_match 1.0R (snd res).cbor (snd v) **
    Trade.trade
      (cbor_match 1.0R (fst res).cbor (fst v))
      (freeable (fst res)) **
    Trade.trade
      (cbor_match 1.0R (snd res).cbor (snd v))
      (freeable (snd res))
{
  unfold (cbor_match_map_entry_with_depth d' pl x v);
  let key = copyd' x.cbor_map_entry_key;
  let value = copyd' x.cbor_map_entry_value;
  fold (cbor_match_map_entry_with_depth d' pl x v);
  (key, value)
}

module S = Pulse.Lib.Slice

inline_for_extraction
let get_cbor_raw_array
  (x: cbor_raw { CBOR_Case_Array? x })
: Tot cbor_array
= let CBOR_Case_Array v = x in v

inline_for_extraction
fn cbor_copy_array_d
  (depth: Ghost.erased nat)
  (copy: (depth': Ghost.erased nat { depth' < depth }) -> cbor_copy_with_depth_t depth')
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match_with_depth depth p x v ** pure (CBOR_Case_Array? x /\ raw_data_item_size v <= Ghost.reveal depth))
returns res: cbor_freeable
ensures
    (
      cbor_match_with_depth depth p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )
{
  cbor_match_with_depth_cases depth p x v;
  let a = get_cbor_raw_array x;
  rewrite (cbor_match_with_depth depth p x v)
    as (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
  cbor_match_with_depth_array_elim depth p a v;
  let ar = a.cbor_array_ptr;
  rewrite each a.cbor_array_ptr as ar;
  S.pts_to_len ar;
  with s . assert (pts_to ar #(p `perm_mul` a.cbor_array_array_perm) s **
    SM.seq_list_match s (Array?.v v) ((depth_cb depth v) (p `perm_mul` a.cbor_array_payload_perm)));
  array_to_unref depth v (p `perm_mul` a.cbor_array_payload_perm) s;
  SM.seq_list_match_length (cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_array_payload_perm)) s (Array?.v v);
  let len = S.len ar;
  let len64 : raw_uint64 = { size = a.cbor_array_length_size; value = SZ.sizet_to_uint64 len };
  assert (pure (len64 == Array?.len v));
  let v' = V.alloc (CBOR_Case_Simple 0uy (* dummy *)) len;
  V.pts_to_len v';
  let vf = V.alloc CBOR_Copy_Unit (* dummy *) len;
  V.pts_to_len vf;
  with s0 . assert (pts_to v' s0);
  with sf0 . assert (pts_to vf sf0);
  let sl = Ghost.hide (Seq.seq_of_list (Array?.v v));
  SM.seq_seq_match_empty_intro (cbor_match 1.0R) s0 sl 0;
  intro
    (Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s0 sl 0 0)
      (SM.seq_seq_match freeable_match' sf0 (Seq.create (SZ.v len) FTUnit (* dummy *)) 0 0)
    )
    #emp
    fn _
  {
    SM.seq_seq_match_empty_elim (cbor_match 1.0R) s0 sl 0;
    SM.seq_seq_match_empty_intro freeable_match' sf0 (Seq.create (SZ.v len) FTUnit (* dummy *)) 0;
  };
  let mut pi = 0sz;
  while (
    let i = !pi;
    (SZ.lt i len)
  ) invariant exists* i s1 j sf st . (
    pts_to ar #(p `perm_mul` a.cbor_array_array_perm) s **
    SM.seq_list_match s (Array?.v v) (cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_array_payload_perm)) **
    pts_to pi i **
    pts_to v' s1 **
    SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j **
    pts_to vf sf **
    Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match' sf st 0 j) **
    pure (
      j == SZ.v i /\
      j <= SZ.v len /\
      Seq.length st == SZ.v len /\
      (Cons? (Array?.v v) ==> Ghost.reveal depth >= 1)
    )
  ) {
    S.pts_to_len ar;
    V.pts_to_len v';
    V.pts_to_len vf;
    let i = !pi;
    with s1 j sf st . assert (pts_to v' s1 ** pts_to vf sf ** Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match' sf st 0 j)
    );
    rewrite each j as (SZ.v i);
    let c = ar.(i);
    SM.seq_list_match_index_trade (cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_array_payload_perm)) s (Array?.v v) (SZ.v i);
    size_array_elt v (List.Tot.index (Array?.v v) (SZ.v i));
    let c' = copy (nat_pred depth) c;
    rewrite each Seq.index s (SZ.v i) as c;
    Trade.elim _ (SM.seq_list_match s (Array?.v v) (cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_array_payload_perm)));
    with v1 . assert (cbor_match 1.0R c'.cbor v1 ** Trade.trade (cbor_match 1.0R c'.cbor v1) (freeable c'));
    V.op_Array_Assignment v' i c'.cbor;
    with s1' . assert (pts_to v' s1');
    V.op_Array_Assignment vf i c'.footprint;
    with sf' . assert (pts_to vf sf');
    SM.seq_seq_match_rewrite_seq_trade (cbor_match 1.0R) s1 s1' sl sl 0 (SZ.v i);
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i)) _ _;
    Trade.prod (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i)) _ (cbor_match 1.0R c'.cbor v1) _;
    SM.seq_seq_match_enqueue_right_trade (cbor_match 1.0R) s1' sl 0 (SZ.v i) c'.cbor v1;
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    let st' = Ghost.hide (Seq.upd st (SZ.v i) c'.tree);
    intro
      (Trade.trade
        (SM.seq_seq_match freeable_match' sf st 0 (SZ.v i) ** freeable c')
        (SM.seq_seq_match freeable_match' sf' st' 0 (SZ.v i + 1))
      )
      #emp
      fn _
    {
      SM.seq_seq_match_rewrite_seq freeable_match' sf sf' st st' 0 (SZ.v i);
      unfold (freeable c');
      SM.seq_seq_match_enqueue_right freeable_match' sf' st' 0 (SZ.v i) c'.footprint c'.tree;
    };
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    pi := (SZ.add i 1sz);
  };
  array_to_ref depth v (p `perm_mul` a.cbor_array_payload_perm) s;
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Array a) v)
    as (cbor_match_with_depth depth p x v);
  with s1 j sf st . assert (pts_to v' s1 ** pts_to vf sf **
    SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j **
    Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match' sf st 0 j)
  );
  rewrite each j as (SZ.v len);
  V.pts_to_len v';
  SM.seq_seq_match_seq_list_match_trade (cbor_match 1.0R) s1 sl;
  CBOR.Pulse.Raw.Iterator.trade_trans_nounify _ _ _ (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len));
  V.pts_to_len vf;
  let lt = Ghost.hide (Seq.seq_to_list st);
  intro
    (Trade.trade
      (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len))
      (SM.seq_list_match sf lt freeable_match')
    )
    #emp
    fn _
  {
    rewrite (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len))
      as (SM.seq_seq_match freeable_match' sf (Seq.seq_of_list lt) 0 (SZ.v len));
    SM.seq_seq_match_seq_list_match freeable_match' sf lt;
  };
  Trade.trans _ _ (SM.seq_list_match sf lt freeable_match');
  V.to_array_pts_to v';
  let ar' = S.from_array (V.vec_to_array v') len;
  S.pts_to_len ar';
  let c' = cbor_match_array_intro len64 ar';
  Trade.trans_concl_r _ _ _ _;
  let fa = {
    array_cbor = v';
    array_footprint = vf;
    array_len = len;
  };
  let res = {
    cbor = c';
    footprint = CBOR_Copy_Array fa;
    tree = FTArray lt;
  };
  intro
    (Trade.trade
      (pts_to ar' s1 ** SM.seq_list_match sf lt freeable_match')
      (freeable res)
    )
    #(S.is_from_array (V.vec_to_array v') ar' ** pts_to vf sf)
    fn _
  {
   S.to_array ar';
   V.to_vec_pts_to v';
   rewrite (pts_to v' s1) as (pts_to fa.array_cbor s1);
   rewrite (pts_to vf sf) as (pts_to fa.array_footprint sf);
   fold (freeable_match' (CBOR_Copy_Array fa) (FTArray lt));
   rewrite freeable_match' (CBOR_Copy_Array fa) (FTArray lt) as
     freeable_match' res.footprint res.tree;
   fold (freeable res)
  };
  Trade.trans _ _ (freeable res);
  with r' . assert cbor_match 1.0R c' (Array len64 r');
  rewrite each cbor_match 1.0R c' (Array len64 r') as cbor_match 1.0R res.cbor v;
  res
}
inline_for_extraction
let get_cbor_raw_map
  (x: cbor_raw { CBOR_Case_Map? x })
: Tot cbor_map
= let CBOR_Case_Map v = x in v

#restart-solver

inline_for_extraction
fn cbor_copy_map_d
  (depth: Ghost.erased nat)
  (copy: (depth': Ghost.erased nat { depth' < depth }) -> cbor_copy_with_depth_t depth')
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match_with_depth depth p x v ** pure (CBOR_Case_Map? x /\ raw_data_item_size v <= Ghost.reveal depth))
returns res: cbor_freeable
ensures
    (
      cbor_match_with_depth depth p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )
{
  cbor_match_with_depth_cases depth p x v;
  let a = get_cbor_raw_map x;
  rewrite (cbor_match_with_depth depth p x v)
    as (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
  cbor_match_with_depth_map_elim depth p a v;
  let ar = a.cbor_map_ptr;
  rewrite each a.cbor_map_ptr as ar;
  S.pts_to_len ar;
  with s . assert (pts_to ar #(p `perm_mul` a.cbor_map_array_perm) s **
    SM.seq_list_match s (Map?.v v) (cbor_match_map_entry0 v ((depth_cb depth v) (p `perm_mul` a.cbor_map_payload_perm))));
  map_to_unref depth v (p `perm_mul` a.cbor_map_payload_perm) s;
  SM.seq_list_match_length (cbor_match_map_entry_with_depth (nat_pred depth) (p `perm_mul` a.cbor_map_payload_perm)) s (Map?.v v);
  let len = S.len ar;
  let len64 : raw_uint64 = { size = a.cbor_map_length_size; value = SZ.sizet_to_uint64 len };
  assert (pure (len64 == Map?.len v));
  let v' = V.alloc
    ({
      cbor_map_entry_key = CBOR_Case_Simple 0uy; (* dummy *)
      cbor_map_entry_value = CBOR_Case_Simple 0uy;
    })
    len;
  V.pts_to_len v';
  let vf = V.alloc
    ({
      map_entry_key = CBOR_Copy_Unit;
      map_entry_value = CBOR_Copy_Unit;
    })
    len;
  V.pts_to_len vf;
  with s0 . assert (pts_to v' s0);
  with sf0 . assert (pts_to vf sf0);
  let sl = Ghost.hide (Seq.seq_of_list (Map?.v v));
  SM.seq_seq_match_empty_intro (cbor_match_map_entry 1.0R) s0 sl 0;
  intro
    (Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s0 sl 0 0)
      (SM.seq_seq_match freeable_match_map_entry sf0 (Seq.create (SZ.v len) (FTUnit, FTUnit) (* dummy *)) 0 0)
    )
    #emp
    fn _
  {
    SM.seq_seq_match_empty_elim (cbor_match_map_entry 1.0R) s0 sl 0;
    SM.seq_seq_match_empty_intro freeable_match_map_entry sf0 (Seq.create (SZ.v len) (FTUnit, FTUnit) (* dummy *)) 0;
  };
  let mut pi = 0sz;
  while (
    let i = !pi;
    (SZ.lt i len)
  ) invariant exists* i s1 j sf st . (
    pts_to ar #(p `perm_mul` a.cbor_map_array_perm) s **
    SM.seq_list_match s (Map?.v v) (cbor_match_map_entry_with_depth (nat_pred depth) (p `perm_mul` a.cbor_map_payload_perm)) **
    pts_to pi i **
    pts_to v' s1 **
    SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j **
    pts_to vf sf **
    Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match_map_entry sf st 0 j) **
    pure (
      j == SZ.v i /\
      j <= SZ.v len /\
      Seq.length st == SZ.v len /\
      (Cons? (Map?.v v) ==> Ghost.reveal depth >= 1)
    )
  ) {
    S.pts_to_len ar;
    V.pts_to_len v';
    V.pts_to_len vf;
    let i = !pi;
    with s1 j sf st . assert (pts_to v' s1 ** pts_to vf sf ** Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match_map_entry sf st 0 j)
    );
    rewrite each j as (SZ.v i);
    let c = S.op_Array_Access ar i;
    SM.seq_list_match_index_trade (cbor_match_map_entry_with_depth (nat_pred depth) (p `perm_mul` a.cbor_map_payload_perm)) s (Map?.v v) (SZ.v i);
    size_map_entry v (List.Tot.index (Map?.v v) (SZ.v i));
    with v1 . assert (cbor_match_map_entry_with_depth (nat_pred depth) (p `perm_mul` a.cbor_map_payload_perm) c v1);
    let key', value' = cbor_copy_map_entry_d (nat_pred depth) (copy (nat_pred depth)) (p `perm_mul` a.cbor_map_payload_perm) c;
    Trade.elim _ (SM.seq_list_match s (Map?.v v) (cbor_match_map_entry_with_depth (nat_pred depth) (p `perm_mul` a.cbor_map_payload_perm)));
    Trade.prod
      (cbor_match 1.0R key'.cbor (fst v1))
      (freeable key')
      (cbor_match 1.0R value'.cbor (snd v1))
      (freeable value');
    let cme' = {
      cbor_map_entry_key = key'.cbor;
      cbor_map_entry_value = value'.cbor;
    };
    Trade.rewrite_with_trade
      (cbor_match 1.0R key'.cbor (fst v1) **
        cbor_match 1.0R value'.cbor (snd v1)
      )
      (cbor_match_map_entry 1.0R cme' v1);
    Trade.trans (cbor_match_map_entry 1.0R cme' v1) _ _;
    V.op_Array_Assignment v' i cme';
    with s1' . assert (pts_to v' s1');
    let cfp' = {
      map_entry_key = key'.footprint;
      map_entry_value = value'.footprint;
    };
    V.op_Array_Assignment vf i cfp';
    with sf' . assert (pts_to vf sf');
    SM.seq_seq_match_rewrite_seq_trade (cbor_match_map_entry 1.0R) s1 s1' sl sl 0 (SZ.v i);
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i)) _ _;
    Trade.prod (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i)) _ (cbor_match_map_entry 1.0R cme' v1) _;
    SM.seq_seq_match_enqueue_right_trade (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i) cme' v1;
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    let tree = Ghost.hide (key'.tree, value'.tree);
    let st' = Ghost.hide (Seq.upd st (SZ.v i) tree);
    intro
      (Trade.trade
        (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v i) ** (freeable key' ** freeable value'))
        (SM.seq_seq_match freeable_match_map_entry sf' st' 0 (SZ.v i + 1))
      )
      #emp
      fn _
    {
      SM.seq_seq_match_rewrite_seq freeable_match_map_entry sf sf' st st' 0 (SZ.v i);
      unfold (freeable key');
      unfold (freeable value');
      rewrite each key'.footprint as cfp'.map_entry_key;
      rewrite each value'.footprint as cfp'.map_entry_value;
      fold (freeable_match_map_entry cfp' (key'.tree, value'.tree));
      SM.seq_seq_match_enqueue_right freeable_match_map_entry sf' st' 0 (SZ.v i) cfp' (key'.tree, value'.tree);
    };
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    pi := (SZ.add i 1sz);
  };
  map_to_ref depth v (p `perm_mul` a.cbor_map_payload_perm) s;
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Map a) v)
    as (cbor_match_with_depth depth p x v);
  with s1 j sf st . assert (pts_to v' s1 ** pts_to vf sf **
    SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j **
    Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match_map_entry sf st 0 j)
  );
  rewrite each j as (SZ.v len);
  V.pts_to_len v';
  SM.seq_seq_match_seq_list_match_trade (cbor_match_map_entry 1.0R) s1 sl;
  CBOR.Pulse.Raw.Iterator.trade_trans_nounify _ _ _ (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len));
  V.pts_to_len vf;
  let lt = Ghost.hide (Seq.seq_to_list st);
  intro
    (Trade.trade
      (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len))
      (SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match'))
    )
    #emp
    fn _
  {
    rewrite (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len))
      as (SM.seq_seq_match freeable_match_map_entry sf (Seq.seq_of_list lt) 0 (SZ.v len));
    SM.seq_seq_match_seq_list_match freeable_match_map_entry sf lt;
    SM.seq_list_match_weaken sf lt freeable_match_map_entry (freeable_match_map_entry' (FTMap lt) freeable_match') (freeable_match_map_entry_weaken_recip lt);
  };
  Trade.trans _ _ (SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match'));
  V.to_array_pts_to v';
  let ar' = S.from_array (V.vec_to_array v') len;
  S.pts_to_len ar';
  let c' = cbor_match_map_intro len64 ar';
  Trade.trans_concl_r _ _ _ _;
  let fa = {
    map_cbor = v';
    map_footprint = vf;
    map_len = len;
  };
  let res = {
    cbor = c';
    footprint = CBOR_Copy_Map fa;
    tree = FTMap lt;
  };
  intro
    (Trade.trade
      (pts_to ar' s1 ** SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match'))
      (freeable res)
    )
    #(S.is_from_array (V.vec_to_array v') ar' ** pts_to vf sf)
    fn _
  {
   S.to_array ar';
   V.to_vec_pts_to v';
   rewrite (pts_to v' s1) as (pts_to fa.map_cbor s1);
   rewrite (pts_to vf sf) as (pts_to fa.map_footprint sf);
   fold (freeable_match' (CBOR_Copy_Map fa) (FTMap lt));
   rewrite (freeable_match' (CBOR_Copy_Map fa) (FTMap lt)) as freeable_match' res.footprint res.tree;
   fold (freeable res)
  };
  Trade.trans _ _ (freeable res);
  with r' . assert cbor_match 1.0R c' (Map len64 r');
  rewrite each cbor_match 1.0R c' (Map len64 r') as
  cbor_match 1.0R res.cbor v;
  res
}

inline_for_extraction
let get_cbor_raw_array_gen
  (x: cbor_raw { CBOR_Case_Array_Gen? x })
: Tot cbor_mixed_list_array
= let CBOR_Case_Array_Gen v = x in v

inline_for_extraction
let get_cbor_raw_map_gen
  (x: cbor_raw { CBOR_Case_Map_Gen? x })
: Tot cbor_mixed_list_map
= let CBOR_Case_Map_Gen v = x in v

// Definitional unfolding of the standalone element match at a record literal,
// with the record projections reduced.  Used to fold the element match during
// the structural array build (Pulse's [rewrite]/[fold] do not reduce record
// projections on a [let]-bound record on their own).
let arraygen_elt_fold
  (fp: cbor_freeable0)
  (r: freeable_tree)
  (be: B.box cbor_raw)
  (bbf baf: B.box (IT.mixed_list U64.t cbor_raw))
: Lemma
  (ensures
    freeable_match_arraygen_elt ({ age_footprint = fp; age_box_elt = be; age_box_before = bbf; age_box_after = baf }) r ==
    (freeable_match' fp r **
      (exists* (w: cbor_raw). R.pts_to (B.box_to_ref be) w) **
      (exists* (wb wa: IT.mixed_list U64.t cbor_raw). R.pts_to (B.box_to_ref bbf) wb ** R.pts_to (B.box_to_ref baf) wa) **
      pure (R.is_full_ref (B.box_to_ref be) /\ R.is_full_ref (B.box_to_ref bbf) /\ R.is_full_ref (B.box_to_ref baf))))
= assert_norm (
    freeable_match_arraygen_elt ({ age_footprint = fp; age_box_elt = be; age_box_before = bbf; age_box_after = baf }) r ==
    (freeable_match' fp r **
      (exists* (w: cbor_raw). R.pts_to (B.box_to_ref be) w) **
      (exists* (wb wa: IT.mixed_list U64.t cbor_raw). R.pts_to (B.box_to_ref bbf) wb ** R.pts_to (B.box_to_ref baf) wa) **
      pure (R.is_full_ref (B.box_to_ref be) /\ R.is_full_ref (B.box_to_ref bbf) /\ R.is_full_ref (B.box_to_ref baf))))

// One fold step for the structural (_Gen) array build.  Given the ArrayBuilder
// trades produced by [cbor_array_append] / [cbor_array_singleton], the copy
// trade for the freshly-copied element, and the accumulated destructor trade
// [owned acc_cur l_acc --* seq_list_match ...], produce the extended destructor
// trade for [acc'] with the new element prepended to the footprint list.
ghost
fn arraygen_step
  (l_acc: Ghost.erased (list raw_data_item))
  (v1: Ghost.erased raw_data_item)
  (acc_cur acc' s_i: cbor_mixed_list_array)
  (c': cbor_freeable)
  (bs: B.box cbor_raw)
  (bb ba: B.box (IT.mixed_list U64.t cbor_raw))
  (ag_acc: Ghost.erased (list cbor_freeable_arraygen_elt))
  (ft_acc: Ghost.erased (list freeable_tree))
requires
  Trade.trade
    (AB.cbor_array_owned acc' (List.Tot.append l_acc [Ghost.reveal v1]))
    (AB.cbor_array_owned acc_cur l_acc ** AB.cbor_array_owned s_i [Ghost.reveal v1] **
      (exists* (vb va: IT.mixed_list U64.t cbor_raw). R.pts_to (B.box_to_ref bb) vb ** R.pts_to (B.box_to_ref ba) va)) **
  Trade.trade
    (AB.cbor_array_owned s_i [Ghost.reveal v1])
    (cbor_match 1.0R c'.cbor v1 ** (exists* (w: cbor_raw). R.pts_to (B.box_to_ref bs) w)) **
  Trade.trade (cbor_match 1.0R c'.cbor v1) (freeable c') **
  Trade.trade
    (AB.cbor_array_owned acc_cur l_acc)
    (SM.seq_list_match (Seq.seq_of_list ag_acc) ft_acc freeable_match_arraygen_elt) **
  pure (
    R.is_full_ref (B.box_to_ref bs) /\
    R.is_full_ref (B.box_to_ref bb) /\
    R.is_full_ref (B.box_to_ref ba)
  )
ensures
  Trade.trade
    (AB.cbor_array_owned acc' (List.Tot.append l_acc [Ghost.reveal v1]))
    (SM.seq_list_match
      (Seq.seq_of_list (({ age_footprint = c'.footprint; age_box_elt = bs; age_box_before = bb; age_box_after = ba } <: cbor_freeable_arraygen_elt) :: ag_acc))
      (c'.tree :: ft_acc)
      freeable_match_arraygen_elt)
{
  let new_elt : cbor_freeable_arraygen_elt = { age_footprint = c'.footprint; age_box_elt = bs; age_box_before = bb; age_box_after = ba };
  intro
    (Trade.trade
      (AB.cbor_array_owned acc' (List.Tot.append l_acc [Ghost.reveal v1]))
      (SM.seq_list_match (Seq.seq_of_list (new_elt :: ag_acc)) (c'.tree :: ft_acc) freeable_match_arraygen_elt))
    #(
      Trade.trade
        (AB.cbor_array_owned acc' (List.Tot.append l_acc [Ghost.reveal v1]))
        (AB.cbor_array_owned acc_cur l_acc ** AB.cbor_array_owned s_i [Ghost.reveal v1] **
          (exists* (vb va: IT.mixed_list U64.t cbor_raw). R.pts_to (B.box_to_ref bb) vb ** R.pts_to (B.box_to_ref ba) va)) **
      Trade.trade
        (AB.cbor_array_owned s_i [Ghost.reveal v1])
        (cbor_match 1.0R c'.cbor v1 ** (exists* (w: cbor_raw). R.pts_to (B.box_to_ref bs) w)) **
      Trade.trade (cbor_match 1.0R c'.cbor v1) (freeable c') **
      Trade.trade
        (AB.cbor_array_owned acc_cur l_acc)
        (SM.seq_list_match (Seq.seq_of_list ag_acc) ft_acc freeable_match_arraygen_elt) **
      pure (
        R.is_full_ref (B.box_to_ref bs) /\
        R.is_full_ref (B.box_to_ref bb) /\
        R.is_full_ref (B.box_to_ref ba)
      )
    )
    fn _
    {
      Trade.elim _
        (AB.cbor_array_owned acc_cur l_acc ** AB.cbor_array_owned s_i [Ghost.reveal v1] **
          (exists* (vb va: IT.mixed_list U64.t cbor_raw). R.pts_to (B.box_to_ref bb) vb ** R.pts_to (B.box_to_ref ba) va));
      Trade.elim _
        (cbor_match 1.0R c'.cbor v1 ** (exists* (w: cbor_raw). R.pts_to (B.box_to_ref bs) w));
      Trade.elim _ (freeable c');
      Trade.elim _ (SM.seq_list_match (Seq.seq_of_list ag_acc) ft_acc freeable_match_arraygen_elt);
      unfold (freeable c');
      arraygen_elt_fold c'.footprint c'.tree bs bb ba;
      rewrite
        (freeable_match' c'.footprint c'.tree **
          (exists* (w: cbor_raw). R.pts_to (B.box_to_ref bs) w) **
          (exists* (wb wa: IT.mixed_list U64.t cbor_raw). R.pts_to (B.box_to_ref bb) wb ** R.pts_to (B.box_to_ref ba) wa) **
          pure (R.is_full_ref (B.box_to_ref bs) /\ R.is_full_ref (B.box_to_ref bb) /\ R.is_full_ref (B.box_to_ref ba)))
        as (freeable_match_arraygen_elt new_elt c'.tree);
      Seq.lemma_seq_of_list_induction (new_elt :: ag_acc);
      SM.seq_list_match_cons_intro new_elt c'.tree (Seq.seq_of_list ag_acc) ft_acc freeable_match_arraygen_elt;
      rewrite (SM.seq_list_match (Seq.cons new_elt (Seq.seq_of_list ag_acc)) (c'.tree :: ft_acc) freeable_match_arraygen_elt)
        as (SM.seq_list_match (Seq.seq_of_list (new_elt :: ag_acc)) (c'.tree :: ft_acc) freeable_match_arraygen_elt);
    };
    rewrite
      (Trade.trade
        (AB.cbor_array_owned acc' (List.Tot.append l_acc [Ghost.reveal v1]))
        (SM.seq_list_match (Seq.seq_of_list (new_elt :: ag_acc)) (c'.tree :: ft_acc) freeable_match_arraygen_elt))
      as
      (Trade.trade
        (AB.cbor_array_owned acc' (List.Tot.append l_acc [Ghost.reveal v1]))
        (SM.seq_list_match (Seq.seq_of_list (({ age_footprint = c'.footprint; age_box_elt = bs; age_box_before = bb; age_box_after = ba } <: cbor_freeable_arraygen_elt) :: ag_acc)) (c'.tree :: ft_acc) freeable_match_arraygen_elt));
}

// Deep-copy a _Gen array by streaming its elements through the depth-aware
// array iterator (which dispatches CBOR_Case_Array_Gen internally) into the
// same CBOR_Copy_Array footprint the inline arm builds.
#restart-solver
inline_for_extraction
fn cbor_copy_array_gen_d
  (depth: Ghost.erased nat)
  (copy: (depth': Ghost.erased nat { depth' < depth }) -> cbor_copy_with_depth_t depth')
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match_with_depth depth p x v ** pure (CBOR_Case_Array_Gen? x /\ raw_data_item_size v <= Ghost.reveal depth))
returns res: cbor_freeable
ensures
    (
      cbor_match_with_depth depth p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )
{
  cbor_match_with_depth_cases depth p x v;
  let a = get_cbor_raw_array_gen x;
  rewrite (cbor_match_with_depth depth p x v)
    as (cbor_match_with_depth depth p (CBOR_Case_Array_Gen a) v);
  // --- get element count as SZ.t and relate it to List.length (Array?.v v) ---
  cbor_match_with_depth_array_gen_elim depth p a v;
  let count = ML.cbor_raw_mixed_list_length a.cbor_array_gen_ptr;
  cbor_match_mixed_list_array_length p a v (depth_cb depth v);
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Array_Gen a) v);
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Array_Gen a) v)
    as (cbor_match_with_depth depth p x v);
  // --- initialize the depth-aware array iterator (dispatches _Gen) ---
  let it = cbor_array_iterator_init_with_depth depth x;
  with p_it . assert (cbor_array_iterator_match_with_depth (nat_pred depth) p_it it (Array?.v v));
  // --- pre-allocate destination vectors ---
  // The element count [count : U64.t] IS the loop bound: the fold iterates
  // [count] times over a u64 counter, so no [size_t] conversion (and hence no
  // [SZ.fits] bound on the whole value) is required.
  array_length_le_size v;
  assert (pure (U64.v count == List.Tot.length (Array?.v v)));
  let len64 : raw_uint64 = { size = a.cbor_array_gen_length_size; value = count };
  assert (pure (len64 == Array?.len v));
  // === build a structural (_Gen) array by folding singletons via ArrayBuilder ===
  let acc0 = AB.cbor_array_empty ();
  let mut pacc = acc0;
  let mut pi = 0uL;
  let mut pit = it;
  // the footprint spine is a heap box-chain built up (one O(1) node per element)
  // alongside the array; it starts empty and is captured into the destructor
  // trade once the array is finalized.
  let mut phead : option (B.box arraygen_node) = None;
  fold (arraygen_spine (None #(B.box arraygen_node)) ([] <: list cbor_freeable_arraygen_elt));
  Trade.refl (cbor_array_iterator_match_with_depth (nat_pred depth) p_it it (Array?.v v));
  // initial destructor trade: the empty owned array is a pure resource, so
  // [owned acc0 []] can be dropped and [seq_list_match] on empty lists built.
  intro
    (Trade.trade
      (AB.cbor_array_owned acc0 [])
      (SM.seq_list_match (Seq.seq_of_list ([] <: list cbor_freeable_arraygen_elt)) ([] <: list freeable_tree) freeable_match_arraygen_elt))
    #emp
    fn _
  {
    drop_ (AB.cbor_array_owned acc0 []);
    SM.seq_list_match_nil_intro (Seq.seq_of_list ([] <: list cbor_freeable_arraygen_elt)) ([] <: list freeable_tree) freeable_match_arraygen_elt;
  };
  while (
    let i = !pi;
    (U64.lt i count)
  ) invariant exists* i gi m pj acc l_acc ag ft hd_ptr . (
    pts_to pi i **
    pts_to pit gi **
    pts_to pacc acc **
    pts_to phead hd_ptr **
    arraygen_spine hd_ptr ag **
    cbor_array_iterator_match_with_depth (nat_pred depth) pj gi m **
    Trade.trade
      (cbor_array_iterator_match_with_depth (nat_pred depth) pj gi m)
      (cbor_array_iterator_match_with_depth (nat_pred depth) p_it it (Array?.v v)) **
    AB.cbor_array_owned acc l_acc **
    Trade.trade
      (AB.cbor_array_owned acc l_acc)
      (SM.seq_list_match (Seq.seq_of_list ag) ft freeable_match_arraygen_elt) **
    pure (
      U64.v i <= U64.v count /\
      U64.v count == List.Tot.length (Ghost.reveal (Array?.v v)) /\
      (len64 <: raw_uint64) == Array?.len v /\
      List.Tot.length (Ghost.reveal l_acc) == U64.v i /\
      Ghost.reveal m == snd (List.Tot.splitAt (U64.v i) (Ghost.reveal (Array?.v v))) /\
      List.Tot.append (Ghost.reveal l_acc) (Ghost.reveal m) == Ghost.reveal (Array?.v v)
    )
  ) {
    let i = !pi;
    with gi m pj acc l_acc ag ft hd_ptr . assert (
      pts_to pit gi **
      pts_to pacc acc **
      pts_to phead hd_ptr **
      arraygen_spine hd_ptr ag **
      cbor_array_iterator_match_with_depth (nat_pred depth) pj gi m **
      Trade.trade
        (cbor_array_iterator_match_with_depth (nat_pred depth) pj gi m)
        (cbor_array_iterator_match_with_depth (nat_pred depth) p_it it (Array?.v v)) **
      AB.cbor_array_owned acc l_acc **
      Trade.trade
        (AB.cbor_array_owned acc l_acc)
        (SM.seq_list_match (Seq.seq_of_list ag) ft freeable_match_arraygen_elt)
    );
    List.Tot.append_length (Ghost.reveal l_acc) (Ghost.reveal m);
    // identify the head of the remaining suffix with the element at index i,
    // and expose the one-step advance [snd (splitAt i) == index i :: snd (splitAt (i+1))]
    splitAt_snd_cons (U64.v i) (Array?.v v);
    let c = cbor_array_iterator_next_with_depth (nat_pred depth) pit;
    Trade.trans _ _ (cbor_array_iterator_match_with_depth (nat_pred depth) p_it it (Array?.v v));
    size_array_elt v (List.Tot.index (Array?.v v) (U64.v i));
    let c' = copy (nat_pred depth) c;
    Trade.elim_hyp_l _ _ (cbor_array_iterator_match_with_depth (nat_pred depth) p_it it (Array?.v v));
    with v1 . assert (cbor_match 1.0R c'.cbor v1 ** Trade.trade (cbor_match 1.0R c'.cbor v1) (freeable c'));
    let bs = B.alloc c'.cbor;
    B.to_ref_pts_to bs;
    let s_i = AB.cbor_array_singleton c'.cbor (B.box_to_ref bs);
    let acc_cur = !pacc;
    let bb = B.alloc (IT.Base IT.Empty <: IT.mixed_list U64.t cbor_raw);
    let ba = B.alloc (IT.Base IT.Empty <: IT.mixed_list U64.t cbor_raw);
    B.to_ref_pts_to bb;
    B.to_ref_pts_to ba;
    AB.cbor_array_owned_length_fits acc_cur;
    let appended = AB.cbor_array_append acc_cur s_i (B.box_to_ref bb) (B.box_to_ref ba);
    match appended {
      Some acc' -> {
        List.Tot.append_assoc (Ghost.reveal l_acc) [Ghost.reveal v1]
          (snd (List.Tot.splitAt (U64.v i + 1) (Ghost.reveal (Array?.v v))));
        arraygen_step l_acc v1 acc_cur acc' s_i c' bs bb ba ag ft;
        let head_cur = !phead;
        let new_head = arraygen_cons ({ age_footprint = c'.footprint; age_box_elt = bs; age_box_before = bb; age_box_after = ba } <: cbor_freeable_arraygen_elt) head_cur;
        phead := new_head;
        pacc := acc';
        pi := (U64.add i 1uL);
      }
      None -> {
        assert (pure (List.Tot.length [Ghost.reveal v1] == 1));
        assert (pure False);
        unreachable ()
      }
    }
  };
  Trade.elim _ (cbor_array_iterator_match_with_depth (nat_pred depth) p_it it (Array?.v v));
  Trade.elim _ (cbor_match_with_depth depth p x v);
  // at loop exit, [i == len == length (Array?.v v)], so the iterator suffix is
  // empty and [l_acc == Array?.v v]
  with acc_g l_acc_g ag_g ft_g hd_g . assert (
    AB.cbor_array_owned acc_g l_acc_g **
    Trade.trade
      (AB.cbor_array_owned acc_g l_acc_g)
      (SM.seq_list_match (Seq.seq_of_list ag_g) ft_g freeable_match_arraygen_elt) **
    pts_to phead hd_g **
    arraygen_spine hd_g ag_g
  );
  FStar.List.Tot.Base.lemma_splitAt_snd_length (U64.v count) (Ghost.reveal (Array?.v v));
  List.Tot.Properties.append_l_nil (Ghost.reveal l_acc_g);
  assert (pure (Ghost.reveal l_acc_g == Ghost.reveal (Array?.v v)));
  assert (pure (List.Tot.length (Ghost.reveal l_acc_g) == U64.v count));
  assert (pure (U64.v (len64.value) == U64.v count));
  let acc = !pacc;
  let head_final = !phead;
  rewrite (arraygen_spine hd_g ag_g) as (arraygen_spine head_final ag_g);
  // finalize with the (possibly non-minimal) length header [len64] of the
  // source, so the resulting match reproduces [v] exactly.
  fold (AB.cbor_array_owned_with_len acc len64 (Ghost.reveal l_acc_g));
  // pin [U64.v len64.value == length l_acc_g] so [Array len64 l_acc_g] (a
  // dependent [nlist]) typechecks below.
  assert (pure (AB.cbor_array_len_ok len64 (Ghost.reveal l_acc_g)));
  let y = AB.cbor_array_finalize_with_len acc len64;
  // [finalize_with_len] now exposes the CONCRETE match [cbor_match y (Array
  // len64 l_acc_g)] (no existential length witness).  Bind the whole finalized
  // array value [a] with a single metavariable (so the frame matcher never has
  // to unify under [Array]'s dependent [nlist] refinement), then unfold.
  with a. assert (AB.cbor_array_finalized_val acc y a);
  unfold (AB.cbor_array_finalized_val acc y a);
  // build the structural result and its destructor trade
  let res : cbor_freeable = {
    cbor = y;
    footprint = CBOR_Copy_ArrayGen head_final;
    tree = FTArrayGen ft_g;
  };
  // [a == Array len64 l_acc_g] (finalize), [len64 == Array?.len v] (invariant),
  // [l_acc_g == Array?.v v] (loop exit) give [a == v]; relabel the concrete
  // finalize match and its destructor trade to the source value [v].
  assert (pure (Ghost.reveal l_acc_g == Ghost.reveal (Array?.v v)));
  assert (pure (a == Ghost.reveal v));
  rewrite (cbor_match 1.0R y a)
    as (cbor_match 1.0R res.cbor v);
  rewrite (Trade.trade
      (cbor_match 1.0R y a)
      (AB.cbor_array_owned acc (Array?.v a)))
    as (Trade.trade
      (cbor_match 1.0R res.cbor v)
      (AB.cbor_array_owned acc (Ghost.reveal l_acc_g)));
  // compose the finalize trade [cbor_match res.cbor v --* owned acc l]
  // with the accumulated destructor trade [owned acc l --* seq_list_match elts]
  Trade.trans _ _
    (SM.seq_list_match (Seq.seq_of_list ag_g) ft_g freeable_match_arraygen_elt);
  // capture the live footprint spine [arraygen_spine head_final ag_g] into the
  // destructor trade, so firing it reproduces the full [freeable res]
  intro
    (Trade.trade
      (cbor_match 1.0R res.cbor v)
      (freeable res))
    #(arraygen_spine head_final ag_g **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (SM.seq_list_match (Seq.seq_of_list ag_g) ft_g freeable_match_arraygen_elt))
    fn _
  {
    Trade.elim _ (SM.seq_list_match (Seq.seq_of_list ag_g) ft_g freeable_match_arraygen_elt);
    SM.seq_list_match_weaken (Seq.seq_of_list ag_g) ft_g
      freeable_match_arraygen_elt
      (freeable_match_arraygen_elt' (FTArrayGen ft_g) freeable_match')
      (freeable_match_arraygen_elt_weaken_recip ft_g);
    fold (freeable_match' (CBOR_Copy_ArrayGen head_final) (FTArrayGen ft_g));
    rewrite (freeable_match' (CBOR_Copy_ArrayGen head_final) (FTArrayGen ft_g))
      as (freeable_match' res.footprint res.tree);
    fold (freeable res);
  };
  res
}

// Gather two [cbor_match_map_entry] shares of the same concrete entry (needed
// as the [gather_t] argument to [Append.mixed_list_singleton]).  Copied from
// CBOR.Pulse.Raw.EverParse.Det.MapInsert.
ghost
fn cbor_match_map_entry_gather
  (x1: cbor_map_entry)
  (#p: perm)
  (#x2: (raw_data_item & raw_data_item))
  (#p': perm)
  (#x2': (raw_data_item & raw_data_item))
requires cbor_match_map_entry p x1 x2 ** cbor_match_map_entry p' x1 x2'
ensures cbor_match_map_entry (p +. p') x1 x2 ** pure (x2 == x2')
{
  unfold (cbor_match_map_entry p x1 x2);
  unfold (cbor_match_map_entry p' x1 x2');
  MP.cbor_raw_gather p x1.cbor_map_entry_key (fst x2) p' (fst x2');
  MP.cbor_raw_gather p x1.cbor_map_entry_value (snd x2) p' (snd x2');
  fold (cbor_match_map_entry (p +. p') x1 x2);
}

// [assert_norm] equality unfolding the per-entry [freeable_match_mapgen_elt]
// for a record literal at [(kr, vr)] (mirrors [arraygen_elt_fold]).
let mapgen_elt_fold
  (kfp vfp: cbor_freeable0)
  (r: (freeable_tree & freeable_tree))
  (be: B.box cbor_map_entry)
  (bbf baf: B.box (IT.mixed_list U64.t cbor_map_entry))
: Lemma
  (ensures
    freeable_match_mapgen_elt ({ mge_key_footprint = kfp; mge_val_footprint = vfp; mge_box_elt = be; mge_box_before = bbf; mge_box_after = baf }) r ==
    (freeable_match' kfp (fst r) **
      freeable_match' vfp (snd r) **
      (exists* (w: cbor_map_entry). R.pts_to (B.box_to_ref be) w) **
      (exists* (wb wa: IT.mixed_list U64.t cbor_map_entry). R.pts_to (B.box_to_ref bbf) wb ** R.pts_to (B.box_to_ref baf) wa) **
      pure (R.is_full_ref (B.box_to_ref be) /\ R.is_full_ref (B.box_to_ref bbf) /\ R.is_full_ref (B.box_to_ref baf))))
= assert_norm (
    freeable_match_mapgen_elt ({ mge_key_footprint = kfp; mge_val_footprint = vfp; mge_box_elt = be; mge_box_before = bbf; mge_box_after = baf }) r ==
    (freeable_match' kfp (fst r) **
      freeable_match' vfp (snd r) **
      (exists* (w: cbor_map_entry). R.pts_to (B.box_to_ref be) w) **
      (exists* (wb wa: IT.mixed_list U64.t cbor_map_entry). R.pts_to (B.box_to_ref bbf) wb ** R.pts_to (B.box_to_ref baf) wa) **
      pure (R.is_full_ref (B.box_to_ref be) /\ R.is_full_ref (B.box_to_ref bbf) /\ R.is_full_ref (B.box_to_ref baf))))

// One fold step for the structural (_Gen) map build.  Mirrors [arraygen_step]
// but folds BOTH the key and value footprints (and the entry-destructor trade
// [cbor_match_map_entry cme' --* (freeable key' ** freeable value')]) into the
// per-entry [freeable_match_mapgen_elt] prepended to the footprint list.
ghost
fn mapgen_step
  (l_acc: Ghost.erased (list (raw_data_item & raw_data_item)))
  (entry_v: Ghost.erased (raw_data_item & raw_data_item))
  (acc_cur acc' s_i: IT.mixed_list U64.t cbor_map_entry)
  (cme': cbor_map_entry)
  (key' value': cbor_freeable)
  (bs: B.box cbor_map_entry)
  (bb ba: B.box (IT.mixed_list U64.t cbor_map_entry))
  (mg_acc: Ghost.erased (list cbor_freeable_mapgen_elt))
  (ft_acc: Ghost.erased (list (freeable_tree & freeable_tree)))
requires
  Trade.trade
    (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc' (List.Tot.append l_acc [Ghost.reveal entry_v]))
    (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_cur l_acc **
      I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R s_i [Ghost.reveal entry_v] **
      (exists* (vb va: IT.mixed_list U64.t cbor_map_entry). R.pts_to (B.box_to_ref bb) vb ** R.pts_to (B.box_to_ref ba) va)) **
  Trade.trade
    (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R s_i [Ghost.reveal entry_v])
    (cbor_match_map_entry 1.0R cme' entry_v ** (exists* (w: cbor_map_entry). R.pts_to (B.box_to_ref bs) w)) **
  Trade.trade (cbor_match_map_entry 1.0R cme' entry_v) (freeable key' ** freeable value') **
  Trade.trade
    (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_cur l_acc)
    (SM.seq_list_match (Seq.seq_of_list mg_acc) ft_acc freeable_match_mapgen_elt) **
  pure (
    R.is_full_ref (B.box_to_ref bs) /\
    R.is_full_ref (B.box_to_ref bb) /\
    R.is_full_ref (B.box_to_ref ba)
  )
ensures
  Trade.trade
    (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc' (List.Tot.append l_acc [Ghost.reveal entry_v]))
    (SM.seq_list_match
      (Seq.seq_of_list (({ mge_key_footprint = key'.footprint; mge_val_footprint = value'.footprint; mge_box_elt = bs; mge_box_before = bb; mge_box_after = ba } <: cbor_freeable_mapgen_elt) :: mg_acc))
      ((key'.tree, value'.tree) :: ft_acc)
      freeable_match_mapgen_elt)
{
  let new_elt : cbor_freeable_mapgen_elt = { mge_key_footprint = key'.footprint; mge_val_footprint = value'.footprint; mge_box_elt = bs; mge_box_before = bb; mge_box_after = ba };
  intro
    (Trade.trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc' (List.Tot.append l_acc [Ghost.reveal entry_v]))
      (SM.seq_list_match (Seq.seq_of_list (new_elt :: mg_acc)) ((key'.tree, value'.tree) :: ft_acc) freeable_match_mapgen_elt))
    #(
      Trade.trade
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc' (List.Tot.append l_acc [Ghost.reveal entry_v]))
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_cur l_acc **
          I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R s_i [Ghost.reveal entry_v] **
          (exists* (vb va: IT.mixed_list U64.t cbor_map_entry). R.pts_to (B.box_to_ref bb) vb ** R.pts_to (B.box_to_ref ba) va)) **
      Trade.trade
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R s_i [Ghost.reveal entry_v])
        (cbor_match_map_entry 1.0R cme' entry_v ** (exists* (w: cbor_map_entry). R.pts_to (B.box_to_ref bs) w)) **
      Trade.trade (cbor_match_map_entry 1.0R cme' entry_v) (freeable key' ** freeable value') **
      Trade.trade
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_cur l_acc)
        (SM.seq_list_match (Seq.seq_of_list mg_acc) ft_acc freeable_match_mapgen_elt) **
      pure (
        R.is_full_ref (B.box_to_ref bs) /\
        R.is_full_ref (B.box_to_ref bb) /\
        R.is_full_ref (B.box_to_ref ba)
      )
    )
    fn _
    {
      Trade.elim _
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_cur l_acc **
          I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R s_i [Ghost.reveal entry_v] **
          (exists* (vb va: IT.mixed_list U64.t cbor_map_entry). R.pts_to (B.box_to_ref bb) vb ** R.pts_to (B.box_to_ref ba) va));
      Trade.elim _
        (cbor_match_map_entry 1.0R cme' entry_v ** (exists* (w: cbor_map_entry). R.pts_to (B.box_to_ref bs) w));
      Trade.elim _ (freeable key' ** freeable value');
      Trade.elim _ (SM.seq_list_match (Seq.seq_of_list mg_acc) ft_acc freeable_match_mapgen_elt);
      unfold (freeable key');
      unfold (freeable value');
      mapgen_elt_fold key'.footprint value'.footprint (key'.tree, value'.tree) bs bb ba;
      rewrite
        (freeable_match' key'.footprint key'.tree **
          freeable_match' value'.footprint value'.tree **
          (exists* (w: cbor_map_entry). R.pts_to (B.box_to_ref bs) w) **
          (exists* (wb wa: IT.mixed_list U64.t cbor_map_entry). R.pts_to (B.box_to_ref bb) wb ** R.pts_to (B.box_to_ref ba) wa) **
          pure (R.is_full_ref (B.box_to_ref bs) /\ R.is_full_ref (B.box_to_ref bb) /\ R.is_full_ref (B.box_to_ref ba)))
        as (freeable_match_mapgen_elt new_elt (key'.tree, value'.tree));
      Seq.lemma_seq_of_list_induction (new_elt :: mg_acc);
      SM.seq_list_match_cons_intro new_elt (key'.tree, value'.tree) (Seq.seq_of_list mg_acc) ft_acc freeable_match_mapgen_elt;
      rewrite (SM.seq_list_match (Seq.cons new_elt (Seq.seq_of_list mg_acc)) ((key'.tree, value'.tree) :: ft_acc) freeable_match_mapgen_elt)
        as (SM.seq_list_match (Seq.seq_of_list (new_elt :: mg_acc)) ((key'.tree, value'.tree) :: ft_acc) freeable_match_mapgen_elt);
    };
    rewrite
      (Trade.trade
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc' (List.Tot.append l_acc [Ghost.reveal entry_v]))
        (SM.seq_list_match (Seq.seq_of_list (new_elt :: mg_acc)) ((key'.tree, value'.tree) :: ft_acc) freeable_match_mapgen_elt))
      as
      (Trade.trade
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc' (List.Tot.append l_acc [Ghost.reveal entry_v]))
        (SM.seq_list_match (Seq.seq_of_list (({ mge_key_footprint = key'.footprint; mge_val_footprint = value'.footprint; mge_box_elt = bs; mge_box_before = bb; mge_box_after = ba } <: cbor_freeable_mapgen_elt) :: mg_acc)) ((key'.tree, value'.tree) :: ft_acc) freeable_match_mapgen_elt));
}

// Deep-copy a _Gen map by streaming its entries through the depth-aware map
// iterator into the same CBOR_Copy_Map footprint the inline arm builds.
#restart-solver
inline_for_extraction
fn cbor_copy_map_gen_d
  (depth: Ghost.erased nat)
  (copy: (depth': Ghost.erased nat { depth' < depth }) -> cbor_copy_with_depth_t depth')
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match_with_depth depth p x v ** pure (CBOR_Case_Map_Gen? x /\ raw_data_item_size v <= Ghost.reveal depth))
returns res: cbor_freeable
ensures
    (
      cbor_match_with_depth depth p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )
{
  cbor_match_with_depth_cases depth p x v;
  let a = get_cbor_raw_map_gen x;
  rewrite (cbor_match_with_depth depth p x v)
    as (cbor_match_with_depth depth p (CBOR_Case_Map_Gen a) v);
  // --- get entry count as SZ.t and relate it to List.length (Map?.v v) ---
  cbor_match_with_depth_map_gen_elim depth p a v;
  let count = ML.cbor_raw_mixed_list_length a.cbor_map_gen_ptr;
  cbor_match_mixed_list_map_length p a v (depth_cb depth v);
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Map_Gen a) v);
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Map_Gen a) v)
    as (cbor_match_with_depth depth p x v);
  // --- initialize the depth-aware map iterator (dispatches _Gen) ---
  let it = cbor_map_iterator_init_with_depth depth x;
  with p_it . assert (cbor_map_iterator_match_with_depth (nat_pred depth) p_it it (Map?.v v));
  // --- pre-allocate destination vectors ---
  // The entry count [count : U64.t] IS the loop bound: the fold iterates
  // [count] times over a u64 counter, so no [size_t] conversion (and hence no
  // [SZ.fits] bound on the whole value) is required.
  map_length_le_size v;
  assert (pure (U64.v count == List.Tot.length (Map?.v v)));
  let len64 : raw_uint64 = { size = a.cbor_map_gen_length_size; value = count };
  assert (pure (len64 == Map?.len v));
  // === build a structural (_Gen) map by folding singletons via Append ===
  Append.mixed_list_empty cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R;
  let acc0 : IT.mixed_list U64.t cbor_map_entry = IT.Base IT.Empty;
  rewrite (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R (IT.Base IT.Empty <: IT.mixed_list U64.t cbor_map_entry) [])
    as (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc0 []);
  let mut pacc = acc0;
  let mut pi = 0uL;
  let mut pit = it;
  // the footprint spine is a heap box-chain built up (one O(1) node per entry)
  // alongside the map; it starts empty and is captured into the destructor
  // trade once the map is finalized.
  let mut phead : option (B.box mapgen_node) = None;
  fold (mapgen_spine (None #(B.box mapgen_node)) ([] <: list cbor_freeable_mapgen_elt));
  Trade.refl (cbor_map_iterator_match_with_depth (nat_pred depth) p_it it (Map?.v v));
  // initial destructor trade: the empty mixed_list is a pure resource, so
  // [mlm acc0 []] can be dropped and [seq_list_match] on empty lists built.
  intro
    (Trade.trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc0 [])
      (SM.seq_list_match (Seq.seq_of_list ([] <: list cbor_freeable_mapgen_elt)) ([] <: list (freeable_tree & freeable_tree)) freeable_match_mapgen_elt))
    #emp
    fn _
  {
    drop_ (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc0 []);
    SM.seq_list_match_nil_intro (Seq.seq_of_list ([] <: list cbor_freeable_mapgen_elt)) ([] <: list (freeable_tree & freeable_tree)) freeable_match_mapgen_elt;
  };
  while (
    let i = !pi;
    (U64.lt i count)
  ) invariant exists* i gi m pj acc l_acc mg ft hd_ptr . (
    pts_to pi i **
    pts_to pit gi **
    pts_to pacc acc **
    pts_to phead hd_ptr **
    mapgen_spine hd_ptr mg **
    cbor_map_iterator_match_with_depth (nat_pred depth) pj gi m **
    Trade.trade
      (cbor_map_iterator_match_with_depth (nat_pred depth) pj gi m)
      (cbor_map_iterator_match_with_depth (nat_pred depth) p_it it (Map?.v v)) **
    I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc l_acc **
    Trade.trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc l_acc)
      (SM.seq_list_match (Seq.seq_of_list mg) ft freeable_match_mapgen_elt) **
    pure (
      U64.v i <= U64.v count /\
      U64.v count == List.Tot.length (Ghost.reveal (Map?.v v)) /\
      (len64 <: raw_uint64) == Map?.len v /\
      List.Tot.length (Ghost.reveal l_acc) == U64.v i /\
      Ghost.reveal m == snd (List.Tot.splitAt (U64.v i) (Ghost.reveal (Map?.v v))) /\
      List.Tot.append (Ghost.reveal l_acc) (Ghost.reveal m) == Ghost.reveal (Map?.v v)
    )
  ) {
    let i = !pi;
    with gi m pj acc l_acc mg ft hd_ptr . assert (
      pts_to pit gi **
      pts_to pacc acc **
      pts_to phead hd_ptr **
      mapgen_spine hd_ptr mg **
      cbor_map_iterator_match_with_depth (nat_pred depth) pj gi m **
      Trade.trade
        (cbor_map_iterator_match_with_depth (nat_pred depth) pj gi m)
        (cbor_map_iterator_match_with_depth (nat_pred depth) p_it it (Map?.v v)) **
      I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc l_acc **
      Trade.trade
        (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc l_acc)
        (SM.seq_list_match (Seq.seq_of_list mg) ft freeable_match_mapgen_elt)
    );
    List.Tot.append_length (Ghost.reveal l_acc) (Ghost.reveal m);
    // identify the head entry with index i, and expose the one-step advance
    splitAt_snd_cons (U64.v i) (Map?.v v);
    let c = cbor_map_iterator_next_with_depth (nat_pred depth) pit;
    Trade.trans _ _ (cbor_map_iterator_match_with_depth (nat_pred depth) p_it it (Map?.v v));
    // size bounds for the recursive key/value copies
    size_map_entry v (List.Tot.index (Map?.v v) (U64.v i));
    // the iterator yields Match's depth-entry predicate; unfold/copy/fold under
    // that (qualified) name to keep it matched against the iterator's trade.
    with pe a1 . assert (Match.cbor_match_map_entry_with_depth (nat_pred depth) pe c a1);
    unfold (Match.cbor_match_map_entry_with_depth (nat_pred depth) pe c a1);
    let key' = copy (nat_pred depth) c.cbor_map_entry_key;
    let value' = copy (nat_pred depth) c.cbor_map_entry_value;
    fold (Match.cbor_match_map_entry_with_depth (nat_pred depth) pe c a1);
    Trade.elim_hyp_l _ _ (cbor_map_iterator_match_with_depth (nat_pred depth) p_it it (Map?.v v));
    // combine the two copies into a single entry match plus a destructor trade
    // [cbor_match_map_entry cme' a1 --* (freeable key' ** freeable value')]
    Trade.prod
      (cbor_match 1.0R key'.cbor (fst a1))
      (freeable key')
      (cbor_match 1.0R value'.cbor (snd a1))
      (freeable value');
    let cme' = {
      cbor_map_entry_key = key'.cbor;
      cbor_map_entry_value = value'.cbor;
    };
    Trade.rewrite_with_trade
      (cbor_match 1.0R key'.cbor (fst a1) **
        cbor_match 1.0R value'.cbor (snd a1)
      )
      (cbor_match_map_entry 1.0R cme' a1);
    Trade.trans (cbor_match_map_entry 1.0R cme' a1) _ _;
    // build a singleton entry mixed_list and append it to the accumulator
    let bs = B.alloc cme';
    B.to_ref_pts_to bs;
    let s_i = Append.mixed_list_singleton cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R cme' a1 (B.box_to_ref bs) cbor_match_map_entry_gather;
    let acc_cur = !pacc;
    let bb = B.alloc (IT.Base IT.Empty <: IT.mixed_list U64.t cbor_map_entry);
    let ba = B.alloc (IT.Base IT.Empty <: IT.mixed_list U64.t cbor_map_entry);
    B.to_ref_pts_to bb;
    B.to_ref_pts_to ba;
    // discharge [io.fits] for the append from the length bounds:
    //   len(acc_cur) == length l_acc == i  and  len(s_i) == 1, so
    //   len(acc_cur) + len(s_i) == i+1 <= count < 2^64.
    I.mixed_list_match_length cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_cur l_acc;
    I.mixed_list_match_length cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R s_i [a1];
    let acc' = Append.mixed_list_append cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_cur l_acc s_i [a1] (B.box_to_ref bb) (B.box_to_ref ba);
    List.Tot.append_assoc (Ghost.reveal l_acc) [a1]
      (snd (List.Tot.splitAt (U64.v i + 1) (Ghost.reveal (Map?.v v))));
    mapgen_step l_acc a1 acc_cur acc' s_i cme' key' value' bs bb ba mg ft;
    let head_cur = !phead;
    let new_head = mapgen_cons ({ mge_key_footprint = key'.footprint; mge_val_footprint = value'.footprint; mge_box_elt = bs; mge_box_before = bb; mge_box_after = ba } <: cbor_freeable_mapgen_elt) head_cur;
    phead := new_head;
    pacc := acc';
    pi := (U64.add i 1uL);
  };
  Trade.elim _ (cbor_map_iterator_match_with_depth (nat_pred depth) p_it it (Map?.v v));
  Trade.elim _ (cbor_match_with_depth depth p x v);
  // at loop exit, [i == len == length (Map?.v v)], so the iterator suffix is
  // empty and [l_acc == Map?.v v]
  with acc_g l_acc_g mg_g ft_g hd_g . assert (
    I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_g l_acc_g **
    Trade.trade
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc_g l_acc_g)
      (SM.seq_list_match (Seq.seq_of_list mg_g) ft_g freeable_match_mapgen_elt) **
    pts_to phead hd_g **
    mapgen_spine hd_g mg_g
  );
  FStar.List.Tot.Base.lemma_splitAt_snd_length (U64.v count) (Ghost.reveal (Map?.v v));
  List.Tot.Properties.append_length (Ghost.reveal l_acc_g) (snd (List.Tot.splitAt (U64.v count) (Ghost.reveal (Map?.v v))));
  List.Tot.Properties.append_l_nil (Ghost.reveal l_acc_g);
  assert (pure (Ghost.reveal l_acc_g == Ghost.reveal (Map?.v v)));
  assert (pure (List.Tot.length (Ghost.reveal l_acc_g) == U64.v count));
  assert (pure (U64.v (len64.value) == U64.v count));
  let acc = !pacc;
  let head_final = !phead;
  rewrite (mapgen_spine hd_g mg_g) as (mapgen_spine head_final mg_g);
  // finalize with the source's (possibly non-minimal) length header [len64],
  // so the resulting match reproduces [v] exactly.
  assert (pure (MB.cbor_map_len_ok len64 (Ghost.reveal l_acc_g)));
  let y = MB.cbor_mk_map_full_with_len 1.0R acc len64;
  // [cbor_mk_map_full_with_len] exposes the CONCRETE match [cbor_match y (Map
  // len64 l_acc_g)] (no existential length witness).  Bind the finalized value
  // with a single metavariable, then unfold.
  with fv . assert (MB.cbor_map_finalized_val 1.0R acc y fv);
  unfold (MB.cbor_map_finalized_val 1.0R acc y fv);
  // build the structural result and its destructor trade
  let res : cbor_freeable = {
    cbor = y;
    footprint = CBOR_Copy_MapGen head_final;
    tree = FTMapGen ft_g;
  };
  // [fv == Map len64 l_acc_g] (finalize), [len64 == Map?.len v] (invariant),
  // [l_acc_g == Map?.v v] (loop exit) give [fv == v]; relabel the concrete
  // finalize match and its destructor trade to the source value [v].
  assert (pure (Ghost.reveal l_acc_g == Ghost.reveal (Map?.v v)));
  assert (pure (fv == Ghost.reveal v));
  rewrite (cbor_match 1.0R y fv)
    as (cbor_match 1.0R res.cbor v);
  rewrite (Trade.trade
      (cbor_match 1.0R y fv)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc (Map?.v fv)))
    as (Trade.trade
      (cbor_match 1.0R res.cbor v)
      (I.mixed_list_match cbor_match_map_entry IO.u64_ops map_entry_parser 1.0R acc (Ghost.reveal l_acc_g)));
  // compose the finalize trade [cbor_match res.cbor v --* mlm acc l] with the
  // accumulated destructor trade [mlm acc l --* seq_list_match entries]
  Trade.trans _ _
    (SM.seq_list_match (Seq.seq_of_list mg_g) ft_g freeable_match_mapgen_elt);
  // capture the live footprint spine [mapgen_spine head_final mg_g] into the
  // destructor trade, so firing it reproduces the full [freeable res]
  intro
    (Trade.trade
      (cbor_match 1.0R res.cbor v)
      (freeable res))
    #(mapgen_spine head_final mg_g **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (SM.seq_list_match (Seq.seq_of_list mg_g) ft_g freeable_match_mapgen_elt))
    fn _
  {
    Trade.elim _ (SM.seq_list_match (Seq.seq_of_list mg_g) ft_g freeable_match_mapgen_elt);
    SM.seq_list_match_weaken (Seq.seq_of_list mg_g) ft_g
      freeable_match_mapgen_elt
      (freeable_match_mapgen_elt' (FTMapGen ft_g) freeable_match')
      (freeable_match_mapgen_elt_weaken_recip ft_g);
    fold (freeable_match' (CBOR_Copy_MapGen head_final) (FTMapGen ft_g));
    rewrite (freeable_match' (CBOR_Copy_MapGen head_final) (FTMapGen ft_g))
      as (freeable_match' res.footprint res.tree);
    fold (freeable res);
  };
  res
}

inline_for_extraction
fn cbor_copy0_body
  (depth: Ghost.erased nat)
  (copy: (depth': Ghost.erased nat { depth' < depth }) -> cbor_copy_with_depth_t depth')
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires cbor_match_with_depth depth p x v ** pure (raw_data_item_size v <= Ghost.reveal depth)
returns res: cbor_freeable
ensures cbor_match_with_depth depth p x v ** cbor_match 1.0R res.cbor v ** Trade.trade (cbor_match 1.0R res.cbor v) (freeable res)
{
  cbor_match_with_depth_cases depth p x v;
  match x {
    norewrite
    CBOR_Case_Int ct -> {
      cbor_match_with_depth_eq_match_int depth p ct v;
      rewrite (cbor_match_with_depth depth p x v) as (cbor_match p x v);
      let ty = cbor_match_int_elim_type x;
      let w = cbor_match_int_elim_value x;
      let c' = cbor_match_int_intro ty w;
      let res = {
        cbor = c';
        footprint = CBOR_Copy_Unit;
        tree = FTUnit;
      };
      intro
        (Trade.trade
          (cbor_match 1.0R c' (Int64 ty w))
          (freeable res)
        )
        #emp
        fn _
      {
        cbor_match_int_free c';
        fold (freeable_match' CBOR_Copy_Unit FTUnit);
        rewrite (freeable_match' CBOR_Copy_Unit FTUnit) as freeable_match' res.footprint res.tree;
        fold (freeable res)
      };
      rewrite each cbor_match 1.0R c' (Int64 ty w)
        as cbor_match 1.0R res.cbor v;
      cbor_match_with_depth_eq_match_int depth p ct v;
      rewrite (cbor_match p x v) as (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_Simple ct -> {
      cbor_match_with_depth_eq_match_simple depth p ct v;
      rewrite (cbor_match_with_depth depth p x v) as (cbor_match p x v);
      let w = cbor_match_simple_elim x;
      let c' = cbor_match_simple_intro w;
      let res = {
        cbor = c';
        footprint = CBOR_Copy_Unit;
        tree = FTUnit;
      };
      intro
        (Trade.trade
          (cbor_match 1.0R c' (Simple w))
          (freeable res)
        )
        #emp
        fn _
      {
        cbor_match_simple_free c';
        fold (freeable_match' CBOR_Copy_Unit FTUnit);
        rewrite (freeable_match' CBOR_Copy_Unit FTUnit) as freeable_match' res.footprint res.tree;
        fold (freeable res)
      };
      rewrite each cbor_match 1.0R c' (Simple w) as cbor_match 1.0R res.cbor v;
      cbor_match_with_depth_eq_match_simple depth p ct v;
      rewrite (cbor_match p x v) as (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_String ct -> {
      cbor_match_with_depth_eq_match_string depth p ct v;
      rewrite (cbor_match_with_depth depth p x v) as (cbor_match p x v);
      let ty = cbor_match_string_elim_type x;
      let len = cbor_match_string_elim_length x;
      let pl = cbor_match_string_elim_payload x;
      S.pts_to_len pl;
      let len_sz = S.len pl;
      let v' = V.alloc 0uy len_sz;
      V.to_array_pts_to v';
      let s' = S.from_array (V.vec_to_array v') len_sz;
      S.pts_to_len s';
      S.copy s' pl;
      Trade.elim _ _;
      with vs' . assert (pts_to s' vs');
      let c' = cbor_match_string_intro ty len s';
      let res = {
        cbor = c';
        footprint = CBOR_Copy_Bytes v';
        tree = FTBytes;
      };
      intro
        (Trade.trade
          (pts_to s' vs')
          (freeable res)
        )
        #(S.is_from_array (V.vec_to_array v') s')
        fn _
      {
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (CBOR_Copy_Bytes v') FTBytes);
        rewrite (freeable_match' (CBOR_Copy_Bytes v') FTBytes) as freeable_match' res.footprint res.tree;
        fold (freeable res)
      };
      Trade.trans _ (pts_to s' vs') _;
      with r_ . assert cbor_match 1.0R c' r_;
      rewrite each cbor_match 1.0R c' r_ as cbor_match 1.0R res.cbor v;
      cbor_match_with_depth_eq_match_string depth p ct v;
      rewrite (cbor_match p x v) as (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_Tagged a -> {
      rewrite (cbor_match_with_depth depth p x v)
        as (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
      cbor_match_with_depth_tagged_elim depth p a v;
      with c0 . assert (pts_to a.cbor_tagged_ptr #(p `perm_mul` a.cbor_tagged_ref_perm) c0 **
        cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_tagged_payload_perm) c0 (Tagged?.v v));
      let tag = a.cbor_tagged_tag;
      let plc = !a.cbor_tagged_ptr;
      rewrite (cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_tagged_payload_perm) c0 (Tagged?.v v))
        as (cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_tagged_payload_perm) plc (Tagged?.v v));
      size_tagged_child v;
      let cpl' = copy (nat_pred depth) plc;
      rewrite (cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_tagged_payload_perm) plc (Tagged?.v v))
        as (cbor_match_with_depth (nat_pred depth) (p `perm_mul` a.cbor_tagged_payload_perm) c0 (Tagged?.v v));
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v)
        as (cbor_match_with_depth depth p x v);
      let bf = B.alloc cpl'.footprint;
      let b = B.alloc cpl'.cbor;
      B.to_ref_pts_to b;
      let c' = cbor_match_tagged_intro tag (B.box_to_ref b);
      Trade.trans_concl_r _ _ _ _;
      let fb = {
          box_cbor = b;
          box_footprint = bf;
      };
      let res = {
        cbor = c';
        footprint = CBOR_Copy_Box fb;
        tree = FTBox cpl'.tree
      };
      intro
        (Trade.trade
          (pts_to (B.box_to_ref b) cpl'.cbor ** freeable cpl')
          (freeable res)
        )
        #(pts_to bf cpl'.footprint)
        fn _
      {
        B.to_box_pts_to b;
        rewrite (pts_to bf cpl'.footprint) as (pts_to fb.box_footprint cpl'.footprint);
        rewrite (pts_to b cpl'.cbor) as (pts_to fb.box_cbor) (cpl'.cbor);
        unfold (freeable cpl');
        fold (freeable_match_box fb cpl'.tree);
        freeable_match_box_eq fb cpl'.tree;
        rewrite (freeable_match_box fb cpl'.tree) as freeable_match' res.footprint res.tree;
        fold (freeable res)
      };
      Trade.trans _ _ (freeable res);
      rewrite each cbor_match 1.0R c' (Tagged tag (Tagged?.v v))
        as cbor_match 1.0R res.cbor v;
      res
    }
    norewrite
    CBOR_Case_Array a -> {
      cbor_copy_array_d depth copy x;
    }
    norewrite
    CBOR_Case_Map a -> {
      cbor_copy_map_d depth copy x;
    }
    norewrite
    CBOR_Case_Array_Gen a -> {
      cbor_copy_array_gen_d depth copy x;
    }
    norewrite
    CBOR_Case_Map_Gen a -> {
      cbor_copy_map_gen_d depth copy x;
    }
    norewrite
    CBOR_Case_Serialized_Array a -> {
      cbor_match_with_depth_eq_match_ser_array depth p a v;
      rewrite (cbor_match_with_depth depth p x v) as (cbor_match p x v);
      Trade.rewrite_with_trade
        (cbor_match p x v)
        (cbor_match_serialized_array a p v);
      unfold (cbor_match_serialized_array a p v);
      let len = S.len (to_slice a.cbor_serialized_payload);
      let v' = V.alloc 0uy len;
      V.pts_to_len v';
      V.to_array_pts_to v';
      let s' = S.from_array (V.vec_to_array v') len;
      S.pts_to_len s';
      cbor_match_serialized_payload_array_copy (to_slice a.cbor_serialized_payload) _ _ s';
      fold (cbor_match_serialized_array a p v);
      Trade.elim _ (cbor_match p x v);
      let a' = {
        cbor_serialized_header = a.cbor_serialized_header;
        cbor_serialized_payload = of_slice s';
        cbor_serialized_perm = 1.0R;
      };
      rewrite cbor_match_serialized_payload_array s' 1.0R (Array?.v v)
        as cbor_match_serialized_payload_array (to_slice a'.cbor_serialized_payload)
        (perm_mul 1.0R a'.cbor_serialized_perm)
        (Array?.v v);
      fold (cbor_match_serialized_array a' 1.0R v);
      let res = {
        cbor = CBOR_Case_Serialized_Array a';
        footprint = CBOR_Copy_Bytes v';
        tree = FTBytes;
      };
      Trade.intro_trade
        (cbor_match_serialized_array a' 1.0R v)
        (freeable res)
        (
          Trade.trade
            (cbor_match_serialized_payload_array s' 1.0R (Array?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        )
        fn _
      {
        unfold (cbor_match_serialized_array a' 1.0R v);
        rewrite     cbor_match_serialized_payload_array (to_slice a'.cbor_serialized_payload)
          (perm_mul 1.0R a'.cbor_serialized_perm)
          (Array?.v v)
          as cbor_match_serialized_payload_array s' 1.0R (Array?.v v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (CBOR_Copy_Bytes v') FTBytes);
        rewrite (freeable_match' (CBOR_Copy_Bytes v') FTBytes) as freeable_match' res.footprint res.tree;
        fold (freeable res)
      };
      Trade.rewrite_with_trade
        (cbor_match_serialized_array a' 1.0R v)
        (cbor_match 1.0R res.cbor v);
      Trade.trans (cbor_match 1.0R res.cbor v) _ _;
      cbor_match_with_depth_eq_match_ser_array depth p a v;
      rewrite (cbor_match p x v) as (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Map a -> {
      cbor_match_with_depth_eq_match_ser_map depth p a v;
      rewrite (cbor_match_with_depth depth p x v) as (cbor_match p x v);
      Trade.rewrite_with_trade
        (cbor_match p x v)
        (cbor_match_serialized_map a p v);
      unfold (cbor_match_serialized_map a p v);
      let len = S.len (to_slice a.cbor_serialized_payload);
      let v' = V.alloc 0uy len;
      V.pts_to_len v';
      V.to_array_pts_to v';
      let s' = S.from_array (V.vec_to_array v') len;
      S.pts_to_len s';
      cbor_match_serialized_payload_map_copy (to_slice a.cbor_serialized_payload) _ _ s';
      fold (cbor_match_serialized_map a p v);
      Trade.elim _ (cbor_match p x v);
      let a' = {
        cbor_serialized_header = a.cbor_serialized_header;
        cbor_serialized_payload = of_slice s';
        cbor_serialized_perm = 1.0R;
      };
      rewrite cbor_match_serialized_payload_map s' 1.0R (Map?.v v) as cbor_match_serialized_payload_map (to_slice a'.cbor_serialized_payload)
        (perm_mul 1.0R a'.cbor_serialized_perm)
        (Map?.v v);
      fold (cbor_match_serialized_map a' 1.0R v);
      let res = {
        cbor = CBOR_Case_Serialized_Map a';
        footprint = CBOR_Copy_Bytes v';
        tree = FTBytes;
      };
      Trade.intro_trade
        (cbor_match_serialized_map a' 1.0R v)
        (freeable res)
        (
          Trade.trade
            (cbor_match_serialized_payload_map s' 1.0R (Map?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        )
        fn _
      {
        unfold (cbor_match_serialized_map a' 1.0R v);
        rewrite cbor_match_serialized_payload_map (to_slice a'.cbor_serialized_payload)
          (perm_mul 1.0R a'.cbor_serialized_perm)
          (Map?.v v)
          as  cbor_match_serialized_payload_map s' 1.0R (Map?.v v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (CBOR_Copy_Bytes v') FTBytes);
        rewrite (freeable_match' (CBOR_Copy_Bytes v') FTBytes) as freeable_match' res.footprint res.tree;
        fold (freeable res)
      };
      Trade.rewrite_with_trade
        (cbor_match_serialized_map a' 1.0R v)
        (cbor_match 1.0R res.cbor v);
      Trade.trans (cbor_match 1.0R res.cbor v) _ _;
      cbor_match_with_depth_eq_match_ser_map depth p a v;
      rewrite (cbor_match p x v) as (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Tagged a -> {
      cbor_match_with_depth_eq_match_ser_tagged depth p a v;
      rewrite (cbor_match_with_depth depth p x v) as (cbor_match p x v);
      Trade.rewrite_with_trade
        (cbor_match p x v)
        (cbor_match_serialized_tagged a p v);
      unfold (cbor_match_serialized_tagged a p v);
      let len = S.len (to_slice a.cbor_serialized_payload);
      let v' = V.alloc 0uy len;
      V.pts_to_len v';
      V.to_array_pts_to v';
      let s' = S.from_array (V.vec_to_array v') len;
      S.pts_to_len s';
      cbor_match_serialized_payload_tagged_copy (to_slice a.cbor_serialized_payload) _ _ s';
      fold (cbor_match_serialized_tagged a p v);
      Trade.elim _ (cbor_match p x v);
      let a' = {
        cbor_serialized_header = a.cbor_serialized_header;
        cbor_serialized_payload = of_slice s';
        cbor_serialized_perm = 1.0R;
      };
      rewrite cbor_match_serialized_payload_tagged s' 1.0R (Tagged?.v v)
        as cbor_match_serialized_payload_tagged (to_slice a'.cbor_serialized_payload)
        (perm_mul 1.0R a'.cbor_serialized_perm)
        (Tagged?.v v);
      fold (cbor_match_serialized_tagged a' 1.0R v);
      let res = {
        cbor = CBOR_Case_Serialized_Tagged a';
        footprint = CBOR_Copy_Bytes v';
        tree = FTBytes;
      };
      Trade.intro_trade
        (cbor_match_serialized_tagged a' 1.0R v)
        (freeable res)
        (
          Trade.trade
            (cbor_match_serialized_payload_tagged s' 1.0R (Tagged?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        )
        fn _
      {
        unfold (cbor_match_serialized_tagged a' 1.0R v);
        rewrite cbor_match_serialized_payload_tagged (to_slice a'.cbor_serialized_payload)
          (perm_mul 1.0R a'.cbor_serialized_perm)
          (Tagged?.v v) as cbor_match_serialized_payload_tagged s' 1.0R (Tagged?.v v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (CBOR_Copy_Bytes v') FTBytes);
        rewrite (freeable_match' (CBOR_Copy_Bytes v') FTBytes) as freeable_match' res.footprint res.tree;
        fold (freeable res)
      };
      Trade.rewrite_with_trade
        (cbor_match_serialized_tagged a' 1.0R v)
        (cbor_match 1.0R res.cbor v);
      Trade.trans (cbor_match 1.0R res.cbor v) _ _;
      cbor_match_with_depth_eq_match_ser_tagged depth p a v;
      rewrite (cbor_match p x v) as (cbor_match_with_depth depth p x v);
      res
    }
  }
}

fn rec cbor_copy0_with_depth (depth: Ghost.erased nat) (x: cbor_raw) (#p: perm) (#v: Ghost.erased raw_data_item)
  requires cbor_match_with_depth depth p x v ** pure (raw_data_item_size v <= Ghost.reveal depth)
  returns res: cbor_freeable
  ensures cbor_match_with_depth depth p x v ** cbor_match 1.0R res.cbor v ** Trade.trade (cbor_match 1.0R res.cbor v) (freeable res)
  decreases (Ghost.reveal depth)
{
  cbor_copy0_body depth (fun (depth': Ghost.erased nat { depth' < depth }) -> cbor_copy0_with_depth depth') x
}

fn cbor_copy0 (x: cbor_raw) (#p: perm) (#v: Ghost.erased raw_data_item)
  requires cbor_match p x v
  returns res: cbor_freeable
  ensures cbor_match p x v ** cbor_match 1.0R res.cbor v ** Trade.trade (cbor_match 1.0R res.cbor v) (freeable res)
{
  let n = Ghost.hide (raw_data_item_size v);
  cbor_match_to_depth n p x v;
  let res = cbor_copy0_with_depth n x;
  cbor_match_with_depth_forget n p x v;
  res
}
