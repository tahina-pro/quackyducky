module CBOR.Pulse.API.Nondet.C
#lang-pulse
module Rust = CBOR.Pulse.Raw.Nondet

[@@pulse_unfold]
let cbor_nondet_match = Rust.cbor_nondet_match

(* raw/-visible interfaces of the everparse/ structural-builder adapters
   (relocated .fsti in raw/, .fst in everparse/, mirroring the proven
   CBOR.Pulse.Raw.Format.Match split). *)
module ANondet = CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder
module NMIS = CBOR.Pulse.Raw.EverParse.Nondet.MapInsertSpec
module NMRS = CBOR.Pulse.Raw.EverParse.Nondet.MapRemoveSpec
module ML = CBOR.Pulse.Raw.Format.MixedList
module RawT = CBOR.Pulse.Raw.Type

(* Needed to realize the dummy scratch-cell / entry placeholder values at the
   end of this module (mirrors CBOR.Pulse.API.Det.Dummy): it exposes
     cbor_nondet_map_entry_insert_cell_t == ML.cbor_raw_mixed_list cbor_map_entry
     cbor_nondet_map_entry_t            == cbor_map_entry. *)
friend CBOR.Pulse.API.Nondet.Type

(* NOTE: This module previously materialized an [FStar.SizeT.fits_u64]
   platform axiom to discharge [SZ.fits_u64] preconditions of the array /
   map-entry-insert adapters.  That is no longer needed: the lowparse
   mixed_list element counts are now [U64.t], so the relevant obligations
   are plain u64 facts ([U64.v _ < pow2 64]) and exact u64 overflow checks.
   The axiom has been ELIMINATED. *)

let cbor_nondet_reset_perm () = Rust.cbor_nondet_reset_perm ()

let cbor_nondet_share = Rust.cbor_nondet_share

let cbor_nondet_gather = Rust.cbor_nondet_gather

let cbor_nondet_parse () = cbor_nondet_parse_from_arrayptr (Rust.cbor_nondet_validate ()) (Rust.cbor_nondet_parse_valid ())

let cbor_nondet_match_with_size = Rust.cbor_nondet_match_with_size

let cbor_nondet_match_with_size_intro () = Rust.cbor_nondet_match_with_size_intro ()

let cbor_nondet_size () x bound #p #x' #v = Rust.cbor_nondet_size () x bound #p #x' #v

let cbor_nondet_serialize () = cbor_nondet_serialize_to_arrayptr (Rust.cbor_nondet_serialize ())

let cbor_nondet_major_type () x #p #y = Rust.cbor_nondet_major_type () x #p #y

let cbor_nondet_read_simple_value () = read_simple_value_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_simple_value ())

let cbor_nondet_elim_simple () = Rust.cbor_nondet_elim_simple ()

let cbor_nondet_read_uint64 () = read_uint64_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_uint64 ())

let cbor_nondet_read_int64 () = read_int64_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_uint64 ())

let cbor_nondet_elim_int64 () = Rust.cbor_nondet_elim_int64 ()

let cbor_nondet_get_string () = get_string_as_arrayptr_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_string_length ()) (get_string_as_arrayptr (Rust.cbor_nondet_get_string ()))

let cbor_nondet_get_byte_string () = get_string_as_arrayptr_safe_gen (cbor_nondet_major_type ()) (cbor_nondet_get_string ()) _

let cbor_nondet_get_text_string () = get_string_as_arrayptr_safe_gen (cbor_nondet_major_type ()) (cbor_nondet_get_string ()) _

let cbor_nondet_get_tagged () = get_tagged_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_tagged_tag ()) (Rust.cbor_nondet_get_tagged_payload ())

let cbor_nondet_get_array_length () = get_array_length_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_array_length ())

let cbor_nondet_array_iterator_match = Rust.cbor_nondet_array_iterator_match

let cbor_nondet_array_iterator_start () = array_iterator_start_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_array_iterator_start ())

let cbor_nondet_array_iterator_is_empty () x #p #y = Rust.cbor_nondet_array_iterator_is_empty () x #p #y

let cbor_nondet_array_iterator_length () x #p #y = Rust.cbor_nondet_array_iterator_length () x #p #y

let cbor_nondet_array_iterator_next () = array_iterator_next_safe (cbor_nondet_array_iterator_is_empty ()) (Rust.cbor_nondet_array_iterator_next ())

let cbor_nondet_array_iterator_truncate () x len #p #y = Rust.cbor_nondet_array_iterator_truncate () x len #p #y

let cbor_nondet_array_iterator_share () = Rust.cbor_nondet_array_iterator_share ()

let cbor_nondet_array_iterator_gather () = Rust.cbor_nondet_array_iterator_gather ()

let cbor_nondet_get_array_item () = get_array_item_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_array_length ()) (Rust.cbor_nondet_get_array_item ())

(* ================================================================ *)
(* STEP 2: structural array builder (nondeterministic).              *)
(* Realized on top of the raw/ adapter interface                     *)
(*   ANondet = CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder          *)
(* (implementation in everparse/).  [cbor_nondet_array_t] is realized *)
(* as [cbor_mixed_list_array]; after that the adapter's ops match the *)
(* public ones.  Placed here (interface order 100-178) so            *)
(* [cbor_nondet_array_t] precedes [cbor_nondet_get_map_length].       *)
(* ================================================================ *)

let cbor_nondet_array_t = CBOR.Pulse.Raw.Type.cbor_mixed_list_array

[@@pulse_unfold]
let cbor_nondet_array_owned = ANondet.cbor_nondet_array_owned

(* [init] delegates to the structural adapter.  (Formerly needed a
   [SZ.fits_u64] platform assumption; no longer — counts are [U64.t].) *)
fn cbor_nondet_array_init
  (x: cbor_nondet_t)
  (r1 r2: R.ref cbor_nondet_array_append_cell_t)
  (#p: perm)
  (#l: Ghost.erased Spec.cbor)
  (#w1 #w2: Ghost.erased cbor_nondet_array_append_cell_t)
requires
  (cbor_nondet_match p x l ** R.pts_to r1 w1 ** R.pts_to r2 w2 ** pure (Spec.CArray? (Spec.unpack l)))
returns y: cbor_nondet_array_t
ensures
  (exists* (l' : list Spec.cbor) .
    cbor_nondet_array_owned y l' **
    Trade.trade
      (cbor_nondet_array_owned y l')
      (cbor_nondet_match p x l ** (exists* w1 w2. R.pts_to r1 w1 ** R.pts_to r2 w2)) **
    pure (Spec.CArray? (Spec.unpack l) /\ l' == Spec.CArray?.v (Spec.unpack l)))
{
  ANondet.cbor_nondet_array_init x r1 r2
}

let cbor_nondet_array_empty = ANondet.cbor_nondet_array_empty
let cbor_nondet_array_singleton = ANondet.cbor_nondet_array_singleton

(* [append] delegates to the structural adapter (no [SZ.fits_u64] needed). *)
fn cbor_nondet_array_append
  (x1 x2: cbor_nondet_array_t)
  (r_before r_after: R.ref cbor_nondet_array_append_cell_t)
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased cbor_nondet_array_append_cell_t)
requires
  (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
   R.pts_to r_before vb0 ** R.pts_to r_after va0)
returns res: option cbor_nondet_array_t
ensures
  (match res with
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
{
  ANondet.cbor_nondet_array_append x1 x2 r_before r_after
}

let cbor_nondet_array_finalize = ANondet.cbor_nondet_array_finalize
let cbor_nondet_array_owned_length_fits = ANondet.cbor_nondet_array_owned_length_fits

let cbor_nondet_get_map_length () = get_map_length_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_map_length ())

let cbor_nondet_map_iterator_match = Rust.cbor_nondet_map_iterator_match

let cbor_nondet_map_iterator_start () = map_iterator_start_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_map_iterator_start ())

let cbor_nondet_map_iterator_is_empty () x #p #y = Rust.cbor_nondet_map_iterator_is_empty () x #p #y

let cbor_nondet_map_entry_match = Rust.cbor_nondet_map_entry_match

let cbor_nondet_map_entry_key () x #p #y = Rust.cbor_nondet_map_entry_key () x #p #y

let cbor_nondet_map_entry_value () x #p #y = Rust.cbor_nondet_map_entry_value () x #p #y

let cbor_nondet_map_iterator_next () = map_iterator_next_safe (cbor_nondet_map_iterator_is_empty ()) (Rust.cbor_nondet_map_iterator_next ()) (Rust.cbor_nondet_map_entry_share ()) (Rust.cbor_nondet_map_entry_gather ()) (cbor_nondet_map_entry_key ()) (cbor_nondet_map_entry_value ())

let cbor_nondet_map_iterator_share () = Rust.cbor_nondet_map_iterator_share ()

let cbor_nondet_map_iterator_gather () = Rust.cbor_nondet_map_iterator_gather ()

let cbor_nondet_map_entry_share () = Rust.cbor_nondet_map_entry_share ()

let cbor_nondet_map_entry_gather () = Rust.cbor_nondet_map_entry_gather ()

let cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2 = Rust.cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2

let cbor_nondet_map_get () = map_get_by_ref_safe (cbor_nondet_major_type ()) (map_get_as_ref (Rust.cbor_nondet_map_get ()))

let cbor_nondet_mk_simple_value () = mk_simple_safe (Rust.cbor_nondet_mk_simple_value ())

let cbor_nondet_mk_uint64 () v = Rust.cbor_nondet_mk_uint64 () v

let cbor_nondet_mk_neg_int64 () v = Rust.cbor_nondet_mk_neg_int64 () v

let cbor_nondet_mk_int64 () v = Rust.cbor_nondet_mk_int64 () v

let cbor_nondet_mk_byte_string () = mk_string_from_arrayptr (Rust.cbor_nondet_mk_string ()) cbor_major_type_byte_string

let cbor_nondet_mk_text_string () = mk_string_from_arrayptr (Rust.cbor_nondet_mk_string ()) cbor_major_type_text_string

let cbor_nondet_mk_tagged () = mk_tagged_safe (Rust.cbor_nondet_mk_tagged ())

let cbor_nondet_mk_array () = mk_array_from_arrayptr (Rust.cbor_nondet_mk_array ())

let cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv = Rust.cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv

let cbor_nondet_mk_map () = cbor_mk_map_from_arrayptr_safe (mk_map_gen_by_ref (Rust.cbor_nondet_mk_map ()))


noextract [@noextract_to "krml"]
let set_snd_None
  (t1 t2: Type)
  (x: (t1 & option t2))
: Tot (t1 & option t2)
= (fst x, None)

module PM = Pulse.Lib.SeqMatch.Util

ghost fn trade_assoc_hyp_r2l
  (a b c d: slprop)
requires
  Trade.trade (a ** (b ** c)) d
ensures
  Trade.trade ((a ** b) ** c) d
{
  slprop_equivs ();
  rewrite Trade.trade (a ** (b ** c)) d as Trade.trade ((a ** b) ** c) d
}

ghost fn trade_assoc_hyp_l2r
  (a b c d: slprop)
requires
  Trade.trade ((a ** b) ** c) d
ensures
  Trade.trade (a ** (b ** c)) d
{
  slprop_equivs ();
  rewrite Trade.trade ((a ** b) ** c) d as Trade.trade (a ** (b ** c)) d
}

ghost fn trade_assoc_concl_r2l
  (a b c d: slprop)
requires
  Trade.trade a (b ** (c ** d))
ensures
  Trade.trade a ((b ** c) ** d)
{
  slprop_equivs ();
  rewrite Trade.trade a (b ** (c ** d)) as Trade.trade a ((b ** c) ** d)
}

ghost fn trade_assoc_concl_l2r
  (a b c d: slprop)
requires
  Trade.trade a ((b ** c) ** d)
ensures
  Trade.trade a (b ** (c ** d))
{
  slprop_equivs ();
  rewrite Trade.trade a ((b ** c) ** d) as Trade.trade a (b ** (c ** d))
}

let list_memP_map_intro_forall
  (#a #b: Type)
  (f: a -> Tot b)
  (l: list a)
: Lemma
  (requires True)
  (ensures (forall x . List.Tot.memP x l ==> List.Tot.memP (f x) (List.Tot.map f l)))
= let prf
    (x: a)
  : Lemma
    (ensures List.Tot.memP x l ==> List.Tot.memP (f x) (List.Tot.map f l))
  = List.Tot.memP_map_intro f x l
  in
  Classical.forall_intro prf

ghost fn lemma_trade_ab_cd_e
  (a b1 b2 c d1 d2 e: slprop)
requires
  Trade.trade (b1 ** d1) (b2 ** d2) **
  Trade.trade ((a ** b2) ** (c ** d2)) e
ensures
  Trade.trade ((a ** b1) ** (c ** d1)) e
{
  slprop_equivs ();
  rewrite (Trade.trade ((a ** b2) ** (c ** d2)) e) as Trade.trade ((a ** c) ** (b2 ** d2)) e;
  Trade.trans_hyp_r (a ** c) _ _ _;
  rewrite Trade.trade ((a ** c) ** (b1 ** d1)) e as (Trade.trade ((a ** b1) ** (c ** d1)) e)
}

ghost fn trade_prod_cancel_hyp_r_concl_l
  (#a b #c #d #e: slprop)
requires
  Trade.trade (a ** b) c ** Trade.trade d (b ** e)
ensures
  Trade.trade (a ** d) (c ** e)
{
  intro
    (Trade.trade (a ** d) (c ** e))
    #(Trade.trade (a ** b) c ** Trade.trade d (b ** e))
    fn _ {
      Trade.elim d _;
      Trade.elim (a ** b) _
    }
}

ghost fn trade_prod_cancel_hyp_l_concl_l
  (b #a #c #d #e: slprop)
requires
  Trade.trade (b ** a) c ** Trade.trade d (b ** e)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (b ** a) c as Trade.trade (a ** b) c;
  trade_prod_cancel_hyp_r_concl_l b
}

ghost fn trade_prod_cancel_hyp_r_concl_r
  (#a b #c #d #e: slprop)
requires
  Trade.trade (a ** b) c ** Trade.trade d (e ** b)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade d (e ** b) as Trade.trade d (b ** e);
  trade_prod_cancel_hyp_r_concl_l b
}

ghost fn trade_prod_cancel_hyp_l_concl_r
  (b #a #c #d #e: slprop)
requires
  Trade.trade (b ** a) c ** Trade.trade d (e ** b)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (b ** a) c as Trade.trade (a ** b) c;
  trade_prod_cancel_hyp_r_concl_r b;
}

ghost fn trade_prod_cancel_concl_r_hyp_l
  (#a #b c #d #e: slprop)
requires
  Trade.trade a (b ** c) ** Trade.trade (c ** d) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (c ** d) e as Trade.trade (d ** c) e;
  trade_prod_cancel_hyp_r_concl_r c;
  rewrite Trade.trade (d ** a) (e ** b) as Trade.trade (a ** d) (b ** e)
}

ghost fn trade_prod_cancel_concl_l_hyp_l
  (#a c #b #d #e: slprop)
requires
  Trade.trade a (c ** b) ** Trade.trade (c ** d) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade a (c ** b) as Trade.trade a (b ** c);
  trade_prod_cancel_concl_r_hyp_l c;
}

ghost fn trade_prod_cancel_concl_r_hyp_r
  (#a #b c #d #e: slprop)
requires
  Trade.trade a (b ** c) ** Trade.trade (d ** c) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (d ** c) e as Trade.trade (c ** d) e;
  trade_prod_cancel_concl_r_hyp_l c
}

ghost fn trade_prod_cancel_concl_l_hyp_r
  (#a c #b #d #e: slprop)
requires
  Trade.trade a (c ** b) ** Trade.trade (d ** c) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade a (c ** b) as Trade.trade a (b ** c);
  trade_prod_cancel_concl_r_hyp_r c
}

ghost fn trade_comm_concl
  (a b c: slprop)
requires Trade.trade a (b ** c)
ensures Trade.trade a (c ** b)
{
  slprop_equivs();
  rewrite Trade.trade a (b ** c) as Trade.trade a (c ** b)
}

let lemma_seq_assoc_cons
  (#t: Type)
  (a: Seq.seq t)
  (b: t)
  (c: Seq.seq t)
: Lemma
  (Seq.equal (Seq.append a (Seq.cons b c)) (Seq.append (Seq.append a (Seq.cons b Seq.empty)) c))
= ()

let lemma_seq_assoc_cons_upd
  (#t: Type)
  (a: Seq.seq t)
  (c: Seq.seq t)
  (b': t)
: Lemma
  (requires Seq.length c > 0)
  (ensures Seq.equal
    (Seq.upd (Seq.append a c) (Seq.length a) b')
    (Seq.append (Seq.append a (Seq.cons b' Seq.empty)) (Seq.tail c))
  )
= ()

ghost fn lemma_trade_rewrite5
  (a b c d ef: slprop)
requires
   Trade.trade (((a **
        b) **
        c) **
        d)
      (ef)
ensures
   Trade.trade (a ** (d ** b ** c))
      (ef)
{
  slprop_equivs ();
  rewrite
   Trade.trade (((a **
        b) **
        c) **
        d)
      (ef)
  as Trade.trade (a ** (d ** b ** c))
      (ef)
}

ghost fn cbor_map_get_multiple_entry_match_snd_prop
  (#t: Type0)
  (vmatch: perm -> t -> Spec.cbor -> slprop)
  (x: cbor_map_get_multiple_entry_t t)
  (y: option Spec.cbor)
requires
  cbor_map_get_multiple_entry_match_snd vmatch true x y
ensures
  cbor_map_get_multiple_entry_match_snd vmatch true x y **
  pure (x.found == Some? y)
{
  if (x.found <> Some? y) {
    rewrite cbor_map_get_multiple_entry_match_snd vmatch true x y as pure False;
    rewrite emp as cbor_map_get_multiple_entry_match_snd vmatch true x y
  }
}

module S = Pulse.Lib.Slice.Util

let cbor_nondet_map_get_multiple () = cbor_map_get_multiple_as_arrayptr cbor_nondet_map_get_multiple_entry_t (cbor_nondet_major_type ()) (Rust.cbor_nondet_map_get_multiple ())

(* ================================================================ *)
(* STEP 2: dummy placeholders + structural map-entry insertion.      *)
(* (interface order 273-284, after cbor_nondet_map_get_multiple).     *)
(* ================================================================ *)

(* Dummy scratch-cell / entry placeholders (mirrors CBOR.Pulse.API.Det.Dummy).
   Realized via [friend CBOR.Pulse.API.Nondet.Type] (declared at the top). *)
let dummy_cbor_nondet_map_entry_insert_cell _ =
  ML.cbor_raw_mixed_list_dummy #RawT.cbor_map_entry ()

let dummy_cbor_nondet_map_entry _ = {
  RawT.cbor_map_entry_key = RawT.CBOR_Case_Simple 0uy;
  RawT.cbor_map_entry_value = RawT.CBOR_Case_Simple 0uy;
}

(* Bridge: the major type of [y] decides whether [unpack y] is a [CMap]. *)
let cmap_of_major_type_nondet (y: Spec.cbor)
: Lemma
    (requires (cbor_major_type y == cbor_major_type_map))
    (ensures (Spec.CMap? (Spec.unpack y)))
= ()

let not_cmap_of_major_type_nondet (y: Spec.cbor)
: Lemma
    (requires (~ (cbor_major_type y == cbor_major_type_map)))
    (ensures (~ (Spec.CMap? (Spec.unpack y))))
= ()

fn cbor_nondet_map_entry_insert
  (x key value: cbor_nondet_t)
  (r1 r2: R.ref cbor_nondet_map_entry_insert_cell_t)
  (ry: R.ref cbor_nondet_map_entry_t)
  (#p: perm) (#y: Ghost.erased Spec.cbor)
  (#pkv: perm) (#vk #vv: Ghost.erased Spec.cbor)
requires
    (cbor_nondet_match p x y **
     cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
     cbor_nondet_map_entry_insert_refs r1 r2 ry)
returns res: option cbor_nondet_t
ensures (match res with
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
{
  let mt = cbor_nondet_major_type () x;
  if (mt = cbor_major_type_map) {
    cmap_of_major_type_nondet y;
    unfold (cbor_nondet_map_entry_insert_refs r1 r2 ry);
    let res = NMIS.cbor_nondet_map_entry_insert_spec x key value r1 r2 ry;
    match res {
      None -> {
        fold (cbor_nondet_map_entry_insert_refs r1 r2 ry);
        None #cbor_nondet_t
      }
      Some m -> {
        Some m
      }
    }
  } else {
    not_cmap_of_major_type_nondet y;
    None #cbor_nondet_t
  }
}

(* ================================================================== *)
(* Zero-copy array slice (sub-range) — nondeterministic API.          *)
(* [cbor_nondet_array_slice] delegates to the structural adapter      *)
(*   ANondet = CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder           *)
(* which bridges the raw slice op                                     *)
(*   CBOR.Pulse.Raw.EverParse.ArrayBuilder.cbor_array_slice           *)
(* back to [cbor_nondet_match].  Both this module's                   *)
(* [cbor_nondet_array_slice_spec] and the adapter's have the same     *)
(* ([FStar.List.Tot.splitAt]-based) body, so their applications are   *)
(* provably equal.                                                    *)
(* ================================================================== *)

fn cbor_nondet_array_slice
  (x: cbor_nondet_t) (i j: U64.t)
  (r1 r2 r3 r4: R.ref cbor_nondet_array_append_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_nondet_array_append_cell_t)
requires
  (cbor_nondet_match p x v ** R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4
     ** pure (Spec.CArray? (Spec.unpack v)))
returns res: cbor_nondet_t
ensures
  (exists* (v': Spec.cbor).
     cbor_nondet_match 1.0R res v' **
     Trade.trade (cbor_nondet_match 1.0R res v')
       (cbor_nondet_match p x v ** (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
     pure (Spec.CArray? (Spec.unpack v) /\ Spec.CArray? (Spec.unpack v') /\
           (Spec.CArray?.v (Spec.unpack v') <: list Spec.cbor) == cbor_nondet_array_slice_spec (Spec.CArray?.v (Spec.unpack v)) i j))
{
  ANondet.cbor_nondet_array_slice_bridge x i j r1 r2 r3 r4
}

(* Bridge: the major type of [y] decides whether [unpack y] is a [CArray]. *)
let carray_of_major_type_nondet (y: Spec.cbor)
: Lemma
    (requires (cbor_major_type y == cbor_major_type_array))
    (ensures (Spec.CArray? (Spec.unpack y)))
= ()

let not_carray_of_major_type_nondet (y: Spec.cbor)
: Lemma
    (requires (~ (cbor_major_type y == cbor_major_type_array)))
    (ensures (~ (Spec.CArray? (Spec.unpack y))))
= ()

(* Safe (no-precondition) variant: runtime null-dest and array-tag checks. *)
fn cbor_nondet_array_slice_safe
  (x: cbor_nondet_t) (i j: U64.t)
  (dest: R.ref cbor_nondet_t)
  (r1 r2 r3 r4: R.ref cbor_nondet_array_append_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor) (#vdest: Ghost.erased cbor_nondet_t)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_nondet_array_append_cell_t)
requires
  (cbor_nondet_match p x v ** ref_pts_to_or_null dest 1.0R vdest **
   R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)
returns res: bool
ensures
  (exists* (vdest': cbor_nondet_t).
     ref_pts_to_or_null dest 1.0R vdest' **
     cbor_nondet_array_slice_safe_post x i j dest p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest' **
     pure (res == cbor_nondet_array_slice_safe_res dest v))
{
  if (R.is_null dest) {
    fold (cbor_nondet_array_slice_safe_post_false x p v r1 r2 r3 r4 w1 w2 w3 w4 (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (cbor_nondet_array_slice_safe_post_false x p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest)
      as (cbor_nondet_array_slice_safe_post x i j dest p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest);
    false
  } else {
    let mt = cbor_nondet_major_type () x;
    if (mt = cbor_major_type_array) {
      carray_of_major_type_nondet v;
      rewrite (ref_pts_to_or_null dest 1.0R vdest) as (pts_to dest vdest);
      let sl = cbor_nondet_array_slice x i j r1 r2 r3 r4;
      dest := sl;
      rewrite (pts_to dest sl) as (ref_pts_to_or_null dest 1.0R sl);
      fold (cbor_nondet_array_slice_safe_post_true x i j p v r1 r2 r3 r4 sl);
      rewrite (cbor_nondet_array_slice_safe_post_true x i j p v r1 r2 r3 r4 sl)
        as (cbor_nondet_array_slice_safe_post x i j dest p v r1 r2 r3 r4 w1 w2 w3 w4 vdest sl);
      true
    } else {
      not_carray_of_major_type_nondet v;
      fold (cbor_nondet_array_slice_safe_post_false x p v r1 r2 r3 r4 w1 w2 w3 w4 (Ghost.reveal vdest) (Ghost.reveal vdest));
      rewrite (cbor_nondet_array_slice_safe_post_false x p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest)
        as (cbor_nondet_array_slice_safe_post x i j dest p v r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest);
      false
    }
  }
}

(* ================================================================== *)
(* Structural map remove-by-key — nondeterministic API.               *)
(* Delegates to the raw/ adapter                                      *)
(*   NMRS = CBOR.Pulse.Raw.EverParse.Nondet.MapRemoveSpec             *)
(* (implementation in everparse/).  The [CMap?] precondition makes    *)
(* the runtime major-type check unnecessary, so we delegate directly. *)
(* [NMRS.map_remove_key] and [cbor_nondet_map_remove_spec] have the   *)
(* same ([cbor_map_filter]-based) body, so their applications agree.  *)
(* ================================================================== *)

fn cbor_nondet_map_remove
  (x key: cbor_nondet_t)
  (r1 r2 r3 r4: R.ref cbor_nondet_map_entry_insert_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#pk: perm) (#vk: Ghost.erased Spec.cbor)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_nondet_map_entry_insert_cell_t)
requires
    (cbor_nondet_match p x v ** cbor_nondet_match pk key vk **
     R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 **
     pure (Spec.CMap? (Spec.unpack v)))
returns res: cbor_nondet_t
ensures
    (exists* (p_res: perm) (v': Spec.cbor).
       cbor_nondet_match p_res res v' **
       cbor_nondet_match pk key vk **
       Trade.trade (cbor_nondet_match p_res res v')
         (cbor_nondet_match p x v ** (exists* w1 w2 w3 w4. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)) **
       pure (Spec.CMap? (Spec.unpack v) /\ Spec.CMap? (Spec.unpack v') /\
             (Spec.CMap?.c (Spec.unpack v') <: Spec.cbor_map) ==
               cbor_nondet_map_remove_spec vk (Spec.CMap?.c (Spec.unpack v))))
{
  NMRS.cbor_nondet_map_remove_bridge x key r1 r2 r3 r4
}

(* Safe (no-precondition) variant: runtime null-dest and map-tag checks. *)
fn cbor_nondet_map_remove_safe
  (x key: cbor_nondet_t)
  (dest: R.ref cbor_nondet_t)
  (r1 r2 r3 r4: R.ref cbor_nondet_map_entry_insert_cell_t)
  (#p: perm) (#v: Ghost.erased Spec.cbor)
  (#pk: perm) (#vk: Ghost.erased Spec.cbor) (#vdest: Ghost.erased cbor_nondet_t)
  (#w1 #w2 #w3 #w4: Ghost.erased cbor_nondet_map_entry_insert_cell_t)
requires
    (cbor_nondet_match p x v ** cbor_nondet_match pk key vk ** ref_pts_to_or_null dest 1.0R vdest **
     R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4)
returns res: bool
ensures
    (exists* (vdest': cbor_nondet_t).
       ref_pts_to_or_null dest 1.0R vdest' **
       cbor_nondet_map_remove_safe_post x key dest p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest' **
       pure (res == cbor_nondet_map_remove_safe_res dest v))
{
  if (R.is_null dest) {
    fold (cbor_nondet_map_remove_safe_post_false x key p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (cbor_nondet_map_remove_safe_post_false x key p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest)
      as (cbor_nondet_map_remove_safe_post x key dest p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest);
    false
  } else {
    let mt = cbor_nondet_major_type () x;
    if (mt = cbor_major_type_map) {
      cmap_of_major_type_nondet v;
      rewrite (ref_pts_to_or_null dest 1.0R vdest) as (pts_to dest vdest);
      let sl = cbor_nondet_map_remove x key r1 r2 r3 r4;
      dest := sl;
      rewrite (pts_to dest sl) as (ref_pts_to_or_null dest 1.0R sl);
      fold (cbor_nondet_map_remove_safe_post_true x key p v pk vk r1 r2 r3 r4 sl);
      rewrite (cbor_nondet_map_remove_safe_post_true x key p v pk vk r1 r2 r3 r4 sl)
        as (cbor_nondet_map_remove_safe_post x key dest p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 vdest sl);
      true
    } else {
      not_cmap_of_major_type_nondet v;
      fold (cbor_nondet_map_remove_safe_post_false x key p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 (Ghost.reveal vdest) (Ghost.reveal vdest));
      rewrite (cbor_nondet_map_remove_safe_post_false x key p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest)
        as (cbor_nondet_map_remove_safe_post x key dest p v pk vk r1 r2 r3 r4 w1 w2 w3 w4 vdest vdest);
      false
    }
  }
}
