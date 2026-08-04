module CBOR.Pulse.Raw.Format.Serialize.Gen
friend CBOR.Pulse.Raw.Format.Match
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
module MLI = LowParse.PulseParse.Iterator
module IO = LowParse.PulseParse.Iterator.IntOps
module LI = LowParse.Pulse.Iterator
module VC = LowParse.Spec.VCList
module LSC = LowParse.Spec.Combinators
module ML = CBOR.Pulse.Raw.Format.MixedList
module LP = LowParse.Pulse.Combinators
module Trade = Pulse.Lib.Trade.Util
module MP = CBOR.Pulse.Raw.Match.Perm

(* depth_cb and depth_match agree on the refined domain. *)
let depth_cb_eq_depth_match
  (n: nat) (r: raw_data_item) (p': perm) (c': cbor_raw) (v': raw_data_item { v' << r })
: Lemma (depth_cb n r p' c' v' == DEP.depth_match n p' c' v')
= if n = 0
  then (depth_cb_zero r p' c' v'; DEP.depth_match_zero p' c' v')
  else (depth_cb_succ n r p' c' v'; DEP.depth_match_succ n p' c' v')

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn write_gen_array_core
  (n: Ghost.erased nat)
  (w: (pm': perm) -> l2r_writer (DEP.depth_match n pm') serialize_raw_data_item)
  (a: cbor_mixed_list_array)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Array? r }))
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
requires
  pts_to out v **
  cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0) **
  pure (
    l2r_writer_for_pre (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0) offset v)
returns res: SZ.t
ensures exists* v'.
  pts_to out v' **
  cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0) **
  pure (l2r_writer_for_post (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0) offset v res v')
{
  cbor_match_mixed_list_array_length pp a xh0 (depth_cb n xh0);
  unfold (cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0));
  ghost
  fn prf_fwd (x1: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y (Array?.v (Ghost.reveal xh0)) })
    requires cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y
    ensures DEP.depth_match n pm0 x1 y
  {
    array_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_bounded_eq (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y;
    rewrite (cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y) as (depth_cb n (Ghost.reveal xh0) pm0 x1 y);
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1 y;
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1 y) as (DEP.depth_match n pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0))) (DEP.depth_match n)
    IO.u64_ops parse_raw_data_item (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)) prf_fwd;
  MLI.mixed_list_match_length (DEP.depth_match n) IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0));
  let count_rt = ML.cbor_raw_mixed_list_length a.cbor_array_gen_ptr;
  fold (LI.mixed_list_match_for_l2r (DEP.depth_match n) IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) (U64.v count_rt) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)));
  let res = LI.l2r_write_mixed_list (DEP.depth_match n) IO.u64_ops serialize_raw_data_item w
    (jump_raw_data_item ()) (DEP.depth_match_share n) (DEP.depth_match_gather n)
    (pp *. a.cbor_array_gen_perm) count_rt a.cbor_array_gen_ptr out offset;
  unfold (LI.mixed_list_match_for_l2r (DEP.depth_match n) IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) (U64.v count_rt) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y (Array?.v (Ghost.reveal xh0)) })
    requires DEP.depth_match n pm0 x1 y
    ensures cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y
  {
    array_elem_precedes (Ghost.reveal xh0) y;
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1 y;
    rewrite (DEP.depth_match n pm0 x1 y) as (depth_cb n (Ghost.reveal xh0) pm0 x1 y);
    cbor_match_bounded_eq (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y;
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1 y) as (cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (DEP.depth_match n) (cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)))
    IO.u64_ops parse_raw_data_item (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0));
  res
}

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn size_gen_array_core
  (n: Ghost.erased nat)
  (cr: (pm': perm) -> compute_remaining_size (DEP.depth_match n pm') serialize_raw_data_item)
  (a: cbor_mixed_list_array)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Array? r }))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  R.pts_to out v **
  cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0) **
  pure True
returns res: bool
ensures exists* v'.
  R.pts_to out v' **
  cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0) **
  pure (
    let bs = Seq.length (bare_serialize (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0)) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v))
{
  cbor_match_mixed_list_array_length pp a xh0 (depth_cb n xh0);
  unfold (cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0));
  ghost
  fn prf_fwd (x1: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y (Array?.v (Ghost.reveal xh0)) })
    requires cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y
    ensures DEP.depth_match n pm0 x1 y
  {
    array_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_bounded_eq (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y;
    rewrite (cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y) as (depth_cb n (Ghost.reveal xh0) pm0 x1 y);
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1 y;
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1 y) as (DEP.depth_match n pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0))) (DEP.depth_match n)
    IO.u64_ops parse_raw_data_item (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)) prf_fwd;
  MLI.mixed_list_match_length (DEP.depth_match n) IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0));
  let count_rt = ML.cbor_raw_mixed_list_length a.cbor_array_gen_ptr;
  fold (LI.mixed_list_match_for_l2r (DEP.depth_match n) IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) (U64.v count_rt) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)));
  let res = LI.compute_remaining_size_mixed_list (DEP.depth_match n) IO.u64_ops serialize_raw_data_item cr
    (jump_raw_data_item ()) (DEP.depth_match_share n) (DEP.depth_match_gather n)
    (pp *. a.cbor_array_gen_perm) count_rt a.cbor_array_gen_ptr out;
  unfold (LI.mixed_list_match_for_l2r (DEP.depth_match n) IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) (U64.v count_rt) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y (Array?.v (Ghost.reveal xh0)) })
    requires DEP.depth_match n pm0 x1 y
    ensures cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y
  {
    array_elem_precedes (Ghost.reveal xh0) y;
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1 y;
    rewrite (DEP.depth_match n pm0 x1 y) as (depth_cb n (Ghost.reveal xh0) pm0 x1 y);
    cbor_match_bounded_eq (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y;
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1 y) as (cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (DEP.depth_match n) (cbor_match_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)))
    IO.u64_ops parse_raw_data_item (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_array pp a xh0 (depth_cb n xh0));
  res
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn pair_proj1 (n: Ghost.erased nat) (pm': perm) (xl: cbor_map_entry) (xh: Ghost.erased (raw_data_item & raw_data_item))
requires DEP.depth_match_pair n pm' xl xh
returns res: cbor_raw
ensures DEP.depth_match n pm' res (fst xh) ** Trade.trade (DEP.depth_match n pm' res (fst xh)) (DEP.depth_match_pair n pm' xl xh)
{
  Trade.rewrite_with_trade
    (DEP.depth_match_pair n pm' xl xh)
    (DEP.depth_match n pm' xl.cbor_map_entry_key (fst xh) ** DEP.depth_match n pm' xl.cbor_map_entry_value (snd xh));
  Trade.elim_hyp_r _ _ _;
  xl.cbor_map_entry_key
}

inline_for_extraction
fn pair_proj2 (n: Ghost.erased nat) (pm': perm) (xl: cbor_map_entry) (xh: Ghost.erased (raw_data_item & raw_data_item))
requires DEP.depth_match_pair n pm' xl xh
returns res: cbor_raw
ensures DEP.depth_match n pm' res (snd xh) ** Trade.trade (DEP.depth_match n pm' res (snd xh)) (DEP.depth_match_pair n pm' xl xh)
{
  Trade.rewrite_with_trade
    (DEP.depth_match_pair n pm' xl xh)
    (DEP.depth_match n pm' xl.cbor_map_entry_key (fst xh) ** DEP.depth_match n pm' xl.cbor_map_entry_value (snd xh));
  Trade.elim_hyp_l _ _ _;
  xl.cbor_map_entry_value
}

inline_for_extraction
let w_map_pair
  (n: Ghost.erased nat)
  (w: (pm': perm) -> l2r_writer (DEP.depth_match n pm') serialize_raw_data_item)
  (pm': perm)
: l2r_writer (DEP.depth_match_pair n pm') (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.l2r_write_nondep_then (w pm') () (w pm') _ (pair_proj1 n pm') (pair_proj2 n pm')

inline_for_extraction
let cr_map_pair
  (n: Ghost.erased nat)
  (cr: (pm': perm) -> compute_remaining_size (DEP.depth_match n pm') serialize_raw_data_item)
  (pm': perm)
: compute_remaining_size (DEP.depth_match_pair n pm') (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.compute_remaining_size_nondep_then (cr pm') () (cr pm') _ (pair_proj1 n pm') (pair_proj2 n pm')

inline_for_extraction
fn write_gen_map_core
  (n: Ghost.erased nat)
  (w: (pm': perm) -> l2r_writer (DEP.depth_match n pm') serialize_raw_data_item)
  (a: cbor_mixed_list_map)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Map? r }))
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
requires
  pts_to out v **
  cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0) **
  pure (
    l2r_writer_for_pre (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0) offset v)
returns res: SZ.t
ensures exists* v'.
  pts_to out v' **
  cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0) **
  pure (l2r_writer_for_post (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0) offset v res v')
{
  cbor_match_mixed_list_map_length pp a xh0 (depth_cb n xh0);
  unfold (cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0));
  ghost
  fn prf_fwd (x1: cbor_map_entry) (pm0: perm) (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v (Ghost.reveal xh0)) })
    requires cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y
    ensures DEP.depth_match_pair n pm0 x1 y
  {
    map_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y;
    rewrite (cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y)
      as (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y) ** depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y));
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y);
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y);
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y)) as (DEP.depth_match n pm0 x1.cbor_map_entry_key (fst y));
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y)) as (DEP.depth_match n pm0 x1.cbor_map_entry_value (snd y));
    fold (DEP.depth_match_pair n pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0))) (DEP.depth_match_pair n)
    IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item) (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)) prf_fwd;
  MLI.mixed_list_match_length (DEP.depth_match_pair n) IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0));
  let count_rt = ML.cbor_raw_mixed_list_length a.cbor_map_gen_ptr;
  fold (LI.mixed_list_match_for_l2r (DEP.depth_match_pair n) IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) (U64.v count_rt) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)));
  let res = LI.l2r_write_mixed_list (DEP.depth_match_pair n) IO.u64_ops (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
    (w_map_pair n w)
    (LP.jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ())) (DEP.depth_match_pair_share n) (DEP.depth_match_pair_gather n)
    (pp *. a.cbor_map_gen_perm) count_rt a.cbor_map_gen_ptr out offset;
  unfold (LI.mixed_list_match_for_l2r (DEP.depth_match_pair n) IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) (U64.v count_rt) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_map_entry) (pm0: perm) (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v (Ghost.reveal xh0)) })
    requires DEP.depth_match_pair n pm0 x1 y
    ensures cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y
  {
    map_elem_precedes (Ghost.reveal xh0) y;
    unfold (DEP.depth_match_pair n pm0 x1 y);
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y);
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y);
    rewrite (DEP.depth_match n pm0 x1.cbor_map_entry_key (fst y)) as (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y));
    rewrite (DEP.depth_match n pm0 x1.cbor_map_entry_value (snd y)) as (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y));
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y;
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y) ** depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y))
      as (cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (DEP.depth_match_pair n) (cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)))
    IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item) (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0));
  res
}

inline_for_extraction
fn size_gen_map_core
  (n: Ghost.erased nat)
  (cr: (pm': perm) -> compute_remaining_size (DEP.depth_match n pm') serialize_raw_data_item)
  (a: cbor_mixed_list_map)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Map? r }))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  R.pts_to out v **
  cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0) **
  pure True
returns res: bool
ensures exists* v'.
  R.pts_to out v' **
  cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0) **
  pure (
    let bs = Seq.length (bare_serialize (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0)) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v))
{
  cbor_match_mixed_list_map_length pp a xh0 (depth_cb n xh0);
  unfold (cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0));
  ghost
  fn prf_fwd (x1: cbor_map_entry) (pm0: perm) (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v (Ghost.reveal xh0)) })
    requires cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y
    ensures DEP.depth_match_pair n pm0 x1 y
  {
    map_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y;
    rewrite (cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y)
      as (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y) ** depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y));
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y);
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y);
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y)) as (DEP.depth_match n pm0 x1.cbor_map_entry_key (fst y));
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y)) as (DEP.depth_match n pm0 x1.cbor_map_entry_value (snd y));
    fold (DEP.depth_match_pair n pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0))) (DEP.depth_match_pair n)
    IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item) (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)) prf_fwd;
  MLI.mixed_list_match_length (DEP.depth_match_pair n) IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0));
  let count_rt = ML.cbor_raw_mixed_list_length a.cbor_map_gen_ptr;
  fold (LI.mixed_list_match_for_l2r (DEP.depth_match_pair n) IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) (U64.v count_rt) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)));
  let res = LI.compute_remaining_size_mixed_list (DEP.depth_match_pair n) IO.u64_ops (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
    (cr_map_pair n cr)
    (LP.jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ())) (DEP.depth_match_pair_share n) (DEP.depth_match_pair_gather n)
    (pp *. a.cbor_map_gen_perm) count_rt a.cbor_map_gen_ptr out;
  unfold (LI.mixed_list_match_for_l2r (DEP.depth_match_pair n) IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) (U64.v count_rt) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_map_entry) (pm0: perm) (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v (Ghost.reveal xh0)) })
    requires DEP.depth_match_pair n pm0 x1 y
    ensures cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y
  {
    map_elem_precedes (Ghost.reveal xh0) y;
    unfold (DEP.depth_match_pair n pm0 x1 y);
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y);
    depth_cb_eq_depth_match n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y);
    rewrite (DEP.depth_match n pm0 x1.cbor_map_entry_key (fst y)) as (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y));
    rewrite (DEP.depth_match n pm0 x1.cbor_map_entry_value (snd y)) as (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y));
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y;
    rewrite (depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_key (fst y) ** depth_cb n (Ghost.reveal xh0) pm0 x1.cbor_map_entry_value (snd y))
      as (cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)) pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (DEP.depth_match_pair n) (cbor_match_map_entry_bounded (Ghost.reveal xh0) (depth_cb n (Ghost.reveal xh0)))
    IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item) (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_map pp a xh0 (depth_cb n xh0));
  res
}

#pop-options

#pop-options

// ============================================================================
// NON-DEPTH (full-recursion) cores. Identical in structure to the depth cores
// above, but the per-element callback is the full [cbor_match] relation (rather
// than [depth_cb n]). These serve the (non-depth) recursive serializer stack.
// ============================================================================

ghost
fn cbor_match_share_t (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires cbor_match p x1 x2
ensures cbor_match (p /. 2.0R) x1 x2 ** cbor_match (p /. 2.0R) x1 x2
{
  MP.cbor_raw_share p x1 x2;
}

ghost
fn cbor_match_gather_t (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires cbor_match p x1 x2 ** cbor_match p' x1 x2'
ensures cbor_match (p +. p') x1 x2 ** pure (x2 == x2')
{
  MP.cbor_raw_gather p x1 x2 p' x2';
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

fn write_gen_array_core_nd
  (w: (pm': perm) -> l2r_writer (cbor_match pm') serialize_raw_data_item)
  (a: cbor_mixed_list_array)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Array? r }))
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
requires
  pts_to out v **
  cbor_match_mixed_list_array pp a xh0 cbor_match **
  pure (
    l2r_writer_for_pre (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0) offset v)
returns res: SZ.t
ensures exists* v'.
  pts_to out v' **
  cbor_match_mixed_list_array pp a xh0 cbor_match **
  pure (l2r_writer_for_post (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0) offset v res v')
{
  cbor_match_mixed_list_array_length pp a xh0 cbor_match;
  unfold (cbor_match_mixed_list_array pp a xh0 cbor_match);
  ghost
  fn prf_fwd (x1: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y (Array?.v (Ghost.reveal xh0)) })
    requires cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y
    ensures cbor_match pm0 x1 y
  {
    array_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 y;
    rewrite (cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y) as (cbor_match pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (cbor_match_bounded (Ghost.reveal xh0) cbor_match) cbor_match
    IO.u64_ops parse_raw_data_item (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)) prf_fwd;
  MLI.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0));
  let count_rt = ML.cbor_raw_mixed_list_length a.cbor_array_gen_ptr;
  fold (LI.mixed_list_match_for_l2r cbor_match IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) (U64.v count_rt) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)));
  let res = LI.l2r_write_mixed_list cbor_match IO.u64_ops serialize_raw_data_item w
    (jump_raw_data_item ()) cbor_match_share_t cbor_match_gather_t
    (pp *. a.cbor_array_gen_perm) count_rt a.cbor_array_gen_ptr out offset;
  unfold (LI.mixed_list_match_for_l2r cbor_match IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) (U64.v count_rt) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y (Array?.v (Ghost.reveal xh0)) })
    requires cbor_match pm0 x1 y
    ensures cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y
  {
    array_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 y;
    rewrite (cbor_match pm0 x1 y) as (cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    cbor_match (cbor_match_bounded (Ghost.reveal xh0) cbor_match)
    IO.u64_ops parse_raw_data_item (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_array pp a xh0 cbor_match);
  res
}

fn size_gen_array_core_nd
  (cr: (pm': perm) -> compute_remaining_size (cbor_match pm') serialize_raw_data_item)
  (a: cbor_mixed_list_array)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Array? r }))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  R.pts_to out v **
  cbor_match_mixed_list_array pp a xh0 cbor_match **
  pure True
returns res: bool
ensures exists* v'.
  R.pts_to out v' **
  cbor_match_mixed_list_array pp a xh0 cbor_match **
  pure (
    let bs = Seq.length (bare_serialize (VC.serialize_nlist (U64.v (Array?.len xh0).value) serialize_raw_data_item) (Array?.v xh0)) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v))
{
  cbor_match_mixed_list_array_length pp a xh0 cbor_match;
  unfold (cbor_match_mixed_list_array pp a xh0 cbor_match);
  ghost
  fn prf_fwd (x1: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y (Array?.v (Ghost.reveal xh0)) })
    requires cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y
    ensures cbor_match pm0 x1 y
  {
    array_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 y;
    rewrite (cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y) as (cbor_match pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (cbor_match_bounded (Ghost.reveal xh0) cbor_match) cbor_match
    IO.u64_ops parse_raw_data_item (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)) prf_fwd;
  MLI.mixed_list_match_length cbor_match IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0));
  let count_rt = ML.cbor_raw_mixed_list_length a.cbor_array_gen_ptr;
  fold (LI.mixed_list_match_for_l2r cbor_match IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) (U64.v count_rt) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)));
  let res = LI.compute_remaining_size_mixed_list cbor_match IO.u64_ops serialize_raw_data_item cr
    (jump_raw_data_item ()) cbor_match_share_t cbor_match_gather_t
    (pp *. a.cbor_array_gen_perm) count_rt a.cbor_array_gen_ptr out;
  unfold (LI.mixed_list_match_for_l2r cbor_match IO.u64_ops parse_raw_data_item
    (pp *. a.cbor_array_gen_perm) (U64.v count_rt) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y (Array?.v (Ghost.reveal xh0)) })
    requires cbor_match pm0 x1 y
    ensures cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y
  {
    array_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 y;
    rewrite (cbor_match pm0 x1 y) as (cbor_match_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    cbor_match (cbor_match_bounded (Ghost.reveal xh0) cbor_match)
    IO.u64_ops parse_raw_data_item (pp *. a.cbor_array_gen_perm) a.cbor_array_gen_ptr (Array?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_array pp a xh0 cbor_match);
  res
}

#pop-options

// ---------------------------------------------------------------------------
// NON-DEPTH map machinery (pair vmatch = [cbor_match_map_entry], unbounded)
// ---------------------------------------------------------------------------

ghost
fn cbor_match_map_entry_share_t (entry: cbor_map_entry) (#pm: perm) (#pair: (raw_data_item & raw_data_item))
requires cbor_match_map_entry pm entry pair
ensures cbor_match_map_entry (pm /. 2.0R) entry pair ** cbor_match_map_entry (pm /. 2.0R) entry pair
{
  unfold (cbor_match_map_entry pm entry pair);
  MP.cbor_raw_share pm entry.cbor_map_entry_key (fst pair);
  MP.cbor_raw_share pm entry.cbor_map_entry_value (snd pair);
  fold (cbor_match_map_entry (pm /. 2.0R) entry pair);
  fold (cbor_match_map_entry (pm /. 2.0R) entry pair);
}

ghost
fn cbor_match_map_entry_gather_t (entry: cbor_map_entry) (#pm: perm) (#pair: (raw_data_item & raw_data_item)) (#pm': perm) (#pair': (raw_data_item & raw_data_item))
requires cbor_match_map_entry pm entry pair ** cbor_match_map_entry pm' entry pair'
ensures cbor_match_map_entry (pm +. pm') entry pair ** pure (pair == pair')
{
  unfold (cbor_match_map_entry pm entry pair);
  unfold (cbor_match_map_entry pm' entry pair');
  MP.cbor_raw_gather pm entry.cbor_map_entry_key (fst pair) pm' (fst pair');
  MP.cbor_raw_gather pm entry.cbor_map_entry_value (snd pair) pm' (snd pair');
  fold (cbor_match_map_entry (pm +. pm') entry pair);
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn pair_proj1_nd (pm': perm) (xl: cbor_map_entry) (xh: Ghost.erased (raw_data_item & raw_data_item))
requires cbor_match_map_entry pm' xl xh
returns res: cbor_raw
ensures cbor_match pm' res (fst xh) ** Trade.trade (cbor_match pm' res (fst xh)) (cbor_match_map_entry pm' xl xh)
{
  Trade.rewrite_with_trade
    (cbor_match_map_entry pm' xl xh)
    (cbor_match pm' xl.cbor_map_entry_key (fst xh) ** cbor_match pm' xl.cbor_map_entry_value (snd xh));
  Trade.elim_hyp_r _ _ _;
  xl.cbor_map_entry_key
}

inline_for_extraction
fn pair_proj2_nd (pm': perm) (xl: cbor_map_entry) (xh: Ghost.erased (raw_data_item & raw_data_item))
requires cbor_match_map_entry pm' xl xh
returns res: cbor_raw
ensures cbor_match pm' res (snd xh) ** Trade.trade (cbor_match pm' res (snd xh)) (cbor_match_map_entry pm' xl xh)
{
  Trade.rewrite_with_trade
    (cbor_match_map_entry pm' xl xh)
    (cbor_match pm' xl.cbor_map_entry_key (fst xh) ** cbor_match pm' xl.cbor_map_entry_value (snd xh));
  Trade.elim_hyp_l _ _ _;
  xl.cbor_map_entry_value
}

inline_for_extraction
let w_map_pair_nd
  (w: (pm': perm) -> l2r_writer (cbor_match pm') serialize_raw_data_item)
  (pm': perm)
: l2r_writer (cbor_match_map_entry pm') (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.l2r_write_nondep_then (w pm') () (w pm') _ (pair_proj1_nd pm') (pair_proj2_nd pm')

inline_for_extraction
let cr_map_pair_nd
  (cr: (pm': perm) -> compute_remaining_size (cbor_match pm') serialize_raw_data_item)
  (pm': perm)
: compute_remaining_size (cbor_match_map_entry pm') (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.compute_remaining_size_nondep_then (cr pm') () (cr pm') _ (pair_proj1_nd pm') (pair_proj2_nd pm')

fn write_gen_map_core_nd
  (w: (pm': perm) -> l2r_writer (cbor_match pm') serialize_raw_data_item)
  (a: cbor_mixed_list_map)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Map? r }))
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
requires
  pts_to out v **
  cbor_match_mixed_list_map pp a xh0 cbor_match **
  pure (
    l2r_writer_for_pre (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0) offset v)
returns res: SZ.t
ensures exists* v'.
  pts_to out v' **
  cbor_match_mixed_list_map pp a xh0 cbor_match **
  pure (l2r_writer_for_post (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0) offset v res v')
{
  cbor_match_mixed_list_map_length pp a xh0 cbor_match;
  unfold (cbor_match_mixed_list_map pp a xh0 cbor_match);
  ghost
  fn prf_fwd (x1: cbor_map_entry) (pm0: perm) (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v (Ghost.reveal xh0)) })
    requires cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y
    ensures cbor_match_map_entry pm0 x1 y
  {
    map_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 y;
    rewrite (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y)
      as (cbor_match pm0 x1.cbor_map_entry_key (fst y) ** cbor_match pm0 x1.cbor_map_entry_value (snd y));
    fold (cbor_match_map_entry pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match) cbor_match_map_entry
    IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item) (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)) prf_fwd;
  MLI.mixed_list_match_length cbor_match_map_entry IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0));
  let count_rt = ML.cbor_raw_mixed_list_length a.cbor_map_gen_ptr;
  fold (LI.mixed_list_match_for_l2r cbor_match_map_entry IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) (U64.v count_rt) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)));
  let res = LI.l2r_write_mixed_list cbor_match_map_entry IO.u64_ops (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
    (w_map_pair_nd w)
    (LP.jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ())) cbor_match_map_entry_share_t cbor_match_map_entry_gather_t
    (pp *. a.cbor_map_gen_perm) count_rt a.cbor_map_gen_ptr out offset;
  unfold (LI.mixed_list_match_for_l2r cbor_match_map_entry IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) (U64.v count_rt) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_map_entry) (pm0: perm) (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v (Ghost.reveal xh0)) })
    requires cbor_match_map_entry pm0 x1 y
    ensures cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y
  {
    map_elem_precedes (Ghost.reveal xh0) y;
    unfold (cbor_match_map_entry pm0 x1 y);
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 y;
    rewrite (cbor_match pm0 x1.cbor_map_entry_key (fst y) ** cbor_match pm0 x1.cbor_map_entry_value (snd y))
      as (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    cbor_match_map_entry (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match)
    IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item) (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_map pp a xh0 cbor_match);
  res
}

fn size_gen_map_core_nd
  (cr: (pm': perm) -> compute_remaining_size (cbor_match pm') serialize_raw_data_item)
  (a: cbor_mixed_list_map)
  (pp: perm)
  (xh0: Ghost.erased (r: raw_data_item { Map? r }))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  R.pts_to out v **
  cbor_match_mixed_list_map pp a xh0 cbor_match **
  pure True
returns res: bool
ensures exists* v'.
  R.pts_to out v' **
  cbor_match_mixed_list_map pp a xh0 cbor_match **
  pure (
    let bs = Seq.length (bare_serialize (VC.serialize_nlist (U64.v (Map?.len xh0).value) (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (Map?.v xh0)) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v))
{
  cbor_match_mixed_list_map_length pp a xh0 cbor_match;
  unfold (cbor_match_mixed_list_map pp a xh0 cbor_match);
  ghost
  fn prf_fwd (x1: cbor_map_entry) (pm0: perm) (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v (Ghost.reveal xh0)) })
    requires cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y
    ensures cbor_match_map_entry pm0 x1 y
  {
    map_elem_precedes (Ghost.reveal xh0) y;
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 y;
    rewrite (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y)
      as (cbor_match pm0 x1.cbor_map_entry_key (fst y) ** cbor_match pm0 x1.cbor_map_entry_value (snd y));
    fold (cbor_match_map_entry pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match) cbor_match_map_entry
    IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item) (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)) prf_fwd;
  MLI.mixed_list_match_length cbor_match_map_entry IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0));
  let count_rt = ML.cbor_raw_mixed_list_length a.cbor_map_gen_ptr;
  fold (LI.mixed_list_match_for_l2r cbor_match_map_entry IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) (U64.v count_rt) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)));
  let res = LI.compute_remaining_size_mixed_list cbor_match_map_entry IO.u64_ops (LSC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
    (cr_map_pair_nd cr)
    (LP.jump_nondep_then (jump_raw_data_item ()) (jump_raw_data_item ())) cbor_match_map_entry_share_t cbor_match_map_entry_gather_t
    (pp *. a.cbor_map_gen_perm) count_rt a.cbor_map_gen_ptr out;
  unfold (LI.mixed_list_match_for_l2r cbor_match_map_entry IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item)
    (pp *. a.cbor_map_gen_perm) (U64.v count_rt) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)));
  ghost
  fn prf_bwd (x1: cbor_map_entry) (pm0: perm) (y: (raw_data_item & raw_data_item) { List.Tot.memP y (Map?.v (Ghost.reveal xh0)) })
    requires cbor_match_map_entry pm0 x1 y
    ensures cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y
  {
    map_elem_precedes (Ghost.reveal xh0) y;
    unfold (cbor_match_map_entry pm0 x1 y);
    cbor_match_map_entry_bounded_eq (Ghost.reveal xh0) cbor_match pm0 x1 y;
    rewrite (cbor_match pm0 x1.cbor_map_entry_key (fst y) ** cbor_match pm0 x1.cbor_map_entry_value (snd y))
      as (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match pm0 x1 y);
  };
  MLI.mixed_list_match_weaken
    cbor_match_map_entry (cbor_match_map_entry_bounded (Ghost.reveal xh0) cbor_match)
    IO.u64_ops (LSC.nondep_then parse_raw_data_item parse_raw_data_item) (pp *. a.cbor_map_gen_perm) a.cbor_map_gen_ptr (Map?.v (Ghost.reveal xh0)) prf_bwd;
  fold (cbor_match_mixed_list_map pp a xh0 cbor_match);
  res
}

#pop-options
