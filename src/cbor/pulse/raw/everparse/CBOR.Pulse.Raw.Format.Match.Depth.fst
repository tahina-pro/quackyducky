module CBOR.Pulse.Raw.Format.Match.Depth
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.Base
open LowParse.Pulse.Base
open CBOR.Pulse.Raw.Match
open CBOR.Pulse.Raw.Match.Perm
open CBOR.Pulse.Raw.Format.Match
open CBOR.Pulse.Raw.Util

module U64 = FStar.UInt64
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module PM = Pulse.Lib.SeqMatch
module I = LowParse.PulseParse.Iterator

(* Element-level, depth-preserving share for cbor_match_with_depth.
   Mirrors CBOR.Pulse.Raw.Match.Perm.cbor_raw_share, threading the depth. *)

ghost
fn rec cbor_match_with_depth_share_array
  (n: nat)
  (r0: raw_data_item)
  (p: perm)
  (c: Seq.seq cbor_raw)
  (r: list raw_data_item { r << r0 })
  (share_cb: (
    (p': perm) ->
    (c': cbor_raw) ->
    (r': raw_data_item { r' << r0 }) ->
    stt_ghost unit emp_inames
      (depth_cb n r0 p' c' r')
      (fun _ -> depth_cb n r0 (p' /. 2.0R) c' r' ** depth_cb n r0 (p' /. 2.0R) c' r')
  ))
  (_: unit)
requires
  PM.seq_list_match c r (depth_cb n r0 p)
ensures
  PM.seq_list_match c r (depth_cb n r0 (p /. 2.0R)) **
  PM.seq_list_match c r (depth_cb n r0 (p /. 2.0R))
decreases r
{
  match r {
    Nil -> {
      PM.seq_list_match_nil_elim c r (depth_cb n r0 p);
      PM.seq_list_match_nil_intro c r (depth_cb n r0 (p /. 2.0R));
      PM.seq_list_match_nil_intro c r (depth_cb n r0 (p /. 2.0R))
    }
    a :: q -> {
      PM.seq_list_match_cons_elim c r (depth_cb n r0 p);
      share_cb p (Seq.head c) _;
      cbor_match_with_depth_share_array n r0 p (Seq.tail c) q share_cb ();
      PM.seq_list_match_cons_intro (Seq.head c) _ (Seq.tail c) q (depth_cb n r0 (p /. 2.0R));
      PM.seq_list_match_cons_intro (Seq.head c) _ (Seq.tail c) q (depth_cb n r0 (p /. 2.0R));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ();
    }
  }
}

(* Depth-preserving version of cbor_match_cases *)
ghost
fn cbor_match_with_depth_cases
  (n: nat)
  (c: cbor_raw)
  (#pm: perm)
  (#r: raw_data_item)
  requires cbor_match_with_depth n pm c r
  ensures cbor_match_with_depth n pm c r ** pure (cbor_match_cases_pred c r)
{
  if cbor_match_cases_pred c r {
    ()
  } else {
    cbor_match_with_depth_eq0 n pm c r;
    rewrite (cbor_match_with_depth n pm c r) as (cbor_match0 pm c r (depth_cb n r));
    rewrite (cbor_match0 pm c r (depth_cb n r)) as (pure False);
    rewrite emp as (cbor_match_with_depth n pm c r);
  }
}

(* Element-level, depth-preserving share over a list of map entries. *)
ghost
fn rec cbor_match_with_depth_share_map
  (n: nat)
  (r0: raw_data_item)
  (p: perm)
  (c: Seq.seq cbor_map_entry)
  (r: list (raw_data_item & raw_data_item) { r << r0 })
  (share_cb: (
    (p': perm) ->
    (c': cbor_raw) ->
    (r': raw_data_item { r' << r0 }) ->
    stt_ghost unit emp_inames
      (depth_cb n r0 p' c' r')
      (fun _ -> depth_cb n r0 (p' /. 2.0R) c' r' ** depth_cb n r0 (p' /. 2.0R) c' r')
  ))
  (_: unit)
requires
  PM.seq_list_match c r (cbor_match_map_entry0 r0 (depth_cb n r0 p))
ensures
  PM.seq_list_match c r (cbor_match_map_entry0 r0 (depth_cb n r0 (p /. 2.0R))) **
  PM.seq_list_match c r (cbor_match_map_entry0 r0 (depth_cb n r0 (p /. 2.0R)))
decreases r
{
  match r {
    Nil -> {
      PM.seq_list_match_nil_elim c r (cbor_match_map_entry0 r0 (depth_cb n r0 p));
      PM.seq_list_match_nil_intro c r (cbor_match_map_entry0 r0 (depth_cb n r0 (p /. 2.0R)));
      PM.seq_list_match_nil_intro c r (cbor_match_map_entry0 r0 (depth_cb n r0 (p /. 2.0R)));
    }
    a :: q -> {
      PM.seq_list_match_cons_elim c r (cbor_match_map_entry0 r0 (depth_cb n r0 p));
      rewrite each (List.Tot.Base.hd r) as a;
      unfold (cbor_match_map_entry0 r0 (depth_cb n r0 p) (Seq.head c) a);
      share_cb p (Seq.head c).cbor_map_entry_key (fst a);
      share_cb p (Seq.head c).cbor_map_entry_value (snd a);
      fold (cbor_match_map_entry0 r0 (depth_cb n r0 (p /. 2.0R)) (Seq.head c) a);
      fold (cbor_match_map_entry0 r0 (depth_cb n r0 (p /. 2.0R)) (Seq.head c) a);
      cbor_match_with_depth_share_map n r0 p (Seq.tail c) q share_cb ();
      PM.seq_list_match_cons_intro (Seq.head c) a (Seq.tail c) q (cbor_match_map_entry0 r0 (depth_cb n r0 (p /. 2.0R)));
      PM.seq_list_match_cons_intro (Seq.head c) a (Seq.tail c) q (cbor_match_map_entry0 r0 (depth_cb n r0 (p /. 2.0R)));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ();
    }
  }
}

(* Main depth-preserving share for a single cbor value. *)
ghost
fn rec cbor_match_with_depth_share
  (n: nat)
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
requires
  cbor_match_with_depth n p c r
ensures
  cbor_match_with_depth n (p /. 2.0R) c r **
  cbor_match_with_depth n (p /. 2.0R) c r
decreases r
{
  ghost
  fn share_cb (p': perm) (c': cbor_raw) (v': raw_data_item { v' << r })
  requires depth_cb n r p' c' v'
  ensures depth_cb n r (p' /. 2.0R) c' v' ** depth_cb n r (p' /. 2.0R) c' v'
  {
    if (n = 0) {
      depth_cb_zero r p' c' v';
      rewrite (depth_cb n r p' c' v') as (pure False);
      rewrite emp as (depth_cb n r (p' /. 2.0R) c' v' ** depth_cb n r (p' /. 2.0R) c' v');
    } else {
      depth_cb_succ n r p' c' v';
      rewrite (depth_cb n r p' c' v') as (cbor_match_with_depth (n - 1) p' c' v');
      cbor_match_with_depth_share (n - 1) p' c' v';
      depth_cb_succ n r (p' /. 2.0R) c' v';
      rewrite (cbor_match_with_depth (n - 1) (p' /. 2.0R) c' v') as (depth_cb n r (p' /. 2.0R) c' v');
      rewrite (cbor_match_with_depth (n - 1) (p' /. 2.0R) c' v') as (depth_cb n r (p' /. 2.0R) c' v');
    }
  };
  cbor_match_with_depth_cases n c;
  match c {
    norewrite
    CBOR_Case_Int v -> {
      cbor_match_with_depth_eq_match_int n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match p c r);
      cbor_raw_share p c r;
      cbor_match_with_depth_eq_match_int n (p /. 2.0R) v r;
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Simple v -> {
      cbor_match_with_depth_eq_match_simple n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match p c r);
      cbor_raw_share p c r;
      cbor_match_with_depth_eq_match_simple n (p /. 2.0R) v r;
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_String v -> {
      cbor_match_with_depth_eq_match_string n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match p c r);
      cbor_raw_share p c r;
      cbor_match_with_depth_eq_match_string n (p /. 2.0R) v r;
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Serialized_Array v -> {
      cbor_match_with_depth_eq_match_ser_array n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match p c r);
      cbor_raw_share p c r;
      cbor_match_with_depth_eq_match_ser_array n (p /. 2.0R) v r;
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Serialized_Map v -> {
      cbor_match_with_depth_eq_match_ser_map n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match p c r);
      cbor_raw_share p c r;
      cbor_match_with_depth_eq_match_ser_map n (p /. 2.0R) v r;
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Serialized_Tagged v -> {
      cbor_match_with_depth_eq_match_ser_tagged n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match p c r);
      cbor_raw_share p c r;
      cbor_match_with_depth_eq_match_ser_tagged n (p /. 2.0R) v r;
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match (p /. 2.0R) c r) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Tagged v -> {
      cbor_match_with_depth_eq_tagged n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match_tagged v p r (depth_cb n r));
      unfold (cbor_match_tagged v p r (depth_cb n r));
      share_cb (perm_mul p v.cbor_tagged_payload_perm) _ (Tagged?.v r);
      R.share v.cbor_tagged_ptr;
      half_mul_l p v.cbor_tagged_ref_perm;
      half_mul_l p v.cbor_tagged_payload_perm;
      with c' . rewrite (depth_cb n r (perm_mul p v.cbor_tagged_payload_perm /. 2.0R) c' (Tagged?.v r)) as (depth_cb n r (perm_mul (p /. 2.0R) v.cbor_tagged_payload_perm) c' (Tagged?.v r));
      fold (cbor_match_tagged v (p /. 2.0R) r (depth_cb n r));
      cbor_match_with_depth_eq_tagged n (p /. 2.0R) v r;
      with c' . rewrite (depth_cb n r (perm_mul p v.cbor_tagged_payload_perm /. 2.0R) c' (Tagged?.v r)) as (depth_cb n r (perm_mul (p /. 2.0R) v.cbor_tagged_payload_perm) c' (Tagged?.v r));
      fold (cbor_match_tagged v (p /. 2.0R) r (depth_cb n r));
      rewrite (cbor_match_tagged v (p /. 2.0R) r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match_tagged v (p /. 2.0R) r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Array v -> {
      cbor_match_with_depth_eq_array n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match_array v p r (depth_cb n r));
      unfold (cbor_match_array v p r (depth_cb n r));
      S.share v.cbor_array_ptr;
      cbor_match_with_depth_share_array n r (perm_mul p v.cbor_array_payload_perm) _ (Array?.v r) share_cb ();
      half_mul_l p v.cbor_array_array_perm;
      half_mul_l p v.cbor_array_payload_perm;
      fold (cbor_match_array v (p /. 2.0R) r (depth_cb n r));
      cbor_match_with_depth_eq_array n (p /. 2.0R) v r;
      rewrite (cbor_match_array v (p /. 2.0R) r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
      fold (cbor_match_array v (p /. 2.0R) r (depth_cb n r));
      rewrite (cbor_match_array v (p /. 2.0R) r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Map v -> {
      cbor_match_with_depth_eq_map0 n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match_map0 v p r (depth_cb n r));
      unfold (cbor_match_map0 v p r (depth_cb n r));
      S.share v.cbor_map_ptr;
      cbor_match_with_depth_share_map n r (perm_mul p v.cbor_map_payload_perm) _ (Map?.v r) share_cb ();
      half_mul_l p v.cbor_map_array_perm;
      half_mul_l p v.cbor_map_payload_perm;
      fold (cbor_match_map0 v (p /. 2.0R) r (depth_cb n r));
      cbor_match_with_depth_eq_map0 n (p /. 2.0R) v r;
      rewrite (cbor_match_map0 v (p /. 2.0R) r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
      fold (cbor_match_map0 v (p /. 2.0R) r (depth_cb n r));
      rewrite (cbor_match_map0 v (p /. 2.0R) r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Array_Gen v -> {
      cbor_match_with_depth_eq_array_gen n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match_mixed_list_array p v r (depth_cb n r));
      cbor_match_mixed_list_array_share p v r (depth_cb n r) share_cb;
      cbor_match_with_depth_eq_array_gen n (p /. 2.0R) v r;
      rewrite (cbor_match_mixed_list_array (p /. 2.0R) v r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match_mixed_list_array (p /. 2.0R) v r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Map_Gen v -> {
      cbor_match_with_depth_eq_map_gen n p v r;
      rewrite (cbor_match_with_depth n p c r) as (cbor_match_mixed_list_map p v r (depth_cb n r));
      cbor_match_mixed_list_map_share p v r (depth_cb n r) share_cb;
      cbor_match_with_depth_eq_map_gen n (p /. 2.0R) v r;
      rewrite (cbor_match_mixed_list_map (p /. 2.0R) v r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
      rewrite (cbor_match_mixed_list_map (p /. 2.0R) v r (depth_cb n r)) as (cbor_match_with_depth n (p /. 2.0R) c r);
    }
  }
}


(* ============================================================ *)
(* Depth-preserving GATHER                                       *)
(* ============================================================ *)

(* Unrefined version of depth_cb (r-refinement erased), usable as the
   (unrefined) element callback of the mixed_list gather. *)
let depth_match (n: nat) : (perm -> cbor_raw -> raw_data_item -> slprop) =
  if n = 0 then (fun _ _ _ -> pure False) else cbor_match_with_depth (n - 1)

let depth_match_zero (p: perm) (c: cbor_raw) (v: raw_data_item)
  : Lemma (depth_match 0 p c v == pure False)
= ()

let depth_match_succ (n: nat { n <> 0 }) (p: perm) (c: cbor_raw) (v: raw_data_item)
  : Lemma (depth_match n p c v == cbor_match_with_depth (n - 1) p c v)
= ()

(* Element-level array gather (over sequences of cbor_raw). *)
ghost
fn rec __cbor_match_with_depth_gather_array
  (n: nat)
  (p1: perm)
  (c: Seq.seq cbor_raw)
  (r1: list raw_data_item)
  (p2: perm)
  (r2: list raw_data_item)
  (gather_cb: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (r1': raw_data_item) ->
    (p2': perm) ->
    (r2': raw_data_item) ->
    stt_ghost unit emp_inames
      (depth_match n p1' c' r1' ** depth_match n p2' c' r2')
      (fun _ -> depth_match n (p1' +. p2') c' r1' ** pure (r1' == r2'))
  ))
  (_: unit)
requires
  PM.seq_list_match c r1 (depth_match n p1) **
  PM.seq_list_match c r2 (depth_match n p2)
ensures
  PM.seq_list_match c r1 (depth_match n (p1 +. p2)) **
  pure (r1 == r2)
decreases r1
{
  match r1 {
    [] -> {
      PM.seq_list_match_nil_elim c [] (depth_match n p1);
      PM.seq_list_match_nil_elim c r2 (depth_match n p2);
      PM.seq_list_match_nil_intro c r1 (depth_match n (p1 +. p2));
    }
    a1 :: q1 -> {
      PM.seq_list_match_cons_elim c (a1 :: q1) (depth_match n p1);
      PM.seq_list_match_cons_elim c r2 (depth_match n p2);
      let a2 :: q2 = r2;
      gather_cb p1 (Seq.head c) a1 p2 a2;
      __cbor_match_with_depth_gather_array n p1 (Seq.tail c) q1 p2 q2 gather_cb ();
      PM.seq_list_match_cons_intro (Seq.head c) a1 (Seq.tail c) q1 (depth_match n (p1 +. p2));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ()
    }
  }
}

(* Array gather at the cbor_match_array level. *)
ghost
fn cbor_match_with_depth_gather_array
  (n: nat)
  (p1: perm)
  (c: cbor_array)
  (r1: raw_data_item {Array? r1})
  (p2: perm)
  (r2: raw_data_item {Array? r2})
  (gather_cb: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (r1': raw_data_item) ->
    (p2': perm) ->
    (r2': raw_data_item) ->
    stt_ghost unit emp_inames
      (depth_match n p1' c' r1' ** depth_match n p2' c' r2')
      (fun _ -> depth_match n (p1' +. p2') c' r1' ** pure (r1' == r2'))
  ))
  (_: unit)
requires
  cbor_match_array c p1 r1 (depth_match n) **
  cbor_match_array c p2 r2 (depth_match n)
ensures
  cbor_match_array c (p1 +. p2) r1 (depth_match n) **
  pure (r1 == r2)
{
  unfold cbor_match_array c p1 r1 (depth_match n);
  with v1 _pm1. assert S.pts_to c.cbor_array_ptr #_pm1 v1;
  unfold cbor_match_array c p2 r2 (depth_match n);
  with v2 _pm2. assert S.pts_to c.cbor_array_ptr #_pm1 v1 ** S.pts_to c.cbor_array_ptr #_pm2 v2;
  assert PM.seq_list_match v1 (Array?.v r1) (depth_match n (p1 `perm_mul` c.cbor_array_payload_perm));
  assert PM.seq_list_match v2 (Array?.v r2) (depth_match n (p2 `perm_mul` c.cbor_array_payload_perm));
  S.gather c.cbor_array_ptr #_ #_ #_pm1 #_pm2;
  assert (pure (v1 == v2));
  rewrite each v2 as v1;
  __cbor_match_with_depth_gather_array n (p1 `perm_mul` c.cbor_array_payload_perm) v1 (Array?.v r1) (p2 `perm_mul` c.cbor_array_payload_perm) (Array?.v r2) gather_cb ();
  perm_mul_add_l p1 p2 c.cbor_array_array_perm;
  perm_mul_add_l p1 p2 c.cbor_array_payload_perm;
  rewrite each (p1 `perm_mul` c.cbor_array_payload_perm +. p2 `perm_mul` c.cbor_array_payload_perm)
            as ((p1 +. p2) `perm_mul` c.cbor_array_payload_perm);
  rewrite each (p1 `perm_mul` c.cbor_array_array_perm +. p2 `perm_mul` c.cbor_array_array_perm)
            as ((p1 +. p2) `perm_mul` c.cbor_array_array_perm);
  fold cbor_match_array c (p1 +. p2) r1 (depth_match n);
  ();
}

(* Element-level map gather (over sequences of cbor_map_entry). *)
ghost
fn rec __cbor_match_with_depth_gather_map0
  (n: nat)
  (r01: raw_data_item)
  (p1: perm)
  (c: Seq.seq cbor_map_entry)
  (r1: list (raw_data_item & raw_data_item) { r1 << r01 })
  (r02: raw_data_item)
  (p2: perm)
  (r2: list (raw_data_item & raw_data_item) { r2 << r02 })
  (gather_cb: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (r1': raw_data_item) ->
    (p2': perm) ->
    (r2': raw_data_item) ->
    stt_ghost unit emp_inames
      (depth_match n p1' c' r1' ** depth_match n p2' c' r2')
      (fun _ -> depth_match n (p1' +. p2') c' r1' ** pure (r1' == r2'))
  ))
  (_: unit)
requires
  PM.seq_list_match c r1 (cbor_match_map_entry0 r01 (depth_match n p1)) **
  PM.seq_list_match c r2 (cbor_match_map_entry0 r02 (depth_match n p2))
ensures
  PM.seq_list_match c r1 (cbor_match_map_entry0 r01 (depth_match n (p1 +. p2))) **
  pure ((r1 <: list (raw_data_item & raw_data_item)) == (r2 <: list (raw_data_item & raw_data_item)))
decreases r1
{
  match r1 {
    [] -> {
      PM.seq_list_match_nil_elim c [] (cbor_match_map_entry0 r01 (depth_match n p1));
      PM.seq_list_match_nil_elim c r2 (cbor_match_map_entry0 r02 (depth_match n p2));
      PM.seq_list_match_nil_intro c r1 (cbor_match_map_entry0 r01 (depth_match n (p1 +. p2)));
    }
    a1 :: q1 -> {
      PM.seq_list_match_cons_elim c (a1 :: q1) (cbor_match_map_entry0 r01 (depth_match n p1));
      PM.seq_list_match_cons_elim c r2 (cbor_match_map_entry0 r02 (depth_match n p2));
      let a2 :: q2 = r2;
      unfold (cbor_match_map_entry0 r02 (depth_match n p2) (Seq.head c) a2);
      unfold (cbor_match_map_entry0 r01 (depth_match n p1) (Seq.head c) a1);
      gather_cb p1 (Seq.head c).cbor_map_entry_key (fst a1) p2 (fst a2);
      gather_cb p1 (Seq.head c).cbor_map_entry_value (snd a1) p2 (snd a2);
      fold (cbor_match_map_entry0 r01 (depth_match n (p1 +. p2)) (Seq.head c) a1);
      __cbor_match_with_depth_gather_map0 n r01 p1 (Seq.tail c) q1 r02 p2 q2 gather_cb ();
      PM.seq_list_match_cons_intro (Seq.head c) a1 (Seq.tail c) q1 (cbor_match_map_entry0 r01 (depth_match n (p1 +. p2)));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ();
    }
  }
}

(* Map gather at the cbor_match_map0 level. *)
ghost
fn cbor_match_with_depth_gather_map
  (n: nat)
  (p1: perm)
  (c: cbor_map)
  (r1: raw_data_item {Map? r1})
  (p2: perm)
  (r2: raw_data_item {Map? r2})
  (gather_cb: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (r1': raw_data_item) ->
    (p2': perm) ->
    (r2': raw_data_item) ->
    stt_ghost unit emp_inames
      (depth_match n p1' c' r1' ** depth_match n p2' c' r2')
      (fun _ -> depth_match n (p1' +. p2') c' r1' ** pure (r1' == r2'))
  ))
  (_: unit)
requires
  cbor_match_map0 c p1 r1 (depth_match n) **
  cbor_match_map0 c p2 r2 (depth_match n)
ensures
  cbor_match_map0 c (p1 +. p2) r1 (depth_match n) **
  pure (eq2 #raw_data_item r1 r2)
{
  unfold cbor_match_map0 c p1 r1 (depth_match n);
  with v1 _pm1. assert S.pts_to c.cbor_map_ptr #_pm1 v1;
  unfold cbor_match_map0 c p2 r2 (depth_match n);
  with v2 _pm2. assert S.pts_to c.cbor_map_ptr #_pm1 v1 ** S.pts_to c.cbor_map_ptr #_pm2 v2;
  assert PM.seq_list_match v1 (Map?.v r1) (cbor_match_map_entry0 r1 (depth_match n (p1 `perm_mul` c.cbor_map_payload_perm)));
  assert PM.seq_list_match v2 (Map?.v r2) (cbor_match_map_entry0 r2 (depth_match n (p2 `perm_mul` c.cbor_map_payload_perm)));
  S.gather c.cbor_map_ptr #_ #_ #_pm1 #_pm2;
  assert (pure (v1 == v2));
  rewrite each v2 as v1;
  __cbor_match_with_depth_gather_map0 n r1 (p1 `perm_mul` c.cbor_map_payload_perm) v1 (Map?.v r1) r2 (p2 `perm_mul` c.cbor_map_payload_perm) (Map?.v r2) gather_cb ();
  perm_mul_add_l p1 p2 c.cbor_map_payload_perm;
  perm_mul_add_l p1 p2 c.cbor_map_array_perm;
  rewrite each (p1 `perm_mul` c.cbor_map_payload_perm +. p2 `perm_mul` c.cbor_map_payload_perm)
            as ((p1 +. p2) `perm_mul` c.cbor_map_payload_perm);
  rewrite each (p1 `perm_mul` c.cbor_map_array_perm +. p2 `perm_mul` c.cbor_map_array_perm)
            as ((p1 +. p2) `perm_mul` c.cbor_map_array_perm);
  fold cbor_match_map0 c (p1 +. p2) r1 (depth_match n);
  ();
}

(* Main depth-preserving gather for a single cbor value. *)
ghost
fn rec cbor_match_with_depth_gather
  (n: nat)
  (p1: perm)
  (c: cbor_raw)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
requires
  cbor_match_with_depth n p1 c r1 **
  cbor_match_with_depth n p2 c r2
ensures
  cbor_match_with_depth n (p1 +. p2) c r1 **
  pure (r1 == r2)
decreases n
{
  ghost
  fn gather_cb (p1': perm) (c': cbor_raw) (v1': raw_data_item) (p2': perm) (v2': raw_data_item)
  requires depth_match n p1' c' v1' ** depth_match n p2' c' v2'
  ensures depth_match n (p1' +. p2') c' v1' ** pure (v1' == v2')
  {
    if (n = 0) {
      depth_match_zero p1' c' v1';
      rewrite (depth_match n p1' c' v1') as (pure False);
      depth_match_zero p2' c' v2';
      rewrite (depth_match n p2' c' v2') as (pure False);
      depth_match_zero (p1' +. p2') c' v1';
      rewrite emp as (depth_match n (p1' +. p2') c' v1' ** pure (v1' == v2'));
    } else {
      depth_match_succ n p1' c' v1';
      rewrite (depth_match n p1' c' v1') as (cbor_match_with_depth (n - 1) p1' c' v1');
      depth_match_succ n p2' c' v2';
      rewrite (depth_match n p2' c' v2') as (cbor_match_with_depth (n - 1) p2' c' v2');
      cbor_match_with_depth_gather (n - 1) p1' c' v1' p2' v2';
      depth_match_succ n (p1' +. p2') c' v1';
      rewrite (cbor_match_with_depth (n - 1) (p1' +. p2') c' v1') as (depth_match n (p1' +. p2') c' v1');
    }
  };
  cbor_match_with_depth_cases n c #p1;
  cbor_match_with_depth_cases n c #p2;
  match c {
    norewrite
    CBOR_Case_Int v -> {
      cbor_match_with_depth_eq_match_int n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match p1 c r1);
      cbor_match_with_depth_eq_match_int n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match p2 c r2);
      cbor_raw_gather p1 c r1 p2 r2;
      cbor_match_with_depth_eq_match_int n (p1 +. p2) v r1;
      rewrite (cbor_match (p1 +. p2) c r1) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Simple v -> {
      cbor_match_with_depth_eq_match_simple n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match p1 c r1);
      cbor_match_with_depth_eq_match_simple n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match p2 c r2);
      cbor_raw_gather p1 c r1 p2 r2;
      cbor_match_with_depth_eq_match_simple n (p1 +. p2) v r1;
      rewrite (cbor_match (p1 +. p2) c r1) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_String v -> {
      cbor_match_with_depth_eq_match_string n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match p1 c r1);
      cbor_match_with_depth_eq_match_string n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match p2 c r2);
      cbor_raw_gather p1 c r1 p2 r2;
      cbor_match_with_depth_eq_match_string n (p1 +. p2) v r1;
      rewrite (cbor_match (p1 +. p2) c r1) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Serialized_Array v -> {
      cbor_match_with_depth_eq_match_ser_array n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match p1 c r1);
      cbor_match_with_depth_eq_match_ser_array n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match p2 c r2);
      cbor_raw_gather p1 c r1 p2 r2;
      cbor_match_with_depth_eq_match_ser_array n (p1 +. p2) v r1;
      rewrite (cbor_match (p1 +. p2) c r1) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Serialized_Map v -> {
      cbor_match_with_depth_eq_match_ser_map n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match p1 c r1);
      cbor_match_with_depth_eq_match_ser_map n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match p2 c r2);
      cbor_raw_gather p1 c r1 p2 r2;
      cbor_match_with_depth_eq_match_ser_map n (p1 +. p2) v r1;
      rewrite (cbor_match (p1 +. p2) c r1) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Serialized_Tagged v -> {
      cbor_match_with_depth_eq_match_ser_tagged n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match p1 c r1);
      cbor_match_with_depth_eq_match_ser_tagged n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match p2 c r2);
      cbor_raw_gather p1 c r1 p2 r2;
      cbor_match_with_depth_eq_match_ser_tagged n (p1 +. p2) v r1;
      rewrite (cbor_match (p1 +. p2) c r1) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Tagged v -> {
      cbor_match_with_depth_eq_tagged n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match_tagged v p1 r1 (depth_cb n r1));
      unfold (cbor_match_tagged v p1 r1 (depth_cb n r1));
      with c1. assert (R.pts_to v.cbor_tagged_ptr #(perm_mul p1 v.cbor_tagged_ref_perm) c1);
      cbor_match_with_depth_eq_tagged n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match_tagged v p2 r2 (depth_cb n r2));
      unfold (cbor_match_tagged v p2 r2 (depth_cb n r2));
      with c2. assert (R.pts_to v.cbor_tagged_ptr #(perm_mul p1 v.cbor_tagged_ref_perm) c1 ** R.pts_to v.cbor_tagged_ptr #(perm_mul p2 v.cbor_tagged_ref_perm) c2);
      R.gather v.cbor_tagged_ptr;
      rewrite each c2 as c1;
      rewrite (depth_cb n r1 (perm_mul p1 v.cbor_tagged_payload_perm) c1 (Tagged?.v r1)) as (depth_match n (perm_mul p1 v.cbor_tagged_payload_perm) c1 (Tagged?.v r1));
      rewrite (depth_cb n r2 (perm_mul p2 v.cbor_tagged_payload_perm) c1 (Tagged?.v r2)) as (depth_match n (perm_mul p2 v.cbor_tagged_payload_perm) c1 (Tagged?.v r2));
      gather_cb (perm_mul p1 v.cbor_tagged_payload_perm) c1 (Tagged?.v r1) (perm_mul p2 v.cbor_tagged_payload_perm) (Tagged?.v r2);
      perm_mul_add_l p1 p2 v.cbor_tagged_ref_perm;
      perm_mul_add_l p1 p2 v.cbor_tagged_payload_perm;
      rewrite each (perm_mul p1 v.cbor_tagged_payload_perm +. perm_mul p2 v.cbor_tagged_payload_perm) as (perm_mul (p1 +. p2) v.cbor_tagged_payload_perm);
      rewrite (depth_match n (perm_mul (p1 +. p2) v.cbor_tagged_payload_perm) c1 (Tagged?.v r1)) as (depth_cb n r1 (perm_mul (p1 +. p2) v.cbor_tagged_payload_perm) c1 (Tagged?.v r1));
      fold (cbor_match_tagged v (p1 +. p2) r1 (depth_cb n r1));
      cbor_match_with_depth_eq_tagged n (p1 +. p2) v r1;
      rewrite (cbor_match_tagged v (p1 +. p2) r1 (depth_cb n r1)) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Array v -> {
      cbor_match_with_depth_eq_array n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match_array v p1 r1 (depth_cb n r1));
      rewrite (cbor_match_array v p1 r1 (depth_cb n r1)) as (cbor_match_array v p1 r1 (depth_match n));
      cbor_match_with_depth_eq_array n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match_array v p2 r2 (depth_cb n r2));
      rewrite (cbor_match_array v p2 r2 (depth_cb n r2)) as (cbor_match_array v p2 r2 (depth_match n));
      cbor_match_with_depth_gather_array n p1 v r1 p2 r2 gather_cb ();
      rewrite (cbor_match_array v (p1 +. p2) r1 (depth_match n)) as (cbor_match_array v (p1 +. p2) r1 (depth_cb n r1));
      cbor_match_with_depth_eq_array n (p1 +. p2) v r1;
      rewrite (cbor_match_array v (p1 +. p2) r1 (depth_cb n r1)) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Map v -> {
      cbor_match_with_depth_eq_map0 n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match_map0 v p1 r1 (depth_cb n r1));
      rewrite (cbor_match_map0 v p1 r1 (depth_cb n r1)) as (cbor_match_map0 v p1 r1 (depth_match n));
      cbor_match_with_depth_eq_map0 n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match_map0 v p2 r2 (depth_cb n r2));
      rewrite (cbor_match_map0 v p2 r2 (depth_cb n r2)) as (cbor_match_map0 v p2 r2 (depth_match n));
      cbor_match_with_depth_gather_map n p1 v r1 p2 r2 gather_cb ();
      rewrite (cbor_match_map0 v (p1 +. p2) r1 (depth_match n)) as (cbor_match_map0 v (p1 +. p2) r1 (depth_cb n r1));
      cbor_match_with_depth_eq_map0 n (p1 +. p2) v r1;
      rewrite (cbor_match_map0 v (p1 +. p2) r1 (depth_cb n r1)) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Array_Gen v -> {
      cbor_match_with_depth_eq_array_gen n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match_mixed_list_array p1 v r1 (depth_cb n r1));
      rewrite (cbor_match_mixed_list_array p1 v r1 (depth_cb n r1)) as (cbor_match_mixed_list_array p1 v r1 (depth_match n));
      cbor_match_with_depth_eq_array_gen n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match_mixed_list_array p2 v r2 (depth_cb n r2));
      rewrite (cbor_match_mixed_list_array p2 v r2 (depth_cb n r2)) as (cbor_match_mixed_list_array p2 v r2 (depth_match n));
      cbor_match_mixed_list_array_gather p1 p2 v r1 r2 (depth_match n) gather_cb;
      rewrite (cbor_match_mixed_list_array (p1 +. p2) v r1 (depth_match n)) as (cbor_match_mixed_list_array (p1 +. p2) v r1 (depth_cb n r1));
      cbor_match_with_depth_eq_array_gen n (p1 +. p2) v r1;
      rewrite (cbor_match_mixed_list_array (p1 +. p2) v r1 (depth_cb n r1)) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Map_Gen v -> {
      cbor_match_with_depth_eq_map_gen n p1 v r1;
      rewrite (cbor_match_with_depth n p1 c r1) as (cbor_match_mixed_list_map p1 v r1 (depth_cb n r1));
      rewrite (cbor_match_mixed_list_map p1 v r1 (depth_cb n r1)) as (cbor_match_mixed_list_map p1 v r1 (depth_match n));
      cbor_match_with_depth_eq_map_gen n p2 v r2;
      rewrite (cbor_match_with_depth n p2 c r2) as (cbor_match_mixed_list_map p2 v r2 (depth_cb n r2));
      rewrite (cbor_match_mixed_list_map p2 v r2 (depth_cb n r2)) as (cbor_match_mixed_list_map p2 v r2 (depth_match n));
      cbor_match_mixed_list_map_gather p1 p2 v r1 r2 (depth_match n) gather_cb;
      rewrite (cbor_match_mixed_list_map (p1 +. p2) v r1 (depth_match n)) as (cbor_match_mixed_list_map (p1 +. p2) v r1 (depth_cb n r1));
      cbor_match_with_depth_eq_map_gen n (p1 +. p2) v r1;
      rewrite (cbor_match_mixed_list_map (p1 +. p2) v r1 (depth_cb n r1)) as (cbor_match_with_depth n (p1 +. p2) c r1);
    }
  }
}

(* Element share_t / gather_t for the unrefined depth_match n vmatch.
   These are exactly what l2r_write_mixed_list needs when the mixed-list match
   is weakened from (cbor_match_bounded r (depth_cb n r)) to (depth_match n). *)

ghost
fn depth_match_share (n: nat) (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires depth_match n p x1 x2
ensures depth_match n (p /. 2.0R) x1 x2 ** depth_match n (p /. 2.0R) x1 x2
{
  if (n = 0) {
    depth_match_zero p x1 x2;
    rewrite (depth_match n p x1 x2) as (pure False);
    rewrite emp as (depth_match n (p /. 2.0R) x1 x2 ** depth_match n (p /. 2.0R) x1 x2);
  } else {
    depth_match_succ n p x1 x2;
    rewrite (depth_match n p x1 x2) as (cbor_match_with_depth (n - 1) p x1 x2);
    cbor_match_with_depth_share (n - 1) p x1 x2;
    depth_match_succ n (p /. 2.0R) x1 x2;
    rewrite (cbor_match_with_depth (n - 1) (p /. 2.0R) x1 x2) as (depth_match n (p /. 2.0R) x1 x2);
    rewrite (cbor_match_with_depth (n - 1) (p /. 2.0R) x1 x2) as (depth_match n (p /. 2.0R) x1 x2);
  }
}

ghost
fn depth_match_gather (n: nat) (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires depth_match n p x1 x2 ** depth_match n p' x1 x2'
ensures depth_match n (p +. p') x1 x2 ** pure (x2 == x2')
{
  if (n = 0) {
    depth_match_zero p x1 x2;
    rewrite (depth_match n p x1 x2) as (pure False);
    depth_match_zero p' x1 x2';
    rewrite (depth_match n p' x1 x2') as (pure False);
    depth_match_zero (p +. p') x1 x2;
    rewrite emp as (depth_match n (p +. p') x1 x2 ** pure (x2 == x2'));
  } else {
    depth_match_succ n p x1 x2;
    rewrite (depth_match n p x1 x2) as (cbor_match_with_depth (n - 1) p x1 x2);
    depth_match_succ n p' x1 x2';
    rewrite (depth_match n p' x1 x2') as (cbor_match_with_depth (n - 1) p' x1 x2');
    cbor_match_with_depth_gather (n - 1) p x1 x2 p' x2';
    depth_match_succ n (p +. p') x1 x2;
    rewrite (cbor_match_with_depth (n - 1) (p +. p') x1 x2) as (depth_match n (p +. p') x1 x2);
  }
}


(* ============================================================ *)
(* Element-writer bridge helpers.                               *)
(*                                                              *)
(* An element writer for a mixed-list at depth n holds          *)
(* (depth_match n) for each live element.  At n=0 this is       *)
(* pure False, so the writer body is vacuous.  At n>=1 it is    *)
(* cbor_match_with_depth (nat_pred n), which the (n-1)-writer   *)
(* handles.  These two helpers convert back and forth and       *)
(* expose n>=1 so the recursive call typechecks.                *)
(* ============================================================ *)

ghost
fn depth_match_to_depth_pos (n: nat) (p: perm) (x1: cbor_raw) (x2: raw_data_item)
requires depth_match n p x1 x2
ensures cbor_match_with_depth (nat_pred n) p x1 x2 ** pure (n >= 1)
{
  if (n = 0) {
    depth_match_zero p x1 x2;
    rewrite (depth_match n p x1 x2) as (pure False);
    rewrite emp as (cbor_match_with_depth (nat_pred n) p x1 x2 ** pure (n >= 1));
  } else {
    depth_match_succ n p x1 x2;
    rewrite (depth_match n p x1 x2) as (cbor_match_with_depth (n - 1) p x1 x2);
    nat_pred_succ n;
    rewrite (cbor_match_with_depth (n - 1) p x1 x2) as (cbor_match_with_depth (nat_pred n) p x1 x2);
  }
}

ghost
fn depth_to_depth_match (n: nat { n >= 1 }) (p: perm) (x1: cbor_raw) (x2: raw_data_item)
requires cbor_match_with_depth (nat_pred n) p x1 x2
ensures depth_match n p x1 x2
{
  nat_pred_succ n;
  rewrite (cbor_match_with_depth (nat_pred n) p x1 x2) as (cbor_match_with_depth (n - 1) p x1 x2);
  depth_match_succ n p x1 x2;
  rewrite (cbor_match_with_depth (n - 1) p x1 x2) as (depth_match n p x1 x2);
}


(* ============================================================ *)
(* Pair-level depth match for the MAP mixed-list case.          *)
(* The map element is a cbor_map_entry matched against a pair   *)
(* (raw_data_item & raw_data_item); the serializer is           *)
(* serialize_nondep_then serialize_raw_data_item ..._item.      *)
(* ============================================================ *)

module Trade = Pulse.Lib.Trade.Util

let depth_match_pair (n: nat) (pm': perm) (entry: cbor_map_entry) (pair: (raw_data_item & raw_data_item)) : slprop =
  depth_match n pm' entry.cbor_map_entry_key (fst pair) **
  depth_match n pm' entry.cbor_map_entry_value (snd pair)

ghost
fn depth_match_pair_share (n: nat) (entry: cbor_map_entry) (#pm: perm) (#pair: (raw_data_item & raw_data_item))
requires depth_match_pair n pm entry pair
ensures depth_match_pair n (pm /. 2.0R) entry pair ** depth_match_pair n (pm /. 2.0R) entry pair
{
  unfold (depth_match_pair n pm entry pair);
  depth_match_share n entry.cbor_map_entry_key #pm #(fst pair);
  depth_match_share n entry.cbor_map_entry_value #pm #(snd pair);
  fold (depth_match_pair n (pm /. 2.0R) entry pair);
  fold (depth_match_pair n (pm /. 2.0R) entry pair);
}

ghost
fn depth_match_pair_gather (n: nat) (entry: cbor_map_entry) (#pm: perm) (#pair: (raw_data_item & raw_data_item)) (#pm': perm) (#pair': (raw_data_item & raw_data_item))
requires depth_match_pair n pm entry pair ** depth_match_pair n pm' entry pair'
ensures depth_match_pair n (pm +. pm') entry pair ** pure (pair == pair')
{
  unfold (depth_match_pair n pm entry pair);
  unfold (depth_match_pair n pm' entry pair');
  depth_match_gather n entry.cbor_map_entry_key #pm #(fst pair) #pm' #(fst pair');
  depth_match_gather n entry.cbor_map_entry_value #pm #(snd pair) #pm' #(snd pair');
  fold (depth_match_pair n (pm +. pm') entry pair);
}

fn depth_match_pair_proj1 (n: nat) (pm': perm) (xl: cbor_map_entry) (xh: Ghost.erased (raw_data_item & raw_data_item))
requires depth_match_pair n pm' xl xh
returns res: cbor_raw
ensures depth_match n pm' res (fst xh) ** Trade.trade (depth_match n pm' res (fst xh)) (depth_match_pair n pm' xl xh)
{
  Trade.rewrite_with_trade
    (depth_match_pair n pm' xl xh)
    (depth_match n pm' xl.cbor_map_entry_key (fst xh) ** depth_match n pm' xl.cbor_map_entry_value (snd xh));
  Trade.elim_hyp_r _ _ _;
  xl.cbor_map_entry_key
}

fn depth_match_pair_proj2 (n: nat) (pm': perm) (xl: cbor_map_entry) (xh: Ghost.erased (raw_data_item & raw_data_item))
requires depth_match_pair n pm' xl xh
returns res: cbor_raw
ensures depth_match n pm' res (snd xh) ** Trade.trade (depth_match n pm' res (snd xh)) (depth_match_pair n pm' xl xh)
{
  Trade.rewrite_with_trade
    (depth_match_pair n pm' xl xh)
    (depth_match n pm' xl.cbor_map_entry_key (fst xh) ** depth_match n pm' xl.cbor_map_entry_value (snd xh));
  Trade.elim_hyp_l _ _ _;
  xl.cbor_map_entry_value
}
