module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Impl
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux

let seq_slice_append_pat
  (#t: Type) (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
  [SMTPat (Seq.append s1 s2)]
= ()

let cbor_parse_prefix_elim
  (p: cbor_parser)
  (x y: Seq.seq FStar.UInt8.t)
: Lemma
  (requires (match p x with
    | Some (_, n) -> Seq.length y >= n /\ Seq.slice x 0 n == Seq.slice y 0 n
    | _ -> False
  ))
  (ensures p x == p y)
= assert (cbor_parse_prefix_prop' p x y)

#lang-pulse

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map
module Util = CBOR.Spec.Util
module SM = Pulse.Lib.SeqMatch
module EqTest = CDDL.Spec.EqTest
module Iterator = CDDL.Pulse.Iterator.Base
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Cbor = CBOR.Spec.API.Format
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module Lemmas = CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas
module Snoc = CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Lemmas.Snoc
module FP = PulseCore.FractionalPermission

inline_for_extraction noextract [@@noextract_to "krml"]
fn slice_split (#t: Type) (s: S.slice t) (#p: FP.perm) (i: SZ.t) (#v: Ghost.erased (Seq.seq t))
    requires S.pts_to s #p v ** pure (SZ.v i <= Seq.length v)
    returns res: (S.slice t & S.slice t)
    ensures (let (s1, s2) = res in exists* v1 v2 .
      S.pts_to s1 #p v1 ** S.pts_to s2 #p v2 ** S.is_split s s1 s2 **
      pure (Lemmas.slice_split_post i v v1 v2)
    )
{
  Seq.lemma_split v (SZ.v i);
  let (s1, s2) = S.split s i;
  (s1, s2)
}

(* ===== Main loop function ===== *)

#push-options "--z3rlimit 384 --fuel 2 --ifuel 2 --split_queries always"

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_iterator_gen
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty': Type0) (#vmatch': FP.perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': FP.perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#[@@@erasable] except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
    (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec ikey) -> [@@@erasable] Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
    (is_empty: cddl_map_iterator_is_empty_gen_t _ _ iterator r)
    (next: cddl_map_iterator_next_gen_t _ _ iterator r)
    (rel_len: rel_map_iterator_length _ _ iterator r)
: Lemmas.impl_serialize_map_zero_or_more_iterator_gen_t #pe #minl #maxl #key #tkey sp1 #ikey r1 #value #tvalue #inj sp2 except #ivalue r2 #p iterator r
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let sp = Ghost.hide (mg_zero_or_more_match_item sp1 sp2 except);
  let mut pc = c0;
  let pm1 = GR.alloc (Map.empty tkey (list tvalue));
  assert (pure (
    let m1 = Map.empty tkey (list tvalue) in
    sp.mg_serializable m1 /\
    sp.mg_serializer m1 `cbor_map_equal` cbor_map_empty
  ));
  let pm2 = GR.alloc (Ghost.reveal v0);
  let mut pres = true;
  let pb = GR.alloc true;
  Trade.refl (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0);
  while (
    let res = !pres;
    if (res) {
      with gc . assert (R.pts_to pc gc);
      let c = !pc;
      rewrite each (Ghost.reveal gc) as c;
      let em = is_empty (Iterator.mk_spec r1) (Iterator.mk_spec r2) c;
      let b = not em;
      GR.op_Colon_Equals pb b;
      b
    } else {
      GR.op_Colon_Equals pb false;
      false
    }
  ) invariant b. exists* c m1 m2' (m2: Map.t (dfst (Iterator.mk_spec r1)) (list (dfst (Iterator.mk_spec r2)))) res w count size . (
    R.pts_to pc c **
    GR.pts_to pm1 m1 **
    GR.pts_to pm2 m2' **
    R.pts_to pres res **
    S.pts_to out w **
    R.pts_to out_count count **
    R.pts_to out_size size **
    GR.pts_to pb b **
    r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c m2 **
    Trade.trade 
      (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c m2)
      (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0) **
    pure (
      Lemmas.impl_serialize_map_zero_or_more_iterator_inv sp1 sp2 except p maxl v0 l res w m1 (Ghost.hide (Ghost.reveal m2)) m2' count size /\
      (b == false ==> (res == false \/ m2 == Map.empty _ _))
    )
  ) {
    rel_len #(Iterator.mk_spec r1) #(Iterator.mk_spec r2) _ _;
    S.pts_to_len out;
    with m1 . assert (GR.pts_to pm1 m1);
    let count = !out_count;
    with c2_ m2_ . assert (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c2_ m2_);
    if (count = pow2_64_m1) {
      Snoc.impl_serialize_map_group_valid_map_zero_or_more_snoc_overflow sp1 key_eq sp2 except maxl l m1 m2_ (SZ.v (S.len out));
      GR.op_Colon_Equals pb false;
      pres := false
    } else {
      let count' = U64.add count 1uL;
      let (ck, cv) = next (Iterator.mk_spec r1) (Iterator.mk_spec r2) pc;
      with ke_ va_ . assert (dsnd (Iterator.mk_spec r1) (fst (ck, cv)) ke_ ** dsnd (Iterator.mk_spec r2) (snd (ck, cv)) va_);
      let ke : Ghost.erased tkey = Ghost.hide (Ghost.reveal ke_);
      let va : Ghost.erased tvalue = Ghost.hide (Ghost.reveal va_);
      Trade.rewrite_with_trade
        (dsnd (Iterator.mk_spec r1) (fst (ck, cv)) _ ** dsnd (Iterator.mk_spec r2) (snd (ck, cv)) _)
        (r1 ck ke ** r2 cv va);
      Trade.trans_hyp_l (r1 ck ke ** r2 cv va) _ _ _;
      Trade.trans _ _ (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0);
      with c2 m2 . assert (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c2 m2);
      rel_len #(Iterator.mk_spec r1) #(Iterator.mk_spec r2) _ _;
      Snoc.impl_serialize_map_group_valid_map_zero_or_more_snoc sp1 key_eq sp2 except maxl l m1 ke va m2 (SZ.v (S.len out));
      let mkv : Ghost.erased (Map.t tkey (list tvalue)) = EqTest.map_singleton (Ghost.reveal ke) (Ghost.reveal key_eq ke) [Ghost.reveal va];
      let m2' : Ghost.erased (Map.t tkey (list tvalue)) = map_of_list_cons key_eq (Ghost.reveal ke) (Ghost.reveal va) m2;
      Classical.forall_intro (EqTest.eq_test_unique key_eq);
      assert (pure (m2' == m2_));
      map_of_list_is_append_cons_snoc_equiv key_eq m1 ke va m2 v0;
      let m1' : Ghost.erased (Map.t tkey (list tvalue)) = map_of_list_snoc key_eq m1 (Ghost.reveal ke) (Ghost.reveal va);
      let size0 = !out_size;
      with w . assert (S.pts_to out w);
      Seq.lemma_split w (SZ.v size0);
      let (outl1, out1) = S.split out size0;
      with z1l . assert (S.pts_to outl1 z1l);
      let sz1 = pa1 ck out1;
      S.pts_to_len out1;
      Trade.assoc_hyp_r _ _ _ _;
      Trade.elim_hyp_l (r1 ck (Ghost.reveal ke)) _ _;
      if (sz1 = 0sz) {
        Trade.elim_hyp_l (r2 cv (Ghost.reveal va)) _ _;
        S.join _ _ out;
        S.pts_to_len out;
        GR.op_Colon_Equals pb false;
        pres := false
      } else {
        with w1 . assert (S.pts_to out1 w1);
        Seq.lemma_split w1 (SZ.v sz1);
        let (outl2, out2) = S.split out1 sz1;
        with z2l . assert (S.pts_to outl2 z2l);
        S.pts_to_len out2;
        let sz2 = pa2 cv out2;
        with w2 . assert (S.pts_to out2 w2);
        S.pts_to_len out2;
        S.pts_to_len outl2;
        Trade.elim_hyp_l (r2 cv (Ghost.reveal va)) _ _;
        if (sz2 = 0sz) {
          S.join _ _ out1;
          S.pts_to_len out1;
          S.pts_to_len outl1;
          S.join _ _ out;
          S.pts_to_len out;
          GR.op_Colon_Equals pb false;
          pres := false
        } else {
          Seq.lemma_split w2 (SZ.v sz2);
          with vl . assert (S.pts_to outl2 vl);
          assert (pure (Seq.equal vl (Seq.slice w1 0 (SZ.v sz1))));
          let Some oo1 = parse outl2;
          rewrite (cbor_parse_post pe vmatch' outl2 1.0R vl (Some oo1))
            as (cbor_parse_post_some pe vmatch' outl2 1.0R vl (fst oo1) (snd oo1));
          unfold (cbor_parse_post_some pe vmatch' outl2 1.0R vl (fst oo1) (snd oo1));
          let o1 = fst oo1;
          let orem1 = snd oo1;
          rewrite each (FStar.Pervasives.Native.fst oo1) as o1;
          rewrite each (FStar.Pervasives.Native.snd oo1) as orem1;
          with ke' . assert (vmatch' 1.0R o1 ke');
          with w1'' . assert (S.pts_to orem1 w1'');
          cbor_parse_prefix_elim pe (Seq.slice w2 0 (SZ.v sz2)) w2;
          let Some oo2 = parse out2;
          rewrite (cbor_parse_post pe vmatch' out2 1.0R w2 (Some oo2))
            as (cbor_parse_post_some pe vmatch' out2 1.0R w2 (fst oo2) (snd oo2));
          unfold (cbor_parse_post_some pe vmatch' out2 1.0R w2 (fst oo2) (snd oo2));
          let o2 = fst oo2;
          let orem2 = snd oo2;
          rewrite each (FStar.Pervasives.Native.fst oo2) as o2;
          rewrite each (FStar.Pervasives.Native.snd oo2) as orem2;
          with va' . assert (vmatch' 1.0R o2 va');
          with (w2'' : Seq.seq U8.t) . assert (S.pts_to orem2 w2'');
          let o = mk_map_entry o1 o2;
          let is_except = va_ex o;
          Trade.elim (vmatch2' 1.0R o _) _;
          Trade.elim (vmatch' 1.0R o2 va' ** S.pts_to orem2 w2'') (pts_to out2 w2);
          Trade.elim (vmatch' 1.0R o1 ke' ** S.pts_to orem1 _) (pts_to outl2 _);
          S.join outl2 out2 out1;
          S.join outl1 out1 out;
          S.pts_to_len out;
          if (is_except) {
            assert (pure (Ghost.reveal except ((sp1.serializer ke <: cbor), (sp2.serializer va <: cbor)) == true));
            GR.op_Colon_Equals pb false;
            pres := false
          } else {
            let size1 = SZ.add size0 sz1;
            let size2 = SZ.add size1 sz2;
            with w' . assert (S.pts_to out w');
            let (outl, outr) = slice_split out size2;
            S.pts_to_len outl;
            S.pts_to_len outr;
            seq_slice_length_zero_left w (SZ.v size0);
            Lemmas.impl_serialize_map_group_insert_prf (Ghost.reveal p) (Ghost.reveal pe) w' (cbor_map_union l (sp.mg_serializer m1)) (SZ.v size0) (sp1.serializer ke) (SZ.v sz1) (sp2.serializer va) (SZ.v sz2) w2;
            let inserted = insert outl (cbor_map_union l (sp.mg_serializer m1)) size0 (sp1.serializer ke) size1 (sp2.serializer va);
            S.pts_to_len outl;
            with wl . assert (S.pts_to outl wl);
            with wr . assert (S.pts_to outr wr);
            S.join _ _ out;
            S.pts_to_len out;
            if (not inserted) {
              GR.op_Colon_Equals pb false;
              pres := false
            } else {
              GR.op_Colon_Equals pm1 m1';
              GR.op_Colon_Equals pm2 m2;
              GR.op_Colon_Equals pb true;
              out_count := count';
              out_size := size2;
              with w_ . assert (S.pts_to out w_);
              seq_slice_append_pat wl wr;
              assert (pure (map_of_list_is_append m1' m2 v0));
              assert (pure (map_of_list_maps_to_nonempty m1'));
              assert (pure (sp.mg_serializable m1'));
              assert (pure (cbor_map_disjoint l (sp.mg_serializer m1')));
              ()
            }
          }
        }
      }
    }
  };
  Trade.elim _ _;
  with m1 . assert (GR.pts_to pm1 m1);
  GR.free pm1;
  GR.free pm2;
  GR.free pb;
  Classical.move_requires (map_of_list_is_append_nil_r_elim m1) v0;
  !pres
}

#pop-options

(* ===== Slice iterator types ===== *)

inline_for_extraction
noeq
type map_slice_iterator_t
  (impl_elt1: Type0) (impl_elt2: Type0)
  ([@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ([@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: Type0
= {
  base: (slice (impl_elt1 & impl_elt2));
  key_eq: Ghost.erased (EqTest.eq_test (dfst spec1));
}

let rel_map_slice_iterator
  (impl_elt1: Type0) (impl_elt2: Type0)
  (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: rel (map_slice_iterator_t impl_elt1 impl_elt2 spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2)))
= mk_rel (fun s l -> rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) s.key_eq (dsnd spec1) (dsnd spec2) s.base l)

(* ===== Slice iterator functions ===== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn map_slice_iterator_is_empty
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_is_empty_gen_t _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (spec1: _) (spec2: _) (s: _) (#l: _)
{
  unfold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 s l);
  unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) s.key_eq (dsnd spec1) (dsnd spec2) s.base l);
  with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  unfold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  S.pts_to_len s.base.s;
  SM.seq_list_match_length (rel_pair (dsnd spec1) (dsnd spec2)) _ _;
  fold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) s.key_eq (dsnd spec1) (dsnd spec2) s.base l);
  fold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 s l);
  Classical.forall_intro (map_of_list_pair_mem_fst s.key_eq l');
  (S.len s.base.s = 0sz)
}

ghost
fn map_slice_iterator_length
  (impl_elt1: Type0) (impl_elt2: Type0)
: rel_map_iterator_length _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (#spec1: _) (#spec2: _) (i: _) (l: _)
{
  unfold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i l);
  unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base l);
  with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  unfold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  S.pts_to_len i.base.s;
  SM.seq_list_match_length (rel_pair (dsnd spec1) (dsnd spec2)) _ _;
  fold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base l);
  fold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i l);
  ()
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn map_slice_iterator_next
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_next_gen_t _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (spec1: _) (spec2: _) (pi: _) (#gi: _) (#m: _)
{
  let i = !pi;
  let r : rel (impl_elt1 & impl_elt2) (dfst spec1 & dfst spec2) = (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2));
  Trade.rewrite_with_trade
    (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 gi m)
    (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  with l . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l);
  rewrite (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l)
    as (rel_slice_of_list r false i.base l);
  unfold (rel_slice_of_list r false i.base l);
  S.pts_to_len i.base.s;
  with s . assert (S.pts_to i.base.s #i.base.p s);
  SM.seq_list_match_length r _ _;
  Seq.lemma_split s 1;
  SM.seq_list_match_cons_elim _ _ r;
  with gres gv . assert (r gres gv);
  let res = S.op_Array_Access i.base.s 0sz;
  rewrite each gres as res;
  let (il, ir) = S.split i.base.s 1sz;
  with sl . assert (S.pts_to il #i.base.p sl);
  with sr . assert (S.pts_to ir #i.base.p sr);
  let i' : map_slice_iterator_t impl_elt1 impl_elt2 spec1 spec2 = {
    base = { s = ir; p = i.base.p; };
    key_eq = i.key_eq;
  };
  rewrite (S.pts_to ir #(i.base.p) sr) as (S.pts_to i'.base.s #i'.base.p (Seq.tail s));
  fold (rel_slice_of_list r false i'.base (List.Tot.tl l));
  rewrite (rel_slice_of_list r false i'.base (List.Tot.tl l))
    as (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base (List.Tot.tl l));
  let m' = Ghost.hide (map_of_list_pair i'.key_eq (List.Tot.tl l));
  fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m');
  Trade.rewrite_with_trade
    (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m')
    (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i' m');
  intro
    (Trade.trade
      (r res gv ** rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m')
      (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m)
    )
    #(S.is_split i.base.s il ir ** S.pts_to il #i.base.p sl)
    fn _
  {
    rewrite (S.is_split i.base.s il ir) as (S.is_split i.base.s il i'.base.s);
    unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m');
    with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base l');
    rewrite (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base l')
      as (rel_slice_of_list r false i'.base l');
    unfold (rel_slice_of_list r false i'.base l');
    with s' . assert (S.pts_to i'.base.s #i'.base.p s');
    SM.seq_list_match_cons_intro res (Ghost.reveal gv) s' l' r;
    S.join il i'.base.s i.base.s;
    with joined . assert (S.pts_to i.base.s #i.base.p joined);
    rewrite (S.pts_to i.base.s #i.base.p joined)
      as (S.pts_to i.base.s #i.base.p (Seq.cons res s'));
    fold (rel_slice_of_list
      (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2))
      false i.base (Ghost.reveal gv :: l')
    );
    fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  };
  Trade.trans_hyp_r _ _ _ _;
  Trade.trans _ _ (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 gi m);
  Trade.rewrite_with_trade
    (r res gv)
    (dsnd spec1 (fst res) (fst gv) ** dsnd spec2 (snd res) (snd gv));
  Trade.trans_hyp_l _ (r res gv) _ _;
  pi := i';
  res
}

(* ===== Slice-based serializer ===== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_slice
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty': Type0) (#vmatch': FP.perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': FP.perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#[@@@erasable] except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_slice_of_table key_eq r1 r2)
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let i : map_slice_iterator_t ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) = {
    base = c0;
    key_eq = key_eq;
  };
  Trade.rewrite_with_trade
    (rel_slice_of_table key_eq r1 r2 c0 v0)
    (rel_map_slice_iterator ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) i v0);
  let mut pi = i;
  let res = impl_serialize_map_zero_or_more_iterator_gen
    parse mk_map_entry insert key_eq pa1 pa2 va_ex
    (map_slice_iterator_t _ _)
    (rel_map_slice_iterator _ _)
    (map_slice_iterator_is_empty _ _)
    (map_slice_iterator_next _ _)
    (map_slice_iterator_length _ _)
    i out out_count out_size l;
  Trade.elim _ _;
  res
}

(* ===== Map iterator wrapper ===== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_iterator
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty: Type0) (#vmatch: FP.perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: FP.perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: FP.perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (#ty': Type0) (#vmatch': FP.perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': FP.perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#[@@@erasable] except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2))
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  impl_serialize_map_zero_or_more_iterator_gen
    parse mk_map_entry insert key_eq pa1 pa2 va_ex
    (map_iterator_t cbor_map_iterator_t _ _ vmatch vmatch2)
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match _ _)
    (cddl_map_iterator_is_empty map_is_empty map_next map_entry_key map_entry_value _ _)
    (cddl_map_iterator_next map_share map_gather map_next map_entry_key map_entry_value map_entry_share map_entry_gather _ _)
    (rel_map_iterator_prop' cbor_map_iterator_match)
    c0 out out_count out_size l
}

