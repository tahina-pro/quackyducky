module CDDL.Pulse.Serialize.Gen.ArrayGroup
#lang-pulse

module SM = Pulse.Lib.SeqMatch.Util
module GR = Pulse.Lib.GhostReference

inline_for_extraction noextract [@@noextract_to "krml";
  FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
]
let pow2_64_m1 : U64.t = U64.uint_to_t (pow2 64 - 1)

let pow2_64_m1_eq : squash (U64.v pow2_64_m1 == pow2 64 - 1) = _ by (
  FStar.Tactics.norm [delta; zeta; iota; primops];
  FStar.Tactics.trefl ()
)

let list_append_length_pat
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (List.Tot.length (List.Tot.append l1 l2) == List.Tot.length l1 + List.Tot.length l2)
  [SMTPat (List.Tot.append l1 l2)]
= List.Tot.append_length l1 l2

let list_append_assoc_pat
  (#t: Type)
  (l1 l2 l3: list t)
: Lemma
  (ensures (List.Tot.append l1 (List.Tot.append l2 l3) == List.Tot.append (List.Tot.append l1 l2) l3))
  [SMTPatOr [
    [SMTPat (List.Tot.append l1 (List.Tot.append l2 l3))];
    [SMTPat (List.Tot.append (List.Tot.append l1 l2) l3)];
  ]]
= List.Tot.append_assoc l1 l2 l3

let list_append_nil_r_pat
  (#t: Type)
  (l1: list t)
: Lemma
  (List.Tot.append l1 [] == l1)
  [SMTPat (List.Tot.append l1 [])]
= List.Tot.append_l_nil l1

let seq_slice_append
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
= ()

#push-options "--z3rlimit_factor 4"

let rec cbor_parse_list_snoc
  (p: cbor_parser) (n: nat) (x: Seq.seq U8.t)
: Lemma
  (requires (match cbor_parse_list p n x with
   | None -> False
   | Some (l, size) -> size < Seq.length x /\
      (match p (Seq.slice x size (Seq.length x)) with
      | None -> False
      | Some (_, na) -> size + na <= Seq.length x)))
  (ensures (
    let Some (l, size) = cbor_parse_list p n x in
    let Some (a, na) = p (Seq.slice x size (Seq.length x)) in
    cbor_parse_list p (n + 1) x == Some (l @ [a], size + na)))
  (decreases n)
= if n = 0
  then ()
  else
    match p x with
    | Some (hd, n_hd) ->
      let x' = Seq.slice x n_hd (Seq.length x) in
      match cbor_parse_list p (n - 1) x' with
      | Some (tl, n_tl) ->
        Seq.slice_slice x n_hd (Seq.length x) n_tl (Seq.length x - n_hd);
        assert (Seq.slice x' n_tl (Seq.length x') == Seq.slice x (n_hd + n_tl) (Seq.length x));
        cbor_parse_list_snoc p (n - 1) x'

#pop-options

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

let rec cbor_parse_list_size_le_max
  (p: cbor_parser)
  (lmax: cbor_max_length p)
  (n: nat) (x: Seq.seq U8.t)
: Lemma
  (requires (match cbor_parse_list p n x with
   | None -> True
   | Some (l, size) -> Some? (cbor_array_max_length lmax l)))
  (ensures (match cbor_parse_list p n x with
   | None -> True
   | Some (l, size) -> Some? (cbor_array_max_length lmax l) /\ size <= Some?.v (cbor_array_max_length lmax l)))
  (decreases n)
= if n = 0 then ()
  else match p x with
  | None -> ()
  | Some (a, na) ->
    let x' = Seq.slice x na (Seq.length x) in
    match cbor_parse_list p (n - 1) x' with
    | None -> ()
    | Some (q, nq) ->
      cbor_parse_list_size_le_max p lmax (n - 1) x'

#pop-options

#push-options "--z3rlimit_factor 8 --fuel 2 --ifuel 1"

let rec cbor_parse_list_split
  (p: cbor_parser)
  (n1 n2: nat)
  (x: Seq.seq U8.t)
: Lemma
  (ensures (match cbor_parse_list p (n1 + n2) x with
   | None -> True
   | Some (l, size) ->
     if n1 <= List.Tot.length l then
       let l1 = fst (List.Tot.splitAt n1 l) in
       let l2 = snd (List.Tot.splitAt n1 l) in
       match cbor_parse_list p n1 x with
       | None -> False
       | Some (l1', size1) ->
         l1' == l1 /\
         (match cbor_parse_list p n2 (Seq.slice x size1 (Seq.length x)) with
          | None -> False
          | Some (l2', size2) -> l2' == l2 /\ size == size1 + size2)
     else True
  ))
  (decreases n1)
= if n1 = 0 then begin
    match cbor_parse_list p n2 x with
    | None -> ()
    | Some (l, size) ->
      assert (Seq.slice x 0 (Seq.length x) `Seq.equal` x)
  end
  else match p x with
  | None -> ()
  | Some (a, na) ->
    let x' = Seq.slice x na (Seq.length x) in
    match cbor_parse_list p (n1 - 1 + n2) x' with
    | None -> ()
    | Some (q, nq) ->
      cbor_parse_list_split p (n1 - 1) n2 x';
      match cbor_parse_list p (n1 - 1) x' with
      | None -> ()
      | Some (l1_tail, size1_tail) ->
        Seq.slice_slice x na (Seq.length x) size1_tail (Seq.length x - na);
        ()

#pop-options

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

let rec cbor_parse_list_size_ge_min
  (p: cbor_parser)
  (lmin: cbor_min_length p)
  (n: nat) (x: Seq.seq U8.t)
: Lemma
  (ensures (match cbor_parse_list p n x with
   | None -> True
   | Some (l, size) -> size >= cbor_array_min_length lmin l))
  (decreases n)
= if n = 0 then ()
  else match p x with
  | None -> ()
  | Some (a, na) ->
    let x' = Seq.slice x na (Seq.length x) in
    match cbor_parse_list p (n - 1) x' with
    | None -> ()
    | Some (q, nq) ->
      cbor_parse_list_size_ge_min p lmin (n - 1) x'

#pop-options

let cbor_parse_list_snoc_input
  (p: cbor_parser)
  (n: nat)
  (w0: Seq.seq U8.t)
  (w1: Seq.seq U8.t)
  (size1: nat)
: Lemma
  (requires (
    match cbor_parse_list p n w0 with
    | None -> False
    | Some (l, size) ->
      size == Seq.length w0 /\
      size1 > 0 /\ size1 <= Seq.length w1 /\
      (match p (Seq.slice w1 0 size1) with
       | None -> False
       | Some (a, na) -> na == size1)
  ))
  (ensures (
    let Some (l, size) = cbor_parse_list p n w0 in
    let Some (a, _) = p (Seq.slice w1 0 size1) in
    let combined = Seq.append w0 w1 in
    cbor_parse_list_prefix p n w0 (Seq.slice combined 0 (Seq.length w0 + size1));
    cbor_parse_list p n (Seq.slice combined 0 (Seq.length w0 + size1)) == Some (l, size) /\
    (let suffix = Seq.slice (Seq.slice combined 0 (Seq.length w0 + size1)) size (Seq.length w0 + size1) in
     Seq.equal suffix (Seq.slice w1 0 size1) /\
     p suffix == Some (a, size1))
  ))
= let Some (l, size) = cbor_parse_list p n w0 in
  let combined = Seq.append w0 w1 in
  let extended = Seq.slice combined 0 (Seq.length w0 + size1) in
  assert (Seq.equal (Seq.slice w0 0 size) (Seq.slice extended 0 size));
  cbor_parse_list_prefix p n w0 extended;
  let suffix = Seq.slice extended size (Seq.length w0 + size1) in
  assert (Seq.equal suffix (Seq.slice w1 0 size1))

let rec cbor_array_max_length_det_is_serialize_list_length
  (l: list Cbor.cbor)
: Lemma
  (ensures (cbor_array_max_length cbor_det_max_length l == Some (Seq.length (Cbor.cbor_det_serialize_list l))))
  (decreases l)
= match l with
  | [] -> Cbor.cbor_det_serialize_list_nil ()
  | a :: q ->
    cbor_array_max_length_det_is_serialize_list_length q;
    Cbor.cbor_det_serialize_list_cons a q

let rec cbor_array_max_length_append
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (l1 l2: list Cbor.cbor)
: Lemma
  (ensures (
    cbor_array_max_length lmax (List.Tot.append l1 l2) == (
      match cbor_array_max_length lmax l1, cbor_array_max_length lmax l2 with
      | Some n1, Some n2 -> Some (n1 + n2)
      | _ -> None
    )
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a :: q ->
    cbor_array_max_length_append lmax q l2

let cbor_array_max_length_append_some
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (l1 l2: list Cbor.cbor)
: Lemma
  (requires Some? (cbor_array_max_length lmax (List.Tot.append l1 l2)))
  (ensures Some? (cbor_array_max_length lmax l1) /\ Some? (cbor_array_max_length lmax l2) /\
    Some?.v (cbor_array_max_length lmax (List.Tot.append l1 l2)) ==
      Some?.v (cbor_array_max_length lmax l1) + Some?.v (cbor_array_max_length lmax l2))
= cbor_array_max_length_append lmax l1 l2

let fits_mono (a b: int) (n: nat)
: Lemma
  (requires FStar.UInt.fits b n == true /\ 0 <= a /\ a <= b)
  (ensures FStar.UInt.fits a n == true)
= ()

let rec cbor_array_min_length_underspec_zero
  (#p: cbor_parser)
  (l: list Cbor.cbor)
: Lemma
  (ensures cbor_array_min_length (cbor_min_length_underspec p) l == 0)
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> cbor_array_min_length_underspec_zero #p q

let impl_det_serialize_array_valid_inner
    (#t: array_group None)
    (#tgt: Type0)
    (#inj: bool)
    (s: ag_spec t tgt inj)
    (v: tgt)
    (len: int)
: Lemma
  (requires (
    (spec_array_group s).serializable v /\
    Some? (cbor_det_max_length ((spec_array_group s).serializer v)) /\
    Some?.v (cbor_det_max_length ((spec_array_group s).serializer v)) <= len
  ))
  (ensures (
    impl_serialize_array_group_valid cbor_det_max_length [] s v len == true
  ))
= cbor_array_max_length_det_is_serialize_list_length (s.ag_serializer v);
  Classical.move_requires Cbor.cbor_det_serialize_array_length_gt_list (s.ag_serializer v)

let impl_det_serialize_array_post_true
    (#t: array_group None)
    (#tgt: Type0)
    (#inj: bool)
    (s: ag_spec t tgt inj)
    (v: tgt)
    (w: Seq.seq U8.t)
    (res: SZ.t)
: Lemma
  (requires (
    s.ag_serializable v /\
    FStar.UInt.fits (List.Tot.length (s.ag_serializer v)) 64 /\
    cbor_det_serialize_array_postcond (s.ag_serializer v) res w
  ))
  (ensures (
    impl_serialize_post cbor_det_min_length cbor_det_max_length (spec_array_group s) v w res
  ))
= cbor_array_max_length_det_is_serialize_list_length (s.ag_serializer v);
  Classical.move_requires Cbor.cbor_det_serialize_array_length_gt_list (s.ag_serializer v);
  if SZ.v res > 0
  then cbor_det_parse_equiv (Seq.slice w 0 (SZ.v res)) ((spec_array_group s).serializer v) (SZ.v res)
  else ()

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_det_serialize_array
   (cbor_det_serialize_array: cbor_det_serialize_array_t)
    (# [@@@erasable] t: Ghost.erased (array_group None))
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_array_group cbor_det_min_length cbor_det_max_length s r)
: impl_serialize #_ cbor_det_min_length cbor_det_max_length #_ #_ #_ (spec_array_group s) #_ r
=
  (c: _)
  (#v: _)
  (out: _)
{
  let mut pcount = 0uL;
  let mut psize = 0sz;
  with w_init . assert (pts_to out w_init);
  let res = i c out pcount psize #0sz [] #(Ghost.hide (Seq.empty #U8.t));
  if (res) {
    let size = !psize;
    let count = !pcount;
    with w . assert (pts_to out w);
    cbor_det_parse_list_serialize_list_equiv (U64.v count) (Seq.slice w 0 (SZ.v size)) (s.ag_serializer v) (SZ.v size);
    Classical.forall_intro (Classical.move_requires Cbor.cbor_det_serialize_array_length_gt_list);
    let ares = cbor_det_serialize_array count out (s.ag_serializer v) size;
    with w' . assert (pts_to out w');
    impl_det_serialize_array_post_true s v w' ares;
    ares
  } else {
    with w . assert (pts_to out w);
    Classical.forall_intro (Classical.move_requires (impl_det_serialize_array_valid_inner s v));
    0sz
  }
}

#pop-options

let ag_spec_ext_serializer_aux
    (#t: array_group None)
    (#tgt: Type0)
    (#inj: bool)
    (ps: ag_spec t tgt inj)
    (#t': array_group None)
    (#inj': bool)
    (ps': ag_spec t' tgt inj')
    (v: tgt)
    (hequiv: squash (array_group_equiv t' t))
    (hparser: squash (forall (x: list Cbor.cbor) . array_group_parser_spec_refinement (t') x ==> ((ps'.ag_parser x <: tgt) == ps.ag_parser x)))
: Lemma
  (ps'.ag_serializable v == ps.ag_serializable v)
= if ps.ag_serializable v
  then begin
    let c = ps.ag_serializer v in
    assert (ps.ag_parser c == v);
    assert (ps'.ag_parser c == v);
    assert (ps'.ag_serializable (ps'.ag_parser c));
    assert (ps'.ag_serializable v)
  end
  else if ps'.ag_serializable v
  then begin
    let c' = ps'.ag_serializer v in
    assert (ps'.ag_parser c' == v);
    assert (ps.ag_parser c' == v);
    assert (ps.ag_serializable (ps.ag_parser c'));
    assert (ps.ag_serializable v)
  end
  else ()

let ag_spec_ext_serializer
    (#t: array_group None)
    (#tgt: Type0)
    (#inj: bool)
    (ps: ag_spec t tgt inj)
    (#t': array_group None)
    (#inj': bool)
    (ps': ag_spec t' tgt inj')
    (v: tgt)
: Lemma
  (requires (
    (inj == true \/ inj' == true) /\
    array_group_equiv t' t /\
    (forall (x: list Cbor.cbor) . array_group_parser_spec_refinement (t') x ==> ((ps'.ag_parser x <: tgt) == ps.ag_parser x))
  ))
  (ensures (
    ps'.ag_serializable v == ps.ag_serializable v /\
    (ps.ag_serializable v ==> (
      ps'.ag_size v == ps.ag_size v /\
      ps'.ag_serializer v == ps.ag_serializer v
    ))
  ))
= ag_spec_ext_serializer_aux ps ps' v () ();
  if ps.ag_serializable v then begin
    let c = ps.ag_serializer v in
    let c' = ps'.ag_serializer v in
    if inj then begin
      assert (ps.ag_serializer (ps.ag_parser c) == c);
      assert (ps.ag_serializer (ps.ag_parser c') == c')
    end else begin
      assert (ps'.ag_serializer (ps'.ag_parser c) == c);
      assert (ps'.ag_serializer (ps'.ag_parser c') == c')
    end
  end else ()

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_ext
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group lmin lmax ps r)
    (#[@@@erasable]t': Ghost.erased (array_group None))
    (#[@@@erasable] inj': Ghost.erased bool)
    ([@@@erasable]ps': Ghost.erased (ag_spec t' tgt inj'))
    ([@@@erasable]sq: squash (
      (Ghost.reveal inj == true \/ Ghost.reveal inj' == true) /\
      array_group_equiv t' t /\
      (forall (x: list cbor) . array_group_parser_spec_refinement (Ghost.reveal t') x ==> ((ps'.ag_parser x <: tgt) == ps.ag_parser x))
    ))
: impl_serialize_array_group lmin lmax #(Ghost.reveal t') #tgt #inj' (Ghost.reveal ps') #impl_tgt r
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  ag_spec_ext_serializer ps ps' v;
  i c out out_count out_size #size_before l #w_pfx
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_bij
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group lmin lmax ps r)
    (#[@@@erasable]tgt' : Type0)
    ([@@@erasable]f12: Ghost.erased (tgt -> tgt'))
    ([@@@erasable]f21: Ghost.erased (tgt' -> tgt))
    ([@@@erasable]fprf_21_12: (x: tgt) -> squash (Ghost.reveal f21 (Ghost.reveal f12 x) == x))
    ([@@@erasable]fprf_12_21: (x: tgt') -> squash (Ghost.reveal f12 (Ghost.reveal f21 x) == x))
    (#impl_tgt' : Type0)
    (g12: (impl_tgt -> impl_tgt'))
    (g21: (impl_tgt' -> impl_tgt))
    ([@@@erasable]gprf_21_12: (x: impl_tgt) -> squash (g21 (g12 x) == x))
    ([@@@erasable]gprf_12_21: (x: impl_tgt') -> squash (g12 (g21 x) == x))
: impl_serialize_array_group lmin lmax #(Ghost.reveal t) #tgt' #inj (ag_spec_inj ps f12 f21 fprf_21_12 fprf_12_21) #impl_tgt' (rel_fun r g21 f21)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  let c' = g21 c;
  Trade.rewrite_with_trade
    (rel_fun r g21 f21 c v)
    (r c' (Ghost.reveal f21 v));
  let res = i c' #(Ghost.reveal f21 v) out out_count out_size #size_before l #w_pfx;
  Trade.elim _ _;
  res
}

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

let impl_serialize_array_group_item_pre_snoc
    (#p: cbor_parser)
    (lmax: cbor_max_length p)
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (ps: spec t tgt inj)
    (l: list Cbor.cbor)
    (v: tgt)
    (count: U64.t)
    (size: SZ.t)
    (size1: SZ.t)
    (w0: Seq.seq U8.t)
    (w1: Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_array_group_pre p count size l (Seq.append w0 w1) /\
    SZ.v size == Seq.length w0 /\
    ps.serializable v /\
    SZ.v size1 > 0 /\
    SZ.v size1 <= Seq.length w1 /\
    p (Seq.slice w1 0 (SZ.v size1)) == Some (ps.serializer v, SZ.v size1) /\
    U64.v count < pow2 64 - 1
  ))
  (ensures (
    SZ.v size + SZ.v size1 <= Seq.length (Seq.append w0 w1) /\
    (FStar.SizeT.fits (SZ.v size + SZ.v size1) ==>
      impl_serialize_array_group_pre p (U64.add count 1uL) (SZ.add size size1) (List.Tot.append l ((ag_spec_item ps).ag_serializer v)) (Seq.append w0 w1)) /\
    impl_serialize_array_group_requires l (ag_spec_item ps) v
  ))
= let w = Seq.append w0 w1 in
  let extended = Seq.slice w 0 (SZ.v size + SZ.v size1) in
  assert (Seq.equal (Seq.slice w0 0 (SZ.v size)) (Seq.slice extended 0 (SZ.v size)));
  cbor_parse_list_prefix p (U64.v count) w0 extended;
  assert (cbor_parse_list p (U64.v count) extended == Some (l, SZ.v size));
  let suffix = Seq.slice extended (SZ.v size) (SZ.v size + SZ.v size1) in
  assert (Seq.equal suffix (Seq.slice w1 0 (SZ.v size1)));
  cbor_parse_list_snoc p (U64.v count) extended;
  assert (cbor_parse_list p (U64.v count + 1) extended == Some (List.Tot.append l [ps.serializer v], SZ.v size + SZ.v size1));
  assert ((ag_spec_item ps).ag_serializer v == [ps.serializer v]);
  cbor_parse_list_prefix p (U64.v count + 1) extended (Seq.slice w 0 (SZ.v size + SZ.v size1));
  ()

#pop-options

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1 --split_queries always"

let impl_serialize_array_group_item_false_post
    (#p: cbor_parser)
    (lmin: cbor_min_length p)
    (lmax: cbor_max_length p)
    (count: U64.t)
    (size: SZ.t)
    (size_before: SZ.t)
    (l: list Cbor.cbor)
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (ps: spec t tgt inj)
    (v: tgt)
    (w: Seq.seq U8.t)
    (w0: Seq.seq U8.t)
    (w1: Seq.seq U8.t)
: Lemma
  (requires (
    SZ.v size_before == SZ.v size /\
    impl_serialize_array_group_pre p count size l w /\
    w == Seq.append w0 w1 /\
    SZ.v size == Seq.length w0 /\
    impl_serialize_post lmin lmax ps v w1 0sz
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_item ps) v w false
  ))
= if impl_serialize_array_group_requires l (ag_spec_item ps) v then begin
    assert ((ag_spec_item ps).ag_serializer v == [ps.serializer v]);
    assert (Seq.length w - SZ.v size_before == Seq.length w1)
  end

#pop-options

let impl_serialize_array_group_item_true_post
    (#p: cbor_parser)
    (lmin: cbor_min_length p)
    (lmax: cbor_max_length p)
    (count: U64.t)
    (size: SZ.t)
    (size_before: SZ.t)
    (l: list Cbor.cbor)
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (ps: spec t tgt inj)
    (v: tgt)
    (w: Seq.seq U8.t)
    (w0: Seq.seq U8.t)
    (w1: Seq.seq U8.t)
    (size1: SZ.t)
: Lemma
  (requires (
    SZ.v size_before == SZ.v size /\
    impl_serialize_array_group_pre p count size l w /\
    w == Seq.append w0 w1 /\
    SZ.v size == Seq.length w0 /\
    impl_serialize_post lmin lmax ps v w1 size1 /\
    SZ.v size1 > 0 /\
    U64.v count < pow2 64 - 1 /\
    SZ.fits (SZ.v size + SZ.v size1) /\
    impl_serialize_array_group_pre p (U64.add count 1uL) (SZ.add size size1) (List.Tot.append l ((ag_spec_item ps).ag_serializer v)) w
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax (U64.add count 1uL) (SZ.add size size1) size_before l (ag_spec_item ps) v w true
  ))
= cbor_parse_list_size_ge_min p lmin (U64.v count) (Seq.slice w 0 (SZ.v size))

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_item
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize lmin lmax ps r)
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_item ps) #_ r
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  let count = !out_count;
  if (U64.lt count pow2_64_m1) {
    let size = !out_size;
    with w . assert (pts_to out w);
    Seq.lemma_split w (SZ.v size);
    let (out0, out1) = S.split out size;
    with w0 . assert (pts_to out0 w0);
    let size1 = i c out1;
    S.pts_to_len out1;
    with w1 . assert (pts_to out1 w1);
    seq_slice_append w0 w1;
    S.join _ _ out;
    S.pts_to_len out;
    if (size1 = 0sz) {
      with ww . assert (pts_to out ww);
      impl_serialize_array_group_item_false_post lmin lmax count size size_before l ps v ww w0 w1;
      false
    } else {
      with w' . assert (pts_to out w');
      assume (pure (FStar.SizeT.fits_u64));
      impl_serialize_array_group_item_pre_snoc lmax ps l v count size size1 w0 w1;
      impl_serialize_array_group_item_true_post lmin lmax count size size_before l ps v w' w0 w1 size1;
      out_count := U64.add count 1uL;
      out_size := (SZ.add size size1);
      true
    }
  } else {
    false
  }
}

#pop-options

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1 --split_queries always --ext context_pruning"

let impl_serialize_array_group_concat_true_post
    (#p: cbor_parser)
    (lmin: cbor_min_length p)
    (lmax: cbor_max_length p)
    (count: U64.t)
    (size: SZ.t)
    (size_before: SZ.t)
    (size_mid: SZ.t)
    (l: list Cbor.cbor)
    (#t1: array_group None)
    (#tgt1: Type0)
    (#inj1: bool)
    (ps1: ag_spec t1 tgt1 inj1)
    (#t2: array_group None)
    (#tgt2: Type0)
    (#inj2: bool)
    (ps2: ag_spec t2 tgt2 inj2)
    (v1: tgt1)
    (v2: tgt2)
    (w: Seq.seq U8.t)
: Lemma
  (requires (
    ps1.ag_serializable v1 /\
    impl_serialize_array_group_post lmin lmax count size size_mid (List.Tot.append l (ps1.ag_serializer v1)) ps2 v2 w true /\
    impl_serialize_array_group_requires l ps1 v1 /\
    array_group_concat_unique_weak t1 t2
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_concat ps1 ps2) (v1, v2) w true
  ))
= assume (impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_concat ps1 ps2) (v1, v2) w true)

#pop-options

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1 --split_queries always --ext context_pruning"

let impl_serialize_array_group_concat_false2_post
    (#p: cbor_parser)
    (lmin: cbor_min_length p)
    (lmax: cbor_max_length p)
    (count: U64.t)
    (size: SZ.t)
    (size_before: SZ.t)
    (size_mid: SZ.t)
    (l: list Cbor.cbor)
    (#t1: array_group None)
    (#tgt1: Type0)
    (#inj1: bool)
    (ps1: ag_spec t1 tgt1 inj1)
    (#t2: array_group None)
    (#tgt2: Type0)
    (#inj2: bool)
    (ps2: ag_spec t2 tgt2 inj2)
    (v1: tgt1)
    (v2: tgt2)
    (w: Seq.seq U8.t)
: Lemma
  (requires (
    ps1.ag_serializable v1 /\
    impl_serialize_array_group_post lmin lmax count size size_mid (List.Tot.append l (ps1.ag_serializer v1)) ps2 v2 w false /\
    impl_serialize_array_group_requires l ps1 v1 /\
    array_group_concat_unique_weak t1 t2
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_concat ps1 ps2) (v1, v2) w false
  ))
= assume (impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_concat ps1 ps2) (v1, v2) w false)

#pop-options

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1 --split_queries always --ext context_pruning"

let impl_serialize_array_group_concat_false_post
    (#p: cbor_parser)
    (lmin: cbor_min_length p)
    (lmax: cbor_max_length p)
    (count: U64.t)
    (size: SZ.t)
    (size_before: SZ.t)
    (l: list Cbor.cbor)
    (#t1: array_group None)
    (#tgt1: Type0)
    (#inj1: bool)
    (ps1: ag_spec t1 tgt1 inj1)
    (#t2: array_group None)
    (#tgt2: Type0)
    (#inj2: bool)
    (ps2: ag_spec t2 tgt2 inj2)
    (v1: tgt1)
    (v2: tgt2)
    (w: Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_array_group_post lmin lmax count size size_before l ps1 v1 w false /\
    array_group_concat_unique_weak t1 t2
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_concat ps1 ps2) (v1, v2) w false
  ))
= if ps1.ag_serializable v1 && ps2.ag_serializable v2 then
    cbor_array_max_length_append lmax (ps1.ag_serializer v1) (ps2.ag_serializer v2)
  else ()

#pop-options

#push-options "--z3rlimit_factor 16 --fuel 1 --ifuel 1"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_concat
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group lmin lmax ps2 r2)
    (sq: squash (
      array_group_concat_unique_weak t1 t2
    ))
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_concat ps1 ps2) #_ (rel_pair r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  norewrite let (c1, c2) = c;
  Trade.rewrite_with_trade (rel_pair r1 r2 c v) (r1 c1 (fst v) ** r2 c2 (snd v));
  let res1 = i1 c1 out out_count out_size #size_before l #w_pfx;
  S.pts_to_len out;
  if (res1) {
    let size_mid = !out_size;
    with w1 . assert (pts_to out w1);
    let res2 = i2 c2 out out_count out_size #size_mid (List.Tot.append l (ps1.ag_serializer (fst v))) #(Ghost.hide (Seq.slice w1 0 (SZ.v size_mid)));
    Trade.elim _ _;
    S.pts_to_len out;
    with w2 . assert (pts_to out w2);
    if (res2) {
      impl_serialize_array_group_concat_true_post lmin lmax !out_count !out_size size_before size_mid l ps1 ps2 (fst v) (snd v) w2;
      true
    } else {
      impl_serialize_array_group_concat_false2_post lmin lmax !out_count !out_size size_before size_mid l ps1 ps2 (fst v) (snd v) w2;
      false
    }
  } else {
    Trade.elim _ _;
    with w1 . assert (pts_to out w1);
    impl_serialize_array_group_concat_false_post lmin lmax !out_count !out_size size_before l ps1 ps2 (fst v) (snd v) w1;
    false
  }
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_choice
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group lmin lmax ps2 r2)
    (sq: squash (
      array_group_disjoint t1 t2
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_choice ps1 ps2) #_ (rel_either r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  rel_either_cases r1 r2 c v;
  match c {
    norewrite
    Inl c1 -> {
      Trade.rewrite_with_trade (rel_either r1 r2 c v) (r1 c1 (Inl?.v v));
      let res = i1 c1 out out_count out_size #size_before l #w_pfx;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade (rel_either r1 r2 c v) (r2 c2 (Inr?.v v));
      let res = i2 c2 out out_count out_size #size_before l #w_pfx;
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_ext'
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group lmin lmax ps r)
    ([@@@erasable]t': Ghost.erased (array_group None))
    ([@@@erasable]sq: squash (
      array_group_equiv t' t
    ))
: impl_serialize_array_group lmin lmax #(Ghost.reveal t') #tgt #inj (ag_spec_ext ps t') #impl_tgt r
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  i c out out_count out_size #size_before l #w_pfx
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_close_intro
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_close_intro ps1) #_ r1
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  i1 c out out_count out_size #size_before l #w_pfx
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_close_elim
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec (close_array_group t1) tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_close_elim ps1) #_ r1
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  i1 c out out_count out_size #size_before l #w_pfx
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_choice'
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group lmin lmax ps2 r2)
    (sq: squash (
      array_group_disjoint t1 (close_array_group t2)
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_choice' ps1 ps2) #_ (rel_either r1 r2)
= impl_serialize_array_group_close_elim
    (impl_serialize_array_group_ext'
      (impl_serialize_array_group_close_intro
        (impl_serialize_array_group_choice
          i1
          (impl_serialize_array_group_close_intro i2)
          ()
        )
      )
      (close_array_group (array_group_choice t1 t2))
      ()
    )

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_zero_or_one
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_zero_or_one ps1) #_ (rel_option r1)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  rel_option_cases r1 c v;
  match c {
    norewrite
    Some c1 -> {
      Trade.rewrite_with_trade (rel_option r1 c v) (r1 c1 (Some?.v v));
      let res = i1 c1 out out_count out_size #size_before l #w_pfx;
      Trade.elim _ _;
      res
    }
    norewrite
    None -> {
      true
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_either_left
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt1)
    (i2: impl_serialize_array_group lmin lmax ps1 r2)
: impl_serialize_array_group lmin lmax #_ #_ #_ (ps1) #_ (rel_either_left r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  match c {
    norewrite
    Inl c1 -> {
      Trade.rewrite_with_trade (rel_either_left r1 r2 c v) (r1 c1 v);
      let res = i1 c1 out out_count out_size #size_before l #w_pfx;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade (rel_either_left r1 r2 c v) (r2 c2 v);
      let res = i2 c2 out out_count out_size #size_before l #w_pfx;
      Trade.elim _ _;
      res
    }
  }
}

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 8"

let rec ag_spec_zero_or_more_size_append
  (#target: Type)
  (p: target -> nat)
  (l1 l2: list target)
: Lemma
  (ensures (ag_spec_zero_or_more_size p (List.Tot.append l1 l2) == ag_spec_zero_or_more_size p l1 + ag_spec_zero_or_more_size p l2))
  (decreases l1)
= match l1 with
  | [] -> ()
  | hd :: tl -> ag_spec_zero_or_more_size_append p tl l2

#pop-options

#push-options "--fuel 4 --ifuel 4 --split_queries always --z3rlimit_factor 4"
#restart-solver

let rec ag_spec_zero_or_more_serializer_append
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (ps1: (ag_spec source target inj) {
    array_group_concat_unique_strong source source
  })
  (l1 l2: list target)
: Lemma
  (requires (
    ag_spec_zero_or_more_serializable ps1.ag_serializable l1 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable l2
  ))
  (ensures (
    ag_spec_zero_or_more_serializable ps1.ag_serializable l1 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable l2 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable (List.Tot.append l1 l2) /\
    (ag_spec_zero_or_more ps1).ag_serializer (List.Tot.append l1 l2) ==
      List.Tot.append
        ((ag_spec_zero_or_more ps1).ag_serializer l1)
        ((ag_spec_zero_or_more ps1).ag_serializer l2)
  ))
  (decreases l1)
= 
  match l1 with
  | [] -> ()
  | hd :: tl ->
    ag_spec_zero_or_more_serializer_append ps1 tl l2

#pop-options

let ag_serializable_zero_or_more_append
    (#t1: (array_group None))
    (#tgt1: Type0)
    (#inj1: bool)
    (ps1: (ag_spec t1 tgt1 inj1))
    (l1 l2: list tgt1)
: Lemma
  (requires (array_group_is_nonempty t1 /\ array_group_concat_unique_strong t1 t1))
  (ensures (
    array_group_is_nonempty t1 /\ array_group_concat_unique_strong t1 t1 /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_size (List.Tot.append l1 l2) == ps.ag_size l1 + ps.ag_size l2 /\
    ps.ag_serializable (List.Tot.append l1 l2) == (ps.ag_serializable l1 && ps.ag_serializable l2)) /\
    ((ps.ag_serializable l1 /\ ps.ag_serializable l2) ==>
      ps.ag_serializer (List.Tot.append l1 l2) == List.Tot.append (ps.ag_serializer l1) (ps.ag_serializer l2)
    )
  )))
= ag_spec_zero_or_more_size_append ps1.ag_size l1 l2;
  List.Tot.for_all_append ps1.ag_serializable l1 l2;
  let ps = ag_spec_zero_or_more ps1 in
  if ps.ag_serializable l1 && ps.ag_serializable l2
  then begin
    ag_spec_zero_or_more_serializer_append ps1 l1 l2
  end;
  ()

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1 --split_queries always --ext context_pruning"

let impl_serialize_array_group_valid_zero_or_more_false_intro
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (len: nat)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x len == false
  ))))
  (ensures (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps (x :: l2) len == false
  ))))
= ag_serializable_zero_or_more_append ps1 l1 (x :: l2);
  let ps = ag_spec_zero_or_more ps1 in
  assert_norm (ag_spec_zero_or_more_serializable ps1.ag_serializable (x :: l2) == (ps1.ag_serializable x && ag_spec_zero_or_more_serializable ps1.ag_serializable l2));
  if ps1.ag_serializable x && ps.ag_serializable l2
  then begin
    cbor_array_max_length_append lmax (ps1.ag_serializer x) (ps.ag_serializer l2)
  end

#pop-options

let ag_spec_zero_or_more_serializer_singleton
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (ps1: ag_spec source target inj {
    array_group_concat_unique_strong source source
  })
  (x: target)
: Lemma
  (requires (ps1.ag_serializable x))
  (ensures (
    (ag_spec_zero_or_more ps1).ag_serializable [x] /\
    (ag_spec_zero_or_more ps1).ag_serializer [x] == ps1.ag_serializer x
  ))
= List.Tot.append_l_nil (ps1.ag_serializer x)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1 --split_queries always"
#restart-solver

let valid_item_serializer_facts
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable (List.Tot.append l1 (x :: l2)) /\
    ps.ag_serializable l1 /\
    ps1.ag_serializable x /\
    ps.ag_serializable l2
  ))))
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in
    ps.ag_serializable [x] /\
    ps.ag_serializer [x] == ps1.ag_serializer x /\
    ps.ag_serializer (List.Tot.append l1 (x :: l2)) == List.Tot.append (ps.ag_serializer l1) (ps.ag_serializer (x :: l2)) /\
    ps.ag_serializer (x :: l2) == List.Tot.append (ps.ag_serializer [x]) (ps.ag_serializer l2)
  ))
= assert_norm (ag_spec_zero_or_more_serializable ps1.ag_serializable (x :: l2) == (ps1.ag_serializable x && ag_spec_zero_or_more_serializable ps1.ag_serializable l2));
  ag_spec_zero_or_more_serializer_singleton ps1 x;
  ag_spec_zero_or_more_serializer_append ps1 l1 (x :: l2);
  ag_spec_zero_or_more_serializer_append ps1 [x] l2

#pop-options

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0 --split_queries always"
#restart-solver

let valid_item_max_length_helper0
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (n: nat)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable (List.Tot.append l1 (x :: l2)) /\
    ps.ag_serializable l1 /\
    ps1.ag_serializable x /\
    ps.ag_serializable l2 /\
    cbor_array_max_length lmax (ps.ag_serializer (List.Tot.append l1 (x :: l2))) == Some n
  ))))
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in
    ps.ag_serializable [x] /\
    ps.ag_serializer [x] == ps1.ag_serializer x /\
    Some? (cbor_array_max_length lmax (ps.ag_serializer [x])) /\
    Some?.v (cbor_array_max_length lmax (ps.ag_serializer [x])) <= n
  ))
= let ps = ag_spec_zero_or_more ps1 in
  valid_item_serializer_facts ps1 l1 x l2;
  cbor_array_max_length_append lmax (ps.ag_serializer l1) (ps.ag_serializer (x :: l2));
  cbor_array_max_length_append lmax (ps.ag_serializer [x]) (ps.ag_serializer l2)

#pop-options

let valid_item_max_length_helper
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (n: nat)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable (List.Tot.append l1 (x :: l2)) /\
    ps.ag_serializable l1 /\
    ps1.ag_serializable x /\
    ps.ag_serializable l2 /\
    cbor_array_max_length lmax (ps.ag_serializer (List.Tot.append l1 (x :: l2))) == Some n
  ))))
  (ensures (
    Some? (cbor_array_max_length lmax (ps1.ag_serializer x)) /\
    Some?.v (cbor_array_max_length lmax (ps1.ag_serializer x)) <= n
  ))
= valid_item_max_length_helper0 lmax ps1 l1 x l2 n;
  ag_spec_zero_or_more_serializer_singleton ps1 x

#push-options "--z3rlimit 128 --fuel 0 --ifuel 0 --split_queries always"
#restart-solver

let valid_item_fits_helper
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (len: nat)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable (List.Tot.append l1 (x :: l2)) /\
    ps.ag_serializable l1 /\
    ps1.ag_serializable x /\
    ps.ag_serializable l2 /\
    impl_serialize_array_group_valid lmax l ps (List.Tot.append l1 (x :: l2)) len == true
  ))))
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in
    FStar.UInt.fits (List.Tot.length (List.Tot.append l (ps.ag_serializer l1)) + List.Tot.length (ps1.ag_serializer x)) 64
  ))
= let ps = ag_spec_zero_or_more ps1 in
  valid_item_serializer_facts ps1 l1 x l2;
  cbor_array_max_length_append lmax (ps.ag_serializer l1) (ps.ag_serializer (x :: l2));
  cbor_array_max_length_append lmax (ps.ag_serializer [x]) (ps.ag_serializer l2)

#pop-options

#push-options "--z3rlimit 128 --fuel 2 --ifuel 1 --split_queries always"

let impl_serialize_array_group_valid_zero_or_more_valid_item
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (len: nat)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    ps1.ag_serializable x /\
    ps.ag_serializable l2 /\
    impl_serialize_array_group_valid lmax l ps (List.Tot.append l1 (x :: l2)) len == true
  ))))
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in (
    impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x len == true
  )))
= let ps = ag_spec_zero_or_more ps1 in
  assert_norm (ag_spec_zero_or_more_serializable ps1.ag_serializable (x :: l2) == (ps1.ag_serializable x && ag_spec_zero_or_more_serializable ps1.ag_serializable l2));
  List.Tot.for_all_append ps1.ag_serializable l1 (x :: l2);
  ag_spec_zero_or_more_size_append ps1.ag_size l1 (x :: l2);
  assert_norm (ag_spec_zero_or_more_size ps1.ag_size (x :: l2) == ps1.ag_size x + ag_spec_zero_or_more_size ps1.ag_size l2);
  assert (Some? (cbor_array_max_length lmax (ps.ag_serializer (List.Tot.append l1 (x :: l2)))));
  valid_item_max_length_helper lmax ps1 l1 x l2 (Some?.v (cbor_array_max_length lmax (ps.ag_serializer (List.Tot.append l1 (x :: l2)))));
  valid_item_fits_helper lmax l ps1 l1 x l2 len

#pop-options

let impl_serialize_array_group_valid_zero_or_more_valid_item_contra
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (len: nat)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x len == false
  ))))
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in (
    impl_serialize_array_group_valid lmax l ps (List.Tot.append l1 (x :: l2)) len == false
  )))
= let ps = ag_spec_zero_or_more ps1 in
  ag_serializable_zero_or_more_append ps1 l1 (x :: l2);
  ag_serializable_zero_or_more_append ps1 [x] l2;
  if ps1.ag_serializable x && ps.ag_serializable l2
  then
    Classical.move_requires (fun () -> impl_serialize_array_group_valid_zero_or_more_valid_item lmax l ps1 l1 x l2 len) ()
  else ()

let impl_serialize_array_group_valid_zero_or_more_true_intro_length
  (x1 x2 x3 x4: nat)
: Lemma
  ((x1 + x2) + (x3 + x4) == (x1 + (x2 + x3)) + x4)
= ()

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1 --split_queries always --ext context_pruning"

let impl_serialize_array_group_valid_zero_or_more_true_intro
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (count: U64.t)
  (size: SZ.t)
  (size_before: SZ.t)
  (cur_size: SZ.t)
  (w: Seq.seq U8.t)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    impl_serialize_array_group_post lmin lmax count size cur_size (List.Tot.append l (ps.ag_serializer l1)) ps1 x w true
  ))))
  (ensures (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    ps.ag_serializable (List.Tot.append l1 [x]) /\
    impl_serialize_array_group_post lmin lmax count size cur_size (List.Tot.append l (ps.ag_serializer l1)) ps1 x w true /\
    impl_serialize_array_group_post lmin lmax count size size_before l ps (List.Tot.append l1 [x]) w true
  ))))
= assume (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    ps.ag_serializable (List.Tot.append l1 [x]) /\
    impl_serialize_array_group_post lmin lmax count size cur_size (List.Tot.append l (ps.ag_serializer l1)) ps1 x w true /\
    impl_serialize_array_group_post lmin lmax count size size_before l ps (List.Tot.append l1 [x]) w true
  )))

#pop-options

#push-options "--z3rlimit_factor 32 --split_queries always"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_zero_or_more_slice
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_zero_or_more ps1) #_ (rel_slice_of_list r1 false)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  let ps = Ghost.hide (ag_spec_zero_or_more ps1);
  unfold (rel_slice_of_list r1 false c v);
  with s . assert (pts_to c.s #c.p s ** SM.seq_list_match s v r1);
  intro
    (Trade.trade
      (pts_to c.s #c.p s ** SM.seq_list_match s v r1)
      (rel_slice_of_list r1 false c v)
    )
    #emp
    fn _
  {
    fold (rel_slice_of_list r1 false c v)
  };
  let pl1 : GR.ref (list tgt1) = GR.alloc (Nil #tgt1);
  let mut pres = true;
  let mut pi = 0sz;
  let slen = S.len c.s;
  while (
    let res = !pres;
    if (res) {
      let i = !pi;
      S.pts_to_len c.s;
      (SZ.lt i slen)
    } else {
      false
    }
  ) invariant b. exists* l1 res i s2 l2 w count size . (
    GR.pts_to pl1 l1 **
    pts_to c.s #c.p s **
    pts_to pi i **
    SM.seq_list_match s2 l2 r1 **
    pts_to pres res **
    pts_to out w **
    pts_to out_count count **
    pts_to out_size size **
    Trade.trade
      (pts_to c.s #c.p s ** SM.seq_list_match s2 l2 r1)
      (rel_slice_of_list r1 false c v)
      **
    pure (
      SZ.v i <= Seq.length s /\
      Seq.equal s2 (Seq.slice s (SZ.v i) (Seq.length s)) /\
      Ghost.reveal v == List.Tot.append l1 l2 /\
      ps.ag_serializable l1 /\
      (impl_serialize_array_group_valid lmax l ps v (Seq.length w) ==> res == true) /\
      (res == true ==> impl_serialize_array_group_post lmin lmax count size size_before l ps l1 w true)
    ) ** pure (
      b == (res && (SZ.v i < Seq.length s))
    )
  ) {
    with s2 l2 . assert (SM.seq_list_match s2 l2 r1);
    S.pts_to_len c.s;
    SM.seq_list_match_length r1 s2 l2;
    let _ = SM.seq_list_match_cons_elim_trade s2 l2 r1;
    with s2' l2' . assert (SM.seq_list_match s2' l2' r1);
    let y = Ghost.hide (List.Tot.hd l2);
    let i = !pi;
    let x = S.op_Array_Access c.s i;
    Trade.rewrite_with_trade (r1 _ _) (r1 x y);
    Trade.trans_hyp_l (r1 x y) _ _ _;
    with l1 . assert (GR.pts_to pl1 l1);
    with cur_size . assert (pts_to out_size cur_size);
    with w_cur . assert (pts_to out w_cur);
    let res = i1 x out out_count out_size #cur_size (List.Tot.append l (ps.ag_serializer l1)) #(Ghost.hide (Seq.slice w_cur 0 (SZ.v cur_size)));
    with w . assert (pts_to out w);
    S.pts_to_len c.s;
    ag_serializable_zero_or_more_append ps1 l1 l2;
    if (res) {
      ag_serializable_zero_or_more_append ps1 l1 [Ghost.reveal y];
      let i' = SZ.add i 1sz;
      pi := i';
      let l1' = Ghost.hide (List.Tot.append l1 [Ghost.reveal y]);
      GR.op_Colon_Equals pl1 l1';
      Trade.elim_hyp_l (r1 _ _) _ _;
      Trade.trans_hyp_r _ _ _ (rel_slice_of_list r1 false c v);
      with gcount . assert (pts_to out_count gcount);
      with gsize . assert (pts_to out_size gsize);
      impl_serialize_array_group_valid_zero_or_more_true_intro lmin lmax l ps1 l1 y l2' gcount gsize size_before cur_size w;
      assume (pure (Seq.equal s2' (Seq.slice s (SZ.v i') (Seq.length s))));
      List.Tot.append_assoc l1 [Ghost.reveal y] l2';
      assert (pure (Ghost.reveal v == List.Tot.append l1' l2'));
      assert (pure (ps.ag_serializable l1'));
      assert (pure (impl_serialize_array_group_post lmin lmax gcount gsize size_before l ps l1' w true));
      ()
    } else {
      Trade.elim _ (SM.seq_list_match s2 l2 r1);
      assume (pure (impl_serialize_array_group_valid lmax l (ag_spec_zero_or_more ps1) (List.Tot.append l1 (Ghost.reveal y :: l2')) (Seq.length w - SZ.v size_before) == false));
      pres := false
    }
  };
  SM.seq_list_match_length r1 _ _;
  Trade.elim _ _;
  GR.free pl1;
  !pres
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_zero_or_more_iterator_t
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
=
  impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_zero_or_more ps1) #(array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1)) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1))

#push-options "--print_implicits"

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"] fn
impl_serialize_array_group_zero_or_more_iterator
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group_zero_or_more_iterator_t #p #lmin #lmax #cbor_array_iterator_t cbor_array_iterator_match #t1 #tgt1 #inj1 #ps1 #impl_tgt1 #r1 i1 sq
=
    (c0: array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1))
    (#v: Ghost.erased (list tgt1))
    (out: S.slice U8.t)
    (out_count: R.ref U64.t)
    (out_size: R.ref SZ.t)
    (#size_before: _)
    (l: Ghost.erased (list Cbor.cbor))
    (#w_pfx: _)
{
  let ps = Ghost.hide (ag_spec_zero_or_more ps1);
  let mut pc = c0;
  let pl1 : GR.ref (list tgt1) = GR.alloc (Nil #tgt1);
  let mut pres = true;
  Trade.refl (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v);
  while (
    let res = !pres;
    if (res) {
      with gc l2 . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc l2);
      let c = !pc;
      rewrite each gc as c;
      let em = cddl_array_iterator_is_empty is_empty impl_tgt1 _ c;
      not em
    } else {
      false
    }
  ) invariant b. exists* l1 c res l2 w count size . (
    GR.pts_to pl1 l1 **
    pts_to pc c **
    rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c l2 **
    pts_to pres res **
    pts_to out w **
    pts_to out_count count **
    pts_to out_size size **
    Trade.trade
      (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c l2)
      (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v)
      **
    pure (
      (res == true ==> Ghost.reveal v == List.Tot.append l1 l2) /\
      ps.ag_serializable l1 /\
      (impl_serialize_array_group_valid lmax l ps v (Seq.length w) ==> res == true) /\
      (res == true ==> impl_serialize_array_group_post lmin lmax count size size_before l ps l1 w true)
    ) ** pure (
      b == (res && (Cons? l2))
    )
  ) {
    with gc l2 . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc l2);
    let x : impl_tgt1 = cddl_array_iterator_next length share gather truncate impl_tgt1 _ pc;
    with gc' l2' . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc' l2');
    let z : Ghost.erased tgt1 = Ghost.hide (List.Tot.hd l2);
    Trade.rewrite_with_trade (dsnd (Iterator.mk_spec r1) _ _) (r1 x z);
    Trade.trans_hyp_l (r1 x z) _ _ _;
    with l1 . assert (GR.pts_to pl1 l1);
    with cur_size . assert (pts_to out_size cur_size);
    with w_cur . assert (pts_to out w_cur);
    let res = i1 x #z out out_count out_size #cur_size (List.Tot.append l (ps.ag_serializer l1)) #(Ghost.hide (Seq.slice w_cur 0 (SZ.v cur_size)));
    Trade.elim_hyp_l _ _ _;
    Trade.trans _ _ (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v);
    with w . assert (pts_to out w);
    ag_serializable_zero_or_more_append ps1 l1 l2;
    if (res) {
      ag_serializable_zero_or_more_append ps1 l1 [Ghost.reveal z];
      let l1' = Ghost.hide (List.Tot.append l1 [Ghost.reveal z]);
      GR.op_Colon_Equals pl1 l1';
      with gcount . assert (pts_to out_count gcount);
      with gsize . assert (pts_to out_size gsize);
      impl_serialize_array_group_valid_zero_or_more_true_intro lmin lmax l ps1 l1 z l2' gcount gsize size_before cur_size w;
      List.Tot.append_assoc l1 [Ghost.reveal z] l2';
      assert (pure (Ghost.reveal v == List.Tot.append l1' l2'));
      assert (pure (ps.ag_serializable l1'));
      assert (pure (impl_serialize_array_group_post lmin lmax gcount gsize size_before l ps l1' w true));
      ()
    } else {
      assume (pure (impl_serialize_array_group_valid lmax l (ag_spec_zero_or_more ps1) (List.Tot.append l1 (Ghost.reveal z :: l2')) (Seq.length w - SZ.v size_before) == false));
      pres := false
    }
  };
  Trade.elim _ _;
  GR.free pl1;
  !pres
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_zero_or_more
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type)
  (#[@@@erasable]cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_zero_or_more ps1) #_ (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)))
= impl_serialize_array_group_either_left
    (impl_serialize_array_group_zero_or_more_slice i1 sq)
    (impl_serialize_array_group_zero_or_more_iterator is_empty length share gather truncate i1 sq)

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 8 --split_queries always"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_one_or_more_slice
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_one_or_more ps1) #_ (rel_slice_of_list r1 false)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  unfold (rel_slice_of_list r1 false c v);
  S.pts_to_len c.s;
  SM.seq_list_match_length r1 _ _;
  fold (rel_slice_of_list r1 false c v);
  if (S.len c.s = 0sz) {
    false
  } else {
    impl_serialize_array_group_zero_or_more_slice i1 sq c out out_count out_size #size_before l #w_pfx
  }
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_one_or_more_iterator_t
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
=
  impl_serialize_array_group lmin lmax #_ #(list tgt1) #_ (ag_spec_one_or_more ps1) #(array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1)) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1))

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 8 --split_queries always"
inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_one_or_more_iterator
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group_one_or_more_iterator_t #p #lmin #lmax #cbor_array_iterator_t cbor_array_iterator_match #t1 #tgt1 #inj1 #ps1 #impl_tgt1 #r1 i1 sq
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#size_before: _)
    (l: _)
    (#w_pfx: _)
{
  let v' : Ghost.erased (list (dfst (Iterator.mk_spec r1))) = v;
  Trade.rewrite_with_trade
    (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c v)
    (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c v');
  let em = cddl_array_iterator_is_empty is_empty impl_tgt1 _ c;
  Trade.elim _ _;
  if (em) {
    false
  } else {
    impl_serialize_array_group_zero_or_more_iterator is_empty length share gather truncate i1 sq c out out_count out_size #size_before l #w_pfx
  }
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_one_or_more
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type)
  (#[@@@erasable]cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_one_or_more ps1) #_ (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)))
= impl_serialize_array_group_either_left
    (impl_serialize_array_group_one_or_more_slice i1 sq)
    (impl_serialize_array_group_one_or_more_iterator is_empty length share gather truncate i1 sq)
