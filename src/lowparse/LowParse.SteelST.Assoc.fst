module LowParse.SteelST.Assoc
include LowParse.SteelST.VCList.Sorted
include LowParse.SteelST.Combinators
include LowParse.Spec.Assoc
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference

[@@__reduce__]
let nlist_assoc_post_failure
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
: Tot vprop
= rkey `star`
  aparse (parse_nlist n0 (pkey `nondep_then` pvalue)) a0 va0 `star`
  (exists_ (R.pts_to pa full_perm)) `star`
  pure (list_ghost_assoc key va0.contents == None)

[@@__reduce__]
let nlist_assoc_post_success_body
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (a: byte_array)
: Tot vprop
= rkey `star`
  exists_ (fun va ->
    R.pts_to pa full_perm a `star`
    aparse pvalue a va `star`
    (aparse pvalue a va `implies_` aparse (parse_nlist n0 (pkey `nondep_then` pvalue)) a0 va0) `star`
    pure (list_ghost_assoc key va0.contents == Some va.contents)
  )

[@@__reduce__]
let nlist_assoc_post_success
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
: Tot vprop
= exists_ (fun a -> nlist_assoc_post_success_body pkey pvalue key rkey n0 va0 a0 pa a)

let nlist_assoc_post
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (res: bool)
: Tot vprop
= if res
  then nlist_assoc_post_success pkey pvalue key rkey n0 va0 a0 pa
  else nlist_assoc_post_failure pkey pvalue key rkey n0 va0 a0 pa

inline_for_extraction
let elim_nlist_assoc_post_success
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: Ghost.erased parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: Ghost.erased tkey)
  (rkey: vprop)
  (n0: Ghost.erased nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (res: bool)
: ST byte_array
    (nlist_assoc_post pkey pvalue key rkey n0 va0 a0 pa res)
    (fun a -> nlist_assoc_post_success_body pkey pvalue key rkey n0 va0 a0 pa a)
    (res == true)
    (fun _ -> True)
= rewrite
    (nlist_assoc_post pkey pvalue key rkey n0 va0 a0 pa res)
    (nlist_assoc_post_success pkey pvalue key rkey n0 va0 a0 pa);
  let _ = gen_elim () in
  let a = read_replace pa in
  vpattern_rewrite (fun (a: byte_array) -> aparse pvalue a _ `star` (aparse pvalue a _ `implies_` _)) a;
  return a

let elim_nlist_assoc_post_failure
  (#opened: _)
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (res: bool)
: STGhost unit opened
    (nlist_assoc_post pkey pvalue key rkey n0 va0 a0 pa res)
    (fun _ ->
      rkey `star`
      aparse (parse_nlist n0 (pkey `nondep_then` pvalue)) a0 va0 `star`
      (exists_ (R.pts_to pa full_perm))
    )
    (res == false)
    (fun _ -> list_ghost_assoc key va0.contents == None)
= rewrite
    (nlist_assoc_post pkey pvalue key rkey n0 va0 a0 pa res)
    (nlist_assoc_post_failure pkey pvalue key rkey n0 va0 a0 pa);
  let _ = gen_elim () in
  noop ()

let nlist_assoc_invariant_aux_continue_prop
  (#kkey: parser_kind)
  (#tkey: Type)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (key: tkey)
  (order: option (tkey -> tkey -> bool))
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (n: nat)
  (va: v (parse_nlist_kind n (and_then_kind kkey kvalue)) (nlist n (tkey & tvalue)))
: GTot prop
= list_ghost_assoc key va0.contents == list_ghost_assoc key va.contents /\
  begin match order with
  | None -> True
  | Some order -> List.Tot.sorted (map_entry_order order tvalue) va.contents
  end

[@@__reduce__]
let nlist_assoc_invariant_aux_continue
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (order: option (tkey -> tkey -> bool))
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (n: nat)
: Tot vprop
= rkey `star`
  exists_ (fun a -> exists_ (fun va ->
    R.pts_to pa full_perm a `star`
    aparse (parse_nlist n (pkey `nondep_then` pvalue)) a va `star`
    nlist_iterator (pkey `nondep_then` pvalue) n0 va0 a0 n va `star`
    pure (nlist_assoc_invariant_aux_continue_prop key order n0 va0 n va)
  ))

[@@CMacro]
let nlist_assoc_in_progress : byte = 0uy

[@@CMacro]
let nlist_assoc_success : byte = 1uy

[@@CMacro]
let nlist_assoc_failure : byte = 2uy

let nlist_assoc_invariant_aux
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (order: option (tkey -> tkey -> bool))
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (n: nat)
  (res: byte)
: Tot vprop
= if res = nlist_assoc_in_progress
  then nlist_assoc_invariant_aux_continue pkey pvalue key rkey order n0 va0 a0 pa n
  else nlist_assoc_post pkey pvalue key rkey n0 va0 a0 pa (res = nlist_assoc_success)

[@@__reduce__]
let nlist_assoc_invariant0
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (order: option (tkey -> tkey -> bool))
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pres: R.ref byte)
  (cont: bool)
: Tot vprop
= exists_ (fun n -> exists_ (fun res ->
    R.pts_to pn full_perm n `star`
    R.pts_to pres full_perm res `star`
    nlist_assoc_invariant_aux pkey pvalue key rkey order n0 va0 a0 pa (SZ.v n) res `star`
    pure (cont == (n <> 0sz && res = nlist_assoc_in_progress))
  ))

let nlist_assoc_invariant
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (order: option (tkey -> tkey -> bool))
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pres: R.ref byte)
  (cont: bool)
= nlist_assoc_invariant0 pkey pvalue key rkey order n0 va0 a0 pa pn pres cont

let intro_nlist_assoc_invariant
  (#opened: _)
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (order: option (tkey -> tkey -> bool))
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pres: R.ref byte)
  (cont: bool)
  (n: _)
  (res: _)
: STGhost unit opened
  (
    R.pts_to pn full_perm n `star`
    R.pts_to pres full_perm res `star`
    nlist_assoc_invariant_aux pkey pvalue key rkey order n0 va0 a0 pa (SZ.v n) res
  )
  (fun _ -> nlist_assoc_invariant pkey pvalue key rkey order n0 va0 a0 pa pn pres cont)
  (cont == (n <> 0sz && res = nlist_assoc_in_progress))
  (fun _ -> True)
= noop ();
  rewrite
    (nlist_assoc_invariant0 pkey pvalue key rkey order n0 va0 a0 pa pn pres cont)
    (nlist_assoc_invariant pkey pvalue key rkey order n0 va0 a0 pa pn pres cont)

inline_for_extraction
let nlist_assoc_invariant_test
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: Ghost.erased parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: Ghost.erased tkey)
  (rkey: vprop)
  (order: Ghost.erased (option (tkey -> tkey -> bool)))
  (n0: Ghost.erased nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pres: R.ref byte)
  ()
: STT bool
    (exists_ (nlist_assoc_invariant pkey pvalue key rkey order n0 va0 a0 pa pn pres))
    (fun cont -> nlist_assoc_invariant pkey pvalue key rkey order n0 va0 a0 pa pn pres cont)
= let gcont = elim_exists () in
  rewrite
    (nlist_assoc_invariant pkey pvalue key rkey order n0 va0 a0 pa pn pres gcont)
    (nlist_assoc_invariant0 pkey pvalue key rkey order n0 va0 a0 pa pn pres gcont);
  let _ = gen_elim () in
  let n = R.read pn in
  let res = R.read pres in
  [@@inline_let]
  let cont = (n <> 0sz && res = nlist_assoc_in_progress) in
  noop ();
  rewrite
    (nlist_assoc_invariant0 pkey pvalue key rkey order n0 va0 a0 pa pn pres cont)
    (nlist_assoc_invariant pkey pvalue key rkey order n0 va0 a0 pa pn pres cont);
  return cont

inline_for_extraction
let nlist_assoc_eq_keys
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (key: Ghost.erased tkey)
  (rkey: vprop)
: Tot Type
= (#va: v kkey tkey) ->
  (a: byte_array) ->
  (sz: SZ.t) ->
  ST bool
    (rkey `star` aparse pkey a va)
    (fun _ -> rkey `star` aparse pkey a va)
    (SZ.v sz == AP.length (array_of va))
    (fun res -> res == true <==> va.contents == Ghost.reveal key)
    
#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
inline_for_extraction
let nlist_assoc_invariant_step
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (#pkey: parser kkey tkey)
  (jump_key: jumper pkey)
  (#kvalue: Ghost.erased parser_kind)
  (#tvalue: Type)
  (#pvalue: parser kvalue tvalue)
  (jump_value: jumper pvalue)
  (#key: Ghost.erased tkey)
  (#rkey: vprop)
  (compare_keys: nlist_assoc_eq_keys pkey key rkey)
  (n0: Ghost.erased nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pres: R.ref byte)
  (_: unit)
: STT unit
    (nlist_assoc_invariant pkey pvalue key rkey None n0 va0 a0 pa pn pres true)
    (fun _ -> exists_ (nlist_assoc_invariant pkey pvalue key rkey None n0 va0 a0 pa pn pres))
= rewrite
    (nlist_assoc_invariant pkey pvalue key rkey None n0 va0 a0 pa pn pres true)
    (nlist_assoc_invariant0 pkey pvalue key rkey None n0 va0 a0 pa pn pres true);
  let _ = gen_elim () in
  let n = read_replace pn in
  let n_pred = n `SZ.sub` 1sz in
  rewrite
    (nlist_assoc_invariant_aux pkey pvalue key rkey None n0 va0 a0 pa _ _)
    (nlist_assoc_invariant_aux_continue pkey pvalue key rkey None n0 va0 a0 pa (SZ.v n));
  let _ = gen_elim () in
  let a = read_replace pa in
  vpattern_rewrite (fun a -> aparse _ a _) a;
  let va = vpattern_replace (fun va -> aparse _ a va `star` nlist_iterator (pkey `nondep_then` pvalue) (n0) va0 a0 (SZ.v n) va) in
  nlist_iterator_parser_kind _ _ _ _ _ _;
  let ga' = elim_nlist_cons _ (SZ.v n) (SZ.v n_pred) a in
  let _ = gen_elim () in
  let gav = g_split_pair pkey pvalue a in
  let _ = gen_elim () in
  let key_size = get_parsed_size jump_key a in
  let av = hop_aparse_aparse_with_size pkey pvalue a key_size gav in
  let res = compare_keys a key_size in
  if res
  then begin
    R.write pa av;
    R.write pres nlist_assoc_success;
    let vav = vpattern_replace (aparse pvalue av) in
    intro_implies
      (aparse pvalue av vav)
      (aparse (parse_nlist (n0) (pkey `nondep_then` pvalue)) a0 va0)
      (aparse pkey a _ `star` aparse _ ga' _ `star` nlist_iterator (pkey `nondep_then` pvalue) (n0) va0 a0 (SZ.v n) va)
      (fun _ ->
        let _ = merge_pair pkey pvalue a av in
        let _ = intro_nlist_cons (SZ.v n) (pkey `nondep_then` pvalue) (SZ.v n_pred) a ga' in
        vpattern_rewrite (aparse _ a) va;
        nlist_iterator_end _ _ _
      );
    rewrite
      (nlist_assoc_post_success pkey pvalue key rkey (n0) va0 a0 pa)
      (nlist_assoc_invariant_aux pkey pvalue key rkey None n0 va0 a0 pa (SZ.v n) nlist_assoc_success);
    rewrite
      (nlist_assoc_invariant0 pkey pvalue key rkey None n0 va0 a0 pa pn pres false)
      (nlist_assoc_invariant pkey pvalue key rkey None n0 va0 a0 pa pn pres false);
    return ()
  end else begin
    let a' = hop_aparse_aparse jump_value (parse_nlist (SZ.v n_pred) (pkey `nondep_then` pvalue)) av ga' in
    R.write pa a';
    R.write pn n_pred;
    let va' = vpattern_replace (aparse _ a') in
    let _ = merge_pair pkey pvalue a av in
    nlist_iterator_next (pkey `nondep_then` pvalue) #n0 #va0 a0 a #(SZ.v n_pred) va';
    noop ();
    rewrite
      (nlist_assoc_invariant_aux_continue pkey pvalue key rkey None n0 va0 a0 pa (SZ.v n_pred))
      (nlist_assoc_invariant_aux pkey pvalue key rkey None n0 va0 a0 pa (SZ.v n_pred) nlist_assoc_in_progress);
    intro_nlist_assoc_invariant pkey pvalue key rkey None n0 va0 a0 pa pn pres (n_pred <> 0sz) _ _;
    return ()
  end

#pop-options
    
#push-options "--z3rlimit 16"

#restart-solver
let nlist_assoc_invariant_end
  (#opened: _)
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
  (key: tkey)
  (rkey: vprop)
  (order: (option (tkey -> tkey -> bool)))
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pres: R.ref byte)
: STGhostT (Ghost.erased byte) opened
    (nlist_assoc_invariant pkey pvalue key rkey order n0 va0 a0 pa pn pres false)
    (fun res ->
      R.pts_to pres full_perm res `star`
      nlist_assoc_post pkey pvalue key rkey n0 va0 a0 pa (Ghost.reveal res = nlist_assoc_success) `star`
      exists_ (R.pts_to pn full_perm)
    )
= rewrite
    (nlist_assoc_invariant pkey pvalue key rkey order n0 va0 a0 pa pn pres false)
    (nlist_assoc_invariant0 pkey pvalue key rkey order n0 va0 a0 pa pn pres false);
  let _ = gen_elim () in
  let n = vpattern (R.pts_to pn _) in
  let res = vpattern_replace_erased (R.pts_to pres _) in
  if Ghost.reveal res = nlist_assoc_in_progress // this test is ghost, that's why we need this separate ghost function
  then begin
    rewrite
      (nlist_assoc_invariant_aux pkey pvalue key rkey order n0 va0 a0 pa _ _)
      (nlist_assoc_invariant_aux_continue pkey pvalue key rkey order n0 va0 a0 pa (SZ.v n));
    let _ = gen_elim () in
    nlist_iterator_end (pkey `nondep_then` pvalue) a0 _;
    noop ();
    rewrite
      (nlist_assoc_post_failure pkey pvalue key rkey n0 va0 a0 pa)
      (nlist_assoc_post pkey pvalue key rkey n0 va0 a0 pa (Ghost.reveal res = nlist_assoc_success));
    noop ();
    res
  end else begin
    rewrite
      (nlist_assoc_invariant_aux pkey pvalue key rkey order n0 va0 a0 pa _ _)
      (nlist_assoc_post pkey pvalue key rkey n0 va0 a0 pa (Ghost.reveal res = nlist_assoc_success));
    noop ();
    res
  end

#pop-options

inline_for_extraction
let nlist_assoc
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (#pkey: parser kkey tkey)
  (jump_key: jumper pkey)
  (#kvalue: Ghost.erased parser_kind)
  (#tvalue: Type)
  (#pvalue: parser kvalue tvalue)
  (jump_value: jumper pvalue)
  (#key: Ghost.erased tkey)
  (#rkey: vprop)
  (compare_keys: nlist_assoc_eq_keys pkey key rkey)
  (n0: SZ.t)
  (#va0: v (parse_nlist_kind (SZ.v n0) (and_then_kind kkey kvalue)) (nlist (SZ.v n0) (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
: ST bool
    (rkey `star`
      aparse (parse_nlist (SZ.v n0) (pkey `nondep_then` pvalue)) a0 va0 `star`
      (exists_ (R.pts_to pa full_perm))
    )
    (fun res ->
      nlist_assoc_post pkey pvalue key rkey (SZ.v n0) va0 a0 pa res
    )
    (kkey.parser_kind_subkind == Some ParserStrong /\
      kvalue.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
= let _ = gen_elim () in
  R.write pa a0;
  let _ = nlist_iterator_begin (pkey `nondep_then` pvalue) #(SZ.v n0) a0 in
  with_local n0 (fun pn ->
    with_local nlist_assoc_in_progress (fun pres ->
      noop ();
      rewrite
        (nlist_assoc_invariant_aux_continue pkey pvalue key rkey None (SZ.v n0) va0 a0 pa (SZ.v n0))
        (nlist_assoc_invariant_aux pkey pvalue key rkey None (SZ.v n0) va0 a0 pa (SZ.v n0) nlist_assoc_in_progress);
      rewrite
        (nlist_assoc_invariant0 pkey pvalue key rkey None (SZ.v n0) va0 a0 pa pn pres (n0 <> 0sz))
        (nlist_assoc_invariant pkey pvalue key rkey None (SZ.v n0) va0 a0 pa pn pres (n0 <> 0sz));
      Steel.ST.Loops.while_loop
        (nlist_assoc_invariant pkey pvalue key rkey None (SZ.v n0) va0 a0 pa pn pres)
        (nlist_assoc_invariant_test pkey pvalue key rkey None (SZ.v n0) va0 a0 pa pn pres)
        (nlist_assoc_invariant_step jump_key jump_value compare_keys (SZ.v n0) va0 a0 pa pn pres);
      let _ = nlist_assoc_invariant_end pkey pvalue key rkey None (SZ.v n0) va0 a0 pa pn pres in
      let _ = gen_elim () in
      let res = R.read pres in
      vpattern_rewrite (nlist_assoc_post pkey pvalue key rkey (SZ.v n0) va0 a0 pa) (res = nlist_assoc_success);
      noop ();
      return (res = nlist_assoc_success)
  ))

(* Default key comparison by directly comparing their byte arrays, since EverParse parsers are always injective *)

let eq_byte_arrays_equal_size_invariant_prop
  (n0: SZ.t)
  (va: AP.v byte)
  (vb: AP.v byte)
  (res: bool)
  (i: SZ.t)
  (cont: bool)
: GTot prop
= AP.len (AP.array_of va) == n0 /\
  AP.len (AP.array_of vb) == n0 /\
  SZ.v i <= SZ.v n0 /\
  Seq.slice (AP.contents_of va) 0 (SZ.v i) `Seq.equal` Seq.slice (AP.contents_of vb) 0 (SZ.v i) /\
  (res == false ==> (~ (AP.contents_of va == AP.contents_of vb))) /\
  (cont == (i `SZ.lt` n0 && res))

[@@__reduce__]
let eq_byte_arrays_equal_size_invariant0
  (n0: SZ.t)
  (va: AP.v byte)
  (vb: AP.v byte)
  (a b: byte_array)
  (pres: R.ref bool)
  (pi: R.ref SZ.t)
  (cont: bool)
: Tot vprop
= 
  exists_ (fun res -> exists_ (fun i ->
    AP.arrayptr a va `star` AP.arrayptr b vb `star`
    R.pts_to pi full_perm i `star`
    R.pts_to pres full_perm res `star`
    pure (eq_byte_arrays_equal_size_invariant_prop n0 va vb res i cont)
  ))

#push-options "--z3rlimit 32"

#restart-solver
let eq_byte_arrays_equal_size
  (n0: SZ.t)
  (#va: AP.v byte)
  (#vb: AP.v byte)
  (a b: byte_array)
: ST bool
    (AP.arrayptr a va `star` AP.arrayptr b vb)
    (fun res -> AP.arrayptr a va `star` AP.arrayptr b vb)
    (AP.len (AP.array_of va) == n0 /\
      AP.len (AP.array_of vb) == n0
    )
    (fun res -> 
      res == true <==> AP.contents_of va `Seq.equal` AP.contents_of vb
    )
= let res =
    with_local true (fun pres ->
    with_local 0sz (fun pi ->
      noop ();
      assert_ (eq_byte_arrays_equal_size_invariant0 n0 va vb a b pres pi (n0 <> 0sz));
      Steel.ST.Loops.while_loop
        (eq_byte_arrays_equal_size_invariant0 n0 va vb a b pres pi)
        (fun _ ->
          let _ = gen_elim () in
          let res = R.read pres in
          let i = R.read pi in
          [@@inline_let]
          let cont = (i `SZ.lt` n0 && res) in
          noop ();
          assert_ (eq_byte_arrays_equal_size_invariant0 n0 va vb a b pres pi cont);
          return cont
        )
        (fun _ ->
          let _ = gen_elim () in
          let i = R.read pi in
          let x = AP.index a i in
          let y = AP.index b i in
          if x = y
          then begin
            let i_succ = i `SZ.add` 1sz in 
            assert (Seq.slice (AP.contents_of va) 0 (SZ.v i_succ) `Seq.equal` Seq.snoc (Seq.slice (AP.contents_of va) 0 (SZ.v i)) x);
            assert (Seq.slice (AP.contents_of vb) 0 (SZ.v i_succ) `Seq.equal` Seq.snoc (Seq.slice (AP.contents_of vb) 0 (SZ.v i)) y);
            R.write pi i_succ;
            assert_ (eq_byte_arrays_equal_size_invariant0 n0 va vb a b pres pi (i_succ `SZ.lt` n0));
            noop ()
          end else begin
            R.write pres false;
            assert_ (eq_byte_arrays_equal_size_invariant0 n0 va vb a b pres pi false);
            noop ()
          end
        );
      let _ = gen_elim () in
      let res = R.read pres in
      noop (); // intro_pure (res == true <==> AP.contents_of va `Seq.equal` AP.contents_of vb);
      return res
    ))
  in
  elim_pure (res == true <==> AP.contents_of va `Seq.equal` AP.contents_of vb);
  return res

#pop-options

let eq_byte_arrays
  (#va: AP.v byte)
  (a: byte_array)
  (na: SZ.t)
  (#vb: AP.v byte)
  (b: byte_array)
  (nb: SZ.t)
: ST bool
    (AP.arrayptr a va `star` AP.arrayptr b vb)
    (fun res -> AP.arrayptr a va `star` AP.arrayptr b vb)
    (AP.len (AP.array_of va) == na /\
      AP.len (AP.array_of vb) == nb
    )
    (fun res ->
      res == true <==> AP.contents_of va `Seq.equal` AP.contents_of vb
    )
= if na = nb
  then eq_byte_arrays_equal_size na a b
  else return false

inline_for_extraction
let nlist_assoc_default_eq_keys
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (va: v kkey tkey)
  (a: byte_array)
  (sz: SZ.t)
: Pure (nlist_assoc_eq_keys pkey va.contents (aparse pkey a va))
    (requires AP.len (array_of' va) == sz)
    (fun _ -> True)
= fun #va' a' sz' ->
  parser_kind_prop_equiv kkey pkey;
  let vb = elim_aparse pkey a in
  let vb' = elim_aparse pkey a' in
  Classical.move_requires (parse_injective pkey (AP.contents_of vb)) (AP.contents_of vb');
  let res = eq_byte_arrays a sz a' sz' in
  let _ = intro_aparse pkey a in
  let _ = intro_aparse pkey a' in
  vpattern_rewrite (aparse _ a) va;
  vpattern_rewrite (aparse _ a') va';
  return res

(* If we know that the list of keys is sorted with a transitive order, then we can interrupt the search as soon as the key in the map is (strictly) greater than the key we are looking for. *)

module I16 = FStar.Int16

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
inline_for_extraction
let nlist_assoc_sorted_step
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (#pkey: parser kkey tkey)
  (jump_key: jumper pkey)
  (#kvalue: Ghost.erased parser_kind)
  (#tvalue: Type)
  (#pvalue: parser kvalue tvalue)
  (jump_value: jumper pvalue)
  (#key: Ghost.erased tkey)
  (#rkey: vprop)
  (key_order: Ghost.erased (tkey -> tkey -> bool))
  (key_order_irrefl: (
    (k1: tkey) ->
    (k2: tkey) ->
    Lemma
    (requires (Ghost.reveal key_order k1 k2))
    (ensures (~ (k1 == k2)))
  ))
  (key_order_trans: (
    (k1: tkey) ->
    (k2: tkey) ->
    (k3: tkey) ->
    Lemma
    (requires (Ghost.reveal key_order k1 k2 /\ Ghost.reveal key_order k2 k3))
    (ensures (Ghost.reveal key_order k1 k3))
  ))
  (#key_compare: Ghost.erased (tkey -> tkey -> int))
  (compare_keys: compare_impl_with pkey key_compare key rkey)
  (key_compare_lt: (
    (k1: tkey) ->
    (k2: tkey) ->
    Lemma
    (Ghost.reveal key_compare k1 k2 < 0 <==> Ghost.reveal key_order k1 k2 == true)
  ))
  (key_compare_eq: (
    (k1: tkey) ->
    (k2: tkey) ->
    Lemma
    (Ghost.reveal key_compare k1 k2 == 0 <==> k1 == k2)
  ))
  (n0: Ghost.erased nat)
  (va0: v (parse_nlist_kind n0 (and_then_kind kkey kvalue)) (nlist n0 (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pres: R.ref byte)
  (_: unit)
: STT unit
    (nlist_assoc_invariant pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres true)
    (fun _ -> exists_ (nlist_assoc_invariant pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres))
= rewrite
    (nlist_assoc_invariant pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres true)
    (nlist_assoc_invariant0 pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres true);
  let _ = gen_elim () in
  let n = read_replace pn in
  let n_pred = n `SZ.sub` 1sz in
  rewrite
    (nlist_assoc_invariant_aux pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa _ _)
    (nlist_assoc_invariant_aux_continue pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa (SZ.v n));
  let _ = gen_elim () in
  let a = read_replace pa in
  vpattern_rewrite (fun a -> aparse _ a _) a;
  let va = vpattern_replace (fun va -> aparse _ a va `star` nlist_iterator (pkey `nondep_then` pvalue) (n0) va0 a0 (SZ.v n) va) in
  nlist_iterator_parser_kind _ _ _ _ _ _;
  let ga' = elim_nlist_cons _ (SZ.v n) (SZ.v n_pred) a in
  let _ = gen_elim () in
  let gav = g_split_pair pkey pvalue a in
  let _ = gen_elim () in
  let key_size = get_parsed_size jump_key a in
  let av = hop_aparse_aparse_with_size pkey pvalue a key_size gav in
  let vak = vpattern (aparse pkey a) in
  key_compare_eq key vak.contents;
  let res = compare_keys a key_size in
  if res = 0s
  then begin
    R.write pa av;
    R.write pres nlist_assoc_success;
    let vav = vpattern_replace (aparse pvalue av) in
    intro_implies
      (aparse pvalue av vav)
      (aparse (parse_nlist (n0) (pkey `nondep_then` pvalue)) a0 va0)
      (aparse pkey a _ `star` aparse _ ga' _ `star` nlist_iterator (pkey `nondep_then` pvalue) (n0) va0 a0 (SZ.v n) va)
      (fun _ ->
        let _ = merge_pair pkey pvalue a av in
        let _ = intro_nlist_cons (SZ.v n) (pkey `nondep_then` pvalue) (SZ.v n_pred) a ga' in
        vpattern_rewrite (aparse _ a) va;
        nlist_iterator_end _ _ _
      );
    rewrite
      (nlist_assoc_post_success pkey pvalue key rkey (n0) va0 a0 pa)
      (nlist_assoc_invariant_aux pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa (SZ.v n) nlist_assoc_success);
    rewrite
      (nlist_assoc_invariant0 pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres false)
      (nlist_assoc_invariant pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres false);
    return ()
  end else if res `I16.lt` 0s
  then begin
    key_compare_lt key vak.contents;
    let vav = vpattern (aparse pvalue av) in
    let va' : v _ (nlist (SZ.v n_pred) _) = vpattern_replace (aparse (parse_nlist (SZ.v n_pred) (pkey `nondep_then` pvalue)) ga') in
    map_entry_order_assoc_order_none key_order key_order_irrefl key_order_trans vak.contents vav.contents va'.contents (Ghost.reveal key);
    R.write pres nlist_assoc_failure;
    let _ = merge_pair pkey pvalue a av in
    let _ = intro_nlist_cons (SZ.v n) (pkey `nondep_then` pvalue) (SZ.v n_pred) a ga' in
    vpattern_rewrite (aparse _ a) va;
    nlist_iterator_end _ _ _;
    rewrite
      (nlist_assoc_post_failure pkey pvalue key rkey (n0) va0 a0 pa)
      (nlist_assoc_invariant_aux pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa (SZ.v n) nlist_assoc_failure);
    rewrite
      (nlist_assoc_invariant0 pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres false)
      (nlist_assoc_invariant pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres false);
    return ()
  end else begin
    let a' = hop_aparse_aparse jump_value (parse_nlist (SZ.v n_pred) (pkey `nondep_then` pvalue)) av ga' in
    R.write pa a';
    R.write pn n_pred;
    let va' = vpattern_replace (aparse _ a') in
    let _ = merge_pair pkey pvalue a av in
    nlist_iterator_next (pkey `nondep_then` pvalue) #n0 #va0 a0 a #(SZ.v n_pred) va';
    noop ();
    rewrite
      (nlist_assoc_invariant_aux_continue pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa (SZ.v n_pred))
      (nlist_assoc_invariant_aux pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa (SZ.v n_pred) nlist_assoc_in_progress);
    intro_nlist_assoc_invariant pkey pvalue key rkey (Some (Ghost.reveal key_order)) n0 va0 a0 pa pn pres (n_pred <> 0sz) _ _;
    return ()
  end

#pop-options

inline_for_extraction
let nlist_assoc_sorted
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (#pkey: parser kkey tkey)
  (jump_key: jumper pkey)
  (#kvalue: Ghost.erased parser_kind)
  (#tvalue: Type)
  (#pvalue: parser kvalue tvalue)
  (jump_value: jumper pvalue)
  (#key: Ghost.erased tkey)
  (#rkey: vprop)
  (key_order: Ghost.erased (tkey -> tkey -> bool))
  (key_order_irrefl: (
    (k1: tkey) ->
    (k2: tkey) ->
    Lemma
    (requires (Ghost.reveal key_order k1 k2))
    (ensures (~ (k1 == k2)))
  ))
  (key_order_trans: (
    (k1: tkey) ->
    (k2: tkey) ->
    (k3: tkey) ->
    Lemma
    (requires (Ghost.reveal key_order k1 k2 /\ Ghost.reveal key_order k2 k3))
    (ensures (Ghost.reveal key_order k1 k3))
  ))
  (#key_compare: Ghost.erased (tkey -> tkey -> int))
  (compare_keys: compare_impl_with pkey key_compare key rkey)
  (key_compare_lt: (
    (k1: tkey) ->
    (k2: tkey) ->
    Lemma
    (Ghost.reveal key_compare k1 k2 < 0 <==> Ghost.reveal key_order k1 k2 == true)
  ))
  (key_compare_eq: (
    (k1: tkey) ->
    (k2: tkey) ->
    Lemma
    (Ghost.reveal key_compare k1 k2 == 0 <==> k1 == k2)
  ))
  (n0: SZ.t)
  (#va0: v (parse_nlist_kind (SZ.v n0) (and_then_kind kkey kvalue)) (nlist (SZ.v n0) (tkey & tvalue)))
  (a0: byte_array)
  (pa: R.ref byte_array)
: ST bool
    (rkey `star`
      aparse (parse_nlist (SZ.v n0) (pkey `nondep_then` pvalue)) a0 va0 `star`
      (exists_ (R.pts_to pa full_perm))
    )
    (fun res ->
      nlist_assoc_post pkey pvalue key rkey (SZ.v n0) va0 a0 pa res
    )
    (kkey.parser_kind_subkind == Some ParserStrong /\
      kvalue.parser_kind_subkind == Some ParserStrong /\
      List.Tot.sorted (map_entry_order key_order tvalue) va0.contents
    )
    (fun _ -> True)
= let _ = gen_elim () in
  R.write pa a0;
  let _ = nlist_iterator_begin (pkey `nondep_then` pvalue) #(SZ.v n0) a0 in
  with_local n0 (fun pn ->
    with_local nlist_assoc_in_progress (fun pres ->
      noop ();
      rewrite
        (nlist_assoc_invariant_aux_continue pkey pvalue key rkey (Some (Ghost.reveal key_order)) (SZ.v n0) va0 a0 pa (SZ.v n0))
        (nlist_assoc_invariant_aux pkey pvalue key rkey (Some (Ghost.reveal key_order)) (SZ.v n0) va0 a0 pa (SZ.v n0) nlist_assoc_in_progress);
      rewrite
        (nlist_assoc_invariant0 pkey pvalue key rkey (Some (Ghost.reveal key_order)) (SZ.v n0) va0 a0 pa pn pres (n0 <> 0sz))
        (nlist_assoc_invariant pkey pvalue key rkey (Some (Ghost.reveal key_order)) (SZ.v n0) va0 a0 pa pn pres (n0 <> 0sz));
      Steel.ST.Loops.while_loop
        (nlist_assoc_invariant pkey pvalue key rkey (Some (Ghost.reveal key_order)) (SZ.v n0) va0 a0 pa pn pres)
        (nlist_assoc_invariant_test pkey pvalue key rkey (Some (Ghost.reveal key_order)) (SZ.v n0) va0 a0 pa pn pres)
        (nlist_assoc_sorted_step jump_key jump_value key_order key_order_irrefl key_order_trans compare_keys key_compare_lt key_compare_eq (SZ.v n0) va0 a0 pa pn pres);
      let _ = nlist_assoc_invariant_end pkey pvalue key rkey (Some (Ghost.reveal key_order)) (SZ.v n0) va0 a0 pa pn pres in
      let _ = gen_elim () in
      let res = R.read pres in
      vpattern_rewrite (nlist_assoc_post pkey pvalue key rkey (SZ.v n0) va0 a0 pa) (res = nlist_assoc_success);
      noop ();
      return (res = nlist_assoc_success)
  ))

(* This type is useful only to determine whether a map is sorted along
   its key. It is useless in the context of querying for a map entry
 *)

inline_for_extraction
let map_entry_order_impl
  (#kkey: Ghost.erased parser_kind)
  (#key: Type0)
  (pkey: parser kkey key)
  (#key_order: Ghost.erased (key -> key -> bool))
  (key_order_impl: order_impl pkey key_order)
  (#kvalue: Ghost.erased parser_kind)
  (#value: Type0)
  (pvalue: parser kvalue value)
: Pure (order_impl (pkey `nondep_then` pvalue) (map_entry_order key_order value))
    (requires (kkey.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #va1 #va2 a1 a2 ->
    let av1 = g_split_pair pkey pvalue a1 in
    let _ = gen_elim () in
    let av2 = g_split_pair pkey pvalue a2 in
    let _ = gen_elim () in
    let res = key_order_impl a1 a2 in
    let _ = merge_pair pkey pvalue a1 av1 in
    vpattern_rewrite (aparse _ a1) va1;
    let _ = merge_pair pkey pvalue a2 av2 in
    vpattern_rewrite (aparse _ a2) va2;
    return res
