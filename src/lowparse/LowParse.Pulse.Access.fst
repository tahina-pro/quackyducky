module LowParse.Pulse.Access
include LowParse.Pulse.Parse
module AP = LowParse.Pulse.ArrayPtr
module SZ = FStar.SizeT
open Pulse.Lib.Pervasives

let jumper_prop_pre
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va: AP.v byte)
: GTot prop
= Some? (parse p (AP.contents_of' va))

let jumper_prop_post
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va: AP.v byte)
  (res: SZ.t)
: GTot prop
=
      match parse p (AP.contents_of' va) with
      | None -> False
      | Some (_, consumed) ->
        SZ.v res == consumed

inline_for_extraction
let jumper
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (va: AP.v byte) ->
  (a: AP.t byte) ->
  stt SZ.t
    (AP.arrayptr a va ** pure (jumper_prop_pre p va))
    (fun res -> AP.arrayptr a va ** pure (jumper_prop_post p va res))

inline_for_extraction
let jump
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (a: AP.t byte)
  (#va: AP.v byte)
: stt SZ.t
    (AP.arrayptr a va ** pure (jumper_prop_pre p va))
    (fun res -> AP.arrayptr a va ** pure (jumper_prop_post p va res))
= j va a


inline_for_extraction
let ifthenelse_jump
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (cond: bool)
  (vtrue: (squash (cond == true) -> Tot (jumper p)))
  (vfalse: (squash (cond == false) -> Tot (jumper p)))
: Tot (jumper p)
= fun va a ->
  if cond
  then vtrue () va a
  else vfalse () va a

#set-options "--print_implicits"

inline_for_extraction
```pulse
fn hop_arrayptr_aparse
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t) // TODO: this should be implicit
  (a1: AP.t byte)
  (sz: SZ.t)
  (a2: Ghost.erased (AP.t byte))
  (#va1: AP.v byte)
  (#va2: v k t)
  requires
    AP.arrayptr a1 va1 ** aparse p a2 va2 ** pure (
        AP.adjacent (AP.array_of va1) (array_of va2) /\
        SZ.v sz == AP.length (AP.array_of va1)
    )
  returns res: AP.t byte
  ensures
    AP.arrayptr a1 va1 ** aparse p res va2 ** pure (
        res == Ghost.reveal a2
    )
{
    elim_aparse p a2;
    let res = AP.split' a1 sz a2;
    intro_aparse p res;
    res
}
```

inline_for_extraction
```pulse
fn hop_aparse_arrayptr_with_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (a1: AP.t byte)
  (sz: SZ.t)
  (a2: Ghost.erased (AP.t byte))
  (#va1: v k t)
  (#va2: AP.v byte)
  requires
    aparse p a1 va1 ** AP.arrayptr a2 va2 ** pure (
        AP.adjacent (array_of va1) (AP.array_of va2) /\
        SZ.v sz == AP.length (array_of va1)
    )
  returns res: AP.t byte
  ensures
    aparse p a1 va1 ** AP.arrayptr res va2 ** pure (
        res == Ghost.reveal a2
    )
{
    elim_aparse p a1;
    let res = AP.split' a1 sz a2;
    intro_aparse p a1;
    res
}
```

inline_for_extraction
```pulse
fn hop_aparse_aparse_with_size
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (a1: AP.t byte)
  (sz: SZ.t)
  (a2: Ghost.erased (AP.t byte))
  (#va1: v k1 t1)
  (#va2: v k2 t2)
  requires
    aparse p1 a1 va1 ** aparse p2 a2 va2 ** pure (
        AP.adjacent (array_of va1) (array_of va2) /\
        SZ.v sz == AP.length (array_of va1)
    )
  returns res: AP.t byte
  ensures
    aparse p1 a1 va1 ** aparse p2 res va2 ** pure (
        res == Ghost.reveal a2
    )
{
    elim_aparse p2 a2;
    let res = hop_aparse_arrayptr_with_size p1 a1 sz a2;
    intro_aparse p2 res;
    res
}
```

inline_for_extraction
```pulse
fn jump_constant_size0
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: (sz: SZ.t {
    SZ.v sz == k.parser_kind_low /\
    k.parser_kind_high == Some k.parser_kind_low
  }))
  (b: AP.v byte)
  (a: AP.t byte)
  requires AP.arrayptr a b ** pure (jumper_prop_pre p b)
  returns res: SZ.t
  ensures AP.arrayptr a b ** pure (jumper_prop_post p b res)
{
    let _lemma_call_1 = parser_kind_prop_equiv k p;
    sz;
}
```

inline_for_extraction
let jump_constant_size
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: (sz: SZ.t {
    SZ.v sz == k.parser_kind_low /\
    k.parser_kind_high == Some k.parser_kind_low
  }))
: Tot (jumper p)
= jump_constant_size0 p sz

inline_for_extraction
```pulse
fn get_parsed_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (a: AP.t byte)
  (#vp: v k t)
  requires aparse p a vp
  returns res: SZ.t
  ensures aparse p a vp ** pure (SZ.v res == AP.length (array_of vp))
{
    elim_aparse p a;
    let res = jump j a;
    intro_aparse p a;
    res
}
```

inline_for_extraction
```pulse
fn hop_aparse_arrayptr
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (a1: AP.t byte)
  (a2: Ghost.erased (AP.t byte))
  (#va1: v k t)
  (#va2: AP.v byte)
  requires
    aparse p a1 va1 ** AP.arrayptr a2 va2 ** pure (
        AP.adjacent (array_of va1) (AP.array_of va2)
    )
  returns res: AP.t byte
  ensures
    aparse p a1 va1 ** AP.arrayptr res va2 ** pure (
        res == Ghost.reveal a2
    )
{
    let sz = get_parsed_size j a1;
    hop_aparse_arrayptr_with_size p a1 sz a2
}
```

inline_for_extraction
```pulse
fn hop_aparse_aparse
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type)
  (p2: parser k2 t2) // FIXME: this should be implicit
  (a1: AP.t byte)
  (a2: Ghost.erased (AP.t byte))
  (#va1: v k1 t1)
  (#va2: v k2 t2)
  requires
    aparse p1 a1 va1 ** aparse p2 a2 va2 ** pure (
        AP.adjacent (array_of va1) (array_of va2)
    )
  returns res: AP.t byte
  ensures
    aparse p1 a1 va1 ** aparse p2 res va2 ** pure (
        res == Ghost.reveal a2
    )
{
    let sz = get_parsed_size j1 a1;
    hop_aparse_aparse_with_size p1 p2 a1 sz a2
}
```

let ghost_peek_strong_post
  (#k: parser_kind)
  (#t: Type)
  (va: AP.v byte)
  (p: parser k t)
  (vp: v k t)
  (vres: AP.v byte)
: GTot prop
=
      let consumed = AP.length (array_of vp) in
      k.parser_kind_subkind == Some ParserStrong /\
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse p (AP.contents_of' va) == Some (vp.contents, consumed) /\
      parse p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)

let parse'
  (#a: Type)
  (#k: parser_kind)
  (p: parser k a)
  (b: bytes)
: GTot (option (a & nat))
= match parse p b with
  | None -> None
  | Some (v, c) -> Some (v, c)

let parse'_strong_prefix
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input1: bytes)
  (input2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\ (
    match parse p input1 with
    | Some (x, consumed) ->
      consumed <= Seq.length input2 /\
      Seq.slice input1 0 consumed `Seq.equal` Seq.slice input2 0 consumed
    | _ -> False
  )))
  (ensures (
    match parse p input1 with
    | Some (x, consumed) ->
      consumed <= Seq.length input2 /\
      parse' p input2 == Some (x, consumed)
    | _ -> False
  ))
= parse_strong_prefix p input1 input2

```pulse
ghost
fn ghost_peek_strong
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: AP.t byte)
  (#va: AP.v byte)
  requires
    AP.arrayptr a va ** pure (
        k.parser_kind_subkind == Some ParserStrong /\
        Some? (parse p (AP.contents_of va))
    )
  returns res: Ghost.erased (AP.t byte)
  ensures exists vp vres .
    aparse p a vp ** AP.arrayptr res vres ** pure (
        ghost_peek_strong_post va p vp vres
    )
{
    let s = AP.contents_of va;
    let sz = SZ.uint_to_t (snd (Some?.v (parse p s)));
    let _l = parse'_strong_prefix p s (Seq.slice s 0 (SZ.v sz));
    let res = AP.gsplit a sz;
    intro_aparse p a;
    res
}
```

```pulse
fn peek_strong_with_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: AP.t byte)
  (sz: SZ.t)
  (#va: AP.v byte)
  requires
    AP.arrayptr a va ** pure (
        k.parser_kind_subkind == Some ParserStrong /\
        begin match parse p (AP.contents_of va) with
        | None -> False
        | Some (_, consumed) -> SZ.v sz == consumed
        end
    )
  returns res: AP.t byte
  ensures exists vp vres .
    aparse p a vp ** AP.arrayptr res vres ** pure (
        ghost_peek_strong_post va p vp vres
    )
{
    let gres = ghost_peek_strong p a;
    elim_aparse p a;
    let res = AP.split' a sz gres;
    intro_aparse p a;
    res
}
```

```pulse
fn peek_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (a: AP.t byte)
  (#va: AP.v byte)
  requires
    AP.arrayptr a va ** pure (
        k.parser_kind_subkind == Some ParserStrong /\
        Some? (parse p (AP.contents_of va))
    )
  returns res: AP.t byte
  ensures exists vp vres .
    aparse p a vp ** AP.arrayptr res vres ** pure (
        ghost_peek_strong_post va p vp vres
    )
{
    let sz = jump j a;
    peek_strong_with_size p a sz
}
```

let ghost_peek_strong_post_inj
  (#k: parser_kind)
  (#t: Type)
  (va1 va2: AP.v byte)
  (p: parser k t)
  (vp: v k t)
  (vres: AP.v byte)
: Lemma
  (requires (
    ghost_peek_strong_post va1 p vp vres /\
    ghost_peek_strong_post va2 p vp vres
  ))
  (ensures (
    va1 == va2
  ))
= parse_injective p (AP.contents_of va1) (AP.contents_of va2);
  FStar.Seq.lemma_split (AP.contents_of va1) (AP.length (AP.array_of va1) - AP.length (AP.array_of vres));
  FStar.Seq.lemma_split (AP.contents_of va2) (AP.length (AP.array_of va2) - AP.length (AP.array_of vres))

```pulse
ghost
fn unpeek_strong
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: AP.t byte)
  (res: AP.t byte)
  (#vp: v k t)
  (#vres: AP.v byte)
  requires
    aparse p a vp ** AP.arrayptr res vres ** pure (
        AP.adjacent (array_of vp) (AP.array_of vres) /\
        k.parser_kind_subkind == Some ParserStrong
    )
  ensures exists va .
    AP.arrayptr a va ** pure (
        ghost_peek_strong_post va p vp vres
    )
{
    elim_aparse p a;
    with vl . assert (AP.arrayptr a vl);
    AP.join a res;
    with va . assert (AP.arrayptr a va);
    let _1 = FStar.Seq.append_slices (AP.contents_of vl) (AP.contents_of vres);
    let _15 = seq_slice_len (AP.contents_of vl);
    let _2 = parse'_strong_prefix p (AP.contents_of vl) (AP.contents_of va);
    ()
}
```

```pulse
ghost
fn peek_consumes_all
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: AP.t byte)
  (#va: AP.v byte)
  requires
    AP.arrayptr a va ** pure (
      k.parser_kind_subkind == Some ParserConsumesAll /\
      Some? (parse p (AP.contents_of va))
    )
  ensures exists vp .
    aparse p a vp ** pure (
        array_of' vp == AP.array_of va /\
        parse p (AP.contents_of va) == Some (vp.contents, AP.length (AP.array_of va))
    )
{
    let _f = parser_kind_prop_equiv k p;
    intro_aparse p a
}
```
