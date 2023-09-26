module LowParse.Pulse.Parse
include LowParse.SteelST.Parse.Base
module AP = LowParse.Pulse.ArrayPtr
open Pulse.Lib.Core

let aparse
  (#k: parser_kind)
  (#t: Type0) // FIXME: Pulse is not universe-polymorphic
  (p: parser k t)
  (a: AP.t byte)
  (vp: v k t)
: Tot vprop
= exists_ (fun va ->
    AP.arrayptr a va ** pure (arrayptr_parse p va == Some vp)
  )

```pulse
ghost
fn intro_aparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: AP.t byte)
  (#va: AP.v byte)
  requires AP.arrayptr a va ** pure (
    Some? (arrayptr_parse p va)
  )
  ensures exists vp . aparse p a vp ** pure (
    AP.array_of va == array_of vp /\
    arrayptr_parse p va == Some vp
  )
{
  fold (aparse p a (Some?.v (arrayptr_parse p va)))
}
```

```pulse
ghost
fn elim_aparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: AP.t byte)
  (#vp: v k t)
  requires aparse p a vp
  ensures exists va . AP.arrayptr a va ** pure (
    AP.array_of va == array_of vp /\
    arrayptr_parse p va == Some vp
  )
{
  unfold (aparse p a vp)
}
```

```pulse
ghost
fn elim_aparse_with_serializer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (a: AP.t byte)
  (#vp: v k t)
  requires aparse p a vp
  ensures exists va . AP.arrayptr a va ** pure (
    AP.array_of va == array_of vp /\
    arrayptr_parse p va == Some vp /\
    serialize s vp.contents == AP.contents_of va
  )
{
  elim_aparse p a;
  with va . assert (AP.arrayptr a va);
  let x = parse_injective p (AP.contents_of va) (serialize s vp.contents);
  ();
}
```

```pulse
ghost
fn rewrite_aparse
  (a: AP.t byte)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#y1: v k1 t1)
  requires aparse p1 a y1 ** pure (
    t1 == t2 /\ (forall bytes . parse p1 bytes == parse p2 bytes)
  )
  ensures exists y2 . aparse p2 a y2 ** pure (
    t1 == t2 /\
    array_of' y1 == array_of' y2 /\
    y1.contents == y2.contents
  )
{
  elim_aparse p1 a;
  intro_aparse p2 a
}
```

module Seq = FStar.Seq

let seq_slice_len
  (#t: Type)
  (s: Seq.seq t)
: Lemma
  (Seq.slice s 0 (Seq.length s) == s)
= assert (Seq.slice s 0 (Seq.length s) `Seq.equal` s)

```pulse
ghost
fn aparse_split_zero_r
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: AP.t byte)
  (#va: v k t)
  requires aparse p a va
  returns a' : Ghost.erased (AP.t byte)
  ensures exists vl vr .
    aparse p a vl **
    AP.arrayptr a' vr **
    pure (
      AP.length (AP.array_of vr) == 0 /\
      va.contents == vl.contents /\
      AP.merge_into (array_of vl) (AP.array_of vr) (array_of va)
    )
{
  elim_aparse p a;
  with vl' . assert (AP.arrayptr a vl');
  let _lemma_call_1 = seq_slice_len (AP.contents_of vl');
  let a' = AP.gsplit a (AP.len (array_of va));
  intro_aparse p a;
  a'
}
```

```pulse
ghost
fn aparse_split_zero_l
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: AP.t byte)
  (#va: v k t)
  requires aparse p a va
  returns a' : Ghost.erased (AP.t byte)
  ensures exists vl vr .
    aparse p a' vr **
    AP.arrayptr a vl **
    pure (
      AP.length (AP.array_of vl) == 0 /\
      va.contents == vr.contents /\
      AP.merge_into (AP.array_of vl) (array_of vr) (array_of va)
    )
{
  elim_aparse p a;
  with vl' . assert (AP.arrayptr a vl');
  let _lemma_call_1 = seq_slice_len (AP.contents_of vl');
  let a' = AP.gsplit a 0sz;
  intro_aparse p a';
  a'
}
```

let seq_append_empty_r
  (#t: Type)
  (vl vr: FStar.Seq.seq t)
: Lemma
  (requires FStar.Seq.length vr == 0)
  (ensures FStar.Seq.append vl vr == vl)
= assert (FStar.Seq.equal (FStar.Seq.append vl vr) vl)

```pulse
ghost
fn aparse_join_zero_r
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (al ar: AP.t byte)
  (#vl: v k t)
  (#vr: AP.v byte)
  requires
    aparse p al vl ** AP.arrayptr ar vr ** pure (
      AP.adjacent (array_of vl) (AP.array_of vr) /\
      AP.length (AP.array_of vr) == 0
    )
  ensures exists va' . aparse p al va' ** pure (
      AP.merge_into (array_of vl) (AP.array_of vr) (array_of va') /\
      va'.contents == vl.contents
    )
{
  elim_aparse p al;
  with vl' . assert (AP.arrayptr al vl');
  let _lemma_call_1 = seq_append_empty_r (AP.contents_of' vl') (AP.contents_of' vr);
  LowParse.Pulse.ArrayPtr.join al ar;
  intro_aparse p al
}
```

let seq_append_empty_l
  (#t: Type)
  (vl vr: FStar.Seq.seq t)
: Lemma
  (requires FStar.Seq.length vl == 0)
  (ensures FStar.Seq.append vl vr == vr)
= assert (FStar.Seq.equal (FStar.Seq.append vl vr) vr)

```pulse
ghost
fn aparse_join_zero_l
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (al ar: AP.t byte)
  (#vl: AP.v byte)
  (#vr: v k t)
  requires
    aparse p ar vr ** AP.arrayptr al vl ** pure (
      AP.adjacent (AP.array_of vl) (array_of vr) /\
      AP.length (AP.array_of vl) == 0
    )
  ensures exists va' . aparse p al va' ** pure (
      AP.merge_into (AP.array_of vl) (array_of vr) (array_of va') /\
      va'.contents == vr.contents
    )
{
  elim_aparse p ar;
  with vr' . assert (AP.arrayptr ar vr');
  let _lemma_call_1 = seq_append_empty_l (AP.contents_of' vl) (AP.contents_of' vr');
  LowParse.Pulse.ArrayPtr.join al ar;
  intro_aparse p al
}
```
