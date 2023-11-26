module LowParse.Pulse.Array
module LA = LowParse.Pulse.ArrayPtr
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
open Pulse.Lib.Pervasives

// FIXME: expose array_ptr in Pulse.Lib.Array.Core
noeq
type t elt = {
    base: A.array elt;
    glen: (glen: Ghost.erased SZ.t {SZ.v glen == A.length base});
    offset: (offset: SZ.t {SZ.v offset <= A.length base});
}

[@@erasable]
noeq
type array elt = {
  array_base: t elt;
  array_len: (array_len: SZ.t {SZ.v array_base.offset + SZ.v array_len <= SZ.v array_base.glen});
  array_perm: perm;
}

let array_len x : GTot SZ.t = x.array_len

let array_length x : GTot nat = SZ.v (array_len x)

let array_perm x = x.array_perm

[@@erasable]
noeq
type v t = {
  v_array: array t;
  v_contents: Seq.lseq t (array_length v_array);
}

let array_of x = x.v_array
let contents_of
    #elt (x: v elt)
: GTot (Seq.lseq elt (SZ.v (array_len (array_of x))))
= x.v_contents

let array_contents_inj
    (#elt: Type0)
    (v1 v2: v elt)
: Lemma
    (requires (array_of v1 == array_of v2 /\
        contents_of v1 == contents_of v2
    ))
    (ensures v1 == v2)
= ()

let arrayptr1
    (#elt: Type0)
    (w: v elt)
: vprop
= A.pts_to_range w.v_array.array_base.base (SZ.v w.v_array.array_base.offset) (SZ.v w.v_array.array_base.offset + SZ.v w.v_array.array_len) #w.v_array.array_perm w.v_contents

let arrayptr
    (#elt: Type0)
    (x: t elt)
    (w: v elt)
: vprop
= arrayptr1 w **
    pure (w.v_array.array_base == x)

unfold
let adjacent x1 x2 : prop =
    x1.array_base.base == x2.array_base.base /\
    x1.array_perm == x2.array_perm /\
    SZ.v x1.array_base.offset + SZ.v x1.array_len == SZ.v x2.array_base.offset

let merge #elt x1 x2 : Ghost (array elt)
    (requires adjacent x1 x2)
    (ensures (fun y ->
        array_length y == array_length x1 + array_length x2 /\
        array_perm y == array_perm x1 /\
        array_perm y == array_perm x2
    ))
= {
    array_base = x1.array_base;
    array_len = x1.array_len `SZ.add` x2.array_len;
    array_perm = x1.array_perm;
}

let merge_assoc x1 x2 x3 : Lemma
        (requires (
            (adjacent x1 x2 /\ adjacent x2 x3) \/
            (adjacent x1 x2 /\ adjacent (merge x1 x2) x3) \/
            (adjacent x2 x3 /\ adjacent x1 (merge x2 x3))
        ))
        (ensures (
            adjacent x1 x2 /\ adjacent (merge x1 x2) x3 /\
            adjacent x2 x3 /\ adjacent x1 (merge x2 x3) /\
            merge (merge x1 x2) x3 == merge x1 (merge x2 x3)
        ))
= ()

inline_for_extraction
let instance0 : LA.array_ptr_step0 t array v = {
    len = array_len;
    array_perm = array_perm;
    array_of = array_of;
    contents_of = contents_of;
    array_contents_inj = array_contents_inj;
    arrayptr = arrayptr;
    adjacent = adjacent;
    merge = merge;
    merge_assoc = merge_assoc;
}

```pulse
ghost
fn manurewrite
    (p: vprop)
    (q: vprop)
requires (p **
    pure (p == q)
)
ensures q
{
    rewrite p as q
}
```

```pulse
fn join
    (_: unit)
: LA.join_t #t #array #v instance0
=
    (#elt: Type0)
    (al: t elt)
    (ar: t elt)
    (#vl: v elt)
    (#vr: v elt)
{
    let res : Ghost.erased (v elt) = Ghost.hide (Mkv // FIXME: WHY WHY WHY can I not use record literals here?
        (merge (array_of vl) (array_of vr))
        (contents_of vl `Seq.append` contents_of vr)
    );
    rewrite (LA.arrayptr instance0 al vl) as (arrayptr al vl);
    unfold (arrayptr al vl);
    rewrite (arrayptr1 vl)
        as (A.pts_to_range res.v_array.array_base.base (SZ.v res.v_array.array_base.offset) (SZ.v vr.v_array.array_base.offset) #res.v_array.array_perm vl.v_contents);
    rewrite (LA.arrayptr instance0 ar vr) as (arrayptr ar vr);
    unfold (arrayptr ar vr);
    rewrite (arrayptr1 vr)
        as (A.pts_to_range res.v_array.array_base.base (SZ.v vr.v_array.array_base.offset) (SZ.v res.v_array.array_base.offset + SZ.v res.v_array.array_len) #res.v_array.array_perm vr.v_contents);
    A.pts_to_range_join res.v_array.array_base.base (SZ.v res.v_array.array_base.offset) (SZ.v vr.v_array.array_base.offset) (SZ.v res.v_array.array_base.offset + SZ.v res.v_array.array_len);
    rewrite (A.pts_to_range res.v_array.array_base.base (SZ.v res.v_array.array_base.offset) (SZ.v res.v_array.array_base.offset + SZ.v res.v_array.array_len) #res.v_array.array_perm (vl.v_contents `Seq.append` vr.v_contents))
        as (arrayptr1 res);
    fold (arrayptr al res);
    rewrite (arrayptr al res) as (LA.arrayptr instance0 al res);
    res
}
```

```pulse
fn gsplit
    (_: unit)
: LA.gsplit_t #t #array #v instance0
=
    (#elt:Type0)
    (x: t elt)
    (i:SZ.t)
    (#value:v elt)
{
    rewrite (LA.arrayptr instance0 x value) as (arrayptr x value);
    unfold (arrayptr x value);
    unfold (arrayptr1 value);
    A.pts_to_range_prop value.v_array.array_base.base;
    let vl : v elt = Mkv
        (Mkarray
            value.v_array.array_base
            i
            value.v_array.array_perm
        )
        (Seq.slice value.v_contents 0 (SZ.v i));
    let vr : v elt = Mkv
        (Mkarray
            (Mkt
                value.v_array.array_base.base
                value.v_array.array_base.glen
                (value.v_array.array_base.offset `SZ.add` i)
            )
            (value.v_array.array_len `SZ.sub` i)
            value.v_array.array_perm
        )
        (Seq.slice value.v_contents (SZ.v i) (Seq.length value.v_contents));
    let res : Ghost.erased (t elt) = Ghost.hide vr.v_array.array_base;
    A.pts_to_range_split value.v_array.array_base.base (SZ.v value.v_array.array_base.offset) (SZ.v vr.v_array.array_base.offset) (SZ.v value.v_array.array_base.offset + SZ.v value.v_array.array_len);
    rewrite
        (A.pts_to_range value.v_array.array_base.base (SZ.v value.v_array.array_base.offset) (SZ.v vr.v_array.array_base.offset) #value.v_array.array_perm (Seq.slice value.v_contents 0 (SZ.v vr.v_array.array_base.offset - SZ.v value.v_array.array_base.offset)))
        as (arrayptr1 vl);
    fold (arrayptr x vl);
    rewrite (arrayptr x vl) as (LA.arrayptr instance0 x vl);
    rewrite
        (A.pts_to_range value.v_array.array_base.base (SZ.v vr.v_array.array_base.offset) (SZ.v value.v_array.array_base.offset + SZ.v value.v_array.array_len) #value.v_array.array_perm (Seq.slice value.v_contents (SZ.v vr.v_array.array_base.offset - SZ.v value.v_array.array_base.offset) (Seq.length value.v_contents)))
        as (arrayptr1 vr);
    fold (arrayptr res vr);
    rewrite (arrayptr res vr) as (LA.arrayptr instance0 res vr);
    res
}
```

inline_for_extraction
```pulse
fn split'
    (_: unit)
: LA.split_t #t #array #v instance0
=
    (#elt:Type)
    (x: t elt)
    (i: SZ.t)
    (x': Ghost.erased (t elt))
    (#vl: Ghost.erased (v elt))
    (#vr: Ghost.erased (v elt))
{
    rewrite (LA.arrayptr instance0 x vl) as (arrayptr x vl);
    unfold (arrayptr x vl);
    fold (arrayptr x vl);
    rewrite (arrayptr x vl) as (LA.arrayptr instance0 x vl);
    rewrite (LA.arrayptr instance0 x' vr) as (arrayptr x' vr); 
    unfold (arrayptr x' vr);
    let res = Mkt
        x.base
        x.glen
        (x.offset `SZ.add` i);
    fold (arrayptr res vr);
    rewrite (arrayptr res vr) as (LA.arrayptr instance0 res vr);
    res
}
```

inline_for_extraction
```pulse
fn index
    (_: unit)
: LA.index_t #t #array #v instance0
=
    (#elt:Type)
    (r: t elt)
    (i: SZ.t)
    (#value: Ghost.erased (v elt))
{
    rewrite (LA.arrayptr instance0 r value) as (arrayptr r value);
    unfold (arrayptr r value);
    rewrite (arrayptr1 value)
        as (A.pts_to_range r.base (SZ.v value.v_array.array_base.offset) (SZ.v value.v_array.array_base.offset + SZ.v value.v_array.array_len) #value.v_array.array_perm value.v_contents);
    let y = A.pts_to_range_index r.base (r.offset `SZ.add` i);
    rewrite (A.pts_to_range r.base (SZ.v value.v_array.array_base.offset) (SZ.v value.v_array.array_base.offset + SZ.v value.v_array.array_len) #value.v_array.array_perm value.v_contents)
        as (arrayptr1 value);
    fold (arrayptr r value);
    rewrite (arrayptr r value) as  (LA.arrayptr instance0 r value);
    y
}
```

inline_for_extraction
```pulse
fn upd
    (_: unit)
: LA.upd_t #t #array #v instance0
=
    (#elt:Type)
    (r: t elt)
    (i:SZ.t)
    (x:elt)
    (#value: Ghost.erased (v elt))
{
    rewrite (LA.arrayptr instance0 r value) as (arrayptr r value);
    unfold (arrayptr r value);
    rewrite (arrayptr1 value)
        as (A.pts_to_range r.base (SZ.v value.v_array.array_base.offset) (SZ.v value.v_array.array_base.offset + SZ.v value.v_array.array_len) #full_perm value.v_contents);
    A.pts_to_range_upd r.base (r.offset `SZ.add` i) x;
    with contents' . assert (A.pts_to_range r.base (SZ.v value.v_array.array_base.offset) (SZ.v value.v_array.array_base.offset + SZ.v value.v_array.array_len) #full_perm contents');
    let value' : Ghost.erased (v elt) = Ghost.hide (Mkv
        value.v_array
        contents'        
    );
    rewrite (A.pts_to_range r.base (SZ.v value.v_array.array_base.offset) (SZ.v value.v_array.array_base.offset + SZ.v value.v_array.array_len) #full_perm contents')
        as (arrayptr1 value');
    fold (arrayptr r value');
    rewrite (arrayptr r value') as (LA.arrayptr instance0 r value');
    value'
}
```

let set_array_perm
    (#elt: Type)
    (a: array elt)
    (p: perm)
:   Ghost (array elt)
        (requires True)
        (ensures (fun y -> instance0.len y == instance0.len a /\
            instance0.array_perm y == p))
= {a with
    array_perm = p;
}

let set_array_perm_idem
    (#elt: Type)
    (a: array elt)
    (p1: perm)
    (p2: perm)
:   Lemma
    (set_array_perm (set_array_perm a p1) p2 == set_array_perm a p2)
= ()

let set_array_perm_eq
    (#elt: Type)
    (a: array elt)
:   Lemma
    (set_array_perm a (instance0.array_perm a) == a)
= ()

let set_array_perm_adjacent
    (#elt: Type)
    (a1: array elt)
    (a2: array elt)
    (p: perm)
:   Lemma
    (requires (instance0.adjacent a1 a2))
    (ensures (
        LA.merge_into instance0 (set_array_perm a1 p) (set_array_perm a2 p) (set_array_perm (instance0.merge a1 a2) p)
    ))
= ()

let seq_slice_full (#elt: Type) (x: Seq.seq elt) : Lemma
    (x == Seq.slice x 0 (Seq.length x))
= assert (x `Seq.equal` Seq.slice x 0 (Seq.length x))

inline_for_extraction
```pulse
fn copy
    (_: unit)
: LA.copy_t #t #array #v instance0
=
    (#elt: Type0)
    (ain: t elt)
    (aout: t elt)
    (len: SZ.t)
    (#vin: Ghost.erased (v elt))
    (#vout: Ghost.erased (v elt))
{
    // FIXME: expose pts_to_range_memcpy in Pulse.Lib.Array
    seq_slice_full vin.v_contents;
    let mut pi = 0sz;
    while
        (
            let i = !pi;
            (i `SZ.lt` len)
        )
    invariant cont . exists i vout' .
        pts_to pi i **
        LA.arrayptr instance0 ain vin ** LA.arrayptr instance0 aout vout' ** pure (
            instance0.array_of vout' == instance0.array_of vout /\
            LA.length instance0 (instance0.array_of vin) == LA.length instance0 (instance0.array_of vout) /\
            SZ.v i <= SZ.v len /\
            Seq.slice (instance0.contents_of vout') 0 (SZ.v i) `Seq.equal` Seq.slice (instance0.contents_of vin) 0 (SZ.v i) /\
            cont == (SZ.v i < SZ.v len)
        )
    {
        let i = !pi;
        let x = index () ain i;
        let prf = upd () aout i x;
        pi := (i `SZ.add` 1sz);
        Seq.lemma_split (Seq.slice prf.v_contents 0 (SZ.v i + 1)) (SZ.v i);
        Seq.lemma_split (Seq.slice vin.v_contents 0 (SZ.v i + 1)) (SZ.v i);
        ()
    };
    with vout' . assert (LA.arrayptr instance0 aout vout');
    seq_slice_full vout'.v_contents;
    Ghost.hide vout'
}
```

inline_for_extraction
let instance1: LA.array_ptr_step1 instance0 = {
    join = join ();
    gsplit = gsplit ();
    split' = split' ();
    index = index ();
    upd = upd ();
    set_array_perm = set_array_perm;
    set_array_perm_idem = set_array_perm_idem;
    set_array_perm_eq = set_array_perm_eq;
    set_array_perm_adjacent = set_array_perm_adjacent;
    copy = copy ();
}
