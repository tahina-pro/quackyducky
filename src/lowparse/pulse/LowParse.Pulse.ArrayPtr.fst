module LowParse.Pulse.ArrayPtr
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT

inline_for_extraction
// class array_ptr_step0
noeq type array_ptr_step0
    (t: Type0 -> Type0)
    (array: Type0 -> Type0)
    (v: Type0 -> Type0)
= {
    len: (#elt: Type0) -> array elt -> GTot SZ.t;
    array_perm: (#elt: Type0) -> array elt -> perm;
    array_of: (#elt: Type0) -> v elt -> GTot (array elt);
    contents_of: (#elt: Type0) -> (x: v elt) -> GTot (Seq.lseq elt (SZ.v (len (array_of x))));
    array_contents_inj: (#elt: Type0) -> (v1: v elt) -> (v2: v elt) -> Lemma
        (requires (array_of v1 == array_of v2 /\
            contents_of v1 == contents_of v2
        ))
        (ensures v1 == v2);
    arrayptr: (#elt: Type0) -> t elt -> v elt -> vprop;
(*    
    null: (#elt: Type0) -> t elt;
    arrayptr_not_null: (#elt: Type0) -> (r: t elt) -> (#value: v elt) -> stt_ghost unit emp_inames
        (arrayptr r value)
        (fun _ -> arrayptr r value ** pure (~ (r == null)));
*)        
    adjacent: (#elt: Type0) -> (x1: array elt) -> (x2: array elt) -> prop;
    merge: (#elt: Type0) -> (x1: array elt) -> (x2: array elt) -> Ghost (array elt)
        (requires (adjacent x1 x2))
        (ensures (fun y -> SZ.v (len y) == SZ.v (len x1) + SZ.v (len x2) /\
            array_perm y == array_perm x1 /\
            array_perm y == array_perm x2
        ));
    merge_assoc: (#elt: Type0) -> (x1: array elt) -> (x2: array elt) -> (x3: array elt) -> Lemma
        (requires (
            (adjacent x1 x2 /\ adjacent x2 x3) \/
            (adjacent x1 x2 /\ adjacent (merge x1 x2) x3) \/
            (adjacent x2 x3 /\ adjacent x1 (merge x2 x3))
        ))
        (ensures (
            adjacent x1 x2 /\ adjacent (merge x1 x2) x3 /\
            adjacent x2 x3 /\ adjacent x1 (merge x2 x3) /\
            merge (merge x1 x2) x3 == merge x1 (merge x2 x3)
        ));
}

let length
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
    (#elt: Type0)
    (r: array elt)
: GTot nat
= SZ.v (instance0.len r)

(*
let arrayptr_or_null
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
    (#elt: Type0)
    (r: t elt)
    (value: v elt)
: Tot vprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (r == instance0.null)
  then emp
  else instance0.arrayptr r value
*)

let merge_into
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
    (#elt: Type0)
    (x1 x2 y: array elt)
: Tot prop
= instance0.adjacent x1 x2 /\
  instance0.merge x1 x2 == y

let arrayptr
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
: (#elt: Type0) -> t elt -> v elt -> vprop
= instance0.arrayptr

unfold
let gsplit_post
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
    (#elt:Type)
    (x: t elt)
    (i:SZ.t)
    (value:v elt)
    (res: Ghost.erased (t elt))
    (vl: v elt)
    (vr: v elt)
: Tot prop
=
    SZ.v i <= length instance0 (instance0.array_of value) /\
    merge_into instance0 (instance0.array_of vl) (instance0.array_of vr) (instance0.array_of value) /\
    instance0.contents_of vl == Seq.slice (instance0.contents_of value) 0 (SZ.v i) /\
    length instance0 (instance0.array_of vl) == SZ.v i /\
    length instance0 (instance0.array_of vr) == length instance0 (instance0.array_of value) - SZ.v i /\
    instance0.contents_of vr == Seq.slice (instance0.contents_of value) (SZ.v i) (length instance0 (instance0.array_of value)) /\
    instance0.contents_of value == instance0.contents_of vl `Seq.append` instance0.contents_of vr /\
    (SZ.v i == 0 ==> Ghost.reveal res == x)

let join_t
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
= (#elt:Type) -> (al: t elt) -> (ar: t elt) -> (#vl: v elt) -> (#vr: v elt) -> stt_ghost (Ghost.erased (v elt)) emp_inames
        (arrayptr instance0 al vl ** arrayptr instance0 ar vr ** pure (
            instance0.adjacent (instance0.array_of vl) (instance0.array_of vr)
        ))
        (fun res -> arrayptr instance0 al res ** pure (
            merge_into instance0 (instance0.array_of vl) (instance0.array_of vr) (instance0.array_of res) /\
            instance0.contents_of res == instance0.contents_of vl `Seq.append` instance0.contents_of vr
        ))

let gsplit_t
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
= (#elt:Type) -> (x: t elt) -> (i:SZ.t) -> (#value:v elt) -> stt_ghost (Ghost.erased (t elt)) emp_inames
        (arrayptr instance0 x value ** pure (
            SZ.v i <= length instance0 (instance0.array_of value)
        ))
        (fun res -> exists_ (fun vl -> exists_ (fun vr ->
            arrayptr instance0 x vl ** arrayptr instance0 res vr ** pure (
                gsplit_post instance0 x i value res vl vr
        ))))

let split_t
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
= (#elt:Type) -> (x: t elt) -> (i: SZ.t) -> (x': Ghost.erased (t elt)) -> (#vl: Ghost.erased (v elt)) -> (#vr: Ghost.erased (v elt)) -> stt (t elt)
        (arrayptr instance0 x vl ** arrayptr instance0 x' vr ** pure (
            instance0.adjacent (instance0.array_of vl) (instance0.array_of vr) /\
            SZ.v i == length instance0 (instance0.array_of vl)
        ))
        (fun res -> arrayptr instance0 x vl ** arrayptr instance0 res vr ** pure (
            res == Ghost.reveal x'
        ))

let index_t
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
= (#elt:Type) -> (r: t elt) -> (i: SZ.t) -> (#value: Ghost.erased (v elt)) -> stt elt
        (arrayptr instance0 r value ** pure (
            SZ.v i < length instance0 (instance0.array_of value)
        ))
        (fun y -> arrayptr instance0 r value ** pure (
            SZ.v i < length instance0 (instance0.array_of value) /\
            y == Seq.index (instance0.contents_of value) (SZ.v i)
        ))

let upd_t
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
= (#elt:Type) -> (r: t elt) -> (i:SZ.t) -> (x:elt) -> (#value: Ghost.erased (v elt)) -> stt (Ghost.erased (v elt))
        (arrayptr instance0 r value ** pure (
            SZ.v i < length instance0 (instance0.array_of value) /\
            instance0.array_perm (instance0.array_of value) == full_perm
        ))
        (fun value' -> arrayptr instance0 r value' ** pure (
            SZ.v i < length instance0 (instance0.array_of value) /\
            instance0.array_of value' == instance0.array_of value /\
            instance0.contents_of value' == Seq.upd (instance0.contents_of value) (SZ.v i) x
        ))

let copy_t
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
=       (#elt: Type) ->
        (ain: t elt) ->
        (aout: t elt) ->
        (len: SZ.t) ->
        (#vin: Ghost.erased (v elt)) ->
        (#vout: Ghost.erased (v elt)) ->
        stt (Ghost.erased (v elt))
            (arrayptr instance0 ain vin ** arrayptr instance0 aout vout ** pure (
                SZ.v len == length instance0 (instance0.array_of vin) /\
                SZ.v len == length instance0 (instance0.array_of vout) /\
                instance0.array_perm (instance0.array_of vout) == full_perm
            ))
            (fun vout' -> arrayptr instance0 ain vin ** arrayptr instance0 aout vout' ** pure (
                instance0.array_of vout' == instance0.array_of vout /\
                length instance0 (instance0.array_of vin) == length instance0 (instance0.array_of vout) /\
                instance0.contents_of vout' == instance0.contents_of vin
            ))

inline_for_extraction
// class array_ptr_step0
noeq type array_ptr_step1
    (#t: Type0 -> Type0)
    (#array: Type0 -> Type0)
    (#v: Type0 -> Type0)
    (instance0: array_ptr_step0 t array v)
= {
(*
    is_null: (#elt: Type0) -> (r: t elt) -> (#value: Ghost.erased (v elt)) -> stt bool
        (arrayptr_or_null instance0 r value)
        (fun res -> arrayptr_or_null instance0 r value ** pure (res == true <==> r == instance0.null));
*)
    join: join_t instance0;
    gsplit: gsplit_t instance0;
    split': split_t instance0;
    index: index_t instance0;
    upd: upd_t instance0;
    set_array_perm: 
        (#elt: Type) ->
        (a: array elt) ->
        (p: perm) ->
        Ghost (array elt)
            (requires True)
            (ensures (fun y -> instance0.len y == instance0.len a /\
                instance0.array_perm y == p));
    set_array_perm_idem:
        (#elt: Type) ->
        (a: array elt) ->
        (p1: perm) ->
        (p2: perm) ->
        Lemma
        (set_array_perm (set_array_perm a p1) p2 == set_array_perm a p2);
    set_array_perm_eq:
        (#elt: Type) ->
        (a: array elt) ->
        Lemma
        (set_array_perm a (instance0.array_perm a) == a);
    set_array_perm_adjacent:
        (#elt: Type) ->
        (a1: array elt) ->
        (a2: array elt) ->
        (p: perm) ->
        Lemma
        (requires (instance0.adjacent a1 a2))
        (ensures (
            merge_into instance0 (set_array_perm a1 p) (set_array_perm a2 p) (set_array_perm (instance0.merge a1 a2) p)
        ));
    copy: copy_t instance0;
}

(*
    share:
        (#elt: Type) ->
        (a: t elt) ->
        (p1: perm) ->
        (p2: perm) ->
        (#x: Ghost.erased (v elt)) ->
        stt_ghost (Ghost.erased (v elt & v elt)) emp_inames
            (arrayptr instance0 a x ** pure (
                instance0.array_perm (instance0.array_of x) == p1 `Steel.FractionalPermission.sum_perm` p2
            ))
            (fun res -> arrayptr instance0 a (fst res) ** arrayptr instance0 a (snd res) ** pure (
                instance0.array_of (fst res) == set_array_perm (instance0.array_of x) p1 /\
                instance0.array_of (snd res) == set_array_perm (instance0.array_of x) p2 /\
                instance0.contents_of (fst res) == instance0.contents_of x /\
                instance0.contents_of (snd res) == instance0.contents_of x
            ));
    gather:
        (#elt: Type) ->
        (a: t elt) ->
        (#x1: Ghost.erased (v elt)) ->
        (#x2: Ghost.erased (v elt)) ->
        stt_ghost (Ghost.erased (v elt)) emp_inames
            (arrayptr instance0 a x1 ** arrayptr instance0 a x2 ** pure (
                instance0.array_of x1 == set_array_perm (instance0.array_of x2) (instance0.array_perm (instance0.array_of x1))
            ))
            (fun res -> arrayptr instance0 a res ** pure (
                instance0.array_of x1 == set_array_perm (instance0.array_of x2) (instance0.array_perm (instance0.array_of x1)) /\
                instance0.array_of res == set_array_perm (instance0.array_of x1) (instance0.array_perm (instance0.array_of x1) `Steel.FractionalPermission.sum_perm` instance0.array_perm (instance0.array_of x2)) /\
                instance0.contents_of res == instance0.contents_of x1 /\
                instance0.contents_of res == instance0.contents_of x2
            ));
}
