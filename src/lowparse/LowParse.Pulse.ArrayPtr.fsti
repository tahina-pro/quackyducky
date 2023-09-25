module LowParse.Pulse.ArrayPtr
include LowParse.SteelST.ArrayPtr.Base
open Pulse.Lib.Core
module SZ = FStar.SizeT
module M = Pulse.Main

val arrayptr
  (#a: Type0)
  (r: t a)
  (value: v a)
: Tot vprop

val join (#a:Type) (al ar:t a) (#vl #vr: v a)
  : stt_ghost unit emp_inames
          (arrayptr al vl ** arrayptr ar vr ** pure (
            adjacent (array_of vl) (array_of vr)
          ))
          (fun _ -> exists_ (fun res -> arrayptr al res ** pure (
            merge_into (array_of vl) (array_of vr) (array_of res) /\
            contents_of res == contents_of vl `Seq.append` contents_of vr
          )))

val gsplit (#a:Type) (x: t a) (i:SZ.t) (#value: v a)
  : stt_ghost (Ghost.erased (t a)) emp_inames
          (arrayptr x value ** pure (
            SZ.v i <= length (array_of value)
          ))
          (fun res -> exists_ (fun vl -> exists_ (fun vr ->
            arrayptr x vl ** arrayptr res vr ** pure (
            SZ.v i <= length (array_of value) /\
            merge_into (array_of vl) (array_of vr) (array_of value) /\
            contents_of' vl == seq_slice (contents_of' value) 0 (SZ.v i) /\
            length (array_of vl) == SZ.v i /\
            length (array_of vr) == length (array_of value) - SZ.v i /\
            contents_of' vr == seq_slice (contents_of' value) (SZ.v i) (length (array_of value)) /\
            contents_of' value == contents_of' vl `Seq.append` contents_of' vr /\
            (SZ.v i == 0 ==> Ghost.reveal res == x)
          ))))

inline_for_extraction
val split' (#a:Type) (x: t a) (i: SZ.t) (x': Ghost.erased (t a)) (#vl #vr: v a)
  : stt (t a)
          (arrayptr x vl ** arrayptr x' vr ** pure (
            adjacent (array_of vl) (array_of vr) /\ SZ.v i == length (array_of vl)
          ))
          (fun res -> arrayptr x vl ** arrayptr res vr ** pure (
            res == Ghost.reveal x'
          ))

inline_for_extraction
```pulse
fn split (#a:Type) (x: t a) (i:SZ.t) (#value: v a)
  requires
    arrayptr x value ** pure (
      SZ.v i <= length (array_of value)
    )
  returns res: t a
  ensures exists vl vr .
    arrayptr x vl ** arrayptr res vr ** pure (
    SZ.v i <= length (array_of value) /\
    merge_into (array_of vl) (array_of vr) (array_of value) /\
    contents_of' vl == seq_slice (contents_of' value) 0 (SZ.v i) /\
    length (array_of vl) == SZ.v i /\
    length (array_of vr) == length (array_of value) - SZ.v i /\
    contents_of' vr == seq_slice (contents_of' value) (SZ.v i) (length (array_of value)) /\
    contents_of' value == contents_of' vl `Seq.append` contents_of' vr /\
    (SZ.v i == 0 ==> res == x)
  )
  {
    let gres = gsplit x i;
    split' x i gres
  }
```

inline_for_extraction
val index (#a:Type) (r: t a) (i: SZ.t) (#value: v a)
  : stt a
             (arrayptr r value ** pure (
               SZ.v i < length (array_of value)             
             ))
             (fun y -> arrayptr r value ** pure (
               SZ.v i < length (array_of value) /\
               y == Seq.index (contents_of' value) (SZ.v i)
             ))

open Steel.FractionalPermission

inline_for_extraction
val upd (#a:Type) (r: t a) (i:SZ.t) (x:a) (#value: v a)
  : stt unit
             (arrayptr r value ** pure (
               SZ.v i < length (array_of value) /\ array_perm (array_of value) == full_perm
             ))
             (fun _ -> exists_ (fun value' -> arrayptr r value' ** pure (
               SZ.v i < length (array_of value) /\
               array_of value' == array_of value /\
               contents_of' value' == Seq.upd (contents_of' value) (SZ.v i) x
             )))

val share
  (#elt: Type)
  (a: t elt)
  (p1 p2: perm)
  (#x: v elt)
: stt_ghost unit emp_inames
    (arrayptr a x ** pure (
      array_perm (array_of x) == p1 `Steel.FractionalPermission.sum_perm` p2
    ))
    (fun _ -> exists_ (fun fst_res -> exists_ (fun snd_res -> arrayptr a fst_res ** arrayptr a snd_res ** pure (
      contents_of' fst_res == contents_of x /\
      contents_of' snd_res == contents_of x /\
      array_of fst_res == set_array_perm (array_of x) p1 /\
      array_of snd_res == set_array_perm (array_of x) p2
    ))))

val gather
  (#elt: Type)
  (a: t elt)
  (#x1 #x2: v elt)
: stt_ghost unit emp_inames
    (arrayptr a x1 ** arrayptr a x2 ** pure (
      array_of x1 == set_array_perm (array_of x2) (array_perm (array_of x1))
    ))
    (fun _ -> exists_ (fun res -> arrayptr a res ** pure (
      contents_of' res == contents_of x1 /\
      contents_of' res == contents_of x2 /\
      array_of res == set_array_perm (array_of x1) (array_perm (array_of x1) `Steel.FractionalPermission.sum_perm` array_perm (array_of x2))
    )))
