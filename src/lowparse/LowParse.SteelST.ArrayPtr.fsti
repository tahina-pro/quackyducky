module LowParse.SteelST.ArrayPtr
include LowParse.SteelST.ArrayPtr.Base

open Steel.Memory
open Steel.FractionalPermission
module SZ = FStar.SizeT
open Steel.ST.GenElim

val arrayptr
  (#a: Type0)
  (r: t a)
  ([@@@smt_fallback] value: v a)
: Tot vprop

val join (#opened: _) (#a:Type) (#vl #vr: v a) (al ar:t a)
  : STGhost (v a) opened
          (arrayptr al vl `star` arrayptr ar vr)
          (fun res -> arrayptr al res)
          (adjacent (array_of vl) (array_of vr))
          (fun res ->
            merge_into (array_of vl) (array_of vr) (array_of res) /\
            contents_of res == contents_of vl `Seq.append` contents_of vr
          )

val gsplit (#opened: _) (#a:Type) (#value: v a) (x: t a) (i:SZ.t)
  : STGhost (Ghost.erased (t a)) opened
          (arrayptr x value)
          (fun res -> exists_ (fun vl -> exists_ (fun vr ->
            arrayptr x vl `star` arrayptr res vr `star` pure (
            SZ.v i <= length (array_of value) /\
            merge_into (array_of vl) (array_of vr) (array_of value) /\
            contents_of' vl == seq_slice (contents_of' value) 0 (SZ.v i) /\
            length (array_of vl) == SZ.v i /\
            length (array_of vr) == length (array_of value) - SZ.v i /\
            contents_of' vr == seq_slice (contents_of' value) (SZ.v i) (length (array_of value)) /\
            contents_of' value == contents_of' vl `Seq.append` contents_of' vr /\
            (SZ.v i == 0 ==> Ghost.reveal res == x)
          ))))
          (SZ.v i <= length (array_of value))
          (fun _ -> True)

inline_for_extraction
val split' (#a:Type) (#vl #vr: v a) (x: t a) (i: SZ.t) (x': Ghost.erased (t a))
  : ST (t a)
          (arrayptr x vl `star` arrayptr x' vr)
          (fun res -> arrayptr x vl `star` arrayptr res vr)
          (adjacent (array_of vl) (array_of vr) /\ SZ.v i == length (array_of vl))
          (fun res -> res == Ghost.reveal x')

inline_for_extraction
let split (#a:Type) (#value: v a) (x: t a) (i:SZ.t)
  : ST (t a)
          (arrayptr x value)
          (fun res -> exists_ (fun vl -> exists_ (fun vr ->
            arrayptr x vl `star` arrayptr res vr `star` pure (
            SZ.v i <= length (array_of value) /\
            merge_into (array_of vl) (array_of vr) (array_of value) /\
            contents_of' vl == seq_slice (contents_of' value) 0 (SZ.v i) /\
            length (array_of vl) == SZ.v i /\
            length (array_of vr) == length (array_of value) - SZ.v i /\
            contents_of' vr == seq_slice (contents_of' value) (SZ.v i) (length (array_of value)) /\
            contents_of' value == contents_of' vl `Seq.append` contents_of' vr /\
            (SZ.v i == 0 ==> res == x)
          ))))
          (SZ.v i <= length (array_of value))
          (fun _ -> True)
= let gres = gsplit x i in
  let _ = gen_elim () in
  let res = split' x i gres in
  res

inline_for_extraction
val index (#a:Type) (#value: v a) (r: t a) (i: SZ.t)
  : ST a
             (arrayptr r value)
             (fun y -> arrayptr r value)
             (SZ.v i < length (array_of value))
             (fun y ->
               SZ.v i < length (array_of value) /\
               y == Seq.index (contents_of' value) (SZ.v i)
             )

inline_for_extraction
val upd (#a:Type) (#value: v a) (r: t a) (i:SZ.t) (x:a)
  : ST (v a)
             (arrayptr r value)
             (fun value' -> arrayptr r value')
             (SZ.v i < length (array_of value) /\ array_perm (array_of value) == full_perm)
             (fun value'->
               SZ.v i < length (array_of value) /\
               array_of value' == array_of value /\
               contents_of' value' == Seq.upd (contents_of' value) (SZ.v i) x
             )

val share
  (#opened: _)
  (#elt: Type)
  (#x: v elt)
  (a: t elt)
  (p1 p2: perm)
: STGhost (Ghost.erased (v elt & v elt)) opened
    (arrayptr a x)
    (fun res -> arrayptr a (fst res) `star` arrayptr a (snd res))
    (array_perm (array_of x) == p1 `Steel.FractionalPermission.sum_perm` p2)
    (fun res ->
      contents_of' (fst res) == contents_of x /\
      contents_of' (snd res) == contents_of x /\
      array_of (fst res) == set_array_perm (array_of x) p1 /\
      array_of (snd res) == set_array_perm (array_of x) p2
    )

val gather
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: v elt)
  (a: t elt)
: STGhost (v elt) opened
    (arrayptr a x1 `star` arrayptr a x2)
    (fun res -> arrayptr a res)
    (array_of x1 == set_array_perm (array_of x2) (array_perm (array_of x1)))
    (fun res ->
      contents_of' res == contents_of x1 /\
      contents_of' res == contents_of x2 /\
      array_of res == set_array_perm (array_of x1) (array_perm (array_of x1) `Steel.FractionalPermission.sum_perm` array_perm (array_of x2))
    )
