module LowParse.SteelST.R2LOutput
include LowParse.Bytes
open Steel.ST.Util

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

(* Right-to-left output buffer *)

inline_for_extraction
val t: Type0

val vp
  (x: t)
  (va: AP.array byte)
: Tot vprop

val vp_perm
  (#opened: _)
  (#va: AP.array byte)
  (x: t)
: STGhost unit opened
    (vp x va)
    (fun _ -> vp x va)
    True
    (fun _ -> 
      AP.array_perm va == full_perm
    )

inline_for_extraction
val len
  (#va: AP.array byte)
  (x: t)
: ST SZ.t
    (vp x va)
    (fun _ -> vp x va)
    True
    (fun res -> res == AP.len va)

inline_for_extraction
val split
  (#va: AP.array byte)
  (x: t)
  (len: SZ.t)
: ST (AP.t byte)
    (vp x va)
    (fun p ->  exists_ (fun vr -> exists_ (fun va' ->
      AP.arrayptr p vr `star`
      vp x va' `star`
      pure (
        AP.merge_into va' (AP.array_of vr) va /\
        AP.array_perm (AP.array_of vr) == full_perm /\
        AP.len (AP.array_of vr) == len
    ))))
    (SZ.v len <= AP.length va)
    (fun _ -> True)

inline_for_extraction
val revert
  (#vx: _)
  (x: t)
  (y: Ghost.erased (AP.t byte))
  (#vy: _)
  (len: SZ.t)
: ST (AP.array byte)
    (vp x vx `star` AP.arrayptr y vy)
    (fun res -> vp x res)
    (AP.adjacent vx (AP.array_of vy) /\
      SZ.v len == AP.length vx + AP.length (AP.array_of vy)
    )
    (fun res ->
      AP.merge_into vx (AP.array_of vy) res
    )

inline_for_extraction
let revert_with
  (#vx: _)
  (x: t)
  (y: Ghost.erased (AP.t byte))
  (a: AP.array byte)
  (#vy: _)
  (len: SZ.t)
: ST unit
    (vp x vx `star` AP.arrayptr y vy)
    (fun res -> vp x a)
    (AP.merge_into vx (AP.array_of vy) a /\
      len == AP.len a
    )
    (fun _ -> True)
= let _ = revert x y len in
  vpattern_rewrite (vp x) a

inline_for_extraction
let merge
  (#vx: _)
  (x: t)
  (y: Ghost.erased (AP.t byte))
  (#vy: _)
  (sz: SZ.t)
: ST (AP.array byte)
    (vp x vx `star` AP.arrayptr y vy)
    (fun res -> vp x res)
    (AP.adjacent vx (AP.array_of vy) /\
      AP.len (AP.array_of vy) == sz
    )
    (fun res ->
      AP.merge_into vx (AP.array_of vy) res
    )
= let len_before = len x in
  revert x y (len_before `SZ.add` sz)

inline_for_extraction
val hop
  (#vx: _)
  (x: t)
  (#vy: _)
  (y: Ghost.erased (AP.t byte))
: ST (AP.t byte)
    (vp x vx `star` AP.arrayptr y vy)
    (fun res -> vp x vx `star` AP.arrayptr res vy)
    (AP.adjacent vx (AP.array_of vy))
    (fun _ -> True)
