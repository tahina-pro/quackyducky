module EverParse3d.Actions.Base2
include EverParse3d.Kinds

val validator:
  (wk: weak_kind) ->
  (nz: bool) ->
  (t: Type0) ->
  (p: (t -> prop)) ->
  Type u#1

val validate_with_error_handler
  (#wk: Ghost.erased weak_kind)
  (#nz: Ghost.erased bool)
  (#t: Type0)
  (#p: (t -> prop))
  (v: validator wk nz t p)
: Tot (validator wk nz t p)

val validate_weaken
  (#nz1: Ghost.erased bool)
  (#wk1: Ghost.erased weak_kind)
  (#t: Type0)
  (#p1: (t -> prop))
  (v: validator wk1 nz1 t p1)
  (nz2: Ghost.erased bool { Ghost.reveal nz2 ==> Ghost.reveal nz1 })
  (wk2: Ghost.erased weak_kind { Ghost.reveal wk2 == WeakKindWeak \/ wk2 == wk1 })
  (p2: (t -> prop) { forall x . p1 x ==> p2 x })
: validator wk2 nz2 t p2
  
let true_cond (#t: Type) (x: t) : Tot prop = True

val validate_empty: validator WeakKindStrongPrefix false unit true_cond

val validate_u8_read: validator WeakKindStrongPrefix true FStar.UInt8.t true_cond
val validate_u8_no_read: validator WeakKindStrongPrefix true unit true_cond
val validate_u16_le_read: validator WeakKindStrongPrefix true FStar.UInt16.t true_cond
val validate_u16_le_no_read: validator WeakKindStrongPrefix true unit true_cond
val validate_u32_le_read: validator WeakKindStrongPrefix true FStar.UInt32.t true_cond
val validate_u32_le_no_read: validator WeakKindStrongPrefix true unit true_cond
val validate_u64_le_read: validator WeakKindStrongPrefix true FStar.UInt64.t true_cond
val validate_u64_le_no_read: validator WeakKindStrongPrefix true unit true_cond
val validate_u16_be_read: validator WeakKindStrongPrefix true FStar.UInt16.t true_cond
val validate_u16_be_no_read: validator WeakKindStrongPrefix true unit true_cond
val validate_u32_be_read: validator WeakKindStrongPrefix true FStar.UInt32.t true_cond
val validate_u32_be_no_read: validator WeakKindStrongPrefix true unit true_cond
val validate_u64_be_read: validator WeakKindStrongPrefix true FStar.UInt64.t true_cond
val validate_u64_be_no_read: validator WeakKindStrongPrefix true unit true_cond

let refine (t: Type) (p: t -> prop) = (x: t { p x })

let pred_dep_pair
  (#t1: Type0)
  (p1: (t1 -> prop))
  (#t2: Type0)
  (p2: (refine t1 p1 -> t2 -> prop))
  (x: (t1 & t2))
: Tot prop
= p1 (fst x) /\ p2 (fst x) (snd x)

val validate_dep_pair
  (#nz1: Ghost.erased bool)
  (#t1: Type0)
  (#p1: (t1 -> prop))
  (v1: validator WeakKindStrongPrefix nz1 t1 p1)
  (#wk2: Ghost.erased weak_kind)
  (#nz2: Ghost.erased bool)
  (#t2: Type0)
  (#p2: (refine t1 p1 -> t2 -> prop))
  (v2: (x1: refine t1 p1) -> validator wk2 nz2 t2 (p2 x1))
: validator wk2 (nz1 || nz2) (t1 & t2) (pred_dep_pair p1 p2) // necessary to keep t1 because we cannot further use dep_pair if wk2 is not WeakKindStrongPrefix

let pred_pair
  (#t1: Type0)
  (p1: (t1 -> prop))
  (#t2: Type0)
  (p2: (t2 -> prop))
  (x: (t1 & t2))
: Tot prop
= p1 (fst x) /\ p2 (snd x)

let validate_pair
  (#nz1: Ghost.erased bool)
  (#t1: Type0)
  (#p1: (t1 -> prop))
  (v1: validator WeakKindStrongPrefix nz1 t1 p1)
  (#wk2: Ghost.erased weak_kind)
  (#nz2: Ghost.erased bool)
  (#t2: Type0)
  (#p2: (t2 -> prop))
  (v2: (validator wk2 nz2 t2 p2))
: validator wk2 (nz1 || nz2) (t1 & t2) (pred_pair p1 p2)
= validate_weaken
    (validate_dep_pair v1 (fun _ -> v2))
    _ _ _

let pred_rewrite
  (#t1: Type0)
  (p1: (t1 -> prop))
  (#t2: Type0)
  (f: t1 -> t2)
  (x2: t2)
: Tot prop
= exists x1 . p1 x1 /\ x2 == f x1

val validate_rewrite
  (#wk1: Ghost.erased weak_kind)
  (#nz1: Ghost.erased bool)
  (#t1: Type0)
  (#p1: (t1 -> prop))
  (v1: validator wk1 nz1 t1 p1)
  (#t2: Type0)
  (f: t1 -> t2)
: validator wk1 nz1 t2 (pred_rewrite p1 f)

let ret_cond (#t: Type) (v: t) (x: t) : Tot prop = x == v

let validate_ret (#t: Type) (v: t) : validator WeakKindStrongPrefix false t (ret_cond v) =
  validate_weaken
    (validate_rewrite validate_empty (fun _ -> v))
    _ _ _

let pred_refine
  (#t: Type0)
  (p1: (t -> prop))
  (p2: (refine t p1 -> bool))
  (x: t)
: Tot prop
= p1 x /\ p2 x

val validate_refine
  (#wk: Ghost.erased weak_kind)
  (#nz: Ghost.erased bool)
  (#t: Type0)
  (#p: (t -> prop))
  (v: validator wk nz t p)
  (q: (refine t p -> bool))
: validator wk nz t (pred_refine p q)

let pred_ifthenelse
  (cond: bool)
  (#t: Type0)
  (p1: (squash (cond == true) -> t -> prop))
  (p2: (squash (cond == false) -> t -> prop))
  (x: t)
: Tot prop
= if cond then p1 () x else p2 () x

val validate_ifthenelse
  (cond: bool)
  (#wk: Ghost.erased weak_kind)
  (#t: Type0)
  (#nz1: Ghost.erased bool)
  (#p1: (squash (cond == true) -> t -> prop))
  (v1: (squash (cond == true) -> validator wk nz1 t (p1 ())))
  (#nz2: Ghost.erased bool)
  (#p2: (squash (cond == false) -> t -> prop))
  (v2: (squash (cond == false) -> validator wk nz2 t (p2 ())))
: validator wk (nz1 && nz2) t (pred_ifthenelse cond p1 p2)

val validate_check_end : validator WeakKindConsumesAll false unit true_cond

val validate_consume_end : validator WeakKindConsumesAll false unit true_cond

val validate_list
  (#t: Type0)
  (#p: (t -> prop))
  (v: validator WeakKindStrongPrefix true t p)
: validator WeakKindConsumesAll false unit true_cond

module SZ = FStar.SizeT

val validate_with_size
  (#nz: Ghost.erased bool)
  (#t: Type0)
  (#p: (t -> prop))
  (v: validator WeakKindConsumesAll nz t p)
  (sz: SZ.t)
  (nz' : Ghost.erased bool { Ghost.reveal nz' ==> SZ.v sz > 0 })
: validator WeakKindStrongPrefix nz' t p

val action (t: Type0): Type u#1

val validate_with_action
  (#wk: Ghost.erased weak_kind)
  (#nz: Ghost.erased bool)
  (#t: Type0)
  (#p: (t -> prop))
  (v: validator wk nz t p)
  (a: (refine t p -> action bool))
: validator wk nz t p
