module LowParse.SteelST.ArrayPtr.Base
open Steel.FractionalPermission
module SZ = FStar.SizeT

inline_for_extraction
val t (t:Type u#0) : Type u#0

[@@erasable]
val array
  (t: Type0)
: Tot Type0

val len
  (#t: Type0)
  (x: array t)
: GTot SZ.t

let length
  (#t: Type0)
  (x: array t)
: GTot nat
= SZ.v (len x)

val array_perm
  (#t: Type)
  (x: array t)
: GTot perm

[@@erasable]
val v (t: Type u#0) : Tot Type0

val array_of (#a: _) (v: v a) : Tot (array a)
val contents_of (#a: _) (v: v a) : GTot (Seq.lseq a (length (array_of v)))
let contents_of' #a (v: v a) : GTot (Seq.seq a) =
  contents_of v

val array_contents_inj
  (#a: _)
  (v1 v2: v a)
: Lemma
  (requires (
    array_of v1 == array_of v2 /\
    contents_of v1 == contents_of v2
  ))
  (ensures (v1 == v2))
  [SMTPatOr [
    [SMTPat (array_of v1); SMTPat (array_of v2)];
    [SMTPat (contents_of v1); SMTPat (contents_of v2)];
  ]]

val adjacent
  (#t: Type0)
  (x1 x2: array t)
: Tot prop

val merge
  (#t: Type0)
  (x1 x2: array t)
: Ghost (array t)
  (requires (adjacent x1 x2))
  (ensures (fun y -> length y == length x1 + length x2 /\ array_perm y == array_perm x1 /\ array_perm y == array_perm x2))

let adjacent_sizes_fit
  (#t: Type0)
  (x1 x2: array t)
: Lemma
  (requires (adjacent x1 x2))
  (ensures (SZ.fits (length x1 + length x2)))
  [SMTPat (adjacent x1 x2)]
= let _ = merge x1 x2 in
  ()

let merge_into
  (#t: Type0)
  (x1 x2 y: array t)
: Tot prop
= adjacent x1 x2 /\
  merge x1 x2 == y

val merge_assoc
  (#t: Type0)
  (x1 x2 x3: array t)
: Lemma
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
  [SMTPatOr [
    [SMTPat (adjacent x1 x2); SMTPat (adjacent x2 x3)];
    [SMTPat (adjacent (merge x1 x2) x3)];
    [SMTPat (adjacent x1 (merge x2 x3))];
  ]]

[@@noextract_to "krml"]
let seq_slice
  (#a:Type) (s:Seq.seq a) (i: nat) (j: nat) : Pure (Seq.seq a)
  (requires (i <= j /\ j <= Seq.length s))
  (ensures (fun _ -> True))
= Seq.slice s i j

val set_array_perm
  (#t: Type)
  (a: array t)
  (p: perm)
: Ghost (array t)
    (requires True)
    (ensures (fun y -> len y == len a /\ array_perm y == p))

val set_array_perm_idem
  (#t: Type)
  (a: array t)
  (p1 p2: perm)
: Lemma
  (set_array_perm (set_array_perm a p1) p2 == set_array_perm a p2)
  [SMTPat (set_array_perm (set_array_perm a p1) p2)]

val set_array_perm_eq
  (#t: Type)
  (a: array t)
: Lemma
  (set_array_perm a (array_perm a) == a)
  [SMTPat (set_array_perm a (array_perm a))]

val set_array_perm_adjacent
  (#t: Type)
  (a1 a2: array t)
  (p: perm)
: Lemma
  (requires (adjacent a1 a2))
  (ensures (
    merge_into (set_array_perm a1 p) (set_array_perm a2 p) (set_array_perm (merge a1 a2) p)
  ))
  [SMTPat (adjacent (set_array_perm a1 p) (set_array_perm a2 p))]
