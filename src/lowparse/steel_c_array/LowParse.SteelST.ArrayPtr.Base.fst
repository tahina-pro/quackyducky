module LowParse.SteelST.ArrayPtr.Base
module STC = Steel.ST.C.Types

let t elt = STC.array_ptr (STC.scalar elt)

[@@erasable]
noeq
type array elt = {
  array_ptr: STC.array (STC.scalar elt);
  array_perm: Steel.FractionalPermission.perm;
//  array_base_len: (len: SZ.t { SZ.v len == SA.base_len (STC.base (STC.array_ptr_of array_ptr)) });
}

let len x = SZ.uint_to_t (STC.array_length x.array_ptr)

let array_perm x = x.array_perm

[@@erasable]
noeq
type v t = {
  v_array: array t;
  v_contents: Seq.lseq t (length v_array);
}

let array_of x = x.v_array
let contents_of x = x.v_contents

let array_contents_inj _ _ = ()

let adjacent x1 x2 =
  x1.array_perm == x2.array_perm /\
  STC.array_ptr_of x2.array_ptr == STC.array_ref_shift (STC.array_ptr_of x1.array_ptr) (len x1)

let merge x1 x2 = {
  array_ptr = (| STC.array_ptr_of x1.array_ptr, Ghost.hide (len x1 `SZ.add` len x2) |);
  array_perm = x1.array_perm;
//  array_base_len = x1.array_base_len;
}

let merge_assoc x1 x2 x3 =
  STC.array_ref_shift_assoc (STC.array_ptr_of x1.array_ptr) (len x1) (len x2)

let set_array_perm
  (#t: Type)
  (a: array t)
  (p: perm)
: Ghost (array t)
    (requires True)
    (ensures (fun y -> len y == len a /\ array_perm y == p))
= {
  a with array_perm = p
}

let set_array_perm_idem
  (#t: Type)
  (a: array t)
  (p1 p2: perm)
: Lemma
  (set_array_perm (set_array_perm a p1) p2 == set_array_perm a p2)
= ()

let set_array_perm_eq
  (#t: Type)
  (a: array t)
: Lemma
  (set_array_perm a (array_perm a) == a)
= ()

let set_array_perm_adjacent
  (#t: Type)
  (a1 a2: array t)
  (p: perm)
: Lemma
  (requires (adjacent a1 a2))
  (ensures (
    merge_into (set_array_perm a1 p) (set_array_perm a2 p) (set_array_perm (merge a1 a2) p)
  ))
= ()
