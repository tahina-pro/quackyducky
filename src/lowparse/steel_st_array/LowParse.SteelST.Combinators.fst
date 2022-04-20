module LowParse.SteelST.Combinators
include LowParse.Spec.Combinators
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
open Steel.ST.Util

module AP = LowParse.SteelST.ArrayPtr
module R = Steel.ST.Reference
module SZ = LowParse.Steel.StdInt

#set-options "--ide_id_info_off"

module T = FStar.Tactics

#push-options "--z3rlimit 24"
#restart-solver

let validate_pair
  #k1 #t1 (#p1: parser k1 t1) (v1: validator p1)
  #k2 #t2 (#p2: parser k2 t2) (v2: validator p2)
: Tot (validator (p1 `nondep_then` p2))
=
  fun #_ #va a len err ->
    nondep_then_eq p1 p2 (AP.contents_of' va);
    let s1 = v1 a len err in
    let _ = gen_elim () in
    let verr = R.read err in
    if verr = 0ul
    then begin
      let ar = AP.split a s1 in
      let _ = gen_elim () in
      let len2 = len `SZ.size_sub` s1 in
      let s2 = v2 ar (len `SZ.size_sub` s1) err in
      let _ = gen_elim () in
      let _ = AP.join a ar in
      noop ();
      return (s1 `SZ.size_add` s2)
    end
    else
    begin
      noop ();
      return s1
    end
