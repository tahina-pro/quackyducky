module LowParse.SteelST.ArrayPtr
friend LowParse.SteelST.ArrayPtr.Base
module SA = Steel.ST.Array

[@__reduce__]
let arrayptr1 (#elt: _) (v: v elt) : Tot vprop =
  SA.pts_to v.v_array.array_ptr v.v_array.array_perm v.v_contents

[@__reduce__]
let arrayptr0 (#elt: _) (r: t elt) (v: v elt) : Tot vprop =
  arrayptr1 v `star` pure (
    SA.ptr_of v.v_array.array_ptr == r
  )

let arrayptr r v = arrayptr0 r v

let join #_ #a #vl #vr al ar =
  rewrite (arrayptr al vl) (arrayptr0 al vl);
  rewrite (arrayptr ar vr) (arrayptr0 ar vr);
  rewrite
    (SA.pts_to vr.v_array.array_ptr vr.v_array.array_perm vr.v_contents)
    (SA.pts_to vr.v_array.array_ptr vl.v_array.array_perm vr.v_contents);
  let _ = gen_elim () in
  SA.ghost_join vl.v_array.array_ptr vr.v_array.array_ptr ();
  let res = {
    v_array = merge (array_of vl) (array_of vr);
    v_contents = Seq.append vl.v_contents vr.v_contents;
  }
  in
  rewrite (arrayptr0 al res) (arrayptr al res);
  res

let gsplit #_ #_ #v x i =
  rewrite (arrayptr x v) (arrayptr0 x v);
  let _ = gen_elim () in
  let _ = SA.ghost_split _ i in
  let _ = gen_elim () in
  let vl_array = {
    array_ptr = SA.split_l v.v_array.array_ptr i;
    array_perm = v.v_array.array_perm;
    array_base_len = v.v_array.array_base_len;
  }
  in
  let vl = {
    v_array = vl_array;
    v_contents = Seq.slice v.v_contents 0 (SZ.v i);
  }
  in
  let vr_array = {
    array_ptr = SA.split_r v.v_array.array_ptr i;
    array_perm = v.v_array.array_perm;
    array_base_len = v.v_array.array_base_len;
  }
  in
  let vr = {
    v_array = vr_array;
    v_contents = Seq.slice v.v_contents (SZ.v i) (Seq.length v.v_contents);
  }
  in
  let res = Ghost.hide (SA.ptr_of vr_array.array_ptr) in
  SA.ptr_shift_zero x;
  rewrite (SA.pts_to (SA.split_l _ _) _ _) (arrayptr1 vl);
  rewrite (arrayptr0 x vl) (arrayptr x vl);
  rewrite (SA.pts_to (SA.split_r _ _) _ _) (arrayptr1 vr);
  rewrite (arrayptr0 res vr) (arrayptr res vr);
  res

let split' #_ #vl #vr x i x' =
  rewrite (arrayptr x vl) (arrayptr0 x vl);
  rewrite (arrayptr x' vr) (arrayptr0 x' vr);
  let _ = gen_elim () in
  let res = SA.ptr_shift x i in
  SA.ptr_base_offset_inj res x';
  rewrite (arrayptr0 x vl) (arrayptr x vl);
  rewrite (arrayptr0 res vr) (arrayptr res vr);
  return res

let index #_ #v r i =
  rewrite (arrayptr r v) (arrayptr0 r v);
  let _ = gen_elim () in
  let a = (| r, Ghost.hide (SA.length v.v_array.array_ptr) |) in
  rewrite (arrayptr1 v) (SA.pts_to a v.v_array.array_perm v.v_contents);
  let res = SA.index a i in
  rewrite (SA.pts_to _ _ _) (arrayptr1 v);
  rewrite (arrayptr0 r v) (arrayptr r v);
  return res

let upd #elt #v r i x =
  rewrite (arrayptr r v) (arrayptr0 r v);
  let _ = gen_elim () in
  let a = (| r, Ghost.hide (SA.length v.v_array.array_ptr) |) in
  rewrite (arrayptr1 v) (SA.pts_to a full_perm v.v_contents);
  SA.upd a i x;
  let s' = vpattern_replace_erased (fun s -> SA.pts_to _ _ s) in
  let res = {
    v_array = v.v_array;
    v_contents = s';
  }
  in
  rewrite (SA.pts_to _ _ _) (arrayptr1 res);
  rewrite (arrayptr0 r res) (arrayptr r res);
  return res

#set-options "--ide_id_info_off"

let share
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
= rewrite (arrayptr a x) (arrayptr0 a x);
  let _ = gen_elim () in
  SA.share x.v_array.array_ptr _ p1 p2;
  let res1 = {
    v_array = set_array_perm x.v_array p1;
    v_contents = x.v_contents;
  }
  in
  let res2 = {
    v_array = set_array_perm x.v_array p2;
    v_contents = x.v_contents;
  }
  in
  let res = Ghost.hide (res1, res2) in
  rewrite (SA.pts_to _ p1 _) (arrayptr1 (fst res));
  rewrite (arrayptr0 a (fst res)) (arrayptr a (fst res));
  rewrite (SA.pts_to _ _ _) (arrayptr1 (snd res));
  rewrite (arrayptr0 a (snd res)) (arrayptr a (snd res));
  res

let gather
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
= rewrite (arrayptr a x1) (arrayptr0 a x1);
  rewrite (arrayptr a x2) (arrayptr0 a x2);
  let _ = gen_elim () in
  rewrite (SA.pts_to _ x2.v_array.array_perm _) (SA.pts_to x1.v_array.array_ptr x2.v_array.array_perm x2.v_contents);
  SA.gather x1.v_array.array_ptr x1.v_array.array_perm x2.v_array.array_perm;
  let res = {
    v_array = set_array_perm x1.v_array (x1.v_array.array_perm `Steel.FractionalPermission.sum_perm` x2.v_array.array_perm);
    v_contents = x1.v_contents;
  }
  in
  rewrite (SA.pts_to _ _ _) (arrayptr1 res);
  rewrite (arrayptr0 a res) (arrayptr a res);
  res
