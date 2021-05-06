module LowParse.SteelSel.Access
include LowParse.SteelSel.VParse

module S = Steel.Memory
module SE = Steel.SelEffect
module SEA = Steel.SelEffect.Atomic
module A = Steel.SelArray
module AP = Steel.SelArrayPtr

module U32 = FStar.UInt32

let parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type0
= (a: byte_array) ->
  SE.SteelSel U32.t
    (vparse p a)
    (fun _ -> vparse p a)
    (fun _ -> True)
    (fun h res h' ->
      h' (vparse p a) == h (vparse p a) /\
      U32.v res == A.length (h (vparse p a)).array
    )

let parsed_size_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: U32.t)
: Pure (parsed_size p)
    (requires (
      k.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_metadata == Some ParserKindMetadataTotal /\
      U32.v sz == k.parser_kind_low
    ))
    (ensures (fun _ -> True))
=
  fun a ->
  elim_vparse p a;
  let _ = SEA.gget (AP.varrayptr a) in // FIXME: WHY WHY WHY is this needed?
  parser_kind_prop_equiv k p;
  intro_vparse p a;
  SEA.return sz

let strong_parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type0
= (a: byte_array) ->
  SE.SteelSel U32.t
    (AP.varrayptr a)
    (fun _ -> AP.varrayptr a)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      h' (AP.varrayptr a) == s /\
      begin match parse p s.AP.contents with
      | None -> False
      | Some (_, consumed) -> U32.v res == consumed
      end
    )

let get_parsed_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: strong_parsed_size p)
: Tot (parsed_size p)
=
  fun a ->
  elim_vparse p a;
  let _ = SEA.gget (AP.varrayptr a) in // FIXME: WHY WHY WHY is this needed?
  let res = j a in
  intro_vparse p a;
  SEA.return res

let peek_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: strong_parsed_size p)
  (a: byte_array)
: SE.SteelSel byte_array
    (AP.varrayptr a)
    (fun res -> vparse p a `SE.star` AP.varrayptr res)
    (fun _ -> k.parser_kind_subkind == Some ParserStrong)
    (fun h res h' ->
      let c_a = h (AP.varrayptr a) in
      let c_a' = h' (vparse p a) in
      let c_res = h' (AP.varrayptr res) in
      let consumed = A.length c_a'.array in
      A.merge_into c_a'.array c_res.AP.array c_a.AP.array /\
      is_byte_repr p c_a'.contents (Seq.slice c_a.AP.contents 0 consumed) /\
      c_res.AP.contents == Seq.slice c_a.AP.contents consumed (A.length c_a.AP.array)
    )
=
  let c_a = SEA.gget (AP.varrayptr a) in
  let n = j a in
  parse_strong_prefix p c_a.AP.contents (Seq.slice c_a.AP.contents 0 (U32.v n)); 
  let res = AP.split a n in
  intro_vparse p a;
  SEA.return res

(* TODO: move to Steel.SelArray *)
val memcpy
  (dst: byte_array)
  (src: byte_array)
  (n: U32.t)
: SE.SteelSel byte_array
    (AP.varrayptr dst `SE.star` AP.varrayptr src)
    (fun _ -> AP.varrayptr dst `SE.star` AP.varrayptr src)
    (fun h ->
      U32.v n <= A.length (h (AP.varrayptr src)).AP.array /\
      U32.v n <= A.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h res h' ->
      let s = h (AP.varrayptr src) in
      let d = h (AP.varrayptr dst) in
      let d' = h' (AP.varrayptr dst) in
      res == dst /\
      h' (AP.varrayptr src) == s /\
      d'.AP.array == d.AP.array /\
      U32.v n <= A.length d.AP.array /\
      U32.v n <= A.length s.AP.array /\
      d'.AP.contents `Seq.equal` (Seq.slice s.AP.contents 0 (U32.v n) `Seq.append` Seq.slice d.AP.contents (U32.v n) (A.length d.AP.array))
    )
    (decreases (U32.v n))

let rec memcpy dst src n =
  if n = 0ul
  then SEA.return dst
  else begin
    let j = n `U32.sub` 1ul in
    let c = AP.index src j in
    AP.upd dst j c;
    memcpy dst src j
  end

val copy_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: byte_array)
  (n: U32.t)
: SE.SteelSel unit
    (vparse p src `SE.star` AP.varrayptr dst)
    (fun _ -> vparse p src `SE.star` vparse p dst)
    (fun h ->
      U32.v n == A.length (h (vparse p src)).array /\
      U32.v n == A.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h _ h' ->
      let s = h (vparse p src) in
      let d = h (AP.varrayptr dst) in
      let d' = h' (vparse p dst) in
      U32.v n == A.length s.array /\
      U32.v n == A.length d.AP.array /\
      h' (vparse p src) == s /\
      d'.array == d.AP.array /\
      d'.contents == s.contents
    )

let copy_exact p src dst n =
  elim_vparse p src;
  let _ = memcpy dst src n in
  let gs : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr src) in
  assert (U32.v n == A.length gs.AP.array); // FIXME: WHY WHY WHY is this needed for the equality on n in the postcond
  let gd : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr dst) in
  assert (U32.v n == A.length gd.AP.array); // same here
  assert (gd.AP.contents `Seq.equal` gs.AP.contents); // ok, this is expected because of `equal`
  intro_vparse p src;
  intro_vparse p dst

val copy_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: byte_array)
  (dst: byte_array)
: SE.SteelSel byte_array
    (vparse p src `SE.star` AP.varrayptr dst)
    (fun res -> vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res)
    (fun h ->
      A.length (h (vparse p src)).array <= A.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h res h' ->
      SE.can_be_split (vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res) (vparse p src) /\ // FIXME: WHY WHY WHY?
      SE.can_be_split (vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res) (vparse p dst) /\ // same here
      begin
        let s = h (vparse p src) in
        let d = h (AP.varrayptr dst) in
        let d' = h' (vparse p dst) in
        let r = h' (AP.varrayptr res) in
        h' (vparse p src) == s /\
        A.merge_into d'.array r.AP.array d.AP.array /\
        d'.contents == s.contents /\
        A.length s.array == A.length d'.array /\ // TODO: this should be a consequence of the equality of the contents, via parser injectivity
        r.AP.contents == Seq.slice d.AP.contents (A.length s.array) (A.length d.AP.array)
      end
    )

let copy_strong #_ #_ #p j src dst =
  let n = j src in
  let res = AP.split dst n in
  let _ = SEA.gget (AP.varrayptr dst) in // FIXME: WHY WHY WHY?
  copy_exact p src dst n;
  SEA.reveal_star_3 (vparse p src) (vparse p dst) (AP.varrayptr res); // for can_be_split
  SEA.return res
