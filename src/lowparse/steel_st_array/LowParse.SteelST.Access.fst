module LowParse.SteelST.Access
include LowParse.SteelST.Parse

module AP = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt

open Steel.ST.Util

let parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (Type u#1)
=
  (base: Type) ->
  (va: AP.v base byte) ->
  (a: byte_array base) ->
  ST SZ.size_t
    (AP.arrayptr a va)
    (fun res -> AP.arrayptr a va)
    (Some? (parse p (AP.contents_of va)))
    (fun res -> 
      match parse p (AP.contents_of' va) with
      | None -> False
      | Some (_, consumed) ->
        SZ.size_v res == consumed
)

let parsed_size_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.size_t)
: Pure (parsed_size p)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      SZ.size_v sz == k.parser_kind_low
    ))
    (ensures (fun _ -> True))
=
  fun base va a ->
  parser_kind_prop_equiv k p;
  noop ();
  return sz

let get_parsed_size
  (#base: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#vp: v base k t)
  (j: parsed_size p)
  (a: byte_array base)
: ST SZ.size_t
    (aparse p a vp)
    (fun res -> aparse p a vp)
    True
    (fun res -> SZ.size_v res == AP.length (array_of vp))
=
  let _ = elim_aparse p a in
  let res = j base _ a in
  let _ = intro_aparse p a in
  return res

let parse'
  (#a: Type)
  (#k: parser_kind)
  (p: parser k a)
  (b: bytes)
: GTot (option (a & nat))
= match parse p b with
  | None -> None
  | Some (v, c) -> Some (v, c)

#push-options "--z3rlimit 16"

let peek_strong_with_size
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (#va: AP.v base byte)
  (p: parser k t)
  (a: byte_array base)
  (sz: SZ.size_t)
: ST (byte_array base)
    (AP.arrayptr a va)
    (fun res -> exists_ (fun vp -> aparse p a vp `star` exists_ (fun vres -> AP.arrayptr res vres `star` pure (
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)
    ))))
    (k.parser_kind_subkind == Some ParserStrong /\
      begin match parse' p (AP.contents_of' va) with
      | None -> False
      | Some (_, consumed) -> (consumed <: nat) == SZ.size_v sz
      end
    )
    (fun _ -> True)
=
  noop ();
  assert (SZ.size_v sz <= Seq.length (AP.contents_of' va));
  parse_strong_prefix p (AP.contents_of' va) (AP.seq_slice (AP.contents_of' va) 0 (SZ.size_v sz));
  let res = AP.split a sz in
  let _ = gen_elim () in
  let _ = intro_aparse p a in
  noop ();
  return res

#pop-options

let peek_strong
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#va: AP.v base byte)
  (j: parsed_size p)
  (a: byte_array base)
: ST (byte_array base)
    (AP.arrayptr a va)
    (fun res -> exists_ (fun vp -> aparse p a vp `star` exists_ (fun vres -> AP.arrayptr res vres `star` pure (
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)
    ))))
    (k.parser_kind_subkind == Some ParserStrong /\
      Some? (parse p (AP.contents_of' va)))
    (fun _ -> True)
=
  let sz = j base _ a in
  let res = peek_strong_with_size p a sz in
  noop ();
  return res

/// useful for validators, which need to roll back peek after reading some contents
let unpeek_strong
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#vp: v base k t)
  (#vres: AP.v base byte)
  (a: byte_array base)
  (res: byte_array base)
: STGhost (AP.v base byte) opened
    (aparse p a vp `star` AP.arrayptr res vres)
    (fun va -> AP.arrayptr a va)
    (AP.adjacent (array_of vp) (AP.array_of vres) /\
    k.parser_kind_subkind == Some ParserStrong)
    (fun va ->
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed)
    )
= let va' = elim_aparse p a in
  let va = AP.join a res in
  let consumed = AP.length (array_of vp) in
  assert (AP.contents_of' vres `Seq.equal` AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)));
  assert (AP.contents_of' va' `Seq.equal` AP.seq_slice (AP.contents_of' va) 0 consumed);
  parse_strong_prefix p (AP.contents_of' va') (AP.contents_of' va);
  noop ();
  va

let peek_consumes_all
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: AP.v base byte)
  (a: byte_array base)
: STGhost (v base k t) opened
    (AP.arrayptr a va)
    (fun vp -> aparse p a vp)
    (k.parser_kind_subkind == Some ParserConsumesAll /\
      Some? (parse p (AP.contents_of' va)))
    (fun vp ->
      array_of vp == AP.array_of va /\
      parse' p (AP.contents_of' va) == Some (vp.contents, AP.length (AP.array_of va))
    )
=
  parser_kind_prop_equiv k p;
  intro_aparse p a
