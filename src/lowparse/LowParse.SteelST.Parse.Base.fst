module LowParse.SteelST.Parse.Base
module AP = LowParse.SteelST.ArrayPtr.Base
include LowParse.Spec.Base

(* For now, we only support parsers with ParserStrong or ParserConsumesAll subkind. *)

inline_for_extraction
let byte_array : Type0 = AP.t byte

let array_prop (k: parser_kind) (a: AP.array byte) : Tot prop =
  let l = AP.length a in
  k.parser_kind_low <= l /\
  (Some? k.parser_kind_high ==> l <= Some?.v k.parser_kind_high)

[@@erasable]
noeq
type v (k: parser_kind) (t: Type) = {
  array_perm : (AP.array byte); // & SP.perm);
  contents : t;
  array_perm_prf: squash (array_prop k ((* fst *) array_perm));
}

let array_t (k: parser_kind) : Tot Type =
  (array: AP.array byte { array_prop k array })

let array_of (#k: parser_kind) (#t: Type) (w: v k t) : GTot (array_t k) =
  w.array_perm

let array_of' (#k: parser_kind) (#t: Type) (w: v k t) : GTot (AP.array byte) =
  array_of w

let arrayptr_parse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va: AP.v byte)
: GTot (option (v k t))
=
  let s = AP.contents_of' va in
  match parse p s with
  | None -> None
  | Some (vt, consumed) ->
    if consumed = Seq.length s
    then
      Some ({
        array_perm = AP.array_of va;
        contents = vt;
        array_perm_prf =
          begin
            parser_kind_prop_equiv k p
          end;
      })
    else
      None

let arrayptr_parse_injective
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va1 va2: AP.v byte)
: Lemma
  (requires (
    let pa1 = arrayptr_parse p va1 in
    let pa2 = arrayptr_parse p va2 in
    pa1 == pa2 /\ (Some? pa1 \/ Some? pa2)
  ))
  (ensures (
    va1 == va2
  ))
= match arrayptr_parse p va1, arrayptr_parse p va2 with
  | Some _, Some _ ->
    parse_injective p (AP.contents_of va1) (AP.contents_of va2)
  | _ -> ()
