let prelude : string =
"
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

(define-fun parse-empty ((x (Seq Int))) (Seq (Pair Int Int))
  (seq.unit (mk-pair 0 0))
)

(define-fun parse-u8 ((x (Seq Int))) (Seq (Pair Int Int))
  (if (= (seq.len x) 0)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit (mk-pair (seq.nth x 0) 1))
  )
)

(define-fun parse-fail ((x (Seq Int))) (Seq Int)
  (as seq.empty (Seq Int))
)
"

let mk_wrap_parser
  (name: string)
  (binders: string)
  (body: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
  Printf.sprintf
"(define-fun %s (%s(%s (Seq Int))) (Seq Int)
   (let ((%s (%s %s)))
     (if (= (seq.len %s) 0)
       (as seq.empty (Seq Int))
       (seq.unit (second (seq.nth %s 0)))
     )
   )
 )
"
  name
  binders
  input
  tmp
  body
  input
  tmp
  tmp

let mk_parse_ifthenelse
  (name: string)
  (binders: string)
  (cond: string)
  (f_then: string)
  (f_else: string)
: string
= let input = Printf.sprintf "%s-input" name in
  Printf.sprintf
"(define-fun %s (%s(%s (Seq Int))) (Seq Int)
   (if %s
     (%s %s)
     (%s %s)
   )
 )
"
  name
  binders
  input
  cond
  f_then
  input
  f_else
  input

let mk_parse_dtuple2
  (name: string)
  (binders: string)
  (dfst: string)
  (new_binder_name: string)
  (dsnd: string) (* already contains the new argument *)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp_has_tag = Printf.sprintf "%s-tmp-has-tag" name in
  let tmp_tag_result = Printf.sprintf "%s-tmp-tag-result" name in
  let tmp_payload = Printf.sprintf "%s-tmp-payload" name in
  Printf.sprintf
"(define-fun %s (%s(%s (Seq Int))) (Seq Int)
   (let ((%s (%s %s)))
     (if (= (seq.len %s) 0)
       (as seq.empty (Seq Int))
       (let ((%s (seq.nth %s 0)))
         (let ((%s (first %s)))
           (let ((%s (%s (seq.extract %s (second %s) (- (seq.len %s) (second %s))))))
             (if (= (seq.len %s) 0)
               (as seq.empty (Seq Int))
               (seq.unit (+ (second %s) (seq.nth %s 0)))
             )
           )
         )
       )
     )
   )
 )"
  name
  binders
  input
  tmp_has_tag
  dfst
  input
  tmp_has_tag
  tmp_tag_result
  tmp_has_tag
  new_binder_name
  tmp_tag_result
  tmp_payload
  dsnd
  input
  tmp_tag_result
  input
  tmp_tag_result
  tmp_payload
  tmp_tag_result
  tmp_payload

type binders = {
  binders: string;
  args: string;
}

let empty_binders : binders = {
  binders = "";
  args = "";
}

let push_binder (name: string) (typ: string) (b: binders) : binders = {
  binders = Printf.sprintf "(%s %s) %s" name typ b.binders;
  args = Printf.sprintf " %s%s" name b.args;
}

let mk_function_call (name: string) (b: binders) =
  Printf.sprintf "%s%s" name b.args

type reading = { call: string }
type not_reading = { call: string }

type 'a parser =
  (* name *) string ->
  (* binders *) binders ->
  (* out *) (string -> unit) ->
  'a

let parse_u8 : reading parser =
  fun _ _ _ -> { call = "parse-u8" }

let parse_empty : reading parser =
  fun _ _ _ -> { call = "parse-empty" }

let parse_fail : not_reading parser =
  fun _ _ _ -> { call = "parse-fail" }

let wrap_parser (p: reading parser) : not_reading parser =
  fun name binders out ->
    let name' = Printf.sprintf "%s-wrapped" name in
    let body = p name' binders out in
    out (mk_wrap_parser name binders.binders body.call);
    { call = mk_function_call name binders }

let parse_ifthenelse (cond: string) (pthen: not_reading parser) (pelse: not_reading parser) =
  fun name binders out ->
    let name_then = Printf.sprintf "%s-then" name in
    let body_then = pthen name_then binders out in
    let name_else = Printf.sprintf "%s-else" name in
    let body_else = pelse name_else binders out in
    out (mk_parse_ifthenelse name binders.binders cond body_then.call body_else.call);
    { call = mk_function_call name binders }

let parse_dtuple2 (tag: reading parser) (new_binder: string) (payload: not_reading parser) : not_reading parser =
  fun name binders out ->
    let name_tag = Printf.sprintf "%s-tag" name in
    let body_tag = tag name_tag binders out in
    let binders' = push_binder new_binder "Int" binders in (* TODO: support more types *)
    let name_payload = Printf.sprintf "%s-payload" name in
    let body_payload = payload name_payload binders' out in
    out (mk_parse_dtuple2 name binders.binders body_tag.call new_binder body_payload.call);
    { call = mk_function_call name binders }

let interlude =
"
(declare-const witness (Seq Int))
(assert (forall ((j Int))
  (if (and (<= 0 j) (< j (seq.len witness)))
    (let ((witnessj (seq.nth witness j)))
      (and (<= 0 witnessj) (< witnessj 256))
    )
    true
  )
))
"

let mk_get_first_witness (name1: string) (name2: string) : string =
  Printf.sprintf
"
(push)
(assert (and (= (seq.len (%s witness)) 1) (= (seq.len (%s witness)) 0)))
(check-sat)
"
  name1
  name2

let tee ch s =
  print_string s;
  output_string ch s;
  flush ch

let read_lisp_from ch =
  let rec aux accu =
    let s = input_line ch in
    print_endline s;
    let accu' = accu ^ s in
    match Sexplib.Sexp.parse accu' with
    | Sexplib.Sexp.Done (res, _) -> (accu', res)
    | _ -> aux accu' (* FIXME: leverage incrementality instead of starting over *)
  in
  aux ""

let mk_want_another_witness letbinding p =
  Printf.sprintf
"(assert (not (= (seq.extract witness 0 (seq.nth (%s witness) 0)) (let %s (seq.extract witness 0 (seq.nth (%s witness) 0))))))
 (check-sat)
"
  p
  letbinding
  p

let rec want_other_witnesses ((from_z3, to_z3) as z3) p i =
  print_endline ";; From z3";
  let status = input_line from_z3 in
  print_endline status;
  if status = "sat" then begin
    print_endline ";; To z3";
    tee to_z3 "(get-value (witness))\n";
    print_endline ";; From z3";
    let (letbinding, _) = read_lisp_from from_z3 in
    if i <= 0
    then ()
    else begin
      print_endline ";; To z3";
      tee to_z3 (mk_want_another_witness letbinding p);
      want_other_witnesses z3 p (i - 1)
    end
  end

let witnesses_for ((from_z3, to_z3) as z3) name1 name2 extra =
  Printf.printf ";; Witnesses that work with %s but not with %s\n" name1 name2;
  print_endline ";; To z3";
  tee to_z3 (mk_get_first_witness name1 name2);
  want_other_witnesses z3 name1 extra;
  print_endline ";; To z3";
  tee to_z3 "(pop)\n"

let dialogue p1 name1 p2 name2 extra =
  let buf = ref "" in
  let out x = buf := Printf.sprintf "%s%s" !buf x in
  let name1 = (p1 name1 empty_binders out).call in
  let name2 = (p2 name2 empty_binders out).call in
  let (from_z3, to_z3) as z3 = Unix.open_process "z3 -in" in
  print_endline ";; To z3";
  tee to_z3 prelude;
  tee to_z3 !buf;
  tee to_z3 interlude;
  witnesses_for z3 name1 name2 extra;
  witnesses_for z3 name2 name1 extra;
  let _ = Unix.close_process z3 in
  ()

let _ =
  let test1 = parse_dtuple2 parse_u8 "x" (parse_ifthenelse "(< x 12)" parse_fail (parse_dtuple2 parse_u8 "y" (parse_ifthenelse "(> (+ x y) 28)" parse_fail (wrap_parser parse_empty)))) in
  let test2 = parse_dtuple2 parse_u8 "x" (parse_ifthenelse "(< x 10)" parse_fail (parse_dtuple2 parse_u8 "y" (parse_ifthenelse "(> (+ x y) 30)" parse_fail (wrap_parser parse_empty)))) in
  dialogue test1 "test1" test2 "test2" 5
