open Globals
open Printf
open Rfc_ast

module SM = Map.Make (String)

type len_info = {
  mutable len_len: int;
  mutable min_len: int;
  mutable max_len: int;
  mutable min_count: int;
  mutable max_count: int;
  mutable vl : bool;
}

(* Recording the boundaries of variable length structures *)
let linfo : len_info SM.t ref = ref SM.empty

(* Storage of inlined types *)
let inliners: gemstone_t SM.t ref = ref SM.empty

let w = fprintf

let log256 k =
  if k <= 255 then 1
  else if k <= 65535 then 2
  else if k <= 16777215 then 3
  else 4

let tname (p:gemstone_t) : string =
  let aux = function
		| Enum (_, _, n) -> n
		| Struct (_, _, n) -> n
    | Typedef (_, _, n, _, _) -> n
	in String.uncapitalize_ascii (aux p)

let module_name (s:string) =
  if !prefix = "" || Str.last_chars !prefix 1 = "." then
    !prefix ^ (String.capitalize_ascii s)
  else
    !prefix ^ (String.uncapitalize_ascii s)

let attr_of = function
  | Enum (a, _, _) -> a
  | Struct (a, _, _) -> a
  | Typedef (a, _, _, _, _) -> a

let has_attr (a:attr list) (s:attr) = List.mem s a

let get_leninfo (t:typ) =
  try SM.find (String.uncapitalize_ascii t) !linfo
  with _ -> failwith ("Failed lookup for type "^t)

let li_add (s:string) (li:len_info) =
  printf "LINFO<%s>: vl=%s lenLen=%d minLen=%d maxLen=%d minCount=%d maxCount=%d\n"
    s (if li.vl then "yes" else "no") li.len_len li.min_len li.max_len li.min_count li.max_count;
  if SM.mem s !linfo then failwith (sprintf "Duplicate type definition: %s\n" s);
  linfo := SM.add s li !linfo

let basic_type = function
  | "opaque" | "uint8" | "uint16" | "uint24" | "uint32" -> true
  | _ -> false

let basic_bounds = function
  | "uint8" -> 1, 255 | "uint16" -> 2, 65535
  | "uint24" -> 3, 16777215 | "uint32" -> 4, 4294967295
  | _ -> failwith "not a base type"

let rec sizeof = function
  | TypeSelect(n, cl, def) ->
    let lil = (List.map (fun (_,ty) -> get_leninfo ty) cl)
              @ (match def with None -> [] | Some ty -> [get_leninfo ty]) in
    let li = { len_len = 0; min_len = max_int; max_len = 0; min_count = 0; max_count = 0; vl = false; } in
    List.iter (fun l ->
      li.min_len <- min li.min_len l.min_len;
      li.max_len <- max li.max_len l.max_len;
      if l.vl then li.vl <- true;
    ) lil; li
  | TypeSimple typ ->
    match typ with
    | "opaque"
    | "uint8"  -> { len_len = 0; min_len = 1; max_len = 1; min_count = 0; max_count = 0; vl = false; }
    | "uint16" -> { len_len = 0; min_len = 2; max_len = 2; min_count = 0; max_count = 0; vl = false; }
    | "uint24" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; }
    | "uint32" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; }
    | s ->
      let li = get_leninfo s in
      {li with len_len = li.len_len} (* shallow copy *)

let compile_type = function
  | "opaque"
  | "uint8" -> "U8.t"
  | "uint16" -> "U16.t"
  | "uint24" -> "U32.t"
  | "uint32" -> "U32.t"
  | t -> String.uncapitalize_ascii t

let metadata_combinator_name = function
  | "U8.t" -> "(LP.get_parser_kind LP.parse_u8).LP.parser_kind_metadata"
  | "U16.t" -> "(LP.get_parser_kind LP.parse_u16).LP.parser_kind_metadata"
  | "U32.t" -> "(LP.get_parser_kind LP.parse_u32).LP.parser_kind_metadata"
  | t -> t ^ "_parser_kind_metadata"

let pcombinator_name = function
  | "U8.t" -> "LP.parse_u8"
  | "U16.t" -> "LP.parse_u16"
  | "U32.t" -> "LP.parse_u32"
  | t -> t^"_parser"

let scombinator_name = function
  | "U8.t" -> "LP.serialize_u8"
  | "U16.t" -> "LP.serialize_u16"
  | "U32.t" -> "LP.serialize_u32"
  | t -> t^"_serializer"

let pcombinator32_name = function
  | "U8.t" -> "LP.parse32_u8"
  | "U16.t" -> "LP.parse32_u16"
  | "U32.t" -> "LP.parse32_u32"
  | t -> t^"_parser32"

let scombinator32_name = function
  | "U8.t" -> "LP.serialize32_u8"
  | "U16.t" -> "LP.serialize32_u16"
  | "U32.t" -> "LP.serialize32_u32"
  | t -> t^"_serializer32"

let size32_name = function
  | "U8.t" -> "LP.size32_u8"
  | "U16.t" -> "LP.size32_u16"
  | "U32.t" -> "LP.size32_u32"
  | t -> t^"_size32"

let add_field (tn:typ) (n:field) (ty:type_t) (v:vector_t) =
  let qname = if tn = "" then n else tn^"@"^n in
  let li = sizeof ty in
  let li' =
    match v with
    | VectorNone -> li
    | VectorFixed k ->
      {li with
        min_len = k;
        max_len = k;
        min_count = k / li.min_len;
        max_count = k / li.max_len;
      }
    | VectorVldata tn ->
      let (len_len, max_len) = basic_bounds tn in
      (*let min', max' = li.min_len, min li.max_len max_len in*)
      {li with len_len = len_len; min_len = len_len + li.min_len; max_len = len_len + li.max_len; vl = true; }
    | VectorSymbolic cst ->
      if tn = "" then failwith "Can't define a symbolic bytelen outide struct";
      let li' = get_leninfo (tn^"@"^cst) in
      (* Important: must reflect parse_bounded_vldata_strong_kind computation *)
      let max' = min li.max_len (match li'.max_len with
      | 1 -> 255 | 2 ->  65535 | 3 -> 16777215 | 4 -> 4294967295
      | _ -> failwith "bad vldata") in
      (* N.B. the len_len will be counted in the explicit length field *)
      {li' with vl = true; len_len = 0; min_len = li.min_len; max_len = max'; }
    | VectorRange (low, high) ->
      let h = log256 high in
      (if li.len_len + li.max_len = 0 then failwith ("Can't compute count bound on "^tn));
      { vl = true;
        min_count = low / (li.len_len + li.max_len);
        max_count = high / (li.len_len + li.min_len);
        len_len = h;
        min_len = h + low;
        max_len = h + high; }
      in
    li_add qname li'

let typedep = function
  | TypeSimple ty -> [ty]
  | TypeSelect (_, l, o) ->
    let l = List.map (fun (_, ty)->ty) l in
    match o with None -> l | Some ty -> ty :: l

let dedup l =
  let r = ref [] in
  List.iter (fun x -> if not (List.mem x !r) then r := x::!r) l;
  List.rev !r

let getdep (p:gemstone_t) : typ list =
  let tn = tname p in
  let dep =
    match p with
    | Enum (_, fl, n) ->
      let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
              with _ -> failwith ("Enum "^n^" is missing a representation hint") in
      let li = { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0;  vl = false; } in
      (match m with
      | EnumFieldAnonymous 255 -> li.min_len <- 1; li.max_len <- 1
      | EnumFieldAnonymous 65535 -> li.min_len <- 2; li.max_len <- 2
      | EnumFieldAnonymous 4294967295 -> li.min_len <- 4; li.max_len <- 4
      | EnumFieldAnonymous d -> failwith ("unsupported enum representation: "^string_of_int d)
      | _ -> failwith "impossible");
      li_add tn li; ([]:typ list list)
    | Struct (_, fl, _) ->
      let li = { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0;  vl = false; } in
      let dep = List.map (fun (al, ty, n, vec, def) ->
        add_field tn n ty vec;
        let lif = get_leninfo (tn^"@"^n) in
        li.vl <- li.vl || lif.vl;
        li.min_len <- li.min_len + lif.min_len;
        li.max_len <- li.max_len + lif.max_len;
        typedep ty) fl in
      li_add tn li; dep
    | Typedef (al, ty, n, vec, def) ->
      add_field "" (String.uncapitalize_ascii n) ty vec;
      [typedep ty]
    in
  dedup (List.flatten dep)

type parser_kind_metadata =
  | MetadataTotal
  | MetadataDefault

let write_api o i is_private (md: parser_kind_metadata) n bmin bmax =
  let parser_kind = match md with
    | MetadataDefault -> "LP.default_parser_kind.LP.parser_kind_metadata"
    | MetadataTotal   -> "({ LP.parser_kind_metadata_total = true })"
    in
  if is_private then
   begin
    w o "noextract let %s_parser_kind = LP.strong_parser_kind %d %d %s\n\n" n bmin bmax parser_kind
   end
  else
   begin
    w i "noextract let %s_parser_kind = LP.strong_parser_kind %d %d %s\n\n" n bmin bmax parser_kind;
    w i "noextract val %s_parser: LP.parser %s_parser_kind %s\n\n" n n n;
    w i "noextract val %s_serializer: LP.serializer %s_parser\n\n" n n;
    w i "noextract let %s_bytesize (x:%s) : GTot nat = Seq.length (%s_serializer x)\n\n" n n n;
    w i "inline_for_extraction val %s_parser32: LP.parser32 %s_parser\n\n" n n;
    w i "inline_for_extraction val %s_serializer32: LP.serializer32 %s_serializer\n\n" n n;
    w i "inline_for_extraction val %s_size32: LP.size32 %s_serializer\n\n" n n
   end

let rec compile_enum o i n (fl: enum_field_t list) (al:attr list) =
  let is_open = has_attr al "open" in
  let is_private = has_attr al "private" in

  let repr_t, int_z, parse_t, blen =
	  let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
		        with _ -> failwith ("Enum "^n^" is missing a representation hint") in
	  match m with
		| EnumFieldAnonymous 255 -> "U8.t", "z", "u8", 1
		| EnumFieldAnonymous 65535 -> "U16.t", "us", "u16", 2
		| EnumFieldAnonymous 4294967295 -> "U32.t", "ul", "u32", 4
		| _ -> failwith ("Cannot represent enum type "^n^" (only u8, u16, u32 supported)")
	in

begin if is_open then
	let rec collect_valid_repr int_z acc acc_rparen = function
	  | [] -> sprintf "%sfalse%s" acc acc_rparen
		| (EnumFieldAnonymous _) :: t -> collect_valid_repr int_z acc acc_rparen t
		| (EnumFieldSimple (_, i)) :: t ->
		  let acc' =
			  sprintf "%sv `%s_repr_eq` %d%s || (" acc n i int_z in
                  let acc_rparen' = sprintf ")%s" acc_rparen in
		  collect_valid_repr int_z acc' acc_rparen' t
		| (EnumFieldRange (_, i, j)) :: t ->
		  let acc' = acc in (* For now we treat enum ranges as unknown
			  (if acc = "" then acc else acc^" /\\ ")^
			  "(v < " ^ (string_of_int i) ^ int_z ^
				" \\/ v > " ^ (string_of_int j) ^ int_z ^ ")" in *)
                  let acc_rparen' = acc_rparen in
		  collect_valid_repr int_z acc' acc_rparen' t
		in

  let unknown_formula = collect_valid_repr int_z "" "" fl in

  w i "let %s_repr = %s\n" n repr_t;
  w i "inline_for_extraction let %s_repr_eq (x1 x2: %s_repr) : Tot bool = (x1 = x2)\n" n n;
  w i "let known_%s_repr (v:%s) : bool = %s\n\n" n repr_t unknown_formula;
  ()
end;
	w i "type %s : eqtype =\n" n;
	List.iter (function
	  | EnumFieldSimple (x, _) ->
		  w i "  | %s\n" (String.capitalize_ascii x)
		| _ -> ()) fl;
  begin if is_open then
	w i "  | Unknown_%s of (v:%s{not (known_%s_repr v)})\n\n" n repr_t n;
        ()
  end;
        

  (* Enum definition *)
	w o "inline_for_extraction let %s_enum : LP.enum %s %s =\n" n n repr_t;
	w o "  [@inline_let] let e = [\n";
	List.iter (function
	  | EnumFieldSimple (x, i) ->
		  w o "    %s, %d%s;\n" (String.capitalize_ascii x) i int_z
		| _ -> ()) fl;
	w o "  ] in\n";
	w o "  [@inline_let] let _ =\n";
	w o "    assert_norm (L.noRepeats (LP.list_map fst e))\n";
        w o "  in\n";
        w o "  [@inline_let] let _ = \n";
	w o "    assert_norm (L.noRepeats (LP.list_map snd e))\n";
	w o "  in e\n\n";

  (* Used in select() *)
  w o "inline_for_extraction let %s_repr_parser = %s\n\n" n (pcombinator_name repr_t);
  w o "inline_for_extraction let %s_repr_serializer = %s\n\n" n (scombinator_name repr_t);
  w o "inline_for_extraction let %s_repr_parser32 = %s\n\n" n (pcombinator32_name repr_t);
  w o "inline_for_extraction let %s_repr_serializer32 = %s\n\n" n (scombinator32_name repr_t);
  w o "inline_for_extraction let %s_repr_size32 = %s\n\n" n (size32_name repr_t);

  write_api o i is_private (if is_open then MetadataTotal else MetadataDefault) n blen blen;

  (* Synth *)
  if is_open then begin
	w o "inline_for_extraction let synth_%s (x:LP.maybe_enum_key %s_enum) : %s = \n" n n n;
	w o "  match x with\n";
	w o "  | LP.Known k -> k\n";
	w o "  | LP.Unknown y ->\n";
	w o "    [@inline_let] let v : %s = y in\n" repr_t;
	w o "    [@inline_let] let _ = assert_norm (LP.list_mem v (LP.list_map snd %s_enum) == known_%s_repr v) in\n" n n;
  w o "    Unknown_%s v\n\n" n;
	w o "inline_for_extraction let synth_%s_inv (x:%s) : LP.maybe_enum_key %s_enum = \n" n n n;
	w o "  match x with\n";
	w o "  | Unknown_%s y ->\n" n;
	w o "    [@inline_let] let v : %s = y in\n" repr_t;
	w o "    [@inline_let] let _ = assert_norm (LP.list_mem v (LP.list_map snd %s_enum) == known_%s_repr v) in\n" n n;
	w o "    LP.Unknown v\n";
	w o "  | x ->\n";
  w o "    [@inline_let] let x1 : %s = x in\n" n;
        w o "    [@inline_let] let _ : squash(not (Unknown_%s? x1) ==> LP.list_mem x1 (LP.list_map fst %s_enum)) =\n" n n;
        w o "      _ by (LP.synth_maybe_enum_key_inv_unknown_tac x1)\n";
        w o "    in\n";
  w o "    LP.Known (x1 <: LP.enum_key %s_enum)\n\n" n;
        w o "let lemma_synth_%s_inv' () : Lemma\n" n;
        w o "  (LP.synth_inverse synth_%s_inv synth_%s)\n" n n;
        w o "= LP.forall_maybe_enum_key %s_enum (fun x -> synth_%s_inv (synth_%s x) == x)\n" n n n;
        w o "    (_ by (LP.forall_maybe_enum_key_known_tac ()))\n";
        w o "    (_ by (LP.forall_maybe_enum_key_unknown_tac ()))\n\n";
	w o "let lemma_synth_%s_inj () : Lemma\n" n;
	w o "  (LP.synth_injective synth_%s) = \n" n;
        w o "  lemma_synth_%s_inv' ();\n" n;
        w o "  LP.synth_inverse_synth_injective synth_%s synth_%s_inv\n\n" n n;
  w o "#push-options \"--max_ifuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0\"\n";
	w o "let lemma_synth_%s_inv () : Lemma\n" n;
  w o "  (LP.synth_inverse synth_%s synth_%s_inv) = allow_inversion %s; ()\n\n" n n n;
  w o "#pop-options\n";
        ()
  end else begin
        w o "inline_for_extraction let synth_%s (x: LP.enum_key %s_enum) : Tot %s = x\n\n" n n n;
        w o "inline_for_extraction let synth_%s_inv (x: %s) : Tot (LP.enum_key %s_enum) =\n" n n n;
        w o "  [@inline_let] let _ : squash (LP.list_mem x (LP.list_map fst %s_enum)) =\n" n;
        w o "    _ by (LP.synth_maybe_enum_key_inv_unknown_tac x)\n";
        w o "  in\n";
        w o "  x\n\n";
	w o "let lemma_synth_%s_inj () : Lemma\n" n;
	w o "  (LP.synth_injective synth_%s) = ()\n\n" n;
	w o "let lemma_synth_%s_inv () : Lemma\n" n;
        w o "  (LP.synth_inverse synth_%s synth_%s_inv) = ()\n\n" n n;
  end;

  (* Parse *)
  let maybe = if is_open then "maybe_" else "" in
	w o "noextract let parse_%s%s_key : LP.parser _ (LP.%senum_key %s_enum) =\n" maybe n maybe n;
  w o "  LP.parse_%senum_key LP.parse_%s %s_enum\n\n" maybe parse_t n;
	w o "noextract let serialize_%s%s_key : LP.serializer parse_%s%s_key =\n" maybe n maybe n;
  w o "  LP.serialize_%senum_key LP.parse_%s LP.serialize_%s %s_enum\n\n" maybe parse_t parse_t n;

  (* Spec *)
	w o "noextract let %s_parser : LP.parser _ %s =\n" n n;
	w o "  lemma_synth_%s_inj ();\n" n;
  w o "  parse_%s%s_key `LP.parse_synth` synth_%s\n\n" maybe n n;
  w o "noextract let %s_serializer : LP.serializer %s_parser =\n" n n;
	w o "  lemma_synth_%s_inj ();\n  lemma_synth_%s_inv ();\n" n n;
	w o "  LP.serialize_synth _ synth_%s serialize_%s%s_key synth_%s_inv ()\n\n" n maybe n n;

  (* Intermediate *)
  w o "inline_for_extraction let parse32_%s%s_key : LP.parser32 parse_%s%s_key =\n" maybe n maybe n;
  w o "  FStar.Tactics.synth_by_tactic (LP.parse32_%senum_key_tac LP.parse32_%s %s_enum)\n\n" maybe parse_t n;
  w o "inline_for_extraction let %s_parser32 : LP.parser32 %s_parser =\n" n n ;
  w o "  lemma_synth_%s_inj ();\n" n;
  w o "  LP.parse32_synth _ synth_%s (fun x->synth_%s x) parse32_%s%s_key ()\n\n" n n maybe n;
	w o "inline_for_extraction let serialize32_%s%s_key : LP.serializer32 serialize_%s%s_key =\n" maybe n maybe n;
  begin if is_open then (* FIXME: harmonize the tactic name in LowParse *)
  w o "  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac\n"
  else
  w o "  FStar.Tactics.synth_by_tactic (LP.serialize32_enum_key_gen_tac\n"
  end;
  w o "    LP.serialize32_%s %s_enum)\n\n" parse_t n;
  w o "inline_for_extraction let %s_serializer32 : LP.serializer32 %s_serializer =\n" n n;
	w o "  lemma_synth_%s_inj ();\n  lemma_synth_%s_inv ();\n" n n;
  w o "  LP.serialize32_synth _ synth_%s _ serialize32_%s%s_key synth_%s_inv (fun x->synth_%s_inv x) ()\n\n" n maybe n n n;

  w o "let %s_size32 =\n" n;
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond %s_serializer %dul) in\n" n blen;
  w o "  LP.size32_constant %s_serializer %dul ()\n\n" n blen;
	()

and compile_select o i n tagn tagt taga cl def al =
  let is_private = has_attr al "private" in
  let li = get_leninfo n in
  let tn = compile_type tagt in
  w o "friend %s\n\n" (module_name tagt);
  w i "type %s : eqtype =\n" n;
  List.iter (fun (case, ty) -> w i "  | Case_%s of %s\n" case (compile_type ty)) cl;
  (match def with Some d -> w i "  | Case_Unknown_%s: v:%s_repr{not (known_%s_repr v)} -> %s -> %s\n" tn tn tn (compile_type d) n | _ -> ());

  w i "\ninline_for_extraction let tag_of_%s (x:%s) : %s = match x with\n" n n (compile_type tagt);
  List.iter (fun (case, ty) -> w i "  | Case_%s _ -> %s\n" case (String.capitalize_ascii case)) cl;
  (match def with Some d -> w i "  | Case_Unknown_%s v _ -> Unknown_%s v\n" tn tn | _ -> ());
  w i "\n";
  write_api o i is_private MetadataDefault n li.min_len li.max_len;

  (** FIXME(adl) for now the t_sum of open and closed sums are independently generated,
  we may try to share more of the declarations between the two cases **)
  (match def with
  | None ->
    (*** Closed Enum ***)
    w o "inline_for_extraction unfold let %s_as_enum_key (x:%s) : Pure (LP.enum_key %s_enum)\n" tn tn tn;
    w o "  (requires norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst %s_enum)) == true)" tn;
    w o " (ensures fun _ -> True) =\n";
    w o "  [@inline_let] let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst %s_enum)) in x\n\n" tn;

    w o "inline_for_extraction let key_of_%s (x:%s) : LP.enum_key %s_enum =\n" n n tn;
    w o "  match x with\n";
    List.iter (fun (case, ty) -> w o "  | Case_%s _ -> %s_as_enum_key %s\n" case tn (String.capitalize_ascii case)) cl;
    w o "\ninline_for_extraction let %s_case_of_%s (x:%s) : Type0 =\n" n tn tn;
    w o "  match x with\n";
    List.iter (fun (case, ty) -> w o "  | %s -> %s\n" (String.capitalize_ascii case) (compile_type ty)) cl;
    w o "\nunfold inline_for_extraction let to_%s_case_of_%s (x:%s) (#x':%s) (y:%s_case_of_%s x')" n tn tn tn n tn;
    w o "  : Pure (norm [delta_only [(`%%%s_case_of_%s)]; iota] (%s_case_of_%s x))\n" n tn n tn;
    w o "  (requires (x == x')) (ensures (fun y' -> y' == y)) =\n";
    w o "  [@inline_let] let _ = norm_spec [delta_only [(`%%%s_case_of_%s)] ; iota] (%s_case_of_%s x) in y\n\n" n tn n tn;
    w o "unfold inline_for_extraction let %s_refine (k:LP.enum_key %s_enum) (x:%s)\n" n tn n;
    w o "  : Pure (LP.refine_with_tag key_of_%s k)" n;
    w o "  (requires norm [delta; iota; zeta] (key_of_%s x) == k) (ensures (fun y -> y == x)) =\n" n;
    w o "  [@inline_let] let _ = norm_spec [delta; iota; zeta] (key_of_%s x) in x\n\n" n;
    w o "inline_for_extraction let synth_%s_cases (x:LP.enum_key %s_enum) (y:%s_case_of_%s x)\n" n tn n tn;
    w o "  : LP.refine_with_tag key_of_%s x =\n  match x with\n" n;
    List.iter (fun (case, ty) -> w o "  | %s -> %s_refine x (Case_%s (to_%s_case_of_%s %s y))\n"
      (String.capitalize_ascii case) n case n tn (String.capitalize_ascii case)) cl;
    w o "\nunfold inline_for_extraction let from_%s_case_of_%s (#x':%s) (x:%s)\n" n tn tn tn;
    w o "  (y: norm [delta_only [(`%%%s_case_of_%s)]; iota] (%s_case_of_%s x))\n" n tn n tn;
    w o "  : Pure (%s_case_of_%s x') (requires (x == x')) (ensures (fun y' -> y' == y)) =\n" n tn;
    w o "  [@inline_let] let _ = norm_spec [delta_only [(`%%%s_case_of_%s)] ; iota] (%s_case_of_%s x) in y\n\n" n tn n tn;
    w o "let synth_%s_cases_recip_pre (k:LP.enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k) : GTot bool =\n  match k with\n" n;
    List.iter (fun (case, ty) -> w o "  | %s -> Case_%s? x\n" (String.capitalize_ascii case) case) cl;
    w o "\nlet synth_%s_cases_recip_pre_intro (k:LP.enum_key %s_enum) (x:LP.refine_with_tag key_of_%s k)\n" n tn n;
    w o "  : Lemma (synth_%s_cases_recip_pre k x == true) =\n" n;
    w o "  norm_spec [delta; iota] (synth_%s_cases_recip_pre k x)\n\n" n;
    w o "inline_for_extraction let synth_%s_cases_recip (k:LP.enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k) : (%s_case_of_%s k) =\n  match k with\n" n n tn;
    List.iter (fun (case, ty) ->
      w o "  | %s -> [@inline_let] let _ = synth_%s_cases_recip_pre_intro %s x in\n"
        (String.capitalize_ascii case) n (String.capitalize_ascii case);
      w o "    (match x with Case_%s y -> (from_%s_case_of_%s %s y))\n"
        case n tn (String.capitalize_ascii case)
    ) cl;
    w o "inline_for_extraction let %s_sum = LP.make_sum' %s_enum key_of_%s\n" n tn n;
    w o "  %s_case_of_%s synth_%s_cases synth_%s_cases_recip\n" n tn n n;
    w o "  (_ by (LP.make_sum_synth_case_recip_synth_case_tac ()))\n";
    w o "  (_ by (LP.synth_case_synth_case_recip_tac ()))\n\n";
    ()

  | Some def ->
    (*** Open enum ***)
    let tyd = compile_type def in
    w o "inline_for_extraction unfold let known_%s_as_enum_key\n" tn;
    w o "  (x: %s { norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst %s_enum)) == true })\n" tn tn;
    w o "  : LP.enum_key %s_enum =\n" tn;
    w o "  [@inline_let] let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst %s_enum)) in x\n\n" tn;
    w o "let unknown_%s_as_enum_key (r:%s_repr) : Pure (LP.unknown_enum_repr %s_enum)\n" tn tn tn;
    w o "  (requires known_%s_repr r == false) (ensures fun _ -> True) =\n" tn;
    w o "  [@inline_let] let _ = assert_norm(LP.list_mem r (LP.list_map snd %s_enum) == known_%s_repr r) in r\n\n" tn tn;

    w o "inline_for_extraction let key_of_%s (x:%s) : LP.maybe_enum_key %s_enum =\n  match x with\n" n n tn;
    List.iter (fun (case, ty) ->
      let cn, ty0 = String.capitalize_ascii case, compile_type ty in
      w o "  | Case_%s _ -> LP.Known (known_%s_as_enum_key %s)\n" case tn cn
    ) cl;
    w o "  | Case_Unknown_%s v _ -> LP.Unknown (unknown_%s_as_enum_key v)\n\n" tn tn;

    w o "inline_for_extraction let %s_case_of_%s (x:%s) : Type0 =\n  match x with\n" n tn tn;
    List.iter (fun (case, ty) ->
      let cn, ty0 = String.capitalize_ascii case, compile_type ty in
      w o "  | %s -> %s\n" cn ty0
    ) cl;
    w o "  | Unknown_%s _ -> False\n" tn;

    w o "\nunfold inline_for_extraction let %s_value_type (x:LP.maybe_enum_key %s_enum) =\n" n tn;
    w o "  LP.dsum_type_of_tag' %s_enum %s_case_of_%s %s x\n\n" tn n tn tyd;
    w o "unfold inline_for_extraction let %s_refine (k:LP.maybe_enum_key %s_enum) (x:%s)\n" n tn n;
    w o "  : Pure (LP.refine_with_tag key_of_%s k)\n" n;
    w o "  (requires key_of_%s x == k) (ensures fun y -> y == x) =\n" n;
    w o "  [@inline_let] let _ = norm_spec [delta; iota; zeta] (key_of_%s x) in x\n\n" n;
    w o "unfold inline_for_extraction let %s_type_of_known_case (k: LP.enum_key %s_enum)\n" n tn;
    w o "  (x:%s) (q: squash ((k <: %s) == x))\n" tn tn;
    w o "  (#x' : LP.maybe_enum_key %s_enum) (y: %s_value_type x')\n" tn n;
    w o "  : Pure (norm [delta_only [(`%%%s_case_of_%s)]; iota] (%s_case_of_%s x))\n" n tn n tn;
    w o "  (requires (LP.Known k == x')) (ensures (fun y' -> y' == y)) =\n";
    w o "  [@inline_let] let _ = norm_spec [delta_only [(`%%%s_case_of_%s)]; iota] (%s_case_of_%s k) in y\n\n" n tn n tn;
    w o "unfold inline_for_extraction let %s_known_case (k: LP.enum_key %s_enum)\n" n tn;
    w o "  (x: %s) (y: norm [delta_only [(`%%%s_case_of_%s)]; iota] (%s_case_of_%s x))\n" tn n tn n tn;
    w o "  : Pure (%s_case_of_%s k) (requires (k == x)) (ensures (fun y' -> y' == y)) =\n" n tn;
    w o "  [@inline_let] let _ = norm_spec [delta_only [(`%%%s_case_of_%s)] ; iota] (%s_case_of_%s x) in y\n\n" n tn n tn;

    w o "inline_for_extraction let synth_known_%s_cases (k:LP.enum_key %s_enum)\n" n tn;
    w o "  (y:%s_value_type (LP.Known k)) : LP.refine_with_tag key_of_%s (LP.Known k) =\n  match k with\n" n n;
    List.iter (fun (case, ty) ->
      let cn, ty0 = String.capitalize_ascii case, compile_type ty in
      w o "  | %s ->\n    [@inline_let] let x : %s = Case_%s (%s_type_of_known_case k %s () y) in\n" cn n case n cn;
      w o "    [@inline_let] let _ = assert_norm (key_of_%s x == LP.Known %s) in\n" n cn;
      w o "    %s_refine (LP.Known %s) x\n" n cn
    ) cl;
    w o "\ninline_for_extraction let synth_%s_cases (x:LP.maybe_enum_key %s_enum)\n" n tn;
    w o "  (y:%s_value_type x) : LP.refine_with_tag key_of_%s x =\n  match x with\n" n n;
    w o "  | LP.Unknown v ->\n";
    w o "    [@inline_let] let x : %s = Case_Unknown_%s v y in\n" n tn;
    w o "    [@inline_let] let _ = assert_norm (key_of_%s x == LP.Unknown v) in\n" n;
    w o "    %s_refine (LP.Unknown v) x\n" n;
    w o "  | LP.Known k -> synth_known_%s_cases k y\n\n" n;

    w o "unfold inline_for_extraction let from_%s_case_of_%s (#x':%s) (x:%s)\n" n tn tn tn;
    w o "  (y: norm [delta_only [(`%%%s_case_of_%s)]; iota] (%s_case_of_%s x))\n" n tn n tn;
    w o "  : Pure (%s_case_of_%s x') (requires (x == x')) (ensures (fun y' -> y' == y)) =\n" n tn;
    w o "  [@inline_let] let _ = norm_spec [delta_only [(`%%%s_case_of_%s)] ; iota] (%s_case_of_%s x) in y\n\n" n tn n tn;

    w o "let synth_%s_cases_recip_pre (k:LP.maybe_enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k) : GTot bool =\n  match k with\n" n;
    List.iter (fun (case, ty) ->
      let cn, ty0 = String.capitalize_ascii case, compile_type ty in
      w o "  | LP.Known %s -> Case_%s? x\n" cn case
    ) cl;
    w o "  | LP.Known _ -> false\n";
    w o "  | LP.Unknown _ -> Case_Unknown_%s? x\n\n" tn;
    w o "let synth_%s_cases_recip_pre_intro' (x: %s) : Lemma (synth_%s_cases_recip_pre (key_of_%s x) x) = ()\n" n n n n;
    w o "let synth_%s_cases_recip_pre_intro (k:LP.maybe_enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k)\n" n;
    w o "  : Lemma (synth_%s_cases_recip_pre k x == true) =\n" n;
    w o "  synth_%s_cases_recip_pre_intro' x\n\n" n;
    w o "inline_for_extraction let synth_%s_cases_recip (k:LP.maybe_enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k) : (%s_value_type k) =\n  match k with\n" n n;
    w o "  | LP.Unknown z ->\n    [@inline_let] let _ = synth_%s_cases_recip_pre_intro (LP.Unknown z) x in\n" n;
    w o "    (match x with Case_Unknown_%s _ y ->  (y <: %s_value_type k))\n" tn n;
    w o "  | LP.Known k' ->\n    match k' with\n";
    List.iter (fun (case, ty) ->
      let cn, ty0 = String.capitalize_ascii case, compile_type ty in
      w o "    | %s -> [@inline_let] let _ = synth_%s_cases_recip_pre_intro (LP.Known %s) x in\n" cn n cn;
      w o "      (match x with Case_%s y -> %s_known_case k' %s y)\n" case n cn
    ) cl;
    w o  "   | _ -> [@inline_let] let _ = synth_%s_cases_recip_pre_intro (LP.Known k') in false_elim ()\n\n" n;

    w o "\ninline_for_extraction let %s_sum : LP.dsum = LP.make_dsum' %s_enum key_of_%s\n" n tn n;
    w o "  %s_case_of_%s %s synth_%s_cases synth_%s_cases_recip\n" n tn tyd n n;
    w o "  (_ by (LP.make_dsum_synth_case_recip_synth_case_known_tac ()))\n";
    w o "  (_ by (LP.make_dsum_synth_case_recip_synth_case_unknown_tac ()))\n";
    w o "  (_ by (LP.synth_case_synth_case_recip_tac ()))\n\n";
    ()
  ); (* End of open/close specialization *)

  let ktype = match def with
    | None -> sprintf "LP.sum_key %s_sum" n
    | Some def -> sprintf "LP.dsum_known_key %s_sum" n in

  w o "noextract let parse_%s_cases (x:%s)\n" n ktype;
  w o "  : k:LP.parser_kind & LP.parser k (%s_case_of_%s x) =\n  match x with\n" n tn;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> let u : (k: LP.parser_kind & LP.parser k (%s_case_of_%s %s)) = (| _, %s |) in u\n" cn n tn cn (pcombinator_name ty0)
  ) cl;
  w o "  | _ -> (| _, LP.parse_false |)\n\n";

  w o "\nnoextract let serialize_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.serializer (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> let u : LP.serializer (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (scombinator_name ty0)
  ) cl;
  w o "  | _ -> LP.serialize_false\n\n";

  w o "\ninline_for_extraction let parse32_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.parser32 (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> [@inline_let] let u : LP.parser32 (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (pcombinator32_name ty0)
  ) cl;
  w o "  | _ -> LP.parse32_false\n\n";

  w o "\ninline_for_extraction let serialize32_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.serializer32 (serialize_%s_cases x) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> [@inline_let] let u : LP.serializer32 (serialize_%s_cases %s) = %s in u\n" cn n cn (scombinator32_name ty0)
  ) cl;
  w o "  | _ -> LP.serialize32_false\n\n";

  w o "\ninline_for_extraction let size32_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.size32 (serialize_%s_cases x) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> [@inline_let] let u : LP.size32 (serialize_%s_cases %s) = %s in u\n" cn n cn (size32_name ty0)
  ) cl;
  w o "  | _ -> LP.size32_false\n\n";

  (* FIXME(adl) can't prove by normalization because of opaque kinds in interfaces *)
  let same_kind = match def with
    | None -> sprintf "  assert_norm (LP.parse_sum_kind (LP.get_parser_kind %s_repr_parser) %s_sum parse_%s_cases == %s_parser_kind);\n" tn n n n
    | Some dt -> sprintf "  assume(LP.parse_dsum_kind (LP.get_parser_kind %s_repr_parser) %s_sum parse_%s_cases %s_parser_kind == %s_parser_kind);\n" tn n n (compile_type dt) n
    in

  let annot = if is_private then " : LP.parser "^n^"_parser_kind "^n else "" in
  w o "\nlet %s_parser%s =\n%s" n annot same_kind;
  (match def with
  | None -> w o "  LP.parse_sum %s_sum %s_repr_parser parse_%s_cases\n\n" n tn n
  | Some dt -> w o "  LP.parse_dsum %s_sum %s_repr_parser parse_%s_cases %s\n\n" n tn n (pcombinator_name (compile_type dt)));

  let annot = if is_private then " : LP.serializer "^(pcombinator_name n) else "" in
  w o "let %s_serializer%s =\n%s" n annot same_kind;
  (match def with
  | None -> w o "  LP.serialize_sum %s_sum %s_repr_serializer serialize_%s_cases\n\n" n tn n
  | Some dt -> w o "  LP.serialize_dsum %s_sum %s_repr_serializer _ serialize_%s_cases _ %s\n\n" n tn n (scombinator_name (compile_type dt)));

  let annot = if is_private then " : LP.parser32 "^(pcombinator_name n) else "" in
  w o "let %s_parser32%s =\n%s" n annot same_kind;
  (match def with
  | None ->
    w o "  LP.parse32_sum %s_sum _ (_ by (LP.parse32_enum_key_tac %s_repr_parser32 %s_enum ()))\n" n tn tn;
    w o "    _ parse32_%s_cases (_ by (LP.enum_destr_tac %s_enum))\n\n" n tn
  | Some dt ->
    w o "  LP.parse32_dsum %s_sum %s_repr_parser32\n" n tn;
    w o "    _ parse32_%s_cases %s (_ by (LP.maybe_enum_destr_t_tac ()))\n\n" n (pcombinator32_name (compile_type dt)));

  let annot = if is_private then " : LP.serializer32 "^(scombinator_name n) else "" in
  w o "let %s_serializer32%s =\n%s" n annot same_kind;
  (match def with
  | None ->
    w o "  LP.serialize32_sum %s_sum _ (_ by (LP.serialize32_enum_key_gen_tac %s_repr_serializer32 %s_enum ()))" n tn tn;
    w o "    _ serialize32_%s_cases (_ by (LP.dep_enum_destr_tac ())) ()\n\n" n
  | Some dt ->
    w o "  LP.serialize32_dsum %s_sum _ (_ by (LP.serialize32_maybe_enum_key_tac %s_repr_serializer32 %s_enum ()))" n tn tn;
    w o "    _ _ serialize32_%s_cases %s (_ by (LP.dep_enum_destr_tac ())) ()\n\n" n (scombinator32_name (compile_type dt)));

  let annot = if is_private then " : LP.size32 "^n else "" in
  w o "let %s_size32%s =\n%s" n annot same_kind;
  (match def with
  | None ->
    w o "  LP.size32_sum %s_sum _ (_ by (LP.size32_enum_key_gen_tac %s_repr_size32 %s_enum ()))" n tn tn;
    w o "    _ size32_%s_cases (_ by (LP.dep_enum_destr_tac ())) ()\n\n" n
  | Some dt ->
    w o "  LP.size32_dsum %s_sum _ (_ by (LP.size32_maybe_enum_key_tac %s_repr_size32 %s_enum ()))\n" n tn tn;
    w o "    _ _ size32_%s_cases %s (_ by (LP.dep_enum_destr_tac ())) ()\n\n" n (size32_name (compile_type dt)));
  ()

and compile_typedef o i tn fn (ty:type_t) vec def al =
  let n = if tn = "" then String.uncapitalize_ascii fn else tn^"_"^fn in
  let qname = if tn = "" then String.uncapitalize_ascii fn else tn^"@"^fn in
  let is_private = has_attr al "private" in
  let li = get_leninfo qname in
  match ty with
  | TypeSelect (sn, cl, def) ->  () (*failwith "Unsupported select"*)
  | TypeSimple ty ->
    let ty0 = compile_type ty in
    match vec with
    (* Type aliasing *)
    | VectorNone ->
      w i "type %s : eqtype = %s\n\n" n ty0;
      write_api o i is_private MetadataDefault n li.min_len li.max_len;
      w o "noextract let %s_parser = %s\n\n" n (pcombinator_name ty0);
      w o "noextract let %s_serializer = %s\n\n" n (scombinator_name ty0);
      w o "inline_for_extraction let %s_parser32 = %s\n\n" n (pcombinator32_name ty0);
      w o "inline_for_extraction let %s_serializer32 = %s\n\n" n (scombinator32_name ty0);
      w o "inline_for_extraction let %s_size32 = %s\n\n" n (size32_name ty0)

    (* Should be replaced with Vldata during normalization *)
    | VectorSymbolic cst -> failwith "not supported"

    | VectorVldata vl ->
      (* N.B. for VectorVldata the size of the length is accounted outside the leninfo, unlike VectorRange *)
      let (len_len, _) = basic_bounds vl in
      let (min, max) = li.min_len, li.max_len in
      w i "noextract val %s_bytesize: %s -> GTot nat\n\n" n ty0;
      w o "let %s_bytesize x = Seq.length (LP.serialize %s x)\n\n" n (scombinator_name ty0);
      w i "type %s : eqtype = x:%s{let l = %s_bytesize x in %d <= l /\\ l <= %d}\n\n" n ty0 n min max;
      write_api o i is_private MetadataDefault n (len_len+li.min_len) (len_len+li.max_len);
      w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d %s\n\n" n min max (scombinator_name ty0);
      w o "let _ = assert_norm (%s' == %s)\n\n" n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_bounded_vldata_strong %d %d %s\n\n" min max (scombinator_name ty0);
      w o "let %s_parser = %s'_parser\n\n" n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_bounded_vldata_strong %d %d %s\n\n" min max (scombinator_name ty0);
      w o "let %s_serializer = %s'_serializer\n\n" n n;
      w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      w o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul %s %s\n\n" min min max max (scombinator_name ty0) (pcombinator32_name ty0);
      w o "let %s_parser32 = %s'_parser32\n\n" n n;
      w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      w o "  LP.serialize32_bounded_vldata_strong %d %d %s\n\n" min max (scombinator32_name ty0);
      w o "let %s_serializer32 = %s'_serializer32\n\n" n n;
      w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      (* assert_norm to be removed when moved to LowParse *)
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u32 4ul) in\n";
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u16 2ul) in\n";
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u8 1ul) in\n";
      w o "  LP.size32_bounded_vldata_strong %d %d %s %dul\n\n" min max (size32_name ty0) len_len;
      w o "let %s_size32 = %s'_size32\n\n" n n

    (* Fixed-length bytes *)
    | VectorFixed k when ty0 = "U8.t" ->
      w i "type %s : eqtype = lbytes %d\n\n" n k;
      write_api o i is_private MetadataTotal n li.min_len li.max_len;
      w o "noextract let %s_parser = LP.parse_flbytes %d\n\n" n k;
      w o "noextract let %s_serializer = LP.serialize_flbytes %d\n\n" n k;
      w o "inline_for_extraction let %s_parser32 = LP.parse32_flbytes %d %dul\n\n" n k k;
      w o "inline_for_extraction let %s_serializer32 = LP.serialize32_flbytes %d\n\n" n k;
      w o "inline_for_extraction let %s_size32 = LP.size32_constant %s_serializer %dul ()\n\n" n n k;

    (* Fixed length list *)
    | VectorFixed k when li.min_len = li.max_len ->
      w i "unfold let %s_pred (l:list %s) (n:nat) : GTot Type0 = L.length l == n\n" n ty0;
      w i "type %s : eqtype = l:list %s{%s_pred l %d}\n\n" n ty0 n li.min_count;
      write_api o i is_private MetadataDefault n li.min_len li.max_len;
      w o "type %s' = LP.array %s %d\n\n" n ty0 li.min_count;
      w o "private let eq () : Lemma (%s' == %s) = admit()\n" n n;
      w o "//  assert(%s'==%s) by (FStar.Tactics.norm [delta_only [`%%(LP.array); `%%(%s); `%%(%s')]])\n\n" n n n n;
      w o "noextract let %s'_parser = LP.parse_array %s %d %d\n\n" n (scombinator_name ty0) k li.min_count;
      w o "let %s_parser = eq(); LP.coerce _ %s'_parser\n\n" n n;
      w o "noextract let %s'_serializer = LP.serialize_array %s %d %d ()\n\n" n (scombinator_name ty0) k li.min_count;
      w o "let %s_serializer = eq(); LP.coerce _ %s'_serializer\n\n" n n;
      w o "inline_for_extraction let %s'_parser32 = LP.parse32_array %s %s %d %dul %d ()\n\n"
        n (scombinator_name ty0) (pcombinator32_name ty0) k k li.min_count;
      w o "let %s_parser32 = eq(); LP.coerce _ %s'_parser32\n\n" n n;
      w o "inline_for_extraction let %s'_serializer32 =\n" n;
      w o "  LP.serialize32_array #_ #_ #_ #%s %s %d %d ()\n\n" (scombinator_name ty0) (scombinator32_name ty0) k li.min_count;
      w o "let %s_serializer32 = eq(); LP.coerce _ %s'_serializer32\n\n" n n;
      w o "let %s_size32 = LP.size32_array %s %d %dul %d ()\n" n (scombinator_name ty0) k k li.min_count

    (* Fixed bytelen list of variable length elements *)
    | VectorFixed(k) ->
      w i "noextract val %s_list_bytesize: list %s -> GTot nat\n\n" n ty0;
      w o "let %s_list_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s) x)\n\n" n (scombinator_name ty0);
      w i "type %s : eqtype = l:list %s{%s_list_bytesize == %d}\n\n" n ty0 n k;
      write_api o i is_private MetadataDefault n li.min_len li.max_len;
      w o "type %s' = LP.parse_fldata_strong_t (LP.serialize_list _ %s) %d\n\n" n (scombinator_name ty0) k;
      w o "let _ = assert_norm (%s' == %s)\n\n" n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_fldata_strong (LP.serialize_list _ %s) %d\n\n" (scombinator_name ty0) k;
      w o "let %s_parser = %s'_parser\n\n" n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_fldata_strong (LP.serialize_list _ %s) %d\n\n" (scombinator_name ty0) k;
      w o "let %s_serializer = %s'_serializer\n\n" n n;
      w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      w o "  LP.parse32_fldata_strong (LP.serialize_list _ %s) (LP.parse32_list %s) %d %dul\n\n" (scombinator_name ty0) (pcombinator32_name ty0) k k;
      w o "let %s_parser32 = %s'_parser32\n\n" n n;
      w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      w o "  LP.serialize32_fldata_strong (LP.partial_serialize32_list _ %s %s ()) %d\n\n" (scombinator_name ty0) (scombinator32_name ty0) k;
      w o "let %s_serializer32 = %s'_serializer32\n\n" n n;
      w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      w o "  LP.size32_fldata_strong (LP.serialize_list _ %s) %d %dul\n\n" (scombinator_name ty0) k k;
      w o "let %s_size32 = %s'_size32\n\n" n n

    (* Variable length bytes *)
    | VectorRange (low, high) when ty0 = "U8.t" ->
      w i "type %s : eqtype = b:bytes{%d <= length b /\\ length b <= %d}\n\n" n low high;
      write_api o i is_private MetadataDefault n li.min_len li.max_len;
      w o "noextract let %s_parser = LP.parse_bounded_vlbytes %d %d\n\n" n low high;
      w o "noextract let %s_serializer = LP.serialize_bounded_vlbytes %d %d\n\n" n low high;
      w o "inline_for_extraction let %s_parser32 = LP.parse32_bounded_vlbytes %d %dul %d %dul\n\n" n low low high high;
      w o "inline_for_extraction let %s_serializer32 = LP.serialize32_bounded_vlbytes %d %d\n\n" n low high;
      w o "inline_for_extraction let %s_size32 = LP.size32_bounded_vlbytes %d %d %dul\n\n" n low high (log256 high)

    (* Variable length list of fixed-length elements *)
    | VectorRange (low, high) when li.min_len = li.max_len ->
      w i "type %s : eqtype = l:list %s{%d <= L.length l /\\ L.length l <= %d}" n ty0 li.min_count li.max_count;
      write_api o i is_private MetadataDefault n li.min_len li.max_len;
      w o "let %s_parser =\n" n;
      w o "  [@inline_let] let _ = assert_norm (LP.vldata_vlarray_precond %d %d %s %d %d == true) in\n" low high (pcombinator_name ty0) li.min_count li.max_count;
      w o "  LP.parse_vlarray %d %d %s %d %d ()\n\n" low high (scombinator_name ty0) li.min_count li.max_count;
      w o "let %s_serializer =\n" n;
      w o "  LP.serialize_vlarray %d %d %s %d %d ()\n\n" low high (scombinator_name ty0) li.min_count li.max_count;
      w o "let %s_parser32 =\n" n;
      w o "  LP.parse32_vlarray %d %dul %d %dul %s %s %d %d ()\n\n" low low high high (scombinator_name ty0) (pcombinator32_name ty0) li.min_count li.max_count;
      w o "let %s_serializer32 =\n" n;
      w o "  LP.serialize32_vlarray %d %d %s %d %d ()\n\n" low high (scombinator32_name ty0) li.min_count li.max_count;
      w o "let %s_size32 =\n" n;
      w o "  LP.size32_vlarray %d %d %s %d %d () %dul %dul\n\n" low high (scombinator_name ty0) li.min_count li.max_count li.len_len li.min_len

    (* Variable length list of variable length elements *)
    | VectorRange(low, high) ->
      let (min, max) = (li.min_len-li.len_len), (li.max_len-li.len_len) in
      w i "noextract val %s_list_bytesize: list %s -> GTot nat\n\n" n ty0;
      w o "let %s_list_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s) x)\n\n" n (scombinator_name ty0);
      w i "type %s : eqtype = l:list %s{let x = %s_list_bytesize l in %d <= x /\\ x <= %d}\n\n" n ty0 n min max;
      write_api o i is_private MetadataDefault n li.min_len li.max_len;
      w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d (LP.serialize_list _ %s)\n\n" n min max (scombinator_name ty0);
      w o "let _ = assert_norm (%s' == %s)\n\n" n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_bounded_vldata_strong %d %d (LP.serialize_list _ %s)\n\n" min max (scombinator_name ty0);
      w o "let %s_parser = %s'_parser\n\n" n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_bounded_vldata_strong %d %d (LP.serialize_list _ %s)\n\n" min max (scombinator_name ty0);
      w o "let %s_serializer = %s'_serializer\n\n" n n;
      w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      w o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul (LP.serialize_list _ %s) (LP.parse32_list %s)\n\n" min min max max (scombinator_name ty0) (pcombinator32_name ty0);
      w o "let %s_parser32 = %s'_parser32\n\n" n n;
      w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      w o "  LP.serialize32_bounded_vldata_strong %d %d (LP.partial_serialize32_list _ %s %s ())\n\n" min max (scombinator_name ty0) (scombinator32_name ty0);
      w o "let %s_serializer32 = %s'_serializer32\n\n" n n;
      w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      (* assert_norm to be removed when moved to LowParse *)
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u32 4ul) in\n";
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u16 2ul) in\n";
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u8 1ul) in\n";
      w o "  LP.size32_bounded_vldata_strong %d %d (LP.size32_list %s ()) %dul\n\n" min max (size32_name ty0) li.len_len;
      w o "let %s_size32 = %s'_size32\n\n" n n

and compile_struct o i n (fl: struct_field_t list) (al:attr list) =
  let li = get_leninfo n in
  let is_private = has_attr al "private" in

  (* Hoist all constructed types (select, vector, etc) into
     sub-definitions using private attribute in implementation *)
  let fields = List.map (fun (al, ty, fn, vec, def) ->
    let fn0 = String.uncapitalize_ascii fn in
    match ty, vec with
    | TypeSimple ty0, VectorNone ->
      (fn0, compile_type ty0)
    | _ ->
      compile_typedef o i n fn ty vec def ("private"::al);
      (fn0, sprintf "%s_%s" n fn)) fl in

  (* application type *)
  if fields = [] then
    w i "type %s : eqtype = lbytes 0\n\n" n
  else
   begin
    w i "type %s : eqtype = {\n" n;
    List.iter (fun (fn, ty) ->
      w i "  %s : %s;\n" fn ty) fields;
    w i "}\n\n"
   end;

  (* Tuple type for nondep_then combination *)
  let tuple = List.fold_left (fun acc (_, ty) -> if acc="" then ty else sprintf "(%s * %s)" acc ty) "" fields in
  let tuple = if fields = [] then "lbytes 0" else tuple in

  w o "type %s' = %s\n\n" n tuple;

  (* synthethizer for tuple type *)
  w o "inline_for_extraction let synth_%s (x: %s') : %s =\n" n n n;

  if fields = [] then
    w o "  x\n\n"
  else
   begin
    let tuple = List.fold_left (fun acc (fn, ty) -> if acc="" then fn else sprintf "(%s, %s)" acc fn) "" fields in
    w o "  let %s = x in\n  {\n" tuple;
    let tuple = List.fold_left (fun acc (fn, ty) -> sprintf "%s    %s = %s;\n" acc fn fn) "" fields in
    w o "%s  }\n\n" tuple;
    w o "inline_for_extraction let synth_%s_recip (x: %s) : %s' =\n" n n n;
    let tuple = List.fold_left (fun acc (fn, ty) -> if acc="" then "x."^fn else sprintf "(%s, x.%s)" acc fn) "" fields in
    w o "  %s\n\n" tuple
   end;

  (* Write parser API *)
  write_api o i is_private MetadataDefault n li.min_len li.max_len;

  (* synthetizer injectivity and inversion lemmas *)
  w o "let synth_%s_injective ()\n  : Lemma (LP.synth_injective synth_%s) = admit() // FIXME \n\n" n n;
  w o "let synth_%s_inverse ()\n  : Lemma (LP.synth_inverse synth_%s synth_%s_recip) =\n" n n n;
  w o "  assert_norm (LP.synth_inverse synth_%s synth_%s_recip)\n\n" n n;

  (* main parser combinator type *)
  w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
  if fields = [] then w o "  LP.parse_flbytes 0";
  let tuple = List.fold_left (
    fun acc (fn, ty) ->
      let c = pcombinator_name ty in
      if acc="" then c else sprintf "%s\n  `LP.nondep_then` %s" acc c
    ) "" fields in
  w o "  %s\n\n" tuple;

  w o "noextract let %s'_parser_kind = LP.get_parser_kind %s'_parser\n\n" n n;
  w o "let %s_parser =\n  synth_%s_injective ();\n  assert_norm (%s_parser_kind == %s'_parser_kind);\n" n n n n;
  w o "  %s'_parser `LP.parse_synth` synth_%s\n\n" n n;

  (* main serializer type *)
  w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
  if fields = [] then w o "  LP.serialize_flbytes 0";
  let tuple = List.fold_right (
    fun (fn, ty) acc ->
      let c = scombinator_name ty in
      if acc="" then c else sprintf "LP.serialize_nondep_then _ (%s) ()\n  _ %s" acc c
    ) (List.rev fields) "" in
  w o "  %s\n\n" tuple;
  w o "let %s_serializer =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize_synth _ synth_%s %s'_serializer synth_%s_recip ()\n\n" n n n;

  (* main parser32 *)
  w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
  if fields = [] then w o "  LP.parse32_flbytes 0 0ul";
  let tuple = List.fold_left (
    fun acc (fn, ty) ->
      let c = pcombinator32_name ty in
      if acc="" then c else sprintf "%s\n  `LP.parse32_nondep_then` %s" acc c
    ) "" fields in
  w o "  %s\n\n" tuple;
  w o "inline_for_extraction let %s_parser32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.parse32_synth _ synth_%s (fun x -> synth_%s x) %s'_parser32 ()\n\n" n n n;

  (* serialize32 *)
  w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
  if fields = [] then w o "  LP.serialize32_flbytes 0";
  let tuple = List.fold_right (
    fun (fn, ty) acc ->
      let c = scombinator32_name ty in
      if acc="" then c else sprintf "LP.serialize32_nondep_then (%s) ()\n  %s ()" acc c
    ) (List.rev fields) "" in
  w o "  %s\n\n" tuple;

  w o "inline_for_extraction let %s_serializer32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize32_synth _ synth_%s _ %s'_serializer32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;

  (* size32, the assert_norms should move to LP *)
  w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u32 4ul) in\n";
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u16 2ul) in\n";
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u8 1ul) in\n";

  if fields = [] then w o "  LP.size32_constant %s'_serializer 0ul ()" n;
  let tuple = List.fold_right (
    fun (fn, ty) acc ->
      let c = size32_name ty in
      if acc="" then c else sprintf "LP.size32_nondep_then (%s) ()\n  (%s)" acc c
    ) (List.rev fields) "" in
  w o "  %s\n\n" tuple;

  w o "let %s_size32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.size32_synth _ synth_%s _ %s'_size32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;
  ()

(* Rewrite {... uintX len; t value[len]; ...} into VectorVldata *)
let rec normalize_symboliclen o i sn (fl:struct_field_t list) : struct_field_t list =
  match fl with
  | [] -> []
  | (al, TypeSimple(tagt), tagn, VectorNone, None)
    :: (al', ty, n, VectorSymbolic k, None) :: r
    when tagn = k ->
      let h =
        match ty with
        | TypeSimple ty -> (al @ al', TypeSimple ty, n, VectorVldata tagt, None)
        | TypeSelect (sel, cl, def) ->
          let cl' = List.map (fun (c,t)->
            let etyp = sprintf "%s_%s_case_%s" sn n c in
            add_field "" etyp (TypeSimple t) (VectorVldata tagt);
            compile_typedef o i "" etyp (TypeSimple t) (VectorVldata tagt) None ("private"::al);
            (c, etyp)
          ) cl in
          let def' = match def with
            | None -> None
            | Some ty ->
              let etyp = sprintf "%s_%s_default" sn n in
              add_field "" etyp (TypeSimple ty) (VectorVldata tagt);
              compile_typedef o i "" etyp (TypeSimple ty) (VectorVldata tagt) None ("private"::al);
              Some etyp
            in
          (al @ al', TypeSelect(sel, cl', def'), n, VectorNone, None)
        in
      h :: (normalize_symboliclen o i sn r)
  | h :: t -> h :: (normalize_symboliclen o i sn t)

let compile o i (p:gemstone_t) =
  let n = tname p in
  let (fst, fsti) = !headers in

  (* .fsti *)
  w i "module %s\n\n" (module_name n);
  w i "open %s\n" !bytes;

  let depl = getdep p in
  let depl = List.filter (fun x -> not (basic_type x)) depl in
  let depl = List.map module_name depl in
  (List.iter (w i "open %s\n") depl);
  w i "\n";

  w i "module U8 = FStar.UInt8\n";
  w i "module U16 = FStar.UInt16\n";
  w i "module U32 = FStar.UInt32\n";
  w i "module LP = LowParse.SLow.Base\n";
  w i "module L = FStar.List.Tot\n";
  (List.iter (w i "%s\n") (List.rev fsti));
  w i "\n";

  (* .fst *)
  w o "module %s\n\n" (module_name n);
  w o "open %s\n" !bytes;
  w o "module U8 = FStar.UInt8\n";
  w o "module U16 = FStar.UInt16\n";
  w o "module U32 = FStar.UInt32\n";
	w o "module LP = LowParse.SLow\n";
	w o "module L = FStar.List.Tot\n";
  (List.iter (w o "%s\n") (List.rev fst));
  w o "\n";

	w o "#reset-options \"--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2\"\n\n";
	match p with
	| Enum(al, fl, _) ->  compile_enum o i n fl al
  | Struct(al, fl, _) ->
    let fl = normalize_symboliclen o i n fl in
    (match fl with
    | [ (al, TypeSimple(tagt), tagn, VectorNone, None);
        (al', TypeSelect (tagn', cases, def), seln, VectorNone, None) ] ->
        compile_select o i n tagn tagt al cases def al'
    | fl -> compile_struct o i n fl al)
  | Typedef(al, ty, _, vec, def) -> compile_typedef o i "" n ty vec def al

let compile_inline o i (p:gemstone_t) =
  if has_attr (attr_of p) "inline" then (
    printf "Warning: type %s will be inlined at use site!\n" (tname p);
    inliners := SM.add (tname p) p !inliners
  ) else compile o i p

let rfc_generate_fstar (p:Rfc_ast.prog) =
  let aux (p:gemstone_t) =
	  let n = tname p in
		let fn = sprintf "%s/%s.fst" !odir (module_name n) in
	  printf "Writing parsers for type <%s> to <%s>...\n" n fn;
		let o, i = try open_out fn, open_out (fn^"i")
               with _ -> failwith "Failed to create output file" in
		compile_inline o i p;
    close_out o
	in List.iter aux p
