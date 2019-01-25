open Globals
open Printf
open Rfc_ast

module SM = Map.Make (String)

type parser_kind_metadata =
  | MetadataTotal
  | MetadataFail
  | MetadataDefault

(* Special case of select over a tag *)
type tag_select_t =
  attr list * attr list * typ * field * field * typ * (typ * typ) list * typ option

let string_of_parser_kind_metadata = function
  | MetadataTotal -> "total"
  | MetadataFail -> "fail"
  | MetadataDefault -> "default"

type len_info = {
  mutable len_len: int;
  mutable min_len: int;
  mutable max_len: int;
  mutable min_count: int;
  mutable max_count: int;
  mutable vl : bool;
  mutable meta: parser_kind_metadata;
}

(* Recording the boundaries of variable length structures *)
let linfo : len_info SM.t ref = ref SM.empty

(* Storage of enum fields for select *)
let fields: (enum_field_t list * bool) SM.t ref = ref SM.empty

(* Substitution map for global type rewriting *)
let subst: typ SM.t ref = ref SM.empty

(* Storage of types that require staged parsing (e.g. implicit tag) *)
let erased: unit SM.t ref = ref SM.empty

let w = fprintf

let log256 k =
  if k <= 255 then 1
  else if k <= 65535 then 2
  else if k <= 16777215 then 3
  else 4

let tname (lower:bool) (p:gemstone_t) : string =
  let n = match p with
		| Enum (_, _, n) -> n
		| Struct (_, _, n) -> n
    | Typedef (_, _, n, _, _) -> n
	  in
  if lower then String.uncapitalize_ascii n else n

let module_name (s:string) =
  if !prefix = "" || Str.last_chars !prefix 1 = "." then
    !prefix ^ (String.capitalize_ascii s)
  else
    !prefix ^ (String.uncapitalize_ascii s)

let open_files n =
  let fn = sprintf "%s/%s.fst" !odir (module_name n) in
  printf "Writing parsers for type <%s> to <%s>...\n" n fn;
  try open_out fn, open_out (fn^"i")
  with _ -> failwith "Failed to create output file"

let close_files o i =
  close_out o; close_out i

let attr_of = function
  | Enum (a, _, _) -> a
  | Struct (a, _, _) -> a
  | Typedef (a, _, _, _, _) -> a

let has_attr (a:attr list) (s:attr) = List.mem s a

let get_leninfo (t:typ) =
  try SM.find (String.uncapitalize_ascii t) !linfo
  with _ -> failwith ("Failed lookup for type "^t)

let li_add (s:string) (li:len_info) =
  printf "LINFO<%s>: vl=%s lenLen=%d minLen=%d maxLen=%d minCount=%d maxCount=%d meta=%s\n"
    s (if li.vl then "yes" else "no") li.len_len li.min_len li.max_len li.min_count li.max_count
    (string_of_parser_kind_metadata li.meta);
  if SM.mem s !linfo then failwith (sprintf "Duplicate type definition: %s\n" s);
  linfo := SM.add s li !linfo

let basic_type = function
  | "opaque" | "uint8" | "uint16" | "uint24" | "uint32" -> true
  | "Empty" | "Fail" -> true
  | _ -> false

let basic_bounds = function
  | "uint8" -> 1, 255 | "uint16" -> 2, 65535
  | "uint24" -> 3, 16777215 | "uint32" -> 4, 4294967295
  | s -> failwith (s^" is not a base type and can't be used as symbolic length")

let rec sizeof = function
  | TypeSelect(n, cl, def) ->
    let lil = (List.map (fun (_,ty) -> sizeof (TypeSimple ty)) cl)
      @ (match def with None -> [] | Some ty -> [sizeof (TypeSimple ty)]) in
    let li = { len_len = 0; min_len = max_int; max_len = 0; min_count = 0; max_count = 0;
      vl = true; meta = MetadataTotal } in
    List.iter (fun l ->
      match l.meta with
      | MetadataFail -> (* Ignore size for the length boundaries *)
        if li.meta <> MetadataFail then li.meta <- MetadataDefault
      | md ->
        li.min_len <- min li.min_len l.min_len;
        li.max_len <- max li.max_len l.max_len;
        (if l.vl then
          (if li.len_len = 0 then li.len_len <- l.len_len;
          if l.len_len <> li.len_len then li.vl <- false)
        else li.vl <- false);
        if li.meta = MetadataFail || md = MetadataDefault then li.meta <- md
    ) lil;
    (* Propagating Fail outside of select() is not supported in LowParse *)
    if li.meta = MetadataFail then failwith (sprintf "Type select(%s) cannot parse any data" n);
    li
  | TypeSimple typ ->
    match typ with
    | "opaque"
    | "uint8"  -> { len_len = 0; min_len = 1; max_len = 1; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "uint16" -> { len_len = 0; min_len = 2; max_len = 2; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "uint24" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "uint32" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "Empty" -> { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "Fail" -> { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0; vl = false; meta = MetadataFail }
    | s ->
      let li = get_leninfo s in
      {li with len_len = li.len_len} (* shallow copy *)

let compile_type = function
  | "opaque"
  | "uint8" -> "U8.t"
  | "uint16" -> "U16.t"
  | "uint24" -> "U32.t"
  | "uint32" -> "U32.t"
  | "Empty" -> "unit"
  | "Fail" -> "(squash False)"
  | t -> String.uncapitalize_ascii t

let pcombinator_name = function
  | "U8.t" -> "LPI.parse_u8"
  | "U16.t" -> "LPI.parse_u16"
  | "U32.t" -> "LPI.parse_u32"
  | "unit" -> "LP.parse_empty"
  | "(squash False)" -> "LP.parse_false"
  | t -> t^"_parser"

let scombinator_name = function
  | "U8.t" -> "LP.serialize_u8"
  | "U16.t" -> "LP.serialize_u16"
  | "U32.t" -> "LP.serialize_u32"
  | "unit" -> "LP.serialize_empty"
  | "(squash False)" -> "LP.serialize_false"
  | t -> t^"_serializer"

let pcombinator32_name = function
  | "U8.t" -> "LP.parse32_u8"
  | "U16.t" -> "LP.parse32_u16"
  | "U32.t" -> "LP.parse32_u32"
  | "unit" -> "LP.parse32_empty"
  | "(squash False)" -> "LP.parse32_false"
  | t -> t^"_parser32"

let scombinator32_name = function
  | "U8.t" -> "LP.serialize32_u8"
  | "U16.t" -> "LP.serialize32_u16"
  | "U32.t" -> "LP.serialize32_u32"
  | "unit" -> "LP.serialize32_empty"
  | "(squash False)" -> "LP.serialize32_false"
  | t -> t^"_serializer32"

let size32_name = function
  | "U8.t" -> "LP.size32_u8"
  | "U16.t" -> "LP.size32_u16"
  | "U32.t" -> "LP.size32_u32"
  | "unit" -> "LP.size32_empty"
  | "(squash False)" -> "LP.size32_false"
  | t -> t^"_size32"

let validator_name = function
  | "U8.t" -> "(LL.validate_u8 ())"
  | "U16.t" -> "(LL.validate_u16 ())"
  | "U32.t" -> "(LL.validate_u32 ())"
  | "unit" -> "(LL.validate_empty ())"
  | "(squash False)" -> "(LL.validate_false ())"
  | t -> t^"_validator"

let jumper_name = function
  | "U8.t" -> "LL.jump_u8"
  | "U16.t" -> "LL.jump_u16"
  | "U32.t" -> "LL.jump_u32"
  | "unit" -> "LL.jump_empty"
  | "(squash False)" -> "LL.jump_false"
  | t -> t^"_jumper"

let bytesize_call t x = match t with
  | "U8.t" -> "1"
  | "U16.t" -> "2"
  | "U32.t" -> "4"
  | "unit" -> "0"
  | "(squash False)" -> "0"
  | _ -> sprintf "(%s_bytesize (%s))" t x

let bytesize_eq_call t x = match t with
  | "U8.t" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_u8 (%s)) == 1))" x
  | "U16.t" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_u16 (%s)) == 2))" x
  | "U32.t" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (%s)) == 4))" x
  | "unit" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_empty (%s)) == 0))" x
  | "(squash False)" -> sprintf "(assert False)"
  | _ -> sprintf "(%s_bytesize_eq (%s))" t x

let leaf_reader_name = function
  | "U8.t" -> "LL.read_u8"
  | "U16.t" -> "LL.read_u16"
  | "U32.t" -> "LL.read_u32"
  | _ -> failwith "leaf_reader_name: should only be called for enum repr"

let leaf_writer_name = function
  | "U8.t" -> "LL.write_u8"
  | "U16.t" -> "LL.write_u16"
  | "U32.t" -> "LL.write_u32"
  | _ -> failwith "leaf_writer_name: should only be called for enum repr"

let add_field al (tn:typ) (n:field) (ty:type_t) (v:vector_t) =
  let qname = if tn = "" then n else tn^"@"^n in
  let li = sizeof ty in
  let li' =
    if has_attr al "implicit" then sizeof (TypeSimple "Empty") else
    match v with
    | VectorNone -> li
    | VectorFixed k ->
      {li with
        min_len = k;
        max_len = k;
        min_count = k / li.min_len;
        max_count = k / li.max_len;
        (* FIXME: should be li.meta but only bytes are total in LowParse currently *)
        meta = match ty with
               | TypeSimple ("uint8") | TypeSimple ("opaque") -> MetadataTotal
               | TypeSimple ("Fail") -> MetadataFail
               | _ -> MetadataDefault;
      }
    | VectorVldata tn ->
      let (len_len, max_len) = basic_bounds tn in
      let max' = len_len + min max_len li.max_len in
      (*let min', max' = li.min_len, min li.max_len max_len in*)
      let meta' = if li.meta = MetadataFail then li.meta else MetadataDefault in
      {li with len_len = len_len; min_len = len_len + li.min_len; max_len = max'; vl = true; meta = meta' }
    | VectorSymbolic cst ->
      if tn = "" then failwith "Can't define a symbolic bytelen outide struct";
      let li' = get_leninfo (tn^"@"^cst) in
      (* Important: must reflect parse_bounded_vldata_strong_kind computation *)
      let max' = min li.max_len (match li'.max_len with
      | 1 -> 255 | 2 ->  65535 | 3 -> 16777215 | 4 -> 4294967295
      | _ -> failwith "bad vldata") in
      let meta' = if li.meta = MetadataFail then li.meta else MetadataDefault in
      (* N.B. the len_len will be counted in the explicit length field *)
      {li' with vl = true; len_len = 0; min_len = li.min_len; max_len = max'; meta = meta' }
    | VectorRange (low, high, repr) ->
      let h = if repr = 0 then log256 high else repr in
      (if h < log256 high then failwith (sprintf "Can't represent <%d..%d> over %d bytes" low high repr));
      (if li.len_len + li.max_len = 0 then failwith ("Can't compute count bound on "^tn));
      { vl = true;
        min_count = low / (li.len_len + li.max_len);
        max_count = high / (li.len_len + li.min_len);
        len_len = h;
        min_len = h + low;
        max_len = h + high;
        meta = if li.meta = MetadataFail then li.meta else MetadataDefault;
      } in
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

let getdep (toplevel:bool) (p:gemstone_t) : typ list =
  let tn = tname toplevel p in
  let dep =
    match p with
    | Enum (a, fl, n) ->
      if not toplevel then failwith "Invalid internal rewrite of an enum";
      let meta = if has_attr a "open" then MetadataTotal else MetadataDefault in
      let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
              with _ -> failwith ("Enum "^n^" is missing a representation hint") in
      let li = { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0;  vl = false; meta = meta; } in
      (match m with
      | EnumFieldAnonymous 255 -> li.min_len <- 1; li.max_len <- 1
      | EnumFieldAnonymous 65535 -> li.min_len <- 2; li.max_len <- 2
      | EnumFieldAnonymous 4294967295 -> li.min_len <- 4; li.max_len <- 4
      | EnumFieldAnonymous d -> failwith ("unsupported enum representation: "^string_of_int d)
      | _ -> failwith "impossible");
      li_add tn li; ([]:typ list list)
    | Struct (_, [(al, ty, _, vec, def)], n)
    | Typedef (al, ty, n, vec, def) ->
      if toplevel then add_field al "" (String.uncapitalize_ascii n) ty vec;
      [typedep ty]
    | Struct (_, fl, _) ->
      if not toplevel then failwith "invalid internal rewrite of a struct";
      let li = { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0;  vl = false; meta = MetadataTotal } in
      let dep = List.map (fun (al, ty, n, vec, def) ->
        add_field al tn n ty vec;
        let lif = get_leninfo (tn^"@"^n) in
        li.min_len <- li.min_len + lif.min_len;
        li.max_len <- li.max_len + lif.max_len;
        if lif.meta = MetadataDefault then li.meta <- MetadataDefault;
        typedep ty) fl in
      li_add tn li; dep
    in
  dedup (List.flatten dep)

let need_validator (md: parser_kind_metadata) bmin bmax =
  match md with
  | MetadataTotal -> bmin <> bmax
  | _ -> true

let need_jumper bmin bmax =
  bmin <> bmax

let get_api_params p n =
  let (* (parg, ptyp, pparse, pser) as *) res = match p with
    | None -> "", n, sprintf "%s_parser" n, sprintf "%s_serializer" n
    | Some t ->
      sprintf " (k:%s)" (compile_type t), sprintf "(%s k)" n,
      sprintf "(%s_parser k)" n, sprintf "(%s_serializer k)" n
    in
  res

let write_bytesize o ?param:(p=None) is_private n =
  let (parg, ptyp, pparse, pser) = get_api_params p n in
  if is_private then ()
  else
    if p = None then begin
        w o "let %s_bytesize (x:%s) : GTot nat = Seq.length (%s x)\n\n" n n pser;
        w o "let %s_bytesize_eq x = ()\n\n" n;
    end else begin
        w o "let %s_bytesize%s (x:%s k) : GTot nat = let s = %s in Seq.length (s x)\n\n" n parg n pser;
        w o "let %s_bytesize_eq k x = ()\n\n" n;
    end
    
let write_api o i ?param:(p=None) is_private (md: parser_kind_metadata) n bmin bmax =
  let (parg, ptyp, pparse, pser) = get_api_params p n in
  let parser_kind = match md with
    | MetadataTotal   -> "(Some LP.ParserKindMetadataTotal)"
    | MetadataFail -> "(Some LP.ParserKindMetadataFail)"
    | MetadataDefault -> "None"
    in
  w i "inline_for_extraction noextract let %s_parser_kind = LP.strong_parser_kind %d %d %s\n\n" n bmin bmax parser_kind;
  w i "noextract val %s_parser%s: LP.parser %s_parser_kind %s\n\n" n parg n ptyp;
  if is_private then ()
  else
   begin
    w i "noextract val %s_serializer%s: LP.serializer %s\n\n" n parg pparse;
    if p = None then begin
      w i "noextract val %s_bytesize (x:%s) : GTot nat\n\n" n n;
      w i "noextract val %s_bytesize_eq (x:%s) : Lemma (%s_bytesize x == Seq.length (LP.serialize %s x))\n\n" n n n pser;
      ()
    end else begin
      w i "noextract val %s_bytesize%s (x:%s k) : GTot nat\n\n" n parg n;
      w i "noextract val %s_bytesize_eq%s (x: %s k) : Lemma (%s_bytesize k x == Seq.length (LP.serialize (%s) x))\n\n" n parg n n pser;
      ()
    end;
    w i "val %s_parser32%s: LP.parser32 %s\n\n" n parg pparse;
    w i "val %s_serializer32%s: LP.serializer32 %s\n\n" n parg pser;
    w i "val %s_size32%s: LP.size32 %s\n\n" n parg pser;
    if need_validator md bmin bmax then
      w i "inline_for_extraction val %s_validator%s: LL.validator %s\n\n" n parg pparse
    else
      w i "inline_for_extraction let %s_validator%s: LL.validator %s = LL.validate_total_constant_size %s %dul ()\n\n" n parg pparse pparse bmin;
    if need_jumper bmin bmax then
      w i "inline_for_extraction val %s_jumper%s: LL.jumper %s\n\n" n parg pparse
    else
      w i "inline_for_extraction let %s_jumper%s: LL.jumper %s = LL.jump_constant_size %s %dul ()\n\n" n parg pparse pparse bmin;
    ()
   end

let rec compile_enum o i n (fl: enum_field_t list) (al:attr list) =
  let is_open = has_attr al "open" in
  let is_private = has_attr al "private" in
  fields := SM.add n (fl, is_open) !fields;

  let repr_t, int_z, parse_t, blen =
	  let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
		        with _ -> failwith ("Enum "^n^" is missing a representation hint") in
	  match m with
		| EnumFieldAnonymous 255 -> "U8.t", "z", "u8", 1
		| EnumFieldAnonymous 65535 -> "U16.t", "us", "u16", 2
		| EnumFieldAnonymous 4294967295 -> "U32.t", "ul", "u32", 4
		| _ -> failwith ("Cannot represent enum type "^n^" (only u8, u16, u32 supported)")
	in

  if is_open then
   begin
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
    w i "let known_%s_repr (v:%s) : bool = %s\n\n" n repr_t unknown_formula
   end;

	w i "type %s =\n" n;
	List.iter (function
	  | EnumFieldSimple (x, _) ->
		  w i "  | %s\n" (String.capitalize_ascii x)
		| _ -> ()) fl;
  if is_open then
	  w i "  | Unknown_%s of (v:%s{not (known_%s_repr v)})\n\n" n repr_t n
  else w i "\n";

	w i "let string_of_%s = function\n" n;
  List.iter (function
	  | EnumFieldSimple (x, _) ->
		  w i "  | %s -> \"%s\"\n" (String.capitalize_ascii x) x
		| _ -> ()) fl;
  if is_open then
	  w i "  | Unknown_%s _ -> \"Unknown_%s\"\n\n" n n
  else w i "\n";

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
  w o "noextract let %s_repr_parser = %s\n\n" n (pcombinator_name repr_t);
  w o "noextract let %s_repr_serializer = %s\n\n" n (scombinator_name repr_t);
  w o "inline_for_extraction noextract let %s_repr_parser32 = %s\n\n" n (pcombinator32_name repr_t);
  w o "inline_for_extraction noextract let %s_repr_serializer32 = %s\n\n" n (scombinator32_name repr_t);
  w o "inline_for_extraction noextract let %s_repr_size32 = %s\n\n" n (size32_name repr_t);
  w o "inline_for_extraction noextract let %s_repr_validator = %s\n\n" n (validator_name repr_t);
  w o "inline_for_extraction noextract let %s_repr_jumper = %s\n\n" n (jumper_name repr_t);
  w o "inline_for_extraction noextract let %s_repr_reader = %s\n\n" n (leaf_reader_name repr_t);
  w o "inline_for_extraction noextract let %s_repr_writer = %s\n\n" n (leaf_writer_name repr_t);

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
  write_bytesize o is_private n;

  (* Intermediate *)
  w o "let parse32_%s%s_key : LP.parser32 parse_%s%s_key =\n" maybe n maybe n;
  w o "  FStar.Tactics.synth_by_tactic (LP.parse32_%senum_key_tac LP.parse32_%s %s_enum)\n\n" maybe parse_t n;
  w o "let %s_parser32 : LP.parser32 %s_parser =\n" n n ;
  w o "  lemma_synth_%s_inj ();\n" n;
  w o "  LP.parse32_synth _ synth_%s (fun x->synth_%s x) parse32_%s%s_key ()\n\n" n n maybe n;
	w o "let serialize32_%s%s_key : LP.serializer32 serialize_%s%s_key =\n" maybe n maybe n;
  begin if is_open then (* FIXME: harmonize the tactic name in LowParse *)
  w o "  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac\n"
  else
  w o "  FStar.Tactics.synth_by_tactic (LP.serialize32_enum_key_gen_tac\n"
  end;
  w o "    LP.serialize32_%s %s_enum)\n\n" parse_t n;
  w o "let %s_serializer32 : LP.serializer32 %s_serializer =\n" n n;
	w o "  lemma_synth_%s_inj ();\n  lemma_synth_%s_inv ();\n" n n;
  w o "  LP.serialize32_synth _ synth_%s _ serialize32_%s%s_key synth_%s_inv (fun x->synth_%s_inv x) ()\n\n" n maybe n n n;

  w o "let %s_size32 =\n" n;
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond %s_serializer %dul) in\n" n blen;
  w o "  LP.size32_constant %s_serializer %dul ()\n\n" n blen;

  (* Low: validator *)
  begin
    if is_open then
      () (* validator not needed, since maybe_enum_key is total constant size *)
    else begin
      w o "inline_for_extraction let validate_%s%s_key : LL.validator parse_%s%s_key =\n" maybe n maybe n;
      w o "  LL.validate_enum_key %s_repr_validator %s_repr_reader %s_enum (_ by (LP.maybe_enum_destr_t_tac ()))\n\n" n n n;
      w o "inline_for_extraction let %s_validator =\n" n;
      w o "  lemma_synth_%s_inj ();\n" n;
      w o "  LL.validate_synth validate_%s%s_key synth_%s ()\n\n" maybe n n
      end
  end;

  (* Low: reader *)
  begin
    if is_open then
      begin
        w o "inline_for_extraction let read_maybe_%s_key : LL.leaf_reader parse_maybe_%s_key =\n" n n;
        w o "  LL.read_maybe_enum_key %s_repr_reader %s_enum (_ by (LP.maybe_enum_destr_t_tac ()))\n\n" n n
      end
    else
      begin
        w o "inline_for_extraction let read_%s_key : LL.leaf_reader parse_%s_key =\n" n n;
        w o "  LL.read_enum_key %s_repr_reader %s_enum (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n n
      end
  end;
  w i "inline_for_extraction val %s_reader: LL.leaf_reader %s_parser\n\n" n n;
          w o "let %s_reader =\n" n;
  w o " [@inline_let] let _ = lemma_synth_%s_inj () in\n" n;
  w o " LL.read_synth' parse_%s%s_key synth_%s read_%s%s_key ()\n\n" maybe n n maybe n;

  (* Low: writer *)
  w o "inline_for_extraction let write_%s%s_key : LL.leaf_writer_strong serialize_%s%s_key =\n" maybe n maybe n;
  w o "  LL.write_%senum_key %s_repr_writer %s_enum (_ by (LP.enum_repr_of_key_tac %s_enum))\n\n" maybe n n n;
  w i "inline_for_extraction val %s_writer: LL.leaf_writer_strong %s_serializer\n\n" n n;
  w o "let %s_writer =\n" n;
  w o "  [@inline_let] let _ = lemma_synth_%s_inj (); lemma_synth_%s_inv () in\n" n n;
  w o "  LL.write_synth write_%s%s_key synth_%s synth_%s_inv (fun x -> synth_%s_inv x) ()\n\n" maybe n n n n;

  (* bytesize lemma *)
  w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d) [SMTPat (%s_bytesize x)]\n\n" n n n blen n;
  w o "let %s_bytesize_eqn x = %s_bytesize_eq x; assert (FStar.Seq.length (LP.serialize %s_serializer x) <= %d); assert (%d <= FStar.Seq.length (LP.serialize %s_serializer x))\n\n" n n n blen blen n;
  ()

and compile_select o i n seln tagn tagt taga cl def al =
  let is_private = has_attr al "private" in
  let is_implicit = has_attr taga "implicit" in
  let li = get_leninfo n in
  let taglen = (get_leninfo tagt).max_len in (* assume tag is constant-sized *)
  let tn = compile_type tagt in
  let cprefix = String.capitalize_ascii seln in

  (* We need to substitute the whole type for encapsulating vlbytes *)
  if is_implicit then erased := SM.add n () !erased;

  (* Complete undefined cases in enum with Fail *)
  let (enum_fields, is_open) = try SM.find tn !fields with
    | _ -> failwith ("Type "^tn^" is not an enum and cannot be used in select()") in

  (* Auto-complete omitted cases, with default case if provided *)
  let cl = (fun l -> let r = ref [] in
    let dty = match def with Some d -> d | None -> "Fail" in
    let li_dty = sizeof (TypeSimple dty) in
    List.iter (function
      | EnumFieldSimple(cn, _) ->
        if not (List.mem_assoc cn l) then (
          if li_dty.meta <> MetadataTotal then li.meta <- MetadataDefault;
          r := (cn, dty) :: !r
        )
      | _ -> ()) enum_fields; l @ !r) cl in

  let def = if is_open then
    (if def = None then failwith ("Missing default case of open sum "^n) else def)
    else None in

  let prime = if is_implicit then "'" else "" in
  w o "friend %s\n\n" (module_name tagt);
  w i "type %s%s =\n" n prime;
  List.iter (fun (case, ty) -> w i "  | %s_%s of %s\n" cprefix case (compile_type ty)) cl;
  (match def with Some d -> w i "  | %s_Unknown_%s: v:%s_repr{not (known_%s_repr v)} -> x:%s -> %s%s\n" cprefix tn tn tn (compile_type d) n prime | _ -> ());

  w i "\ninline_for_extraction let tag_of_%s (x:%s%s) : %s = match x with\n" n n prime (compile_type tagt);
  List.iter (fun (case, ty) -> w i "  | %s_%s _ -> %s\n" cprefix case (String.capitalize_ascii case)) cl;
  (match def with Some d -> w i "  | %s_Unknown_%s v _ -> Unknown_%s v\n" cprefix tn tn | _ -> ());
  w i "\n";

  if is_implicit then
    w i "type %s (k:%s) = x:%s'{tag_of_%s x == k}\n\n" n (compile_type tagt) n n;

  write_api o i is_private li.meta n li.min_len li.max_len ~param:(if is_implicit then Some tagt else None);
  let need_validator = need_validator li.meta li.min_len li.max_len in
  let need_jumper = need_jumper li.min_len li.max_len in

  (* FIXME(adl) scalability is still not great *)
  w o "// Need high Z3 limits for large sum types\n#set-options \"--z3rlimit 120\"\n\n";

  (** FIXME(adl) for now the t_sum of open and closed sums are independently generated,
  we may try to share more of the declarations between the two cases **)
  (match def with
  | None ->
    (*** Closed Enum ***)
    w o "inline_for_extraction unfold let %s_as_enum_key (x:%s) : Pure (LP.enum_key %s_enum)\n" tn tn tn;
    w o "  (requires norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst %s_enum)) == true)" tn;
    w o " (ensures fun _ -> True) =\n";
    w o "  [@inline_let] let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst %s_enum)) in x\n\n" tn;

    w o "inline_for_extraction let key_of_%s (x:%s%s) : LP.enum_key %s_enum =\n" n n prime tn;
    w o "  match x with\n";
    List.iter (fun (case, ty) -> w o "  | %s_%s _ -> %s_as_enum_key %s\n" cprefix case tn (String.capitalize_ascii case)) cl;
    w o "\ninline_for_extraction let %s_case_of_%s (x:%s) : Type0 =\n" n tn tn;
    w o "  match x with\n";
    List.iter (fun (case, ty) -> w o "  | %s -> %s\n" (String.capitalize_ascii case) (compile_type ty)) cl;
    w o "\nunfold inline_for_extraction let to_%s_case_of_%s (x:%s) (#x':%s) (y:%s_case_of_%s x')" n tn tn tn n tn;
    w o "  : Pure (norm [delta_only [(`%%%s_case_of_%s)]; iota] (%s_case_of_%s x))\n" n tn n tn;
    w o "  (requires (x == x')) (ensures (fun y' -> y' == y)) =\n";
    w o "  [@inline_let] let _ = norm_spec [delta_only [(`%%%s_case_of_%s)] ; iota] (%s_case_of_%s x) in y\n\n" n tn n tn;
    w o "unfold inline_for_extraction let %s_refine (k:LP.enum_key %s_enum) (x:%s%s)\n" n tn n prime;
    w o "  : Pure (LP.refine_with_tag key_of_%s k)" n;
    w o "  (requires norm [delta; iota; zeta] (key_of_%s x) == k) (ensures (fun y -> y == x)) =\n" n;
    w o "  [@inline_let] let _ = norm_spec [delta; iota; zeta] (key_of_%s x) in x\n\n" n;
    w o "inline_for_extraction let synth_%s_cases (x:LP.enum_key %s_enum) (y:%s_case_of_%s x)\n" n tn n tn;
    w o "  : LP.refine_with_tag key_of_%s x =\n  match x with\n" n;
    List.iter (fun (case, ty) -> w o "  | %s -> %s_refine x (%s_%s (to_%s_case_of_%s %s y))\n"
      (String.capitalize_ascii case) n cprefix case n tn (String.capitalize_ascii case)) cl;
    w o "\nunfold inline_for_extraction let from_%s_case_of_%s (#x':%s) (x:%s)\n" n tn tn tn;
    w o "  (y: norm [delta_only [(`%%%s_case_of_%s)]; iota] (%s_case_of_%s x))\n" n tn n tn;
    w o "  : Pure (%s_case_of_%s x') (requires (x == x')) (ensures (fun y' -> y' == y)) =\n" n tn;
    w o "  [@inline_let] let _ = norm_spec [delta_only [(`%%%s_case_of_%s)] ; iota] (%s_case_of_%s x) in y\n\n" n tn n tn;
    w o "let synth_%s_cases_recip_pre (k:LP.enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k) : GTot bool =\n  match k with\n" n;
    List.iter (fun (case, ty) -> w o "  | %s -> %s_%s? x\n" (String.capitalize_ascii case) cprefix case) cl;
    w o "\nlet synth_%s_cases_recip_pre_intro (k:LP.enum_key %s_enum) (x:LP.refine_with_tag key_of_%s k)\n" n tn n;
    w o "  : Lemma (synth_%s_cases_recip_pre k x == true) =\n" n;
    w o "  norm_spec [delta; iota] (synth_%s_cases_recip_pre k x)\n\n" n;
    w o "inline_for_extraction let synth_%s_cases_recip (k:LP.enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k) : (%s_case_of_%s k) =\n  match k with\n" n n tn;
    List.iter (fun (case, ty) ->
      w o "  | %s -> [@inline_let] let _ = synth_%s_cases_recip_pre_intro %s x in\n"
        (String.capitalize_ascii case) n (String.capitalize_ascii case);
      w o "    (match x with %s_%s y -> (from_%s_case_of_%s %s y))\n"
        cprefix case n tn (String.capitalize_ascii case)
    ) cl;
    w o "\ninline_for_extraction let %s_sum = LP.make_sum' %s_enum key_of_%s\n" n tn n;
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
    w o "inline_for_extraction let unknown_%s_as_enum_key (r:%s_repr) : Pure (LP.unknown_enum_repr %s_enum)\n" tn tn tn;
    w o "  (requires known_%s_repr r == false) (ensures fun _ -> True) =\n" tn;
    w o "  [@inline_let] let _ = assert_norm(LP.list_mem r (LP.list_map snd %s_enum) == known_%s_repr r) in r\n\n" tn tn;
    w o "inline_for_extraction let unknown_enum_repr_%s_as_repr (r:LP.unknown_enum_repr %s_enum) : Pure %s_repr\n" tn tn tn;
    w o "  (requires True) (ensures fun r -> known_%s_repr r == false) =\n" tn;
    w o "  [@inline_let] let _ = assert_norm(LP.list_mem r (LP.list_map snd %s_enum) == known_%s_repr r) in r\n\n" tn tn;

    w o "inline_for_extraction let key_of_%s (x:%s%s) : LP.maybe_enum_key %s_enum =\n  match x with\n" n n prime tn;
    List.iter (fun (case, ty) ->
      let cn, ty0 = String.capitalize_ascii case, compile_type ty in
      w o "  | %s_%s _ -> LP.Known (known_%s_as_enum_key %s)\n" cprefix case tn cn
    ) cl;
    w o "  | %s_Unknown_%s v _ -> LP.Unknown (unknown_%s_as_enum_key v)\n\n" cprefix tn tn;

    w o "inline_for_extraction let %s_case_of_%s (x:%s) : Type0 =\n  match x with\n" n tn tn;
    List.iter (fun (case, ty) ->
      let cn, ty0 = String.capitalize_ascii case, compile_type ty in
      w o "  | %s -> %s\n" cn ty0
    ) cl;
    w o "  | Unknown_%s _ -> squash False\n" tn;

    w o "\nunfold inline_for_extraction let %s_value_type (x:LP.maybe_enum_key %s_enum) =\n" n tn;
    w o "  LP.dsum_type_of_tag' %s_enum %s_case_of_%s %s x\n\n" tn n tn tyd;
    w o "unfold inline_for_extraction let %s_refine (k:LP.maybe_enum_key %s_enum) (x:%s%s)\n" n tn n prime;
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
      w o "  | %s ->\n    [@inline_let] let x : %s%s = %s_%s (%s_type_of_known_case k %s () y) in\n" cn n prime cprefix case n cn;
      w o "    [@inline_let] let _ = assert_norm (key_of_%s x == LP.Known %s) in\n" n cn;
      w o "    %s_refine (LP.Known %s) x\n" n cn
    ) cl;
    w o "\ninline_for_extraction let synth_%s_cases (x:LP.maybe_enum_key %s_enum)\n" n tn;
    w o "  (y:%s_value_type x) : LP.refine_with_tag key_of_%s x =\n  match x with\n" n n;
    w o "  | LP.Unknown v ->\n";
    w o "    [@inline_let] let x : %s%s = %s_Unknown_%s (unknown_enum_repr_%s_as_repr v) y in\n" n prime cprefix tn tn;
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
      w o "  | LP.Known %s -> %s_%s? x\n" cn cprefix case
    ) cl;
    w o "  | LP.Known _ -> false\n";
    w o "  | LP.Unknown _ -> %s_Unknown_%s? x\n\n" cprefix tn;
    w o "let synth_%s_cases_recip_pre_intro' (x: %s%s)\n  : Lemma (synth_%s_cases_recip_pre (key_of_%s x) x) = ()\n\n" n n prime n n;
    w o "let synth_%s_cases_recip_pre_intro (k:LP.maybe_enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k)\n" n;
    w o "  : Lemma (synth_%s_cases_recip_pre k x == true) =\n" n;
    w o "  synth_%s_cases_recip_pre_intro' x\n\n" n;
    w o "inline_for_extraction let synth_%s_cases_recip (k:LP.maybe_enum_key %s_enum)\n" n tn;
    w o "  (x:LP.refine_with_tag key_of_%s k) : (%s_value_type k) =\n  match k with\n" n n;
    w o "  | LP.Unknown z ->\n    [@inline_let] let _ = synth_%s_cases_recip_pre_intro (LP.Unknown z) x in\n" n;
    w o "    (match x with %s_Unknown_%s _ y ->  (y <: %s_value_type k))\n" cprefix tn n;
    w o "  | LP.Known k' ->\n    match k' with\n";
    List.iter (fun (case, ty) ->
      let cn, ty0 = String.capitalize_ascii case, compile_type ty in
      w o "    | %s -> [@inline_let] let _ = synth_%s_cases_recip_pre_intro (LP.Known %s) x in\n" cn n cn;
      w o "      (match x with %s_%s y -> %s_known_case k' %s y)\n" cprefix case n cn
    ) cl;
    w o  "   | _ -> [@inline_let] let _ = synth_%s_cases_recip_pre_intro (LP.Known k') in false_elim ()\n\n" n;

    w o "inline_for_extraction let %s_sum : LP.dsum = LP.make_dsum' %s_enum key_of_%s\n" n tn n;
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
    w o "  | %s -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (%s_case_of_%s %s)) = (| _, %s |) in u\n" cn n tn cn (pcombinator_name ty0)
  ) cl;
  w o "  | _ -> (| _, LP.parse_false |)\n\n";

  w o "noextract let serialize_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.serializer (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> [@inline_let] let u : LP.serializer (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (scombinator_name ty0)
  ) cl;
  w o "  | _ -> LP.serialize_false\n\n";

  w o "inline_for_extraction noextract let parse32_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.parser32 (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> [@inline_let] let u : LP.parser32 (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (pcombinator32_name ty0)
  ) cl;
  w o "  | _ -> LP.parse32_false\n\n";

  w o "inline_for_extraction noextract let serialize32_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.serializer32 (serialize_%s_cases x) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> [@inline_let] let u : LP.serializer32 (serialize_%s_cases %s) = %s in u\n" cn n cn (scombinator32_name ty0)
  ) cl;
  w o "  | _ -> LP.serialize32_false\n\n";

  w o "inline_for_extraction noextract let size32_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.size32 (serialize_%s_cases x) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    let ty0 = compile_type ty in
    w o "  | %s -> [@inline_let] let u : LP.size32 (serialize_%s_cases %s) = %s in u\n" cn n cn (size32_name ty0)
  ) cl;
  w o "  | _ -> LP.size32_false\n\n";

  if need_validator then
   begin
    w o "inline_for_extraction noextract let validate_%s_cases (x:%s)\n" n ktype;
    w o "  : LL.validator (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
    List.iter (fun (case, ty) ->
      let cn = String.capitalize_ascii case in
      let ty0 = compile_type ty in
      w o "  | %s -> [@inline_let] let u : LL.validator (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (validator_name ty0)
    ) cl;
    w o "  | _ -> LL.validate_false ()\n\n"
   end;

  if need_jumper then
   begin
    w o "inline_for_extraction noextract let jump_%s_cases (x:%s)\n" n ktype;
    w o "  : LL.jumper (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
    List.iter (fun (case, ty) ->
      let cn = String.capitalize_ascii case in
      let ty0 = compile_type ty in
      w o "  | %s -> [@inline_let] let u : LL.jumper (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (jumper_name ty0)
    ) cl;
    w o "  | _ -> LL.jump_false\n\n"
   end;

  if is_implicit then (
    match def with
    | None ->
      w o "let _ : squash (%s_parser_kind == LP.weaken_parse_cases_kind %s_sum parse_%s_cases) =\n" n n n;
      w o "  _ by (FStar.Tactics.norm [delta; iota; primops]; FStar.Tactics.trefl ())\n\n";
      w o "let %s_eq_lemma (k:%s) : Lemma (%s k == LP.sum_cases %s_sum (%s_as_enum_key k)) [SMTPat (%s k)] =\n" n tn n n tn n;
      w o "  match k with\n";
      List.iter (fun (case, ty) ->
        let cn, ty0 = String.capitalize_ascii case, compile_type ty in
        w o "  | %s -> assert_norm (%s %s == LP.sum_cases %s_sum (%s_as_enum_key %s))\n" cn n cn n tn cn
      ) cl;
      w o "\nlet %s_parser k =\n  LP.parse_sum_cases %s_sum parse_%s_cases (%s_as_enum_key k)\n\n" n n n tn;
      w o "let %s_serializer k =\n  LP.serialize_sum_cases %s_sum parse_%s_cases serialize_%s_cases (%s_as_enum_key k)\n\n" n n n n tn;
      write_bytesize o is_private n  ~param:(if is_implicit then Some tagt else None);
      w o "let %s_parser32 k =\n  LP.parse32_sum_cases %s_sum parse_%s_cases parse32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
      w o "let %s_serializer32 k =\n  LP.serialize32_sum_cases %s_sum serialize_%s_cases serialize32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
      w o "let %s_size32 k =\n  LP.size32_sum_cases %s_sum serialize_%s_cases size32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
      if need_validator then
        w o "let %s_validator k =\n  LL.validate_sum_cases %s_sum parse_%s_cases validate_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
      if need_jumper then
        w o "let %s_jumper k =\n  LL.jump_sum_cases %s_sum parse_%s_cases jump_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
    | Some def -> (* Horible synth boilerplate to deal with refine_with_tag *)
      let dt = compile_type def in
      w o "let _ : squash (%s_parser_kind == LP.weaken_parse_dsum_cases_kind %s_sum parse_%s_cases (LP.get_parser_kind %s)) =\n" n n n (pcombinator_name dt);
      w o "  _ by (FStar.Tactics.norm [delta; iota; primops]; FStar.Tactics.trefl ())\n\n";
      w o "inline_for_extraction let synth_%s (k:%s) (x:LP.refine_with_tag key_of_%s (synth_%s_inv k)) : %s k = x\n\n" n tn n tn n;
      w o "inline_for_extraction let synth_%s_recip (k:%s) (x:%s k) : LP.refine_with_tag key_of_%s (synth_%s_inv k) = x\n\n" n tn n n tn;
      w o "let synth_%s_inj (k:%s) : Lemma (LP.synth_injective (synth_%s k)) = ()\n\n" n tn n;
      w o "let synth_%s_inv (k:%s) : Lemma (LP.synth_inverse (synth_%s k) (synth_%s_recip k)) = ()\n\n" n tn n n;
      w o "noextract inline_for_extraction let %s_parser' = LP.parse_dsum_cases %s_sum parse_%s_cases %s\n\n" n n n (pcombinator_name dt);
      w o "let %s_parser k = %s_parser' (synth_%s_inv k) `LP.parse_synth` synth_%s k\n\n" n n tn n;
      w o "noextract let %s_serializer' = LP.serialize_dsum_cases %s_sum parse_%s_cases serialize_%s_cases %s %s\n\n" n n n n (pcombinator_name dt) (scombinator_name dt);
      w o "let %s_serializer k = LP.serialize_synth _ (synth_%s k) (%s_serializer' (synth_%s_inv k)) (synth_%s_recip k) ()\n\n" n n n tn n;
      write_bytesize o is_private n  ~param:(if is_implicit then Some tagt else None);
      w o "noextract inline_for_extraction let %s_parser32' = LP.parse32_dsum_cases %s_sum parse_%s_cases parse32_%s_cases %s %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n (pcombinator_name dt) (pcombinator32_name dt);
      w o "let %s_parser32 k = LP.parse32_synth' (%s_parser' (synth_%s_inv k)) (synth_%s k) (LP.parse32_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_parser32' k) ()\n\n" n n tn n tn n n n;
      w o "noextract inline_for_extraction let %s_serializer32' = LP.serialize32_dsum_cases %s_sum parse_%s_cases serialize_%s_cases serialize32_%s_cases %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n n (scombinator32_name dt);
      w o "let %s_serializer32 k = LP.serialize32_synth' (%s_parser' (synth_%s_inv k)) (synth_%s k) (%s_serializer' (synth_%s_inv k))\n" n n tn n n tn;
      w o "   (LP.serialize32_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_serializer' %s_serializer32' k) (synth_%s_recip k) ()\n\n" tn n n n n n;
      w o "noextract inline_for_extraction let %s_size32' = LP.size32_dsum_cases %s_sum parse_%s_cases serialize_%s_cases size32_%s_cases %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n n (size32_name dt);
      w o "let %s_size32 k = LP.size32_synth' (%s_parser' (synth_%s_inv k)) (synth_%s k) (%s_serializer' (synth_%s_inv k)) (LP.size32_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_serializer' %s_size32' k) (synth_%s_recip k) ()\n\n" n n tn n n tn tn n n n n n;
      if need_validator then (
        w o "noextract inline_for_extraction let %s_validator' = LL.validate_dsum_cases %s_sum parse_%s_cases validate_%s_cases %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n (validator_name dt);
        w o "let %s_validator k = LL.validate_synth (LL.validate_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_validator' k) (synth_%s k) ()\n\n" n tn n n n n
      );
      if need_jumper then (
        w o "noextract inline_for_extraction let %s_jumper' = LL.jump_dsum_cases %s_sum parse_%s_cases jump_%s_cases %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n (jumper_name dt);
        w o "let %s_jumper k = LL.jump_synth (LL.jump_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_jumper' k) (synth_%s k) ()\n\n" n tn n n n n
      )
  ) else (* tag is not erased *)
   begin
    let same_kind = match def with
      | None -> sprintf "  assert_norm (LP.parse_sum_kind (LP.get_parser_kind %s_repr_parser) %s_sum parse_%s_cases == %s_parser_kind);\n" tn n n n
      | Some dt -> sprintf "  assert_norm (LP.parse_dsum_kind (LP.get_parser_kind %s_repr_parser) %s_sum parse_%s_cases (LP.get_parser_kind %s) == %s_parser_kind);\n" tn n n (pcombinator_name (compile_type dt)) n
      in
    let annot = if is_private then " : LP.parser "^n^"_parser_kind "^n else "" in
    w o "let %s_parser%s =\n%s" n annot same_kind;
    (match def with
    | None -> w o "  LP.parse_sum %s_sum %s_repr_parser parse_%s_cases\n\n" n tn n
    | Some dt -> w o "  LP.parse_dsum %s_sum %s_repr_parser parse_%s_cases %s\n\n" n tn n (pcombinator_name (compile_type dt)));

    let annot = if is_private then " : LP.serializer "^(pcombinator_name n) else "" in
    w o "let %s_serializer%s =\n%s" n annot same_kind;
    (match def with
    | None -> w o "  LP.serialize_sum %s_sum %s_repr_serializer serialize_%s_cases\n\n" n tn n
    | Some dt -> w o "  LP.serialize_dsum %s_sum %s_repr_serializer _ serialize_%s_cases _ %s\n\n" n tn n (scombinator_name (compile_type dt)));
    write_bytesize o is_private n  ~param:(if is_implicit then Some tagt else None);

    let annot = if is_private then " : LP.parser32 "^(pcombinator_name n) else "" in
    w o "let %s_parser32%s =\n%s" n annot same_kind;
    (match def with
    | None ->
      w o "  LP.parse32_sum2 %s_sum %s_repr_parser %s_repr_parser32 parse_%s_cases parse32_%s_cases (_ by (LP.enum_destr_tac %s_enum)) (_ by (LP.maybe_enum_key_of_repr_tac %s_enum))\n\n" n tn tn n n tn tn;
    | Some dt ->
      w o "  LP.parse32_dsum %s_sum %s_repr_parser32\n" n tn;
      w o "    _ parse32_%s_cases %s (_ by (LP.maybe_enum_destr_t_tac ()))\n\n" n (pcombinator32_name (compile_type dt)));

    let annot = if is_private then " : LP.serializer32 "^(scombinator_name n) else "" in
    w o "let %s_serializer32%s =\n%s" n annot same_kind;
    (match def with
    | None ->
      w o "  assert_norm (LP.serializer32_sum_gen_precond (LP.get_parser_kind %s_repr_parser) (LP.weaken_parse_cases_kind %s_sum parse_%s_cases));\n" tn n n;
      w o "  LP.serialize32_sum2 %s_sum %s_repr_serializer %s_repr_serializer32 serialize_%s_cases serialize32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac %s_enum)) ()\n\n" n tn tn n n tn
    | Some dt ->
      w o "  assert_norm (LP.serializer32_sum_gen_precond (LP.get_parser_kind %s_repr_parser) (LP.weaken_parse_dsum_cases_kind %s_sum parse_%s_cases %s_parser_kind));\n" tn n n n;
      w o "  LP.serialize32_dsum %s_sum %s_repr_serializer (_ by (LP.serialize32_maybe_enum_key_tac %s_repr_serializer32 %s_enum ()))" n tn tn tn;
      w o "    _ _ serialize32_%s_cases %s (_ by (LP.dep_enum_destr_tac ())) ()\n\n" n (scombinator32_name (compile_type dt)));

    let annot = if is_private then " : LP.size32 "^n else "" in
    w o "let %s_size32%s =\n%s" n annot same_kind;
    (match def with
    | None ->
      w o "  assert_norm (LP.size32_sum_gen_precond (LP.get_parser_kind %s_repr_parser) (LP.weaken_parse_cases_kind %s_sum parse_%s_cases));\n" tn n n;
      w o "  LP.size32_sum2 %s_sum %s_repr_serializer %s_repr_size32 serialize_%s_cases size32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac %s_enum)) ()\n\n" n tn tn n n tn
    | Some dt ->
      w o "  assert_norm (LP.size32_sum_gen_precond (LP.get_parser_kind %s_repr_parser) (LP.weaken_parse_dsum_cases_kind %s_sum parse_%s_cases %s_parser_kind));\n" tn n n n;
      w o "  LP.size32_dsum %s_sum _ (_ by (LP.size32_maybe_enum_key_tac %s_repr_size32 %s_enum ()))\n" n tn tn;
      w o "    _ _ size32_%s_cases %s (_ by (LP.dep_enum_destr_tac ())) ()\n\n" n (size32_name (compile_type dt)));

    if need_validator then
     begin
      let annot = if is_private then " : LL.validator "^(pcombinator_name n) else "" in
      w o "let %s_validator%s =\n%s" n annot same_kind;
      (match def with
      | None ->
        w o "  LL.validate_sum %s_sum %s_repr_validator %s_repr_reader parse_%s_cases validate_%s_cases (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n tn tn n n;
      | Some dt ->
        w o "  LL.validate_dsum %s_sum %s_repr_validator %s_repr_reader parse_%s_cases validate_%s_cases %s (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n tn tn n n (validator_name (compile_type dt)));
     end;

    if need_jumper then
     begin
      let annot = if is_private then " : LL.jumper "^(pcombinator_name n) else "" in
      w o "let %s_jumper%s =\n%s" n annot same_kind;
      (match def with
      | None ->
        w o "  LL.jump_sum %s_sum %s_repr_jumper %s_repr_reader parse_%s_cases jump_%s_cases (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n tn tn n n;
      | Some dt ->
        w o "  LL.jump_dsum %s_sum %s_repr_jumper %s_repr_reader parse_%s_cases jump_%s_cases %s (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n tn tn n n (jumper_name (compile_type dt)))
     end;

    if need_validator then
     begin
      let maybe = match def with
        | None -> ""
        | _ -> "maybe_"
      in
      w i "val lemma_valid_%s_valid_%s: s:LL.slice -> pos:U32.t -> h:HyperStack.mem -> Lemma\n" n tn;
      w i "  (requires LL.valid %s_parser h s pos)\n" n;
      w i "  (ensures (LL.valid %s_parser h s pos /\\ LL.contents %s_parser h s pos == tag_of_%s (LL.contents %s_parser h s pos)))\n" tn tn n n;
      w i "  [SMTPat (LL.valid %s_parser h s pos)]\n\n" n;
      w o "let lemma_valid_%s_valid_%s s pos h =\n%s" n tn same_kind;
      begin match def with
      | None ->
         w o "  LL.valid_sum_elim_tag h %s_sum %s_repr_parser parse_%s_cases s pos;\n" n tn n
      | Some dt ->
         w o "  LL.valid_dsum_elim_tag h %s_sum %s_repr_parser parse_%s_cases %s s pos;\n" n tn n (pcombinator_name (compile_type dt))
      end;
      w o "  lemma_synth_%s_inj ();\n" tn;
      w o "  LL.valid_synth h parse_%s%s_key synth_%s s pos\n" maybe tn tn;
      w o "\n"
     end;

    (* bytesize *)
    begin match def with
    | None ->
       List.iter
         (fun (case, ty) ->
           let ty0 = compile_type ty in
           let constr = sprintf "%s_%s" cprefix case in
           w i "val %s_bytesize_eqn_%s (x: %s) : Lemma (%s_bytesize (%s x) == %d + %s) [SMTPat (%s_bytesize (%s x))]\n\n" n case ty0 n constr taglen (bytesize_call ty0 "x") n constr;
           w o "let %s_bytesize_eqn_%s x =\n\n" n case;
           w o "  LP.serialize_sum_eq %s_sum %s_repr_serializer serialize_%s_cases (%s x);\n" n tn n constr;
           w o "  %s\n\n" (bytesize_eq_call ty0 "x")
         )
         cl
    | Some dt ->
       let dt0 = compile_type dt in
       let write_constr vbind vvar (case, ty) =
           let ty0 = compile_type ty in
           let constr = sprintf "%s_%s" cprefix case in
           w i "val %s_bytesize_eqn_%s %s (x: %s) : Lemma (%s_bytesize (%s %s x) == %d + %s) [SMTPat (%s_bytesize (%s %s x))]\n\n" n case vbind ty0 n constr vvar taglen (bytesize_call ty0 "x") n constr vvar;
           w o "let %s_bytesize_eqn_%s %s x =\n" n case vvar;
           w o "  LP.serialize_dsum_eq %s_sum %s_repr_serializer parse_%s_cases serialize_%s_cases %s %s (%s %s x) ;\n" n tn n n (pcombinator_name dt0) (scombinator_name dt0) constr vvar;
           w o "  %s\n\n" (bytesize_eq_call ty0 "x")
       in
       List.iter (write_constr "" "") cl;
       write_constr (sprintf "(v: %s_repr { not (known_%s_repr v) } )" tn tn) "v" (sprintf "Unknown_%s" tn, dt)
    end;

    (* finalizers *)
    let write_finalizer case =
      match def with
      | None ->
         w o "  LL.finalize_sum_case %s_sum %s_repr_serializer %s_repr_writer parse_%s_cases (_ by (LP.enum_repr_of_key_tac %s_enum)) %s input pos\n\n" n tn tn n tn (String.capitalize_ascii case)
      | Some dt ->
         w o "  [@inline_let] let _ = %s () in\n" same_kind;
         w o "  LL.finalize_dsum_case_known %s_sum %s_repr_serializer %s_repr_writer parse_%s_cases %s (_ by (LP.enum_repr_of_key_tac %s_enum)) (known_%s_as_enum_key %s) input pos\n\n" n tn tn n (pcombinator_name (compile_type dt)) tn tn (String.capitalize_ascii case)
    in
       List.iter
         (fun (case, ty) ->
           let ty0 = compile_type ty in
           let constr = sprintf "%s_%s" cprefix case in
           let casep = pcombinator_name ty0 in
           match ty with
           | "Fail" -> () (* impossible case *)
           | "Empty" -> (* parse_empty is not in the user context, so we need to "inline" it here *)
              w i "val finalize_%s_%s (input: LL.slice) (pos: U32.t) : HST.Stack unit\n" n case;
              w i "  (requires (fun h -> LL.live_slice h input /\\ U32.v pos + %d <= U32.v input.LL.len))\n" taglen;
              w i "  (ensures (fun h _ h' ->\n";
              w i "    let pos_payload = pos `U32.add` %dul in\n" taglen;
              w i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
              w i "    LL.valid_content_pos %s_parser h' input pos (%s ()) pos_payload\n" n constr;
              w i "  ))\n\n";
              w o "let finalize_%s_%s input pos =\n" n case;
              w o "  let h = HST.get () in\n";
              w o "  [@inline_let] let _ = LL.valid_facts LL.parse_empty h input (pos `U32.add` %dul) in\n" taglen;
              write_finalizer case
           | _ ->
              w i "val finalize_%s_%s (input: LL.slice) (pos: U32.t) : HST.Stack unit\n" n case;
              w i "  (requires (fun h -> U32.v pos + %d < 4294967296 /\\ LL.valid %s h input (pos `U32.add` %dul)))\n" taglen casep taglen;
              w i "  (ensures (fun h _ h' ->\n";
              w i "    let pos_payload = pos `U32.add` %dul in\n" taglen;
              w i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
              w i "    LL.valid_content_pos %s_parser h' input pos (%s (LL.contents %s h input pos_payload)) (LL.get_valid_pos %s h input pos_payload)\n" n constr casep casep;
              w i "  ))\n\n";
              w o "let finalize_%s_%s input pos =\n" n case;
              write_finalizer case
         )
         cl
     ;
       (* finalizer for unknown case *)
       begin match def with
       | Some dt when dt <> "Fail" ->
          let dp = pcombinator_name (compile_type dt) in
          w i "val finalize_%s_Unknown_%s (v: %s_repr) (input: LL.slice) (pos: U32.t) : HST.Stack unit\n" n tn tn;
          if dt = "Empty" then
            w i "  (requires (fun h -> U32.v pos + %d <= U32.v input.LL.len /\\ LL.live_slice h input /\\ not (known_%s_repr v)))\n" taglen tn
          else
            w i "  (requires (fun h -> U32.v pos + %d < 4294967296 /\\ LL.valid %s h input (pos `U32.add` %dul) /\\ not (known_%s_repr v)))\n" taglen dp taglen tn
          ;
          w i "  (ensures (fun h _ h' ->\n";
          w i "    let pos_payload = pos `U32.add` %dul in\n" taglen;
          w i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
          if dt = "Empty" then
            w i "    LL.valid_content_pos %s_parser h' input pos (%s_Unknown_%s v ()) pos_payload\n" n cprefix tn
          else
            w i "    LL.valid_content_pos %s_parser h' input pos (%s_Unknown_%s v (LL.contents %s h input pos_payload)) (LL.get_valid_pos %s h input pos_payload)\n" n cprefix tn dp dp
          ;
          w i "  ))\n\n";
          w o "let finalize_%s_Unknown_%s v input pos =\n" n tn;
          w o "  [@inline_let] let _ = (%s ()) in\n" same_kind;
          if dt = "Empty" then begin
            w o "  let h = HST.get () in\n";
            w o "  [@inline_let] let _ = LL.valid_facts LL.parse_empty h input (pos `U32.add` %dul) in\n" taglen;
          end;
          w o "  LL.finalize_dsum_case_unknown %s_sum %s_repr_serializer %s_repr_writer parse_%s_cases %s (unknown_%s_as_enum_key v) input pos\n\n" n tn tn n dp tn
       | _ -> ()
       end
  end

and compile_typedef o i tn fn (ty:type_t) vec def al =
  let n = if tn = "" then String.uncapitalize_ascii fn else tn^"_"^fn in
  let qname = if tn = "" then String.uncapitalize_ascii fn else tn^"@"^fn in
  let is_private = has_attr al "private" in
  let elem_li = sizeof ty in
  let li = get_leninfo qname in
  let need_validator = is_private || need_validator li.meta li.min_len li.max_len in
  let need_jumper = is_private || need_jumper li.min_len li.max_len in
  let (ty, vec) =
    match ty, vec with
    | TypeSimple(t), VectorVldata vl when SM.mem (compile_type t) !erased ->
      let (len_len, max_len) = basic_bounds vl in
      TypeSimple("opaque"), VectorRange(max 0 (li.min_len-len_len), min max_len (max 0 (li.max_len-len_len)), len_len)
    | _ -> ty, vec in
  match ty with
  | TypeSelect (sn, cl, def) ->  () (*failwith "Unsupported select"*)
  | TypeSimple ty ->
    let ty0 = compile_type ty in
    match vec with
    (* Type aliasing *)
    | VectorNone ->
      w i "type %s = %s\n\n" n ty0;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "noextract let %s_parser = %s\n\n" n (pcombinator_name ty0);
      w o "noextract let %s_serializer = %s\n\n" n (scombinator_name ty0);
      write_bytesize o is_private n;
      w o "let %s_parser32 = %s\n\n" n (pcombinator32_name ty0);
      w o "let %s_serializer32 = %s\n\n" n (scombinator32_name ty0);
      w o "let %s_size32 = %s\n\n" n (size32_name ty0);
      (if need_validator then w o "inline_for_extraction let %s_validator = %s\n\n" n (validator_name ty0));
      (if need_jumper then
         let jumper_annot = if is_private then Printf.sprintf " : LL.jumper %s_parser" n else "" in
         w o "inline_for_extraction let %s_jumper%s = %s\n\n" n jumper_annot (jumper_name ty0));
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %s) [SMTPat (%s_bytesize x)]\n\n" n n n (bytesize_call ty0 "x") n;
      w o "let %s_bytesize_eqn x = %s\n\n" n (bytesize_eq_call ty0 "x");
      ()

    (* Should be replaced with Vldata during normalization *)
    | VectorSymbolic cst -> failwith "not supported"

    | VectorVldata vl ->
      let (len_len, smax) = basic_bounds vl in
      let (min, max) = li.min_len, li.max_len in
      if elem_li.max_len <= smax then
       begin
        w i "type %s = %s\n\n" n ty0;
        write_api o i is_private li.meta n min max;
        w o "let %s_parser =\n" n;
        w o "  LP.parse_bounded_vldata %d %d %s\n\n" 0 smax (pcombinator_name ty0);
        w o "let %s_serializer =\n" n;
        w o "  LP.serialize_bounded_vldata %d %d %s\n\n" 0 smax (scombinator_name ty0);
        write_bytesize o is_private n;
        w o "let %s_parser32 =\n" n;
        w o "  LP.parse32_bounded_vldata %d %dul %d %dul %s\n\n" 0 0 smax smax (pcombinator32_name ty0);
        w o "let %s_serializer32 =\n" n;
        w o "  LP.serialize32_bounded_vldata %d %d %s\n\n" 0 smax (scombinator32_name ty0);
        w o "let %s_size32 =\n" n;
        w o "  LP.size32_bounded_vldata %d %d %s %dul\n\n" 0 smax (size32_name ty0) (log256 smax);
        if need_validator then (
          w o "let %s_validator =\n" n;
          w o "  LL.validate_bounded_vldata %d %d %s ()\n\n" 0 smax (validator_name ty0);
        );
        if need_jumper then (
          let jumper_annot = if is_private then Printf.sprintf " : LL.jumper %s_parser" n else "" in
          w o "let %s_jumper%s =\n\n" n jumper_annot;
          w o "  LL.jump_bounded_vldata %d %d %s ()\n\n" 0 smax (pcombinator_name ty0)
        );
        (* accessor *)
        if ty <> "Empty" && ty <> "Fail" then begin
            w i "val %s_gaccessor : LL.gaccessor %s_parser %s (LL.clens_id %s)\n\n" n n (pcombinator_name ty0) ty0;
            w o "let %s_gaccessor = LL.gaccessor_bounded_vldata_payload %d %d %s\n\n" n 0 smax (pcombinator_name ty0);
            w i "val %s_accessor : LL.accessor %s_gaccessor\n\n" n n;
            w o "let %s_accessor = LL.accessor_bounded_vldata_payload %d %d %s\n\n" n 0 smax (pcombinator_name ty0);
            ()
        end;
        (* finalizer *)
        begin match ty with
        | "Fail" -> () (* impossible *)
        | "Empty" ->
            w i "val %s_finalize (input: LL.slice) (pos: U32.t) : HST.Stack unit\n" n;
            w i "  (requires (fun h ->\n";
            w i "    U32.v pos + %d <= U32.v input.LL.len /\\\n" len_len;
            w i "    LL.live_slice h input\n";
            w i "  ))\n";
            w i "  (ensures (fun h _ h' ->\n";
            w i "    B.modifies (LL.loc_slice_from_to input pos (pos `U32.add` %dul)) h h' /\\\n" len_len;
            w i "    LL.valid_pos %s_parser h' input pos (pos `U32.add` %dul)\n" n len_len;
            w i "  ))\n\n";
            w o "let %s_finalize input pos =\n" n;
            w o "  let h = HST.get () in\n";
            w o "  [@inline_let] let _ = LL.valid_facts LL.parse_empty h input (pos `U32.add` %dul) in\n" len_len;
            w o "  LL.finalize_bounded_vldata %d %d LL.parse_empty input pos (pos `U32.add` %dul) \n\n" 0 smax len_len
        | _ ->
            w i "val %s_finalize (input: LL.slice) (pos: U32.t) (pos' : U32.t) : HST.Stack unit\n" n;
            w i "  (requires (fun h ->\n";
            w i "    U32.v pos + %d <= U32.v input.LL.len /\\\n" len_len;
            w i "    LL.valid_pos %s h input (pos `U32.add` %dul) pos'\n" (pcombinator_name ty0) len_len;
            w i "  ))\n";
            w i "  (ensures (fun h _ h' ->\n";
            w i "    B.modifies (LL.loc_slice_from_to input pos (pos `U32.add` %dul)) h h' /\\\n" len_len;
            w i "    LL.valid_content_pos %s_parser h' input pos (LL.contents %s h input (pos `U32.add` %dul)) pos'\n" n (pcombinator_name ty0) len_len;
            w i "  ))\n\n";
            w o "let %s_finalize input pos pos' =\n" n;
            w o "  LL.finalize_bounded_vldata %d %d %s input pos pos'\n\n" 0 smax (pcombinator_name ty0)
        end;
        ()
       end
      else
       begin
        let sizef =
          if basic_type ty then sprintf "Seq.length (LP.serialize %s x)" (scombinator_name ty0)
          else sprintf "%s_bytesize x" ty0 in
        (if not (basic_type ty) then w o "friend %s\n\n" (module_name ty0));
        w i "type %s = x:%s{let l = %s in %d <= l /\\ l <= %d}\n\n" n ty0 sizef 0 smax;
        write_api o i is_private li.meta n min max;
        w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d %s\n\n" n 0 smax (scombinator_name ty0);
        let eqtypes = sprintf "[@inline_let] let _ = assert_norm (%s' == %s) in" n n in
        w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
        w o "  LP.parse_bounded_vldata_strong %d %d %s\n\n" 0 smax (scombinator_name ty0);
        w o "let %s_parser = %s %s'_parser\n\n" n eqtypes n;
        w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
        w o "  LP.serialize_bounded_vldata_strong %d %d %s\n\n" 0 smax (scombinator_name ty0);
        w o "let %s_serializer = %s %s'_serializer\n\n" n eqtypes n;
        write_bytesize o is_private n;
        w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
        w o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul %s %s\n\n" 0 0 smax smax (scombinator_name ty0) (pcombinator32_name ty0);
        w o "let %s_parser32 = %s %s'_parser32\n\n" n eqtypes n;
        w o "inline_for_extraction noextract let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
        w o "  LP.serialize32_bounded_vldata_strong %d %d %s\n\n" 0 smax (scombinator32_name ty0);
        w o "let %s_serializer32 = %s %s'_serializer32\n\n" n eqtypes n;
        w o "inline_for_extraction noextract let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
        w o "  LP.size32_bounded_vldata_strong %d %d %s %dul\n\n" 0 smax (size32_name ty0) (log256 smax);
        w o "let %s_size32 = %s %s'_size32\n\n" n eqtypes n;
        if need_validator then (
          w o "inline_for_extraction let %s'_validator : LL.validator %s'_parser =\n" n n;
          w o "  LL.validate_bounded_vldata_strong %d %d %s %s ()\n\n" 0 smax (scombinator_name ty0) (validator_name ty0);
          w o "let %s_validator = %s %s'_validator\n\n" n eqtypes n
        );
        if need_jumper then (
          w o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser =\n" n n;
          w o "  LL.jump_bounded_vldata_strong %d %d %s ()\n\n" 0 smax (scombinator_name ty0);
          let jumper_annot = if is_private then Printf.sprintf " : LL.jumper %s_parser" n else "" in
          w o "let %s_jumper%s = %s %s'_jumper\n\n" n jumper_annot eqtypes n
        );
        (* accessor *)
        if ty <> "Empty" && ty <> "Fail" then begin
            w i "let %s_clens : LL.clens %s %s = {\n" n n ty0;
            w i "  LL.clens_cond = (fun _ -> True);\n";
            w i "  LL.clens_get = (fun (x: %s) -> (x <: %s));\n" n ty0;
            w i "}\n\n";
            w i "val %s_gaccessor : LL.gaccessor %s_parser %s %s_clens\n\n" n n (pcombinator_name ty0) n;
            w o "let %s_gaccessor = %s LL.gaccessor_bounded_vldata_strong_payload %d %d %s\n\n" n eqtypes 0 smax (scombinator_name ty0);
            w i "val %s_accessor : LL.accessor %s_gaccessor\n\n" n n;
            w o "let %s_accessor = %s LL.accessor_bounded_vldata_strong_payload %d %d %s\n\n" n eqtypes 0 smax (scombinator_name ty0);
            ()
        end;
        ()
       end;
      (* lemma about bytesize: works in both cases *)
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + %s) [SMTPat (%s_bytesize x)]\n\n" n n n li.len_len (bytesize_call ty0 "x") n;
      w o "let %s_bytesize_eqn x = %s\n\n" n (bytesize_eq_call ty0 "x");
      ()

    (* Fixed-length bytes *)
    | VectorFixed k when ty0 = "U8.t" ->
      w i "type %s = lbytes %d\n\n" n k;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "noextract let %s_parser = LP.parse_flbytes %d\n\n" n k;
      w o "noextract let %s_serializer = LP.serialize_flbytes %d\n\n" n k;
      write_bytesize o is_private n;
      w o "let %s_parser32 = LP.parse32_flbytes %d %dul\n\n" n k k;
      w o "let %s_serializer32 = LP.serialize32_flbytes %d\n\n" n k;
      w o "let %s_size32 = LP.size32_constant %s_serializer %dul ()\n\n" n n k;
      (* validator and jumper not needed unless private, we are total constant size *)
      if is_private then
       begin
        w o "inline_for_extraction let %s_validator = LL.validate_flbytes %d %dul\n\n" n k k;
        w o "inline_for_extraction let %s_jumper : LL.jumper %s_parser = LL.jump_flbytes %d %dul\n\n" n n k k
       end;
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == BY.length x) [SMTPat (%s_bytesize x)]\n\n" n n n n;
      w o "let %s_bytesize_eqn x = ()\n\n" n;
      (* intro *)
      w i "val %s_intro (h: HS.mem) (input: LL.slice) (pos: U32.t) : Lemma\n" n;
      w i "  (requires (\n";
      w i "    LL.live_slice h input /\\\n";
      w i "    U32.v pos + %d <= U32.v input.LL.len\n" k;
      w i "  ))\n";
      w i "  (ensures (\n";
      w i "    LL.valid_content_pos %s_parser h input pos (BY.hide (B.as_seq h (B.gsub input.LL.base pos %dul))) (pos `U32.add` %dul)\n" n k k;
      w i "  ))\n";
      w o "let %s_intro h input pos =\n" n;
      w o "  LL.valid_flbytes_intro h %d input pos\n\n" k;
      (* elim *)
      w i "val %s_elim (h: HS.mem) (input: LL.slice) (pos: U32.t) : Lemma\n" n;
      w i "  (requires (LL.valid %s_parser h input pos))\n" n;
      w i "  (ensures (\n";
      w i "    U32.v pos + %d <= U32.v input.LL.len /\\\n" k;
      w i "    LL.valid_content_pos %s_parser h input pos (BY.hide (B.as_seq h (B.gsub input.LL.base pos %dul))) (pos `U32.add` %dul)\n" n k k;
      w i "  ))\n";
      w o "let %s_elim h input pos =\n" n;
      w o "  LL.valid_flbytes_elim h %d input pos\n\n" k;      
      ()

    (* Fixed length list *)
    | VectorFixed k when elem_li.min_len = elem_li.max_len ->
      w i "unfold let %s_pred (l:list %s) (n:nat) : GTot Type0 = L.length l == n\n" n ty0;
      w i "type %s = l:list %s{%s_pred l %d}\n\n" n ty0 n li.min_count;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "type %s' = LP.array %s %d\n\n" n ty0 li.min_count;
      w o "private let %s_eq () : Lemma (%s' == %s) =\n" n n n;
      w o "  assert(%s'==%s) by (FStar.Tactics.norm [delta_only [`%%(LP.array); `%%(%s); `%%(%s')]]; FStar.Tactics.trefl ())\n\n" n n n n;
      w o "noextract let %s'_parser = LP.parse_array %s %d %d\n\n" n (scombinator_name ty0) k li.min_count;
      w o "let %s_parser = %s_eq(); LP.coerce (LP.parser %s_parser_kind %s) %s'_parser\n\n" n n n n n;
      w o "noextract let %s'_serializer = LP.serialize_array %s %d %d ()\n\n" n (scombinator_name ty0) k li.min_count;
      w o "let %s_serializer = %s_eq(); LP.coerce (LP.serializer %s_parser) %s'_serializer\n\n" n n n n;
      write_bytesize o is_private n;
      w o "inline_for_extraction let %s'_parser32 = LP.parse32_array %s %s %d %dul %d ()\n\n"
        n (scombinator_name ty0) (pcombinator32_name ty0) k k li.min_count;
      w o "let %s_parser32 = %s_eq(); LP.coerce (LP.parser32 %s_parser) %s'_parser32\n\n" n n n n;
      w o "inline_for_extraction noextract let %s'_serializer32 =\n" n;
      w o "  LP.serialize32_array #_ #_ #_ #%s %s %d %d ()\n\n" (scombinator_name ty0) (scombinator32_name ty0) k li.min_count;
      w o "let %s_serializer32 = %s_eq(); LP.coerce (LP.serializer32 %s_serializer) %s'_serializer32\n\n" n n n n;
      w o "let %s_size32 = LP.size32_array %s %d %dul %d ()\n" n (scombinator_name ty0) k k li.min_count;
      (if need_validator then w o "let %s_validator = LL.validate_array %s %s %d %dul %d ()\n\n" n (scombinator_name ty0) (validator_name ty0) k k li.min_count);
      (* jumper not needed unless private, we are constant size *)
      (if is_private then w o "let %s_jumper : LL.jumper %s_parser = LL.jump_array %s %d %dul %d ()\n\n" n n (scombinator_name ty0) k k li.min_count);
      w i "noextract let clens_%s_nth (i: nat { i < %d } ) : LL.clens %s %s = {\n" n li.min_count n ty0;
      w i "  LL.clens_cond = (fun _ -> True);\n";
      w i "  LL.clens_get = (fun (l: %s) -> L.index l i);\n" n;
      w i "}\n\n";
      w i "val %s_nth_ghost (i: nat {i < %d}) : LL.gaccessor %s_parser %s (clens_%s_nth i)\n\n" n li.max_count n (pcombinator_name ty0) n;
      w o "let %s_nth_ghost i = LL.array_nth_ghost %s %d %d i\n\n" n (scombinator_name ty0) li.max_len li.max_count;
      w i "inline_for_extraction val %s_nth (i: U32.t { U32.v i < %d } ) : LL.accessor (%s_nth_ghost (U32.v i))\n\n" n li.max_count n;
      w o "let %s_nth i = LL.array_nth %s %d %d i\n\n" n (scombinator_name ty0) li.max_len li.max_count;
      (* intro lemma *)
      w i "val %s_intro (h: HS.mem) (input: LL.slice) (pos pos' : U32.t) : Lemma\n" n;
      w i "  (requires (\n";
      w i "     LL.valid_list %s h input pos pos' /\\\n" (pcombinator_name ty0);
      w i "     (L.length (LL.contents_list %s h input pos pos') == %d \\/ U32.v pos' - U32.v pos == %d)\n" (pcombinator_name ty0) li.max_count li.max_len;
      w i "  ))\n";
      w i "  (ensures (\n";
      w i "    let x = LL.contents_list %s h input pos pos' in\n" (pcombinator_name ty0);
      w i "    L.length x = %d /\\\n" li.max_count;
      w i "    U32.v pos' - U32.v pos == %d /\\\n" li.max_len;
      w i "    LL.valid_content_pos %s_parser h input pos x pos'\n" n;
      w i "  ))\n\n";
      w o "let %s_intro h input pos pos' = %s_eq (); LL.valid_list_valid_array %s %d %dul %d () h input pos pos'\n\n" n n (scombinator_name ty0) li.max_len li.max_len li.max_count;
      (* elim lemma *)
      w i "val %s_elim (h: HS.mem) (input: LL.slice) (pos: U32.t) : Lemma\n" n;
      w i "  (requires (LL.valid %s_parser h input pos))\n" n;
      w i "  (ensures (\n";
      w i "    let pos' = LL.get_valid_pos %s_parser h input pos in\n" n;
      w i "    U32.v pos' - U32.v pos == %d /\\\n" li.max_len;
      w i "    LL.valid_list %s h input pos pos' /\\\n" (pcombinator_name ty0);
      w i "    LL.contents_list %s h input pos pos' == LL.contents %s_parser h input pos\n" (pcombinator_name ty0) n;
      w i "  ))\n";
      w o "let %s_elim h input pos = %s_eq (); LL.valid_array_valid_list %s %d %dul %d () h input pos\n\n" n n (scombinator_name ty0) li.max_len li.max_len li.max_count;
      (* lemmas about bytesize *)
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == L.length x `FStar.Mul.op_Star` %d) [SMTPat (%s_bytesize x)]\n\n" n n n elem_li.min_len n;
      w o "let %s_bytesize_eqn x =\n" n;
      w o "  assert_norm (LP.fldata_array_precond %s %d %d == true);\n" (pcombinator_name ty0) li.max_len li.max_count;
      w o "  LP.length_serialize_array %s %d %d () x\n\n"(scombinator_name ty0) li.max_len li.max_count;
      ()

    (* Fixed bytelen list of variable length elements *)
    | VectorFixed(k) ->
      w i "noextract val %s_list_bytesize: list %s -> GTot nat\n\n" n ty0;
      w o "let %s_list_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s) x)\n\n" n (scombinator_name ty0);
      w i "type %s = l:list %s{%s_list_bytesize l == %d}\n\n" n ty0 n k;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "type %s' = LP.parse_fldata_strong_t (LP.serialize_list _ %s) %d\n\n" n (scombinator_name ty0) k;
      w o "let %s_eq () : Lemma (%s' == %s) = assert_norm (%s' == %s)\n\n" n n n n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_fldata_strong (LP.serialize_list _ %s) %d\n\n" (scombinator_name ty0) k;
      w o "let %s_parser = %s_eq (); LP.coerce (LP.parser %s_parser_kind %s) %s'_parser\n\n" n n n n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_fldata_strong (LP.serialize_list _ %s) %d\n\n" (scombinator_name ty0) k;
      w o "let %s_serializer = %s_eq () ; LP.coerce (LP.serializer %s_parser) %s'_serializer\n\n" n n n n;
      write_bytesize o is_private n;
      w o "inline_for_extraction noextract let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      w o "  LP.parse32_fldata_strong (LP.serialize_list _ %s) (LP.parse32_list %s) %d %dul\n\n" (scombinator_name ty0) (pcombinator32_name ty0) k k;
      w o "let %s_parser32 = %s_eq (); LP.coerce (LP.parser32 %s_parser) %s'_parser32\n\n" n n n n;
      w o "inline_for_extraction noextract let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      w o "  LP.serialize32_fldata_strong (LP.partial_serialize32_list _ %s %s ()) %d\n\n" (scombinator_name ty0) (scombinator32_name ty0) k;
      w o "let %s_serializer32 = %s_eq (); LP.coerce (LP.serializer32 %s_serializer) %s'_serializer32\n\n" n n n n;
      w o "inline_for_extraction noextract let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      w o "  LP.size32_fldata_strong (LP.serialize_list _ %s) %d %dul\n\n" (scombinator_name ty0) k k;
      w o "let %s_size32 = %s_eq (); LP.coerce (LP.size32 %s_serializer) %s'_size32\n\n" n n n n;
      w o "inline_for_extraction let %s'_validator : LL.validator %s'_parser =\n" n n;
      w o "  LL.validate_fldata_strong (LL.serialize_list _ %s) (LL.validate_list %s ()) %d %dul\n\n" (scombinator_name ty0) (validator_name ty0) k k;
      w o "let %s_validator = %s_eq (); LP.coerce (LL.validator %s_parser) %s'_validator\n\n" n n n n;
      (* jumper not needed unless private, we are constant size *)
      if is_private then
       begin
        w o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser =\n" n n;
        w o "  LL.jump_fldata_strong (LL.serialize_list _ %s) %d %dul\n\n" (scombinator_name ty0) k k;
        w o "let %s_jumper : LL.jumper %s_parser = %s_eq (); LP.coerce (LL.jumper %s_parser) %s'_jumper\n\n" n n n n n
       end;
      ()

    (* Variable length bytes *)
    | VectorRange (low, high, repr) when ty0 = "U8.t" && (repr = 0 || repr = log256 high) ->
      w i "inline_for_extraction noextract let min_len = %d\ninline_for_extraction noextract let max_len = %d\n" low high;
      w i "type %s = b:bytes{%d <= length b /\\ length b <= %d}\n\n" n low high;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "noextract let %s_parser = LP.parse_bounded_vlbytes %d %d\n\n" n low high;
      w o "noextract let %s_serializer = LP.serialize_bounded_vlbytes %d %d\n\n" n low high;
      write_bytesize o is_private n;
      w o "let %s_parser32 = LP.parse32_bounded_vlbytes %d %dul %d %dul\n\n" n low low high high;
      w o "let %s_serializer32 = LP.serialize32_bounded_vlbytes %d %d\n\n" n low high;
      w o "let %s_size32 = LP.size32_bounded_vlbytes %d %d\n\n" n low high;
      if need_validator then  w o "inline_for_extraction let %s_validator = LL.validate_bounded_vlbytes %d %d\n\n" n low high;
      if need_jumper then begin
        let jumper_annot = if is_private then Printf.sprintf " : LL.jumper %s_parser" n else "" in
        w o "inline_for_extraction let %s_jumper%s = LL.jump_bounded_vlbytes %d %d\n\n" n jumper_annot low high
      end;
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + BY.length x) [SMTPat (%s_bytesize x)]\n\n" n n n li.len_len n;
      w o "let %s_bytesize_eqn x = LP.length_serialize_bounded_vlbytes %d %d x\n\n" n low high;
      (* length *)
      w i "val %s_length (input: LL.slice) (pos: U32.t) : HST.Stack U32.t\n" n;
      w i "  (requires (fun h -> LL.valid %s_parser h input pos))\n" n;
      w i "  (ensures (fun h res h' ->\n";
      w i "    let x = LL.contents %s_parser h input pos in\n" n;
      w i "    B.modifies B.loc_none h h' /\\\n";
      w i "    U32.v pos + %d + U32.v res == U32.v (LL.get_valid_pos %s_parser h input pos) /\\\n" li.len_len n;
      w i "    res == BY.len x /\\\n";
      w i "    B.as_seq h (B.gsub input.LL.base (pos `U32.add` %dul) res) == BY.reveal x\n" li.len_len;
      w i "  ))\n\n";
      w o "let %s_length input pos =\n" n;
      w o "  [@inline_let] let _ = assert_norm (%s == LP.parse_bounded_vlbytes_t %d %d) in\n" n low high;
      w o "  LL.bounded_vlbytes_payload_length %d %d input pos\n\n" low high;
      (* finalizer *)
      w i "val %s_finalize (input: LL.slice) (pos: U32.t) (len: U32.t) : HST.Stack U32.t\n\n" n;
      w i "  (requires (fun h ->\n";
      w i "    LL.live_slice h input /\\\n";
      w i "    %d <= U32.v len /\\ U32.v len <= %d /\\\n" low high;
      w i "    U32.v pos + %d + U32.v len <= U32.v input.LL.len\n" li.len_len;
      w i "  ))\n";
      w i "  (ensures (fun h pos' h' ->\n";
      w i "    let pos_payload = pos `U32.add` %dul in\n" li.len_len;
      w i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
      w i "    LL.valid_content_pos %s_parser h' input pos (BY.hide (B.as_seq h (B.gsub input.LL.base pos_payload len))) pos' /\\\n" n;
      w i "    U32.v pos' == U32.v pos_payload + U32.v len\n";
      w i "  ))\n\n";
      w o "let %s_finalize input pos len =\n" n;
      w o "  [@inline_let] let _ = assert_norm (%s == LP.parse_bounded_vlbytes_t %d %d) in\n" n low high;
      w o "  LL.finalize_bounded_vlbytes %d %d input pos len\n\n" low high;
      ()

    (* Variable length bytes where the size of the length is explicit *)
    | VectorRange (low, high, repr) when ty0 = "U8.t" ->
      w i "inline_for_extraction noextract let min_len = %d\ninline_for_extraction noextract let max_len = %d\n" low high;
      w i "type %s = b:bytes{%d <= length b /\\ length b <= %d}\n\n" n low high;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "noextract let %s_parser = LP.parse_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      w o "noextract let %s_serializer = LP.serialize_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      write_bytesize o is_private n;
      w o "let %s_parser32 = LP.parse32_bounded_vlbytes' %d %dul %d %dul %d\n\n" n low low high high repr;
      w o "let %s_serializer32 = LP.serialize32_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      w o "let %s_size32 = LP.size32_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      if need_validator then  w o "inline_for_extraction let %s_validator = LL.validate_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      if need_jumper then begin
        let jumper_annot = if is_private then Printf.sprintf " : LL.jumper %s_parser" n else "" in
        w o "inline_for_extraction let %s_jumper%s = LL.jump_bounded_vlbytes' %d %d %d\n\n" n jumper_annot low high repr
      end;
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + BY.length x) [SMTPat (%s_bytesize x)]\n\n" n n n repr n;
      w o "let %s_bytesize_eqn x = LP.length_serialize_bounded_vlbytes' %d %d %d x\n\n" n low high repr;
      (* length *)
      w i "val %s_length (input: LL.slice) (pos: U32.t) : HST.Stack U32.t\n" n;
      w i "  (requires (fun h -> LL.valid %s_parser h input pos))\n" n;
      w i "  (ensures (fun h res h' ->\n";
      w i "    let x = LL.contents %s_parser h input pos in\n" n;
      w i "    B.modifies B.loc_none h h' /\\\n";
      w i "    U32.v pos + %d + U32.v res == U32.v (LL.get_valid_pos %s_parser h input pos) /\\\n" repr n;
      w i "    res == BY.len x /\\\n";
      w i "    B.as_seq h (B.gsub input.LL.base (pos `U32.add` %dul) res) == BY.reveal x\n" repr;
      w i "  ))\n\n";
      w o "let %s_length input pos =\n" n;
      w o "  [@inline_let] let _ = assert_norm (%s == LP.parse_bounded_vlbytes_t %d %d) in\n" n low high;
      w o "  LL.bounded_vlbytes'_payload_length %d %d %d input pos\n\n" low high repr;
      (* finalizer *)
      w i "val %s_finalize (input: LL.slice) (pos: U32.t) (len: U32.t) : HST.Stack U32.t\n\n" n;
      w i "  (requires (fun h ->\n";
      w i "    LL.live_slice h input /\\\n";
      w i "    %d <= U32.v len /\\ U32.v len <= %d /\\\n" low high;
      w i "    U32.v pos + %d + U32.v len <= U32.v input.LL.len\n" repr;
      w i "  ))\n";
      w i "  (ensures (fun h pos' h' ->\n";
      w i "    let pos_payload = pos `U32.add` %dul in\n" repr;
      w i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
      w i "    LL.valid_content_pos %s_parser h' input pos (BY.hide (B.as_seq h (B.gsub input.LL.base pos_payload len))) pos' /\\\n" n;
      w i "    U32.v pos' == U32.v pos_payload + U32.v len\n";
      w i "  ))\n\n";
      w o "let %s_finalize input pos len =\n" n;
      w o "  [@inline_let] let _ = assert_norm (%s == LP.parse_bounded_vlbytes_t %d %d) in\n" n low high;
      w o "  LL.finalize_bounded_vlbytes' %d %d %d input pos len\n\n" low high repr;
      ()
      
    (* Variable length list of fixed-length elements *)
    | VectorRange (low, high, _) when elem_li.min_len = elem_li.max_len ->
      w i "inline_for_extraction noextract let min_count = %d\ninline_for_extraction noextract let max_count = %d\n" li.min_count li.max_count;
      w i "type %s = l:list %s{%d <= L.length l /\\ L.length l <= %d}\n\n" n ty0 li.min_count li.max_count;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "let %s_parser =\n" n;
      w o "  [@inline_let] let _ = assert_norm (LP.vldata_vlarray_precond %d %d %s %d %d == true) in\n" low high (pcombinator_name ty0) li.min_count li.max_count;
      w o "  LP.parse_vlarray %d %d %s %d %d ()\n\n" low high (scombinator_name ty0) li.min_count li.max_count;
      w o "let %s_serializer =\n" n;
      w o "  LP.serialize_vlarray %d %d %s %d %d ()\n\n" low high (scombinator_name ty0) li.min_count li.max_count;
      write_bytesize o is_private n;
      w o "let %s_parser32 =\n" n;
      w o "  LP.parse32_vlarray %d %dul %d %dul %s %s %d %d ()\n\n" low low high high (scombinator_name ty0) (pcombinator32_name ty0) li.min_count li.max_count;
      w o "let %s_serializer32 =\n" n;
      w o "  LP.serialize32_vlarray %d %d #_ #_ #_ #%s %s %d %d ()\n\n" low high (scombinator_name ty0) (scombinator32_name ty0) li.min_count li.max_count;
      w o "let %s_size32 =\n" n;
      w o "  [@inline_let] let _ = assert_norm (LP.vldata_vlarray_precond %d %d %s %d %d == true) in\n" low high (pcombinator_name ty0) li.min_count li.max_count;
      w o "  LP.size32_vlarray %d %d %s %d %d () %dul %dul\n\n" low high (scombinator_name ty0) li.min_count li.max_count li.len_len elem_li.min_len;
      if need_validator then begin
        w o "let %s_validator =\n" n;
        w o " LL.validate_vlarray %d %d %s %s %d %d () %dul\n\n" low high (scombinator_name ty0) (validator_name ty0) li.min_count li.max_count li.len_len
      end;
      if need_jumper then begin
        let jumper_annot = if is_private then Printf.sprintf " : LL.jumper %s_parser" n else "" in
        w o "let %s_jumper%s =\n" n jumper_annot;
        w o " LL.jump_vlarray %d %d %s %d %d () %dul\n\n" low high (scombinator_name ty0) li.min_count li.max_count li.len_len
      end;
      (* finalizer *)
      w i "inline_for_extraction val finalize_%s (sl: LL.slice) (pos pos' : U32.t) : HST.Stack unit\n" n;
      w i "(requires (fun h ->\n";
      w i "  U32.v pos + %d < 4294967296 /\\\n" li.len_len;
      w i "  LL.valid_list %s h sl (pos `U32.add` %dul) pos' /\\ (\n" (pcombinator_name ty0) li.len_len;
      w i "  let count = L.length (LL.contents_list %s h sl (pos `U32.add` %dul) pos') in\n" (pcombinator_name ty0) li.len_len;
      w i "  let len = U32.v pos' - (U32.v pos + %d) in\n" li.len_len;
      w i "  ((%d <= len /\\ len <= %d) \\/ (%d <= count /\\ count <= %d))\n" low high li.min_count li.max_count;
      w i ")))\n";
      w i "(ensures (fun h _ h' ->\n";
      w i "  B.modifies (LL.loc_slice_from_to sl pos (pos `U32.add` %dul)) h h' /\\ (\n" li.len_len;
      w i "  let l = LL.contents_list %s h sl (pos `U32.add` %dul) pos' in\n" (pcombinator_name ty0) li.len_len;
      w i "  %d <= L.length l /\\ L.length l <= %d /\\\n" li.min_count li.max_count;
      w i "  LL.valid_content_pos %s_parser h' sl pos l pos'\n" n;
      w i ")))\n\n";
      w o "let _ : squash (%s == LL.vlarray %s %d %d) = _ by (FStar.Tactics.trefl ())\n\n" n ty0 li.min_count li.max_count;
      w o "let finalize_%s sl pos pos' =\n" n;
      w o "  LL.finalize_vlarray %d %d %s %d %d sl pos pos'\n\n" low high (scombinator_name ty0) li.min_count li.max_count;
      (* length (elem count) and elim *)
      w i "val %s_count (input: LL.slice) (pos: U32.t) : HST.Stack U32.t\n" n;
      w i "  (requires (fun h -> LL.valid %s_parser h input pos))\n" n;
      w i "  (ensures (fun h res h' ->\n";
      w i "    let x = LL.contents %s_parser h input pos in\n" n;
      w i "    let pos' = LL.get_valid_pos %s_parser h input pos in\n" n;
      w i "    U32.v res == L.length x /\\\n";
      w i "    U32.v pos' == U32.v pos + %d + (U32.v res `FStar.Mul.op_Star` %d) /\\\n" li.len_len elem_li.min_len;
      w i "    LL.valid_list %s h input (pos `U32.add` %dul) pos' /\\\n" (pcombinator_name ty0) li.len_len;
      w i "    LL.contents_list %s h input (pos `U32.add` %dul) pos' == x\n" (pcombinator_name ty0) li.len_len;
      w i "  ))\n";
      w o "let %s_count input pos = LL.vlarray_list_length %d %d %s %d %d input pos\n\n" n low high (scombinator_name ty0) li.min_count li.max_count;
      (* nth *)
      w i "let %s_clens_nth (i: nat) : Tot (LL.clens %s %s) = {\n" n n ty0;
      w i "  LL.clens_cond = (fun (l: %s) -> i < L.length l);\n" n;
      w i "  LL.clens_get = (fun (l: %s) -> L.index l i);\n" n;
      w i "}\n\n";
      w i "val %s_nth_ghost (i: nat) : Tot (LL.gaccessor %s_parser %s (%s_clens_nth i))\n\n" n n (pcombinator_name ty0) n;
      w o "let %s_nth_ghost i = LL.vlarray_nth_ghost %d %d %s %d %d i\n\n" n low high (scombinator_name ty0) li.min_count li.max_count;
      w i "val %s_nth (i: U32.t) : Tot (LL.accessor (%s_nth_ghost (U32.v i)))\n\n" n n;
      w o "let %s_nth i = LL.vlarray_nth %d %d %s %d %d i\n\n" n low high (scombinator_name ty0) li.min_count li.max_count;
      (* lemmas about bytesize *)
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + (L.length x `FStar.Mul.op_Star` %d)) [SMTPat (%s_bytesize x)]\n\n" n n n li.len_len elem_li.min_len n;
      w o "let %s_bytesize_eqn x = LP.length_serialize_vlarray %d %d %s %d %d () x\n\n" n low high (scombinator_name ty0) li.min_count li.max_count;
      ()

    (* Variable length list of variable length elements *)
    | VectorRange(low, high, _) ->
      let (min, max) = (li.min_len-li.len_len), (li.max_len-li.len_len) in
      w i "noextract val %s_list_bytesize: list %s -> GTot nat\n\n" n ty0;
      w o "let %s_list_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s) x)\n\n" n (scombinator_name ty0);
      w i "type %s = l:list %s{let x = %s_list_bytesize l in %d <= x /\\ x <= %d}\n\n" n ty0 n min max;
      w i "val %s_list_bytesize_nil : squash (%s_list_bytesize [] == 0)\n\n" n n;
      w o "let %s_list_bytesize_nil = LP.serialize_list_nil %s %s\n\n" n (pcombinator_name ty0) (scombinator_name ty0);
      w i "val %s_list_bytesize_cons (x: %s) (y: list %s) : Lemma (%s_list_bytesize (x :: y) == %s + %s_list_bytesize y) [SMTPat (%s_list_bytesize (x :: y))]\n\n" n ty0 ty0 n (bytesize_call ty0 "x") n n;
      w o "let %s_list_bytesize_cons x y = LP.serialize_list_cons %s %s x y; %s\n\n" n (pcombinator_name ty0) (scombinator_name ty0) (bytesize_eq_call ty0 "x");
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d (LP.serialize_list _ %s)\n\n" n min max (scombinator_name ty0);
      w o "inline_for_extraction let synth_%s (x: %s') : Tot %s = x\n\n" n n n;
      w o "inline_for_extraction let synth_%s_recip (x: %s) : Tot %s' = x\n\n" n n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_bounded_vldata_strong %d %d (LP.serialize_list _ %s)\n\n" min max (scombinator_name ty0);
      w o "let %s_parser = %s'_parser `LP.parse_synth` synth_%s \n\n" n n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_bounded_vldata_strong %d %d (LP.serialize_list _ %s)\n\n" min max (scombinator_name ty0);
      w o "let %s_serializer = LP.serialize_synth _ synth_%s %s'_serializer synth_%s_recip ()\n\n" n n n n;
      write_bytesize o is_private n;
      w o "inline_for_extraction noextract let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      w o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul (LP.serialize_list _ %s) (LP.parse32_list %s)\n\n" min min max max (scombinator_name ty0) (pcombinator32_name ty0);
      w o "let %s_parser32 = LP.parse32_synth' _ synth_%s %s'_parser32 ()\n\n" n n n;
      w o "inline_for_extraction noextract let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      w o "  LP.serialize32_bounded_vldata_strong %d %d (LP.partial_serialize32_list _ %s %s ())\n\n" min max (scombinator_name ty0) (scombinator32_name ty0);
      w o "let %s_serializer32 = LP.serialize32_synth' _ synth_%s _ %s'_serializer32 synth_%s_recip ()\n\n" n n n n;
      w o "inline_for_extraction noextract let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      w o "  LP.size32_bounded_vldata_strong %d %d (LP.size32_list %s ()) %dul\n\n" min max (size32_name ty0) li.len_len;
      w o "let %s_size32 = LP.size32_synth' _ synth_%s _ %s'_size32 synth_%s_recip ()\n\n" n n n n;
      if need_validator then begin
        w o "inline_for_extraction let %s'_validator : LL.validator %s'_parser =\n" n n;
        w o "  LL.validate_bounded_vldata_strong %d %d (LP.serialize_list _ %s) (LL.validate_list %s ()) ()\n\n" min max (scombinator_name ty0) (validator_name ty0);
        w o "let %s_validator = LL.validate_synth %s'_validator synth_%s ()\n\n" n n n
      end;
      if need_jumper then begin
        w o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser =\n" n n;
        w o "  LL.jump_bounded_vldata_strong %d %d (LP.serialize_list _ %s) ()\n\n" min max (scombinator_name ty0);
        let jumper_annot = if is_private then Printf.sprintf " : LL.jumper %s_parser" n else "" in
        w o "let %s_jumper%s = LL.jump_synth %s'_jumper synth_%s ()\n\n" n jumper_annot n n
      end;
      (* finalizer *)
      w i "inline_for_extraction val finalize_%s (sl: LL.slice) (pos pos' : U32.t) : HST.Stack unit\n" n;
      w i "(requires (fun h ->\n";
      w i "  U32.v pos + %d < 4294967296 /\\\n" li.len_len;
      w i "  LL.valid_list %s h sl (pos `U32.add` %dul) pos' /\\ (\n" (pcombinator_name ty0) li.len_len;
      w i "  let len = U32.v pos' - (U32.v pos + %d) in\n" li.len_len;
      w i "  let len_ser = %s_list_bytesize (LL.contents_list %s h sl (pos `U32.add` %dul) pos') in\n" n (pcombinator_name ty0) li.len_len;
      w i "  ((%d <= len /\\ len <= %d) \\/ (%d <= len_ser /\\ len_ser <= %d))\n" low high low high;
      w i ")))\n";
      w i "(ensures (fun h _ h' ->\n";
      w i "  B.modifies (LL.loc_slice_from_to sl pos (pos `U32.add` %dul)) h h' /\\ (\n" li.len_len;
      w i "  let l = LL.contents_list %s h sl (pos `U32.add` %dul) pos' in\n" (pcombinator_name ty0) li.len_len;
      w i "  %s_list_bytesize l == U32.v pos' - (U32.v pos + %d) /\\\n" n li.len_len;
      w i "  LL.valid_content_pos %s_parser h' sl pos l pos'\n" n;
      w i ")))\n\n";
      (*
      w o "let _ : squash (%s == LL.parse_bound %s %d %d) = _ by (FStar.Tactics.trefl ())\n\n" n ty0 li.min_count li.max_count;
       *)
      w o "let finalize_%s sl pos pos' =\n" n;
      w o "  LL.finalize_bounded_vldata_strong_list %d %d %s sl pos pos';\n" low high (scombinator_name ty0);
      w o "  let h = HST.get () in\n";
      w o "  LL.valid_synth h %s'_parser synth_%s sl pos\n\n" n n;
      (* elim *)
      w i "val %s_elim (h: HS.mem) (input: LL.slice) (pos: U32.t) : Lemma\n" n;
      w i "  (requires (LL.valid %s_parser h input pos))\n" n;
      w i "  (ensures (\n";
      w i "    let pos' = LL.get_valid_pos %s_parser h input pos in\n" n;
      w i "    U32.v pos + %d <= U32.v pos' /\\ (\n" li.len_len;
      w i "    let pos1 = pos `U32.add` %dul in\n" li.len_len;
      w i "    LL.valid_list %s h input pos1 pos' /\\\n" (pcombinator_name ty0);
      w i "    LL.contents_list %s h input pos1 pos' == LL.contents %s_parser h input pos\n" (pcombinator_name ty0) n;
      w i "  )))\n\n";
      w o "let %s_elim h input pos =\n" n;
      w o "  LL.valid_synth h %s'_parser synth_%s input pos;\n" n n;
      w o "  LL.valid_bounded_vldata_strong_list_valid_list %d %d %s %s input pos h\n\n" low high (pcombinator_name ty0) (scombinator_name ty0);
      (* lemmas about bytesize *)
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + %s_list_bytesize x) [SMTPat (%s_bytesize x)]\n\n" n n n li.len_len n n;
      w o "let %s_bytesize_eqn x = LP.serialize_synth_eq %s'_parser synth_%s %s'_serializer synth_%s_recip () x" n n n n n;
      ()

and compile_struct o i n (fl: struct_field_t list) (al:attr list) =
  let li = get_leninfo n in
  let is_private = has_attr al "private" in

  (* Hoist all constructed types (select, vector, etc) into
     sub-definitions using private attribute in implementation *)
  let fields = List.map (fun (al, ty, fn, vec, def) ->
    if has_attr al "implicit" then failwith "Only tags of select() can be implicit currently";
    let fn0 = String.uncapitalize_ascii fn in
    match ty, vec with
    | TypeSimple ty0, VectorNone ->
      (fn0, compile_type ty0)
    | _ ->
      let n' = sprintf "%s_%s" n fn in
      let p = Typedef (al, ty, fn, vec, def) in
      let (o', i') = open_files n' in
      compile o' i' n p;
      w i "(* Type of field %s*)\ninclude %s\n\n" fn (module_name n');
      w o "(* Type of field %s*)\nopen %s\n\n" fn (module_name n');
      (* compile_typedef o i n fn ty vec def ("private"::al); *)
      (fn0, n')) fl in

  (* application type *)
  if fields = [] then
    w i "type %s = lbytes 0\n\n" n
  else
   begin
    w i "type %s = {\n" n;
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
   end;

  w o "inline_for_extraction let synth_%s_recip (x: %s) : %s' =\n" n n n;
  let tuple =
    if fields = [] then "x"
    else List.fold_left (fun acc (fn, ty) ->
      if acc="" then "x."^fn else sprintf "(%s, x.%s)" acc fn) "" fields in
  w o "  %s\n\n" tuple;

  (* Write parser API *)
  write_api o i is_private li.meta n li.min_len li.max_len;

  (* synthetizer injectivity and inversion lemmas *)
  let case_count = List.length fields in

  w o "let synth_%s_recip_inverse' () : Tot (squash (LP.synth_inverse synth_%s_recip synth_%s)) =\n" n n n;
  if case_count = 0
  then w o "  ()\n\n"
  else w o "  _ by (LP.synth_pairs_to_struct_to_pairs_tac' %d)\n\n" (case_count - 1);
  w o "let synth_%s_recip_inverse () : Lemma (LP.synth_inverse synth_%s_recip synth_%s) =\n" n n n;
  w o "  synth_%s_recip_inverse' ()\n\n" n;
  w o "let synth_%s_injective () : Lemma (LP.synth_injective synth_%s) =\n" n n;
  w o "  LP.synth_inverse_synth_injective synth_%s_recip synth_%s;\n" n n;
  w o "  synth_%s_recip_inverse ()\n\n" n;
  w o "let synth_%s_inverse () : Lemma (LP.synth_inverse synth_%s synth_%s_recip) =\n" n n n;
  w o "  assert_norm (LP.synth_inverse synth_%s synth_%s_recip)\n\n" n n;
  w o "let synth_%s_recip_injective () : Lemma (LP.synth_injective synth_%s_recip) =\n" n n;
  w o "  LP.synth_inverse_synth_injective synth_%s synth_%s_recip;\n" n n;
  w o "  synth_%s_inverse ()\n\n" n;

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
  write_bytesize o is_private n;

  (* main parser32 *)
  w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
  if fields = [] then w o "  LP.parse32_flbytes 0 0ul";
  let tuple = List.fold_left (
    fun acc (fn, ty) ->
      let c = pcombinator32_name ty in
      if acc="" then c else sprintf "%s\n  `LP.parse32_nondep_then` %s" acc c
    ) "" fields in
  w o "  %s\n\n" tuple;
  w o "let %s_parser32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
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

  w o "let %s_serializer32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize32_synth _ synth_%s _ %s'_serializer32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;

  w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
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

  (* validator *)
  if need_validator li.meta li.min_len li.max_len then
   begin
    w o "inline_for_extraction let %s'_validator : LL.validator %s'_parser =\n" n n;
    if fields = [] then w o "  LL.validate_flbytes 0 0ul";
    let tuple = List.fold_left (
      fun acc (fn, ty) ->
        let c = validator_name ty in
        if acc="" then c else sprintf "%s\n  `LL.validate_nondep_then` %s" acc c
      ) "" fields in
    w o "  %s\n\n" tuple;
    w o "let %s_validator =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
    w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
    w o "  LL.validate_synth %s'_validator synth_%s ()\n\n" n n
   end;

  (* jumper *)
  if need_jumper li.min_len li.max_len then
   begin
    w o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser =\n" n n;
    if fields = [] then w o "  LL.jump_flbytes 0 0ul";
    let tuple = List.fold_left (
      fun acc (fn, ty) ->
        let c = jumper_name ty in
        if acc="" then c else sprintf "%s\n  `LL.jump_nondep_then` %s" acc c
      ) "" fields in
    w o "  %s\n\n" tuple;
    w o "let %s_jumper =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
    w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
    w o "  LL.jump_synth %s'_jumper synth_%s ()\n\n" n n
   end;

  (* bytesize *)
  w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %s) [SMTPat (%s_bytesize x)]\n\n"
    n n n
    (List.fold_left
       (fun acc (fn, ty) ->
         let x' = sprintf "x.%s" fn in
         let bs = bytesize_call ty x' in
         if acc = "" then bs else sprintf "%s + %s" acc bs
       )
       ""
       fields
    )
    n
  ;
  w o "let %s_bytesize_eqn x =\n" n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize_synth_eq _ synth_%s %s'_serializer synth_%s_recip () x" n n n;
  begin match fields with
  | [] -> ()
  | (fn1, ty1) :: qf ->
     List.fold_left
       (fun (lhs, arg) (fn, ty) ->
         let s = scombinator_name ty in
         let arg' = sprintf "(%s, x.%s)" arg fn in
         w o ";\n  LP.serialize_nondep_then_eq _ %s () _ %s %s" lhs s arg';
         let lhs' = sprintf "(LP.serialize_nondep_then _ %s () _ %s)" lhs s in
         (lhs', arg')
       )
       (scombinator_name ty1, sprintf "x.%s" fn1)
       qf
     ;
     List.iter
       (fun (fn, ty) ->
         let bseq = bytesize_eq_call ty (sprintf "x.%s" fn) in
         if bseq <> "()" then w o ";\n  %s" bseq
       )
       fields
     ;
     w o "\n\n"
  end;

  (* accessors for fields *)
  begin
    let write_accessor fn ty g_before_synth a_before_synth =
      w i "val gaccessor_%s_%s : LL.gaccessor %s_parser %s clens_%s_%s\n\n" n fn n (pcombinator_name ty) n fn;
      w o "let gaccessor''_%s_%s : LL.gaccessor %s_parser %s _ =\n" n fn n (pcombinator_name ty);
      w o "  assert_norm (%s_parser_kind == %s'_parser_kind);\n" n n;
      w o "  synth_%s_recip_inverse (); synth_%s_inverse (); synth_%s_recip_injective (); synth_%s_injective ();\n" n n n n;
      w o "  LL.gaccessor_synth %s'_parser synth_%s synth_%s_recip () `LL.gaccessor_compose` %s\n\n" n n n g_before_synth;
      w o "let clens'_%s_%s : LL.clens %s %s = LL.get_gaccessor_clens gaccessor''_%s_%s\n\n" n fn n ty n fn;
      w o "let gaccessor'_%s_%s : LL.gaccessor %s_parser %s clens'_%s_%s = gaccessor''_%s_%s\n\n" n fn n (pcombinator_name ty) n fn n fn;
      w o "let clens_%s_%s_eq : squash (LL.clens_eq clens'_%s_%s clens_%s_%s) =\n" n fn n fn n fn;
      w o "  (LL.clens_eq_intro' _ _ (fun x -> _ by (FStar.Tactics.(norm [delta; iota; primops]; smt ()))) (fun x h -> _ by (FStar.Tactics.(norm [delta; iota; primops]; smt ()))))\n\n";
      w o "let gaccessor_%s_%s =\n" n fn;
      w o "  LL.gaccessor_ext gaccessor'_%s_%s clens_%s_%s clens_%s_%s_eq\n\n" n fn n fn n fn;
      w i "inline_for_extraction val accessor_%s_%s : LL.accessor gaccessor_%s_%s\n\n" n fn n fn;
      w o "inline_for_extraction let accessor'_%s_%s : LL.accessor gaccessor'_%s_%s =\n" n fn n fn;
      w o "  assert_norm (%s_parser_kind == %s'_parser_kind);\n" n n;
      w o "  synth_%s_recip_inverse (); synth_%s_inverse (); synth_%s_recip_injective (); synth_%s_injective ();\n" n n n n;
      w o "  LL.accessor_compose (LL.accessor_synth %s'_parser synth_%s synth_%s_recip ()) %s ()\n\n" n n n a_before_synth;
      w o "let accessor_%s_%s =\n" n fn;
      w o "  LL.accessor_ext accessor'_%s_%s clens_%s_%s clens_%s_%s_eq\n\n" n fn n fn n fn;
      ()
    in
    (* write the lenses *)
    List.iter
      (fun (fn, ty) ->
        w i "noextract let clens_%s_%s : LL.clens %s %s = {\n" n fn n ty;
        w i "  LL.clens_cond = (fun _ -> True);\n";
        w i "  LL.clens_get = (fun x -> x.%s);\n" fn;
        w i "}\n\n";
      )
      fields;
    match fields with
    | [] -> ()
    | [(fn, ty)] -> failwith "1-field struct should have been turned into its field"
    | (fn1, ty1) :: fields_tl ->
       (* produce the accessor for the first field *)
       let leftmost_gaccessor = List.fold_left (fun g (_, ty) -> Printf.sprintf "(LL.gaccessor_fst_then %s %s ())" g (pcombinator_name ty)) (Printf.sprintf "(LL.gaccessor_id %s)" (pcombinator_name ty1)) fields_tl in
       let leftmost_accessor = List.fold_left (fun g (_, ty) -> Printf.sprintf "(LL.accessor_fst_then %s %s ())" g (pcombinator_name ty)) (Printf.sprintf "(LL.accessor_id %s)" (pcombinator_name ty1)) fields_tl in
       write_accessor fn1 ty1 leftmost_gaccessor leftmost_accessor;
       (* for each field starting from the second one, build the left-hand-side parser and jumper at the time accessor_snd will be called *)
       let (_, pj_lhs_tl_rev) =
         List.fold_left
           (fun ((parser_lhs, jumper_lhs) as pj_lhs, pj_lhs_tl_rev) ((_, ty) as fd) ->
             let parser_lhs' = Printf.sprintf "(%s `LP.nondep_then` %s)" parser_lhs (pcombinator_name ty) in
             let jumper_lhs' = Printf.sprintf "(%s `LL.jump_nondep_then` %s)" jumper_lhs (jumper_name ty) in
             let pj_lhs_tl_rev' = (fd, pj_lhs) :: pj_lhs_tl_rev in
             ((parser_lhs', jumper_lhs'), pj_lhs_tl_rev')
           )
           ((pcombinator_name ty1, jumper_name ty1), [])
           fields_tl
       in
       let pj_lhs_tl = List.rev pj_lhs_tl_rev in
       (* produce the accessors for the other fields *)
       let rec produce_accessors = function
         | [] -> ()
         | ((fn, ty), (parser_lhs, jumper_lhs)) :: q ->
            let gaccessor_before_synth =
              List.fold_left
                (fun g ((_, ty'), _) ->
                  Printf.sprintf "(LL.gaccessor_fst_then %s %s ())" g (pcombinator_name ty'))
                (Printf.sprintf "(LL.gaccessor_snd %s %s)" parser_lhs (pcombinator_name ty))
                q
            in
            let accessor_before_synth =
              List.fold_left
                (fun g ((_, ty'), _) ->
                  Printf.sprintf "(LL.accessor_fst_then %s %s ())" g (pcombinator_name ty'))
                (Printf.sprintf "(LL.accessor_snd %s %s)" jumper_lhs (pcombinator_name ty))
                q
            in
            write_accessor fn ty gaccessor_before_synth accessor_before_synth;
            produce_accessors q
       in
       produce_accessors pj_lhs_tl;
       ()
  end;
  ()

(* Rewrite {... uintX len; t value[len]; ...} into VectorVldata *)
and normalize_symboliclen sn (fl:struct_field_t list) : struct_field_t list =
  match fl with
  | [] -> []
  | (al, TypeSimple(tagt), tagn, VectorNone, None)
    :: (al', ty, n, VectorSymbolic k, None) :: r
    when tagn = k ->
      let h =
        match ty with
        | TypeSimple ty -> (al @ al', TypeSimple ty, n, VectorVldata tagt, None)
        | TypeSelect (sel, cl, def) ->
          let r = ref [] in
          let cl' = List.map (fun (c,t)->
              let etyp = sprintf "%s_%s_%s" sn n c in
              r := (etyp, t) :: !r; (c, etyp)
            ) cl in
          let def' = match def with
            | None -> None
            | Some ty ->
              let etyp = sprintf "%s_%s_default" sn n in
              r := (etyp, ty) :: !r; Some etyp
            in
          List.iter (fun (etyp, t) ->
            let p = Typedef(al @ al', TypeSimple t, etyp, VectorVldata tagt, None) in
            let (o', i') = open_files etyp in
            compile o' i' "" p
          ) !r;
          (al @ al', TypeSelect(sel, cl', def'), n, VectorNone, None)
        in
      h :: (normalize_symboliclen sn r)
  | h :: t -> h :: (normalize_symboliclen sn t)

(* Hoist {... tag t; select(t){} ...} when other fields are present *)
and normalize_select sn (fl:struct_field_t list)
  (acc:struct_field_t list) (acc':tag_select_t list)
  : struct_field_t list * tag_select_t list =
  match fl with
  | [] -> List.rev acc, List.rev acc'
  | (al, TypeSimple(tagt), tagn, VectorNone, None)
    :: (al', TypeSelect (tagn', cases, def), seln, VectorNone, None)
    :: r when tagn = tagn' ->
    let etyp = sprintf "%s_%s" sn seln in
    let sel' = (al, al', etyp, tagn, seln, tagt, cases, def) in
    let f' = (al, TypeSimple etyp, seln, VectorNone, None) in
    normalize_select sn r (f'::acc) (sel'::acc')
  | (_, TypeSelect (_, _, _), seln, _, _) :: t ->
    failwith (sprintf "Field %s contains an invalid select in struct %s" seln sn)
  | h :: t -> normalize_select sn t (h::acc) acc'

(* Global type Substitution, this is use for staging sums on implicit tags *)
and subst_of (x:typ) = try SM.find x !subst with _ -> x
and apply_subst_t (t:type_t) =
  match t with
  | TypeSimple(ty) -> TypeSimple(subst_of ty)
  | TypeSelect(sel, cl, def) ->
    let cl' = List.map (fun (case, ty) -> case, subst_of ty) cl in
    let def' = match def with None -> None | Some ty -> Some (subst_of ty) in
    TypeSelect(sel, cl', def')
and apply_subst_field (al, ty, n, vec, def) = al, apply_subst_t ty, n, vec, def
and apply_subst (p:gemstone_t) =
  match p with
  | Enum _ -> p
  | Typedef tdef -> Typedef (apply_subst_field tdef)
  | Struct(al, fl, n) ->
    let fl' = List.map apply_subst_field fl in
    Struct(al, fl', n)

and compile o i (tn:typ) (p:gemstone_t) =
  let p = apply_subst p in
  let n = if tn = "" then tname true p else tn^"_"^(tname false p) in
  let mn = module_name n in
  let (fst, fsti) = !headers in

  (* .fsti *)
  w i "module %s\n\n" mn;
  w i "open %s\n" !bytes;
  w i "module U8 = FStar.UInt8\n";
  w i "module U16 = FStar.UInt16\n";
  w i "module U32 = FStar.UInt32\n";
  w i "module LP = LowParse.SLow.Base\n";
  w i "module LPI = LowParse.Spec.Int\n";
  w i "module LL = LowParse.Low.Base\n";
  w i "module L = FStar.List.Tot\n";
  w i "module B = LowStar.Buffer\n";
  w i "module BY = FStar.Bytes\n";
  w i "module HS = FStar.HyperStack\n";
  w i "module HST = FStar.HyperStack.ST\n";
  (List.iter (w i "%s\n") (List.rev fsti));
  w i "\n";

  (* .fst *)
  w o "module %s\n\n" mn;
  w o "open %s\n" !bytes;
  w o "module U8 = FStar.UInt8\n";
  w o "module U16 = FStar.UInt16\n";
  w o "module U32 = FStar.UInt32\n";
	w o "module LP = LowParse.SLow\n";
  w o "module LPI = LowParse.Spec.Int\n";
  w o "module LL = LowParse.Low\n";
	w o "module L = FStar.List.Tot\n";
  w o "module B = LowStar.Buffer\n";
  w o "module BY = FStar.Bytes\n";
  w o "module HS = FStar.HyperStack\n";
  w o "module HST = FStar.HyperStack.ST\n";
  (List.iter (w o "%s\n") (List.rev fst));
  w o "\n";

  (* Rewrite synbolic vldata before computing length *)
  let p = match p with
    | Struct(al, fl, nn) -> Struct(al, normalize_symboliclen n fl, nn)
    | p -> p in

  let depl = getdep (tn = "") p in
  let depl = List.filter (fun x -> not (basic_type x)) depl in
  let depl = List.map module_name depl in
  (List.iter (fun dep ->
    if BatString.starts_with dep (mn^"_") then w i "include %s\n" dep
    else w i "open %s\n" dep) depl);
  w i "\n";

	w o "#reset-options \"--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2\"\n\n";

  try let _ =
    match p with
  	| Enum(al, fl, _) ->  compile_enum o i n fl al
    | Typedef(al, ty, n', vec, def) -> compile_typedef o i tn n' ty vec def al
    | Struct(al, fl, _) ->
      match normalize_select n fl [] [] with
      | [_, TypeSimple etyp', seln', VectorNone, None], [al, al', etyp, tagn, seln, tagt, cases, def] ->
        if etyp' <> etyp || seln' <> seln then failwith "Invalid rewrite of a select (QD bug)";
        compile_select o i n seln tagn tagt al cases def al'
      | fl, sell ->
        List.iter (fun (al, al', etyp, tagn, seln, tagt, cases, def) ->
          let p = Struct([], [(al, TypeSimple(tagt), tagn, VectorNone, None);
            (al', TypeSelect (tagn, cases, def), seln, VectorNone, None)], etyp) in
          let (o', i') = open_files etyp in
          compile o' i' "" p;
          w i "(* Internal select() for %s *)\ninclude %s\n\n" etyp (module_name etyp);
          w o "(* Internal select() for %s *)\nopen %s\n\n" etyp (module_name etyp);
        ) sell;
        match fl with
        | [] -> compile_typedef o i tn n (TypeSimple "empty") VectorNone None al
        | [(al, ty, _, vec, def)] -> compile_typedef o i tn n ty vec def al
        | _ -> compile_struct o i n fl al
  in close_files o i with e -> close_files o i; raise e

let rfc_generate_fstar (p:Rfc_ast.prog) =
  let aux (p:gemstone_t) =
	  let n = tname true p in
    let (o, i) = open_files n in
		compile o i "" p
	in List.iter aux p
