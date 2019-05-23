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

type ite_t =
  attr list * attr list * typ * typ * typ * int * string * typ * typ

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
let wh x = if !emit_high then fprintf x else ifprintf x
let wl x = if !emit_low then fprintf x else ifprintf x

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
  | "opaque" | "uint8" | "uint16" | "uint24" | "uint32"
  | "uint16_le" | "uint24_le" | "uint32_le"
  | "asn1_len" | "asn1_len8" | "bitcoin_varint"
  | "Empty" | "Fail" -> true
  | _ -> false

let basic_bounds = function
  | "uint8" -> 1, 1, 255
  | "uint16" | "uint16_le" -> 2, 2, 65535
  | "uint24" | "uint24_le" -> 3, 3, 16777215
  | "uint32" | "uint32_le" -> 4, 4, 4294967295
  | "asn1_len8" -> 1, 2, 255
  | "asn1_len" | "bitcoin_varint" -> 1, 5, 4294967295
  | s -> failwith (s^" is not a base type and can't be used as symbolic length")

let rec sizeof = function
  | TypeIfeq(tag, v, t, f) ->
    let lit = sizeof (TypeSimple t) in
    let lif = sizeof (TypeSimple f) in
    {len_len = 0; min_len = min lit.min_len lif.min_len; max_len = max lit.max_len lif.max_len;
      min_count = 0; max_count = 0; vl = lit.vl || lif.vl; meta =
      match lit.meta, lif.meta with
      | MetadataTotal, MetadataTotal -> MetadataTotal
      | MetadataFail, MetadataFail -> MetadataFail
      | _ -> MetadataDefault}
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
    | "uint16" | "uint16_le" -> { len_len = 0; min_len = 2; max_len = 2; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "uint24" | "uint24_le" -> { len_len = 0; min_len = 3; max_len = 3; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "uint32" | "uint32_le" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "asn1_len8" -> { len_len = 0; min_len = 1; max_len = 2; min_count = 0; max_count = 0; vl = true; meta = MetadataDefault }
    | "asn1_len"
    | "bitcoin_varint" -> { len_len = 0; min_len = 1; max_len = 5; min_count = 0; max_count = 0; vl = true; meta = MetadataDefault }
    | "Empty" -> { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0; vl = false; meta = MetadataTotal }
    | "Fail" -> { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0; vl = false; meta = MetadataFail }
    | s ->
      let li = get_leninfo s in
      {li with len_len = li.len_len} (* shallow copy *)

let compile_type = function
  | "opaque"
  | "uint8" -> "U8.t"
  | "uint16" | "uint16_le" -> "U16.t"
  | "uint24" | "uint24_le" -> "(LPI.bounded_integer 3)"
  | "uint32" | "uint32_le" -> "U32.t"
  | (( "asn1_len8" | "asn1_len") as s) -> failwith (sprintf "compile_type: for now %s not standalone" s)
  | "bitcoin_varint" -> "U32.t"
  | "Empty" -> "unit"
  | "Fail" -> "(squash False)"
  | t -> String.uncapitalize_ascii t

(* for size headers with bounds *)
let make_combinator_length_header_name combino dup x min max =
  let typename = match x with
    | "asn1_len8"
    | "asn1_len" -> "bounded_der_length32"
    | _ -> failwith (sprintf "make_combinator_length_header_name: %s not found" x)
  in
  let lengths = if dup then sprintf "%d %dul %d %dul" min min max max else sprintf "%d %d" min max in
  sprintf "(%s_%s %s)" combino typename lengths

let pcombinator_length_header_name = make_combinator_length_header_name "LPI.parse" false
let scombinator_length_header_name = make_combinator_length_header_name "LPI.serialize" false
let pcombinator32_length_header_name = make_combinator_length_header_name "LP.parse32" true
let scombinator32_length_header_name = make_combinator_length_header_name "LP.serialize32" false
let size32_length_header_name = make_combinator_length_header_name "LP.size32" false
let validator_length_header_name = make_combinator_length_header_name "LL.validate" true
let jumper_length_header_name = make_combinator_length_header_name "LL.jump" false
let reader_length_header_name = make_combinator_length_header_name "LL.read" false

let pcombinator_name = function
  | "opaque" | "uint8" -> "LPI.parse_u8"
  | "uint16" -> "LPI.parse_u16"
  | "uint16_le" -> "LPI.parse_u16_le"
  | "uint24" -> "(LPI.parse_bounded_integer 3)"
  | "uint24_le" -> "(LPI.parse_bounded_integer_le 3)"
  | "uint32" -> "LPI.parse_u32"
  | "uint32_le" -> "LPI.parse_u32_le"
  | "asn1_len" -> failwith "pcombinator_name: for now asn1_len not standalone"
  | "bitcoin_varint" -> "LPI.parse_bcvli"
  | "Empty" -> "LP.parse_empty"
  | "Fail" -> "LP.parse_false"
  | t -> String.uncapitalize_ascii t^"_parser"

let scombinator_name = function
  | "opaque" | "uint8" -> "LPI.serialize_u8"
  | "uint16" -> "LPI.serialize_u16"
  | "uint16_le" -> "LPI.serialize_u16_le"
  | "uint24" -> "(LPI.serialize_bounded_integer 3)"
  | "uint24_le" -> "(LPI.serialize_bounded_integer_le 3)"
  | "uint32" -> "LPI.serialize_u32"
  | "uint32_le" -> "LPI.serialize_u32_le"
  | "asn1_len" -> failwith "scombinator_name: for now asn1_len not standalone"
  | "bitcoin_varint" -> "LPI.serialize_bcvli"
  | "Empty" -> "LP.serialize_empty"
  | "Fail" -> "LP.serialize_false"
  | t -> String.uncapitalize_ascii t^"_serializer"

let pcombinator32_name = function
  | "opaque" | "uint8" -> "LP.parse32_u8"
  | "uint16" -> "LP.parse32_u16"
  | "uint16_le" -> "LP.parse32_u16_le"
  | "uint24" -> "(LP.parse32_bounded_integer 3)"
  | "uint24_le" -> "LP.parse32_bounded_integer_le_3"
  | "uint32" -> "LP.parse32_u32"
  | "uint32_le" -> "LP.parse32_u32_le"
  | "asn1_len" -> failwith "pcombinator32_name: for now asn1_len not standalone"
  | "bitcoin_varint" -> "LP.parse32_bcvli"
  | "Empty" -> "LP.parse32_empty"
  | "Fail" -> "LP.parse32_false"
  | t -> String.uncapitalize_ascii t^"_parser32"

let scombinator32_name = function
  | "opaque" | "uint8" -> "LP.serialize32_u8"
  | "uint16" -> "LP.serialize32_u16"
  | "uint16_le" -> "LP.serialize32_u16_le"
  | "uint24" -> "(LP.serialize32_bounded_integer 3)"
  | "uint24_le" -> "LP.serialize32_bounded_integer_le_3"
  | "uint32" -> "LP.serialize32_u32"
  | "uint32_le" -> "LP.serialize32_u32_le"
  | "asn1_len" -> failwith "scombinator32_name: for now asn1_len not standalone"
  | "bitcoin_varint" -> "LP.serialize32_bcvli"
  | "Empty" -> "LP.serialize32_empty"
  | "Fail" -> "LP.serialize32_false"
  | t -> String.uncapitalize_ascii  t^"_serializer32"

let size32_name = function
  | "opaque" | "uint8" -> "LP.size32_u8"
  | "uint16" -> "LP.size32_u16"
  | "uint16_le" -> "(LP.size32_constant LP.serialize_u16_le 2ul ())"
  | "uint24" -> "(LP.size32_constant (LP.serialize_bounded_integer 3) 3ul ())"
  | "uint24_le" -> "(LP.size32_constant (LP.serialize_bounded_integer_le 3) 3ul ())"
  | "uint32" -> "LP.size32_u32"
  | "uint32_le" -> "LP.size32_u32_le"
  | "asn1_len" -> failwith "size32_name: for now asn1_len not standalone"
  | "bitcoin_varint" -> "LP.size32_bcvli"
  | "Empty" -> "LP.size32_empty"
  | "Fail" -> "LP.size32_false"
  | t -> String.uncapitalize_ascii t^"_size32"

let validator_name = function
  | "opaque" | "uint8" -> "(LL.validate_u8 ())"
  | "uint16" -> "(LL.validate_u16 ())"
  | "uint16_le" -> "(LL.validate_u16_le ())"
  | "uint24" -> "(LL.validate_bounded_integer 3)"
  | "uint24_le" -> "(magic())"
  | "uint32" -> "(LL.validate_u32 ())"
  | "uint32_le" -> "(LL.validate_u32_le ())"
  | "asn1_len" -> failwith "validator_name: for now asn1_len not standalone"
  | "bitcoin_varint" -> "LL.validate_bcvli"
  | "Empty" -> "(LL.validate_empty ())"
  | "Fail" -> "(LL.validate_false ())"
  | t -> String.uncapitalize_ascii t^"_validator"

let jumper_name = function
  | "opaque" | "uint8" -> "LL.jump_u8"
  | "uint16" -> "LL.jump_u16"
  | "uint16_le" -> "LL.jump_u16_le"
  | "uint24" -> "(LL.jump_constant_size (LP.parse_bounded_integer 3) 3ul)"
  | "uint24_le" -> "(LL.jump_constant_size LP.parse_bounded_integer_le_3 3ul)"
  | "uint32" -> "LL.jump_u32"
  | "uint32_le" -> "LL.jump_u32_le"
  | "asn1_len" -> failwith "jumper_name: for now asn1_len not standalone"
  | "bitcoin_varint" -> "LL.jump_bcvli"
  | "Empty" -> "LL.jump_empty"
  | "Fail" -> "LL.jump_false"
  | t -> String.uncapitalize_ascii t^"_jumper"

let bytesize_call t x = match t with
  | "opaque" | "uint8" -> "1"
  | "uint16" | "uint16_le" -> "2"
  | "uint24" | "uint24_le" -> "3"
  | "uint32" | "uint32_le" -> "4"
  | "asn1_len" -> sprintf "(if U32.v %s < 128 then 1 else if U32.v %s < 256 then 2 else if U32.v %s < 65536 then 3 else if U32.v %s < 16777216 then 4 else 5)" x x x x
  | "bitcoin_varint" -> sprintf "(if U32.v %s <= 252 then 1 else if U32.v %s <= 65535 then 3 else 5)" x x
  | "Empty" | "Fail" -> "0"
  | _ -> sprintf "(%s_bytesize (%s))" (String.uncapitalize_ascii t) x

let bytesize_eq_call t x = match t with
  | "opaque" | "uint8" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_u8 (%s)) == 1))" x
  | "uint16" | "uint16_le" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_u16 (%s)) == 2))" x
  | "uint24" | "uint24_le" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (%s)) == 4))" x
  | "uint32" | "uint32_le" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (%s)) == 4))" x
  | "asn1_len" -> sprintf "(LP.serialize_bounded_der_length32_size 0 4294967295 %s)" x
  | "bitcoin_varint" -> sprintf "(LP.serialize_bcvli_eq %s)" x
  | "Empty" -> sprintf "(assert (FStar.Seq.length (LP.serialize LP.serialize_empty (%s)) == 0))" x
  | "Fail" -> sprintf "(assert False)"
  | _ -> sprintf "(%s_bytesize_eq (%s))" (String.uncapitalize_ascii t) x

let leaf_reader_name = function
  | "opaque" | "uint8" -> "LL.read_u8"
  | "uint16" -> "LL.read_u16"
  | "uint16_le" -> "LL.read_u16_le"
  | "uint24" -> "LL.read_u32"
  | "uint24_le" -> "LL.read_u32_le"
  | "uint32" -> "LL.read_u32"
  | "uint32_le" -> "LL.read_u32_le"
  | "asn1_len" -> "(LL.read_bounded_der_length32 0 4294967295)"
  | "bitcoin_varint" -> "LL.read_bcvli"
  | t -> failwith "leaf_reader_name: should only be called for enum repr"

let leaf_writer_name = function
  | "opaque" | "uint8" -> "LL.write_u8"
  | "uint16" -> "LL.write_u16"
  | "uint16_le" -> "LL.write_u16_le"
  | "uint24" -> "LL.write_u32"
  | "uint24_le" -> "LL.write_u32_le"
  | "uint32" -> "LL.write_u32"
  | "uint32_le" -> "LL.write_u32_le"
  | "asn1_len" -> "(LL.write_bounded_der_length32 0 4294967295)"
  | "bitcoin_varint" -> "LL.write_bcvli"
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
    | VectorFixedCount k ->
      { li with
        min_count = k;
        max_count = k;
        min_len = k * li.min_len;
        max_len = k * li.max_len;
        meta = if li.meta = MetadataFail then li.meta else MetadataDefault;
      }
    | VectorVldata tn ->
      let (len_len_min, len_len_max, max_len) = basic_bounds tn in
      let (li_min_len, li_max_len) =
        if ty = TypeSimple "opaque" then (0, max_len)
        else (li.min_len, li.max_len) in
      let max' = len_len_max + min max_len li_max_len in
      (*let min', max' = li.min_len, min li.max_len max_len in*)
      let meta' = if li.meta = MetadataFail then li.meta else MetadataDefault in
      {li with len_len = len_len_min; min_len = len_len_min + li_min_len; max_len = max'; vl = true; meta = meta' }
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
    | VectorCount (low, high, repr) ->
      let (l, h, meta) = match repr with
        | None -> let x = log256 high in (x, x, MetadataTotal)
        | Some t ->
          let (l, h, _) = basic_bounds t in
          let len_li = sizeof (TypeSimple t) in
          (l, h, len_li.meta)
        in
      { vl = true;
        min_count = low;
        max_count = high;
        len_len = h;
        min_len = l + low * li.min_len;
        max_len = h + high * li.max_len;
        meta = match li.meta with (* See parse_vclist_payload_kind *)
               | MetadataFail -> li.meta
               | d -> if high = 0 then meta else MetadataDefault;
      }
    | VectorRange (low, high, repr) ->
      let h = match repr with
        | None -> log256 high
        | Some t -> let (_, l, _) = basic_bounds t in l in
      (if h < log256 high then failwith (sprintf "Can't represent <%d..%d> over %d bytes" low high h));
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
  | TypeIfeq (tag, v, t, f) -> [t; f]
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
    wh i "val %s_parser32%s: LP.parser32 %s\n\n" n parg pparse;
    wh i "val %s_serializer32%s: LP.serializer32 %s\n\n" n parg pser;
    wh i "val %s_size32%s: LP.size32 %s\n\n" n parg pser;
    if need_validator md bmin bmax then
      wl i "val %s_validator%s: LL.validator %s\n\n" n parg pparse
    else
      wl i "let %s_validator%s: LL.validator %s = LL.validate_total_constant_size %s %dul ()\n\n" n parg pparse pparse bmin;
    if need_jumper bmin bmax then
      wl i "val %s_jumper%s: LL.jumper %s\n\n" n parg pparse
    else
      wl i "let %s_jumper%s: LL.jumper %s = LL.jump_constant_size %s %dul ()\n\n" n parg pparse pparse bmin;
    ()
   end

(* binary trees to compile struct fields into log nesting instead of a comb *)

type 'a btree =
  | TLeaf of 'a
  | TNode of (int * ('a btree) * ('a btree))

let rec btree_count (t: 'a btree) =
  match t with
  | TLeaf _ -> 1
  | TNode (n, _, _) -> n

let rec btree_insert (t: 'a btree) (x: 'a) =
  (* always insert to the right-hand-side, leaving the left-hand-side complete *)
  match t with
  | TLeaf y -> TNode (2, t, TLeaf x)
  | TNode (n, left, right) ->
     if btree_count left = btree_count right
     then TNode (n + 1, t, TLeaf x)
     else TNode (n + 1, left, btree_insert right x)

let rec btree_fold
          (f: 'global -> 'local -> 'elem -> 'global) pushl plpr popr (* : 'global -> 'global *) left right (* : 'local -> 'local *) (ginit: 'global) (linit: 'local) (t: 'elem btree) : 'global =
  match t with
  | TLeaf x -> f ginit linit x
  | TNode (_, tleft, tright) ->
     let g1 = btree_fold f pushl plpr popr left right (pushl ginit) (left linit) tleft in
     let g2 = btree_fold f pushl plpr popr left right (plpr g1) (right linit) tright in
     popr g2
  
let rec compile_enum o i n (fl: enum_field_t list) (al:attr list) =
  let is_open = has_attr al "open" in
  let is_private = has_attr al "private" in
  fields := SM.add n (fl, is_open) !fields;

  let repr_t, int_z, parse_t, blen =
	  let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
		        with _ -> failwith ("Enum "^n^" is missing a representation hint") in
	  match m with
		| EnumFieldAnonymous 255 -> "uint8", "z", "u8", 1
		| EnumFieldAnonymous 65535 -> "uint16", "us", "u16", 2
		| EnumFieldAnonymous 4294967295 -> "uint32", "ul", "u32", 4
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

    w i "let %s_repr = %s\n" n (compile_type repr_t);
    w i "inline_for_extraction let %s_repr_eq (x1 x2: %s_repr) : Tot bool = (x1 = x2)\n" n n;
    w i "let known_%s_repr (v:%s) : bool = %s\n\n" n (compile_type repr_t) unknown_formula
   end;

	w i "type %s =\n" n;
	List.iter (function
	  | EnumFieldSimple (x, _) ->
		  w i "  | %s\n" (String.capitalize_ascii x)
		| _ -> ()) fl;
  if is_open then
	  w i "  | Unknown_%s of (v:%s{not (known_%s_repr v)})\n\n" n (compile_type repr_t) n
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
	w o "inline_for_extraction let %s_enum : LP.enum %s %s =\n" n n (compile_type repr_t);
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
  if is_open then
   begin
  	w o "inline_for_extraction let synth_%s (x:LP.maybe_enum_key %s_enum) : %s = \n" n n n;
  	w o "  match x with\n";
  	w o "  | LP.Known k -> k\n";
  	w o "  | LP.Unknown y ->\n";
  	w o "    [@inline_let] let v : %s = y in\n" (compile_type repr_t);
  	w o "    [@inline_let] let _ = assert_norm (LP.list_mem v (LP.list_map snd %s_enum) == known_%s_repr v) in\n" n n;
    w o "    Unknown_%s v\n\n" n;
  	w o "inline_for_extraction let synth_%s_inv (x:%s) : LP.maybe_enum_key %s_enum = \n" n n n;
  	w o "  match x with\n";
  	w o "  | Unknown_%s y ->\n" n;
  	w o "    [@inline_let] let v : %s = y in\n" (compile_type repr_t);
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
   end
  else
   begin
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
  wh o "let parse32_%s%s_key : LP.parser32 parse_%s%s_key =\n" maybe n maybe n;
  wh o "  FStar.Tactics.synth_by_tactic (LP.parse32_%senum_key_tac LP.parse32_%s %s_enum)\n\n" maybe parse_t n;
  wh o "let %s_parser32 : LP.parser32 %s_parser =\n" n n ;
  wh o "  lemma_synth_%s_inj ();\n" n;
  wh o "  LP.parse32_synth _ synth_%s (fun x->synth_%s x) parse32_%s%s_key ()\n\n" n n maybe n;
	wh o "let serialize32_%s%s_key : LP.serializer32 serialize_%s%s_key =\n" maybe n maybe n;
  (if is_open then (* FIXME: harmonize the tactic name in LowParse *)
    wh o "  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac\n"
  else
    wh o "  FStar.Tactics.synth_by_tactic (LP.serialize32_enum_key_gen_tac\n");
  wh o "    LP.serialize32_%s %s_enum)\n\n" parse_t n;
  wh o "let %s_serializer32 : LP.serializer32 %s_serializer =\n" n n;
	wh o "  lemma_synth_%s_inj ();\n  lemma_synth_%s_inv ();\n" n n;
  wh o "  LP.serialize32_synth _ synth_%s _ serialize32_%s%s_key synth_%s_inv (fun x->synth_%s_inv x) ()\n\n" n maybe n n n;

  wh o "let %s_size32 =\n" n;
  wh o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond %s_serializer %dul) in\n" n blen;
  wh o "  LP.size32_constant %s_serializer %dul ()\n\n" n blen;

  (* Low: validator *)
  if is_open then
    () (* validator not needed, since maybe_enum_key is total constant size *)
  else
   begin
    wl o "inline_for_extraction let validate_%s%s_key : LL.validator parse_%s%s_key =\n" maybe n maybe n;
    wl o "  LL.validate_enum_key %s_repr_validator %s_repr_reader %s_enum (_ by (LP.maybe_enum_destr_t_tac ()))\n\n" n n n;
    wl o "let %s_validator =\n" n;
    wl o "  lemma_synth_%s_inj ();\n" n;
    wl o "  LL.validate_synth validate_%s%s_key synth_%s ()\n\n" maybe n n
   end;

  (* Low: reader *)
  begin
    if is_open then
      begin
        wl o "inline_for_extraction let read_maybe_%s_key : LL.leaf_reader parse_maybe_%s_key =\n" n n;
        wl o "  LL.read_maybe_enum_key %s_repr_reader %s_enum (_ by (LP.maybe_enum_destr_t_tac ()))\n\n" n n
      end
    else
      begin
        wl o "inline_for_extraction let read_%s_key : LL.leaf_reader parse_%s_key =\n" n n;
        wl o "  LL.read_enum_key %s_repr_reader %s_enum (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n n
      end
  end;
  wl i "val %s_reader: LL.leaf_reader %s_parser\n\n" n n;
  wl o "let %s_reader =\n" n;
  wl o " [@inline_let] let _ = lemma_synth_%s_inj () in\n" n;
  wl o " LL.read_synth' parse_%s%s_key synth_%s read_%s%s_key ()\n\n" maybe n n maybe n;

  (* Low: writer *)
  wl o "inline_for_extraction let write_%s%s_key : LL.leaf_writer_strong serialize_%s%s_key =\n" maybe n maybe n;
  wl o "  LL.write_%senum_key %s_repr_writer %s_enum (_ by (LP.enum_repr_of_key_tac %s_enum))\n\n" maybe n n n;
  wl i "val %s_writer: LL.leaf_writer_strong %s_serializer\n\n" n n;
  wl o "let %s_writer =\n" n;
  wl o "  [@inline_let] let _ = lemma_synth_%s_inj (); lemma_synth_%s_inv () in\n" n n;
  wl o "  LL.write_synth write_%s%s_key synth_%s synth_%s_inv (fun x -> synth_%s_inv x) ()\n\n" maybe n n n n;

  (* bytesize lemma *)
  wl i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d) [SMTPat (%s_bytesize x)]\n\n" n n n blen n;
  wl o "let %s_bytesize_eqn x = %s_bytesize_eq x; assert (FStar.Seq.length (LP.serialize %s_serializer x) <= %d); assert (%d <= FStar.Seq.length (LP.serialize %s_serializer x))\n\n" n n n blen blen n;
  ()

and compile_ite o i n sn fn tagn clen cval tt tf al  =
  let is_private = has_attr al "private" in
  let li = get_leninfo (sn^"@"^fn) in
  let ncap = String.capitalize_ascii n in
  let tagt = sprintf "%s_%s" sn tagn in
  if clen = 0 then failwith "Tag cannot be empty in if-then-else.";
  compile_typedef o i sn tagn (TypeSimple "opaque") (VectorFixed clen) None al;

  w i "let %s_cst : %s_%s =\n  let b = BY.bytes_of_hex \"%s\" in\n  assume(BY.length b == %d); b\n\n" n sn tagn cval clen;
  w i "type %s_false = {\n  tag: t:%s_%s{t <> %s_cst};\n  value: %s\n}\n\n" n n tagn n (compile_type tf);
  w i "type %s =\n  | %s_true of %s\n  | %s_false of %s_false\n\n" n ncap (compile_type tt) ncap n;
  write_api o i is_private li.meta n (clen+li.min_len) (clen+li.max_len);

  (* Spec *)
  w o "inline_for_extraction let %s_cond (x:%s_%s) : Tot bool = x = %s_cst\n\n" n n tagn n;
  w o "inline_for_extraction let %s_payload (b:bool) : Tot Type =\n  if b then %s else %s\n\n" n (compile_type tt) (compile_type tf);
  w o "inline_for_extraction let parse_%s_payload (b:bool) : Tot (k: LP.parser_kind & LP.parser k (%s_payload b)) =\n" n n;
  w o "  if b then (| _ , %s |) else (| _, %s |)\n\n" (pcombinator_name tt) (pcombinator_name tf);
  w o "inline_for_extraction let %s_synth (x:%s_%s) (y:%s_payload (%s_cond x)) : Tot %s =\n" n n tagn n n n;
  w o "  if %s_cond x then %s_true y else %s_false ({ tag = x; value = y })\n\n" n ncap ncap;
  w o "inline_for_extraction noextract let parse_%s_param = {\n" n;
  w o "  LP.parse_ifthenelse_tag_kind = _; LP.parse_ifthenelse_tag_t = _;\n";
  w o "  LP.parse_ifthenelse_tag_parser = %s; LP.parse_ifthenelse_tag_cond = %s_cond;\n" (pcombinator_name tagt) n;
  w o "  LP.parse_ifthenelse_payload_t = %s_payload; LP.parse_ifthenelse_payload_parser = parse_%s_payload;\n" n n;
  w o "  LP.parse_ifthenelse_t = _;  LP.parse_ifthenelse_synth = %s_synth;\n" n;
  w o "  LP.parse_ifthenelse_synth_injective = (fun t1 x1 t2 x2 -> ());\n}\n\n";
  w o "let _ : squash (LP.parse_ifthenelse_kind parse_%s_param == %s_parser_kind) =\n" n n;
  w o "  _ by (FStar.Tactics.norm [delta; iota; primops]; FStar.Tactics.trefl ())\n\n";
  w o "let %s_parser = LP.parse_ifthenelse parse_%s_param\n\n" n n;
  w o "inline_for_extraction let serialize_%s_payload (b:bool) : Tot (LP.serializer (dsnd (parse_%s_param.LP.parse_ifthenelse_payload_parser b))) =\n" n n;
  w o "  if b then %s else %s\n\n" (scombinator_name tt) (scombinator_name tf);
  w o "inline_for_extraction let %s_synth_recip (x:%s) : GTot (t:%s_%s & (%s_payload (%s_cond t))) =\n" n n n tagn n n;
  w o "  match x with\n  | %s_true y -> (| %s_cst, y |)\n  | %s_false m -> (| m.tag, m.value |)\n\n" ncap n ncap;
  w o "inline_for_extraction noextract let serialize_%s_param : LP.serialize_ifthenelse_param parse_%s_param = {\n" n n;
  w o "  LP.serialize_ifthenelse_tag_serializer = %s;\n" (scombinator_name tagt);
  w o "  LP.serialize_ifthenelse_payload_serializer = serialize_%s_payload;\n" n;
  w o "  LP.serialize_ifthenelse_synth_recip = %s_synth_recip;\n" n;
  w o "  LP.serialize_ifthenelse_synth_inverse = (fun x -> ());\n}\n\n";
  w o "let %s_serializer = LP.serialize_ifthenelse serialize_%s_param\n\n" n n;
  write_bytesize o is_private n;

  (* Intermediate *)
  wh o "let %s_parser32 = LP.parse32_ifthenelse parse_%s_param %s\n" n n (pcombinator32_name tagt);
  wh o "  (fun x -> %s_cond x) (fun b -> if b then %s else %s)\n" n (pcombinator32_name tt) (pcombinator32_name tf);
  wh o "  (fun b -> if b then (fun _ pl -> %s_true pl) else (fun t pl -> %s_false ({ tag = t; value = pl; })))\n\n" ncap ncap;
  wh o "let %s_serializer32 = LP.serialize32_ifthenelse serialize_%s_param %s\n" n n (scombinator32_name tagt);
  wh o "  (fun x -> match x with %s_true _ -> %s_cst | %s_false m -> m.tag)\n" ncap n ncap;
  wh o "  (fun x -> %s_cond x) (fun b -> if b then (fun (%s_true y) -> y) else (fun (%s_false m) -> m.value))\n" n ncap ncap;
  wh o "  (fun b -> if b then %s else %s)\n\n" (scombinator32_name tt) (scombinator32_name tf);
  wh o "let %s_size32 = LP.size32_ifthenelse serialize_%s_param %s\n" n n (size32_name tagt);
  wh o "  (fun x -> match x with %s_true _ -> %s_cst | %s_false m -> m.tag)" ncap n ncap;
  wh o "  (fun x -> %s_cond x) (fun b -> if b then (fun (%s_true y) -> y) else (fun (%s_false m) -> m.value))\n" n ncap ncap;
  wh o "  (fun b -> if b then %s else %s)\n\n" (size32_name tt) (size32_name tf);

  (* Low *)
  wl o "inline_for_extraction let test_%s : LL.test_ifthenelse_tag parse_%s_param =" n n;
  wl o "  fun #_ #_ input pos -> LL.valid_slice_equals_bytes %s_cst input pos\n\n" n;
  wl o "let %s_validator = LL.validate_ifthenelse parse_%s_param %s\n" n n (validator_name tagt);
  wl o "  test_%s (fun b -> if b then %s else %s)\n\n" n (validator_name tt) (validator_name tf);
  wl o "let %s_jumper = LL.jump_ifthenelse parse_%s_param %s\n" n n (jumper_name tagt);
  wl o "  test_%s (fun b -> if b then %s else %s)\n\n" n (jumper_name tt) (jumper_name tf);
  wl i "val %s_elim (h:HS.mem) (#rrel: _) (#rel: _) (input:LL.slice rrel rel) (pos: U32.t) : Lemma\n" n;
  wl i "  (requires (LL.valid %s_parser h input pos))\n" n;
  wl i "  (ensures (\n    LL.valid %s h input pos /\\ (\n" (pcombinator_name tagt);
  wl i "    let x = LL.contents %s_parser h input pos in\n" n;
  wl i "    let y = LL.contents %s h input pos in\n" (pcombinator_name tagt);
  wl i "    y == (match x with | %s_true _ -> %s_cst | %s_false m -> m.tag))))\n\n" ncap n ncap;
  wl o "let %s_elim h #_ #_ input pos = LL.valid_ifthenelse_elim parse_%s_param h input pos\n\n" n n;
  wl i "val %s_test (#rrel: _) (#rel: _) (input:LL.slice rrel rel) (pos: U32.t) : HST.Stack bool\n" n;
  wl i "  (requires (fun h -> LL.valid %s_parser h input pos))\n" n;
  wl i "  (ensures (fun h res h' -> B.modifies B.loc_none h h' /\\\n";
  wl i "    (res == true <==> %s_true? (LL.contents %s_parser h input pos))))\n\n" ncap n;
  wl o "let %s_test #_ #_ input pos = let h = HST.get () in %s_elim h input pos; test_%s input pos\n\n" n n n;
  wl i "noextract let %s_clens_true : LL.clens %s %s = {\n" n n (compile_type tt);
  wl i "  LL.clens_cond = (fun x -> %s_true? x);\n" ncap;
  wl i "  LL.clens_get = (fun x -> (match x with %s_true y -> y) <: Ghost %s (requires (%s_true? x)) (ensures (fun _ -> True)));\n}\n\n" ncap (compile_type tt) ncap;
  wl i "val %s_gaccessor_true: LL.gaccessor %s_parser %s %s_clens_true\n\n" n n (pcombinator_name tt) n;
  wl i "val %s_accessor_true: LL.accessor %s_gaccessor_true\n\n" n n;
  wl i "noextract let %s_clens_false : LL.clens %s %s = {\n" n n (compile_type tf);
  wl i "  LL.clens_cond = (fun x -> %s_false? x);\n" ncap;
  wl i "  LL.clens_get = (fun x -> (match x with %s_false m -> m.value) <: Ghost %s (requires (%s_false? x)) (ensures (fun _ -> True)));\n}\n\n" ncap (compile_type tf) ncap;
  wl i "val %s_gaccessor_false: LL.gaccessor %s_parser %s %s_clens_false\n\n" n n (pcombinator_name tf) n;
  wl i "val %s_accessor_false: LL.accessor %s_gaccessor_false\n\n" n n;
  wl o "let %s_gaccessor_true = LL.gaccessor_ext (LL.gaccessor_ifthenelse_payload serialize_%s_param true) %s_clens_true ()\n\n" n n n;
  wl o "let %s_accessor_true = LL.accessor_ext (LL.accessor_ifthenelse_payload serialize_%s_param %s true) %s_clens_true ()\n\n" n n (jumper_name tagt) n;
  wl o "let %s_gaccessor_false = LL.gaccessor_ext (LL.gaccessor_ifthenelse_payload serialize_%s_param false) %s_clens_false ()\n\n" n n n;
  wl o "let %s_accessor_false = LL.accessor_ext (LL.accessor_ifthenelse_payload serialize_%s_param %s false) %s_clens_false ()\n\n" n n (jumper_name tagt) n;
  wl i "val %s_intro_true (h: HS.mem) (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : Lemma\n" n;
  wl i "  (requires (LL.valid %s h input pos /\\ (\n" (pcombinator_name tagt);
  wl i "    let x = LL.contents %s h input pos in\n" (pcombinator_name tagt);
  wl i "    let pos1 = LL.get_valid_pos %s h input pos in\n" (pcombinator_name tagt);
  wl i "    x == %s_cst /\\ LL.valid %s h input pos1\n" n (pcombinator_name tt);
  wl i "  ))) (ensures (\n";
  wl i "    let pos1 = LL.get_valid_pos %s h input pos in\n" (pcombinator_name tagt);
  wl i "    LL.valid_content_pos %s_parser h input pos (%s_true (LL.contents %s h input pos1)) (LL.get_valid_pos %s h input pos1)\n  ))\n\n" n ncap (pcombinator_name tt) (pcombinator_name tt);
  wl o "let %s_intro_true h #_ #_ input pos = LL.valid_ifthenelse_intro parse_%s_param h input pos\n\n" n n;
  wl i "val %s_intro_false (h: HS.mem) (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : Lemma\n" n;
  wl i "  (requires (LL.valid %s h input pos /\\ (\n" (pcombinator_name tagt);
  wl i "    let x = LL.contents %s h input pos in\n" (pcombinator_name tagt);
  wl i "   let pos1 = LL.get_valid_pos %s h input pos in\n" (pcombinator_name tagt);
  wl i "    x =!= %s_cst /\\ LL.valid %s h input pos1\n" n (pcombinator_name tf);
  wl i "  ))) (ensures (\n";
  wl i "    let x = LL.contents %s h input pos in\n" (pcombinator_name tagt);
  wl i "    let pos1 = LL.get_valid_pos %s h input pos in\n" (pcombinator_name tagt);
  wl i "    LL.valid_content_pos %s_parser h input pos (%s_false ({ tag = x; value = (LL.contents %s h input pos1) })) (LL.get_valid_pos %s h input pos1)\n  ))\n\n" n ncap (pcombinator_name tf) (pcombinator_name tf);
  wl o "let %s_intro_false h #_ #_ input pos = LL.valid_ifthenelse_intro parse_%s_param h input pos\n\n" n n;
  ()

and compile_select o i n seln tagn tagt taga cl def al =
  let is_private = has_attr al "private" in
  let is_implicit = has_attr taga "implicit" in
  let has_fail_missing = has_attr al "failmissing" in (* autocomplete missing cases with Fail even if default is provided *)
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
    let dty = match def with Some d when not has_fail_missing -> d | _ -> "Fail" in
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
  w o "// Need high Z3 limits for large sum types\n#set-options \"--z3rlimit %d\"\n\n" (60 * List.length cl);

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
      let cn = String.capitalize_ascii case in
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
      let cn = String.capitalize_ascii case in
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
      let cn = String.capitalize_ascii case in
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
      let cn = String.capitalize_ascii case in
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
    w o "  | %s -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (%s_case_of_%s %s)) = (| _, %s |) in u\n" cn n tn cn (pcombinator_name ty)
  ) cl;
  w o "  | _ -> (| _, LP.parse_false |)\n\n";

  w o "noextract let serialize_%s_cases (x:%s)\n" n ktype;
  w o "  : LP.serializer (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    w o "  | %s -> [@inline_let] let u : LP.serializer (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (scombinator_name ty)
  ) cl;
  w o "  | _ -> LP.serialize_false\n\n";

  wh o "inline_for_extraction noextract let parse32_%s_cases (x:%s)\n" n ktype;
  wh o "  : LP.parser32 (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    wh o "  | %s -> [@inline_let] let u : LP.parser32 (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (pcombinator32_name ty)
  ) cl;
  wh o "  | _ -> LP.parse32_false\n\n";

  wh o "inline_for_extraction noextract let serialize32_%s_cases (x:%s)\n" n ktype;
  wh o "  : LP.serializer32 (serialize_%s_cases x) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    wh o "  | %s -> [@inline_let] let u : LP.serializer32 (serialize_%s_cases %s) = %s in u\n" cn n cn (scombinator32_name ty)
  ) cl;
  wh o "  | _ -> LP.serialize32_false\n\n";

  wh o "inline_for_extraction noextract let size32_%s_cases (x:%s)\n" n ktype;
  wh o "  : LP.size32 (serialize_%s_cases x) =\n  match x with\n" n;
  List.iter (fun (case, ty) ->
    let cn = String.capitalize_ascii case in
    wh o "  | %s -> [@inline_let] let u : LP.size32 (serialize_%s_cases %s) = %s in u\n" cn n cn (size32_name ty)
  ) cl;
  wh o "  | _ -> LP.size32_false\n\n";

  if need_validator then
   begin
    wl o "inline_for_extraction noextract let validate_%s_cases (x:%s)\n" n ktype;
    wl o "  : LL.validator (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
    List.iter (fun (case, ty) ->
      let cn = String.capitalize_ascii case in
      wl o "  | %s -> [@inline_let] let u : LL.validator (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (validator_name ty)
    ) cl;
    wl o "  | _ -> LL.validate_false ()\n\n"
   end;

  if need_jumper then
   begin
    wl o "inline_for_extraction noextract let jump_%s_cases (x:%s)\n" n ktype;
    wl o "  : LL.jumper (dsnd (parse_%s_cases x)) =\n  match x with\n" n;
    List.iter (fun (case, ty) ->
      let cn = String.capitalize_ascii case in
      wl o "  | %s -> [@inline_let] let u : LL.jumper (dsnd (parse_%s_cases %s)) = %s in u\n" cn n cn (jumper_name ty)
    ) cl;
    wl o "  | _ -> LL.jump_false\n\n"
   end;

  if is_implicit then (
    match def with
    | None ->
      w o "let _ : squash (%s_parser_kind == LP.weaken_parse_cases_kind %s_sum parse_%s_cases) =\n" n n n;
      w o "  _ by (FStar.Tactics.norm [delta; iota; primops]; FStar.Tactics.trefl ())\n\n";
      w o "let %s_eq_lemma (k:%s) : Lemma (%s k == LP.sum_cases %s_sum (%s_as_enum_key k)) [SMTPat (%s k)] =\n" n tn n n tn n;
      w o "  match k with\n";
      List.iter (fun (case, ty) ->
        let cn = String.capitalize_ascii case in
        w o "  | %s -> assert_norm (%s %s == LP.sum_cases %s_sum (%s_as_enum_key %s))\n" cn n cn n tn cn
      ) cl;
      w o "\nlet %s_parser k =\n  LP.parse_sum_cases %s_sum parse_%s_cases (%s_as_enum_key k)\n\n" n n n tn;
      w o "let %s_serializer k =\n  LP.serialize_sum_cases %s_sum parse_%s_cases serialize_%s_cases (%s_as_enum_key k)\n\n" n n n n tn;
      write_bytesize o is_private n  ~param:(if is_implicit then Some tagt else None);
      wh o "let %s_parser32 k =\n  LP.parse32_sum_cases %s_sum parse_%s_cases parse32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
      wh o "let %s_serializer32 k =\n  LP.serialize32_sum_cases %s_sum serialize_%s_cases serialize32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
      wh o "let %s_size32 k =\n  LP.size32_sum_cases %s_sum serialize_%s_cases size32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
      if need_validator then
        wl o "let %s_validator k =\n  LL.validate_sum_cases %s_sum parse_%s_cases validate_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
      if need_jumper then
        wl o "let %s_jumper k =\n  LL.jump_sum_cases %s_sum parse_%s_cases jump_%s_cases (_ by (LP.dep_enum_destr_tac ())) (%s_as_enum_key k)\n\n" n n n n tn;
    | Some def -> (* Horible synth boilerplate to deal with refine_with_tag *)
      w o "let _ : squash (%s_parser_kind == LP.weaken_parse_dsum_cases_kind %s_sum parse_%s_cases (LP.get_parser_kind %s)) =\n" n n n (pcombinator_name def);
      w o "  _ by (FStar.Tactics.norm [delta; iota; primops]; FStar.Tactics.trefl ())\n\n";
      w o "inline_for_extraction let synth_%s (k:%s) (x:LP.refine_with_tag key_of_%s (synth_%s_inv k)) : %s k = x\n\n" n tn n tn n;
      w o "inline_for_extraction let synth_%s_recip (k:%s) (x:%s k) : LP.refine_with_tag key_of_%s (synth_%s_inv k) = x\n\n" n tn n n tn;
      w o "let synth_%s_inj (k:%s) : Lemma (LP.synth_injective (synth_%s k)) = ()\n\n" n tn n;
      w o "let synth_%s_inv (k:%s) : Lemma (LP.synth_inverse (synth_%s k) (synth_%s_recip k)) = ()\n\n" n tn n n;
      w o "noextract inline_for_extraction let %s_parser' = LP.parse_dsum_cases %s_sum parse_%s_cases %s\n\n" n n n (pcombinator_name def);
      w o "let %s_parser k = %s_parser' (synth_%s_inv k) `LP.parse_synth` synth_%s k\n\n" n n tn n;
      w o "noextract let %s_serializer' = LP.serialize_dsum_cases %s_sum parse_%s_cases serialize_%s_cases %s %s\n\n" n n n n (pcombinator_name def) (scombinator_name def);
      w o "let %s_serializer k = LP.serialize_synth _ (synth_%s k) (%s_serializer' (synth_%s_inv k)) (synth_%s_recip k) ()\n\n" n n n tn n;
      write_bytesize o is_private n  ~param:(if is_implicit then Some tagt else None);
      wh o "noextract inline_for_extraction let %s_parser32' = LP.parse32_dsum_cases %s_sum parse_%s_cases parse32_%s_cases %s %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n (pcombinator_name def) (pcombinator32_name def);
      wh o "let %s_parser32 k = LP.parse32_synth' (%s_parser' (synth_%s_inv k)) (synth_%s k) (LP.parse32_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_parser32' k) ()\n\n" n n tn n tn n n n;
      wh o "noextract inline_for_extraction let %s_serializer32' = LP.serialize32_dsum_cases %s_sum parse_%s_cases serialize_%s_cases serialize32_%s_cases %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n n (scombinator32_name def);
      wh o "let %s_serializer32 k = LP.serialize32_synth' (%s_parser' (synth_%s_inv k)) (synth_%s k) (%s_serializer' (synth_%s_inv k))\n" n n tn n n tn;
      wh o "   (LP.serialize32_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_serializer' %s_serializer32' k) (synth_%s_recip k) ()\n\n" tn n n n n n;
      wh o "noextract inline_for_extraction let %s_size32' = LP.size32_dsum_cases %s_sum parse_%s_cases serialize_%s_cases size32_%s_cases %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n n (size32_name def);
      wh o "let %s_size32 k = LP.size32_synth' (%s_parser' (synth_%s_inv k)) (synth_%s k) (%s_serializer' (synth_%s_inv k)) (LP.size32_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_serializer' %s_size32' k) (synth_%s_recip k) ()\n\n" n n tn n n tn tn n n n n n;
      if need_validator then (
        wl o "noextract inline_for_extraction let %s_validator' = LL.validate_dsum_cases %s_sum parse_%s_cases validate_%s_cases %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n (validator_name def);
        wl o "let %s_validator k = LL.validate_synth (LL.validate_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_validator' k) (synth_%s k) ()\n\n" n tn n n n n
      );
      if need_jumper then (
        wl o "noextract inline_for_extraction let %s_jumper' = LL.jump_dsum_cases %s_sum parse_%s_cases jump_%s_cases %s (_ by (LP.dep_enum_destr_tac ()))\n\n" n n n n (jumper_name def);
        wl o "let %s_jumper k = LL.jump_synth (LL.jump_compose_context synth_%s_inv (LP.refine_with_tag key_of_%s) %s_parser' %s_jumper' k) (synth_%s k) ()\n\n" n tn n n n n
      )
  ) else (* tag is not erased *)
   begin
    let same_kind = match def with
      | None -> sprintf "  assert_norm (LP.parse_sum_kind (LP.get_parser_kind %s_repr_parser) %s_sum parse_%s_cases == %s_parser_kind);\n" tn n n n
      | Some dt -> sprintf "  assert_norm (LP.parse_dsum_kind (LP.get_parser_kind %s_repr_parser) %s_sum parse_%s_cases (LP.get_parser_kind %s) == %s_parser_kind);\n" tn n n (pcombinator_name dt) n
      in
    let annot = if is_private then " : LP.parser "^n^"_parser_kind "^n else "" in
    w o "let %s_parser%s =\n%s" n annot same_kind;
    (match def with
    | None -> w o "  LP.parse_sum %s_sum %s_repr_parser parse_%s_cases\n\n" n tn n
    | Some dt -> w o "  LP.parse_dsum %s_sum %s_repr_parser parse_%s_cases %s\n\n" n tn n (pcombinator_name dt));

    let annot = if is_private then " : LP.serializer "^(pcombinator_name n) else "" in
    w o "let %s_serializer%s =\n%s" n annot same_kind;
    (match def with
    | None -> w o "  LP.serialize_sum %s_sum %s_repr_serializer serialize_%s_cases\n\n" n tn n
    | Some dt -> w o "  LP.serialize_dsum %s_sum %s_repr_serializer _ serialize_%s_cases _ %s\n\n" n tn n (scombinator_name dt));
    write_bytesize o is_private n  ~param:(if is_implicit then Some tagt else None);

    let annot = if is_private then " : LP.parser32 "^(pcombinator_name n) else "" in
    wh o "let %s_parser32%s =\n%s" n annot same_kind;
    (match def with
    | None ->
      wh o "  LP.parse32_sum2 %s_sum %s_repr_parser %s_repr_parser32 parse_%s_cases parse32_%s_cases (_ by (LP.enum_destr_tac %s_enum)) (_ by (LP.maybe_enum_key_of_repr_tac %s_enum))\n\n" n tn tn n n tn tn;
    | Some dt ->
      wh o "  LP.parse32_dsum %s_sum %s_repr_parser32\n" n tn;
      wh o "    _ parse32_%s_cases %s (_ by (LP.maybe_enum_destr_t_tac ()))\n\n" n (pcombinator32_name dt));

    let annot = if is_private then " : LP.serializer32 "^(scombinator_name n) else "" in
    wh o "let %s_serializer32%s =\n%s" n annot same_kind;
    (match def with
    | None ->
      wh o "  assert_norm (LP.serializer32_sum_gen_precond (LP.get_parser_kind %s_repr_parser) (LP.weaken_parse_cases_kind %s_sum parse_%s_cases));\n" tn n n;
      wh o "  LP.serialize32_sum2 %s_sum %s_repr_serializer %s_repr_serializer32 serialize_%s_cases serialize32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac %s_enum)) ()\n\n" n tn tn n n tn
    | Some dt ->
      wh o "  assert_norm (LP.serializer32_sum_gen_precond (LP.get_parser_kind %s_repr_parser) (LP.weaken_parse_dsum_cases_kind %s_sum parse_%s_cases %s_parser_kind));\n" tn n n n;
      wh o "  LP.serialize32_dsum %s_sum %s_repr_serializer (_ by (LP.serialize32_maybe_enum_key_tac %s_repr_serializer32 %s_enum ()))" n tn tn tn;
      wh o "    _ _ serialize32_%s_cases %s (_ by (LP.dep_enum_destr_tac ())) ()\n\n" n (scombinator32_name dt));

    let annot = if is_private then " : LP.size32 "^n else "" in
    wh o "let %s_size32%s =\n%s" n annot same_kind;
    (match def with
    | None ->
      wh o "  assert_norm (LP.size32_sum_gen_precond (LP.get_parser_kind %s_repr_parser) (LP.weaken_parse_cases_kind %s_sum parse_%s_cases));\n" tn n n;
      wh o "  LP.size32_sum2 %s_sum %s_repr_serializer %s_repr_size32 serialize_%s_cases size32_%s_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac %s_enum)) ()\n\n" n tn tn n n tn
    | Some dt ->
      wh o "  assert_norm (LP.size32_sum_gen_precond (LP.get_parser_kind %s_repr_parser) (LP.weaken_parse_dsum_cases_kind %s_sum parse_%s_cases %s_parser_kind));\n" tn n n n;
      wh o "  LP.size32_dsum %s_sum _ (_ by (LP.size32_maybe_enum_key_tac %s_repr_size32 %s_enum ()))\n" n tn tn;
      wh o "    _ _ size32_%s_cases %s (_ by (LP.dep_enum_destr_tac ())) ()\n\n" n (size32_name dt));

    if need_validator then
     begin
      let annot = if is_private then " : LL.validator "^(pcombinator_name n) else "" in
      wl o "let %s_validator%s =\n%s" n annot same_kind;
      (match def with
      | None ->
        wl o "  LL.validate_sum %s_sum %s_repr_validator %s_repr_reader parse_%s_cases validate_%s_cases (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n tn tn n n;
      | Some dt ->
        wl o "  LL.validate_dsum %s_sum %s_repr_validator %s_repr_reader parse_%s_cases validate_%s_cases %s (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n tn tn n n (validator_name dt));
     end;

    if need_jumper then
     begin
      let annot = if is_private then " : LL.jumper "^(pcombinator_name n) else "" in
      wl o "let %s_jumper%s =\n%s" n annot same_kind;
      (match def with
      | None ->
        wl o "  LL.jump_sum %s_sum %s_repr_jumper %s_repr_reader parse_%s_cases jump_%s_cases (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n tn tn n n;
      | Some dt ->
        wl o "  LL.jump_dsum %s_sum %s_repr_jumper %s_repr_reader parse_%s_cases jump_%s_cases %s (_ by (LP.dep_maybe_enum_destr_t_tac ()))\n\n" n tn tn n n (jumper_name dt))
     end;

    if need_validator then
     begin
      let maybe = match def with
        | None -> ""
        | _ -> "maybe_"
      in
      wl i "val lemma_valid_%s_valid_%s: #rrel: _ -> #rel: _ -> s:LL.slice rrel rel -> pos:U32.t -> h:HyperStack.mem -> Lemma\n" n tn;
      wl i "  (requires LL.valid %s_parser h s pos)\n" n;
      wl i "  (ensures (LL.valid %s_parser h s pos /\\ LL.contents %s_parser h s pos == tag_of_%s (LL.contents %s_parser h s pos)))\n" tn tn n n;
      wl i "  [SMTPat (LL.valid %s_parser h s pos)]\n\n" n;
      wl o "let lemma_valid_%s_valid_%s #_ #_ s pos h =\n%s" n tn same_kind;
      begin match def with
      | None ->
         wl o "  LL.valid_sum_elim_tag h %s_sum %s_repr_parser parse_%s_cases s pos;\n" n tn n
      | Some dt ->
         wl o "  LL.valid_dsum_elim_tag h %s_sum %s_repr_parser parse_%s_cases %s s pos;\n" n tn n (pcombinator_name dt)
      end;
      wl o "  lemma_synth_%s_inj ();\n" tn;
      wl o "  LL.valid_synth h parse_%s%s_key synth_%s s pos\n" maybe tn tn;
      wl o "\n"
     end;

    (* bytesize *)
    begin match def with
    | None ->
       List.iter
         (function (case, ty) when ty <> "Fail" ->
           let constr = sprintf "%s_%s" cprefix case in
           w i "val %s_bytesize_eqn_%s (x: %s) : Lemma (%s_bytesize (%s x) == %d + %s) [SMTPat (%s_bytesize (%s x))]\n\n" n case (compile_type ty) n constr taglen (bytesize_call ty "x") n constr;
           w o "let %s_bytesize_eqn_%s x =\n" n case;
           w o "  %s\n" same_kind;
           w o "  LP.serialize_sum_eq %s_sum %s_repr_serializer serialize_%s_cases (%s x);\n" n tn n constr;
           w o "  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ %s_repr_serializer (LP.sum_enum %s_sum)) (key_of_%s (%s x))) in assert (%d <= ln /\\ ln <= %d));\n" tn n n constr taglen taglen;
           w o "  %s\n\n" (bytesize_eq_call ty "x")
                 | _ -> ()
         )
         cl
    | Some dt ->
       let write_constr vbind vvar (case, ty) =
         if ty <> "Fail" then begin
           let constr = sprintf "%s_%s" cprefix case in
           w i "val %s_bytesize_eqn_%s %s (x: %s) : Lemma (%s_bytesize (%s %s x) == %d + %s) [SMTPat (%s_bytesize (%s %s x))]\n\n" n case vbind (compile_type ty) n constr vvar taglen (bytesize_call ty "x") n constr vvar;
           w o "let %s_bytesize_eqn_%s %s x =\n" n case vvar;
           w o "  %s\n" same_kind;
           w o "  LP.serialize_dsum_eq %s_sum %s_repr_serializer parse_%s_cases serialize_%s_cases %s %s (%s %s x) ;\n" n tn n n (pcombinator_name dt) (scombinator_name dt) constr vvar;
           w o "  let tg = LL.dsum_tag_of_data %s_sum (%s %s x) in\n" n constr vvar;
           if vvar = "" then
             w o "  assert_norm (tg == LL.Known (known_%s_as_enum_key %s));\n" tn (String.capitalize_ascii case)
           else
             w o "  assert_norm (tg == LL.Unknown (unknown_%s_as_enum_key %s));\n" tn vvar;
           w o "  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_maybe_enum_key _ %s_repr_serializer (LP.dsum_enum %s_sum)) tg) in assert (%d <= ln /\\ ln <= %d));\n" tn n taglen taglen;
           w o "  %s\n\n" (bytesize_eq_call ty "x")
         end
       in
       List.iter (write_constr "" "") cl;
       write_constr (sprintf "(v: %s_repr { not (known_%s_repr v) } )" tn tn) "v" (sprintf "Unknown_%s" tn, dt)
    end;
    (* accessors *)
    begin
      let d = match def with None -> "" | _ -> "d" in
      let unknown_parser =
        match def with
        | None -> ""
        | Some dt -> pcombinator_name dt
        in
       List.iter
         (fun (case, ty) ->
           if ty <> "Fail" && ty <> "Empty" then
             begin
               let ty0 = compile_type ty in
               wl i "noextract let %s_clens_%s : LL.clens %s %s = {\n" n case n ty0;
               wl i "  LL.clens_cond = (fun (x: %s) -> tag_of_%s x == %s);\n" n n (String.capitalize_ascii case);
               wl i "  LL.clens_get = (fun (x: %s) -> (match x with %s_%s y -> y) <: (Ghost %s (requires (tag_of_%s x == %s)) (ensures (fun y -> True))));\n" n cprefix case ty0 n (String.capitalize_ascii case);
               wl i "}\n\n";
               wl i "val %s_gaccessor_%s : LL.gaccessor %s_parser %s %s_clens_%s\n\n" n case n (pcombinator_name ty) n case;
               wl o "noextract let %s_clens'_%s : LL.clens %s %s = LL.clens_%ssum_payload %s_sum " n case n ty0 d n;
               if d = "" then
                 wl o "(%s_as_enum_key %s)\n\n" tn (String.capitalize_ascii case)
               else
                 wl o "(LL.Known (known_%s_as_enum_key %s))\n\n" tn (String.capitalize_ascii case);
               wl o "let %s_gaccessor'_%s : LL.gaccessor %s_parser %s %s_clens'_%s =\n" n case n (pcombinator_name ty) n case;
               let write_accessor' g parser_or_jumper =
                 wl o "[@inline_let] let _ = %s () in\n" same_kind;
                 wl o "  LL.%saccessor_clens_%ssum_payload\n" g d;
                 wl o "    %s_sum\n" n;
                 wl o "    %s_repr_%s\n" tn parser_or_jumper;
                 wl o "    parse_%s_cases\n" n;
                 if d = "" then
                   wl o "    (%s_as_enum_key %s)\n" tn (String.capitalize_ascii case)
                 else begin
                   wl o "    %s\n" unknown_parser;
                   wl o "    (LL.Known (known_%s_as_enum_key %s))\n" tn (String.capitalize_ascii case)
                 end;
                 wl o "\n"
               in
               write_accessor' "g" "parser";
               wl o "inline_for_extraction\n";
               wl o "let %s_accessor'_%s : LL.accessor %s_gaccessor'_%s =\n" n case n case;
               write_accessor' "" "jumper";
               wl o "let %s_clens_eq_%s : squash (LL.clens_eq %s_clens'_%s %s_clens_%s) =\n" n case n case n case;
               wl o "    (_ by (LL.sum_accessor_ext (`%s)))\n\n" n;
               let write_accessor g =
                 wl o "let %s_%saccessor_%s =\n" n g case;
                 wl o "  LL.%saccessor_ext\n" g;
                 wl o "    %s_%saccessor'_%s\n" n g case;
                 wl o "    %s_clens_%s\n" n case;
                 wl o "    %s_clens_eq_%s\n\n" n case
               in
               write_accessor "g";
               wl i "val %s_accessor_%s : LL.accessor %s_gaccessor_%s\n\n" n case n case;
               write_accessor "";
               ()
             end
         )
         cl;
       match def with
       | Some dt when dt <> "Empty" && dt <> "Fail" ->
          (* accessor to the default case payload *)
          let dt0 = compile_type dt in
          wl i "noextract let %s_clens_Unknown : LL.clens %s %s = {\n" n n dt0;
          wl i "  LL.clens_cond = (fun (x: %s) -> %s_Unknown_%s? x);\n" n cprefix tn;
          wl i "  LL.clens_get = (fun (x: %s) -> (match x with %s_Unknown_%s _ y -> y) <: (Ghost %s (requires (%s_Unknown_%s? x)) (ensures (fun y -> True))));\n" n cprefix tn dt0 cprefix tn;
          wl i "}\n\n";
          wl o "let %s_clens_eq_Unknown : squash (LL.clens_eq (LL.clens_dsum_unknown_payload %s_sum) %s_clens_Unknown) =\n" n n n;
          wl o "    (_ by (LL.sum_accessor_ext (`%s)))\n\n" n;
          let write_accessor g parser_or_jumper =
            wl o "let %s_%saccessor_Unknown =\n" n g;
            wl o "  [@inline_let] let _ = %s () in\n" same_kind;
            wl o "  LL.%saccessor_ext\n" g;
            wl o "    (LL.%saccessor_clens_dsum_unknown_payload\n" g;
            wl o "      %s_sum\n" n;
            wl o "      %s_repr_%s\n" tn parser_or_jumper;
            wl o "      parse_%s_cases\n" n;
            wl o "      %s\n" (pcombinator_name dt);
            wl o "    )\n";
            wl o "    %s_clens_Unknown\n" n;
            wl o "    %s_clens_eq_Unknown\n\n" n
          in
          wl i "val %s_gaccessor_Unknown : LL.gaccessor %s_parser %s %s_clens_Unknown\n\n" n n (pcombinator_name dt) n;
          write_accessor "g" "parser";
          wl i "val %s_accessor_Unknown : LL.accessor %s_gaccessor_Unknown\n\n" n n;
          write_accessor "" "jumper"
       | _ -> ()
    end;
    (* finalizers *)
    let write_finalizer case =
      wl o "  [@inline_let] let _ = %s" same_kind;
      match def with
      | None ->
         wl o "    let tg = %s_as_enum_key %s in\n" tn (String.capitalize_ascii case);
         wl o "    let len = LL.serialized_length (LP.serialize_enum_key _ %s_repr_serializer (LP.sum_enum %s_sum)) tg in\n" tn n;
         wl o "    let pk = LP.get_parser_kind (LP.parse_enum_key %s_repr_parser (LP.sum_enum %s_sum)) in\n" tn n;
         wl o "    assert_norm (pk.LP.parser_kind_low == %d /\\ pk.LP.parser_kind_high == Some %d);\n" taglen taglen;
         wl o "    assert (%d <= len /\\ len <= %d);\n" taglen taglen;
         wl o "    assert_norm (pow2 32 == 4294967296)\n";
         wl o "  in\n";
         wl o "  LL.finalize_sum_case %s_sum %s_repr_serializer %s_repr_writer parse_%s_cases (_ by (LP.enum_repr_of_key_tac %s_enum)) (%s_as_enum_key %s) input pos\n\n" n tn tn n tn tn (String.capitalize_ascii case)
      | Some dt ->
         wl o "    let tg = known_%s_as_enum_key %s in\n" tn (String.capitalize_ascii case);
         wl o "    let len = LL.serialized_length (LP.serialize_enum_key _ %s_repr_serializer (LP.dsum_enum %s_sum)) tg in\n" tn n;
         wl o "    let pk = LP.get_parser_kind (LP.parse_enum_key %s_repr_parser (LP.dsum_enum %s_sum)) in\n" tn n;
         wl o "    assert_norm (pk.LP.parser_kind_low == %d /\\ pk.LP.parser_kind_high == Some %d);\n" taglen taglen;
         wl o "    assert (%d <= len /\\ len <= %d);\n" taglen taglen;
         wl o "    assert_norm (pow2 32 == 4294967296)\n";
         wl o "  in\n";
         wl o "  LL.finalize_dsum_case_known %s_sum %s_repr_serializer %s_repr_writer parse_%s_cases %s (_ by (LP.enum_repr_of_key_tac %s_enum)) (known_%s_as_enum_key %s) input pos\n\n" n tn tn n (pcombinator_name dt) tn tn (String.capitalize_ascii case)
    in
       List.iter
         (fun (case, ty) ->
           let constr = sprintf "%s_%s" cprefix case in
           let casep = pcombinator_name ty in
           match ty with
           | "Fail" -> () (* impossible case *)
           | "Empty" -> (* parse_empty is not in the user context, so we need to "inline" it here *)
              wl i "val finalize_%s_%s (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : HST.Stack unit\n" n case;
              wl i "  (requires (fun h ->\n";
              wl i "    assert_norm (pow2 32 == 4294967296);\n";
              wl i "    LL.live_slice h input /\\ U32.v pos + %d <= U32.v input.LL.len /\\ LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h))\n" taglen taglen;
              wl i "  (ensures (fun h _ h' ->\n";
              wl i "    assert_norm (pow2 32 == 4294967296);\n";
              wl i "    let pos_payload = pos `U32.add` %dul in\n" taglen;
              wl i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
              wl i "    LL.valid_content_pos %s_parser h' input pos (%s ()) pos_payload\n" n constr;
              wl i "  ))\n\n";
              wl o "let finalize_%s_%s #_ #_ input pos =\n" n case;
              wl o "  let h = HST.get () in\n";
              wl o "  [@inline_let] let _ = LL.valid_facts LL.parse_empty h input (pos `U32.add` %dul) in\n" taglen;
              write_finalizer case
           | _ ->
              wl i "val finalize_%s_%s (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : HST.Stack unit\n" n case;
              wl i "  (requires (fun h ->\n";
              wl i "    assert_norm (pow2 32 == 4294967296);\n";
              wl i "U32.v pos + %d < 4294967296 /\\ LL.valid %s h input (pos `U32.add` %dul) /\\ LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h))\n" taglen casep taglen taglen;
              wl i "  (ensures (fun h _ h' ->\n";
              wl i "    assert_norm (pow2 32 == 4294967296);\n";
              wl i "    let pos_payload = pos `U32.add` %dul in\n" taglen;
              wl i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
              wl i "    LL.valid_content_pos %s_parser h' input pos (%s (LL.contents %s h input pos_payload)) (LL.get_valid_pos %s h input pos_payload)\n" n constr casep casep;
              wl i "  ))\n\n";
              wl o "let finalize_%s_%s #_ #_ input pos =\n" n case;
              write_finalizer case
         )
         cl
     ;
       (* finalizer for unknown case *)
       begin match def with
       | Some dt when dt <> "Fail" ->
          let dp = pcombinator_name dt in
          wl i "val finalize_%s_Unknown_%s (v: %s_repr) (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : HST.Stack unit\n" n tn tn;
          wl i "  (requires (fun h ->\n";
          wl i "    assert_norm (pow2 32 == 4294967296);\n";
          if dt = "Empty" then
            wl i "    U32.v pos + %d <= U32.v input.LL.len /\\ LL.live_slice h input /\\ not (known_%s_repr v) /\\ LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h))\n" taglen tn taglen
          else
            wl i "  U32.v pos + %d < 4294967296 /\\ LL.valid %s h input (pos `U32.add` %dul) /\\ not (known_%s_repr v) /\\ LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h))\n" taglen dp taglen tn taglen
          ;
          wl i "  (ensures (fun h _ h' ->\n";
          wl i "    assert_norm (pow2 32 == 4294967296);\n";
          wl i "    let pos_payload = pos `U32.add` %dul in\n" taglen;
          wl i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
          if dt = "Empty" then
            wl i "    LL.valid_content_pos %s_parser h' input pos (%s_Unknown_%s v ()) pos_payload\n" n cprefix tn
          else
            wl i "    LL.valid_content_pos %s_parser h' input pos (%s_Unknown_%s v (LL.contents %s h input pos_payload)) (LL.get_valid_pos %s h input pos_payload)\n" n cprefix tn dp dp
          ;
          wl i "  ))\n\n";
          wl o "let finalize_%s_Unknown_%s v #_ #_ input pos =\n" n tn;
          wl o "  [@inline_let] let _ =\n";
          wl o "    %s\n" same_kind;
          wl o "    let tg = unknown_%s_as_enum_key v in\n" tn;
          wl o "    let len = LL.serialized_length %s_repr_serializer tg in\n" tn;
          wl o "    assert (%d <= len /\\ len <= %d);\n" taglen taglen;
          wl o "    assert_norm (pow2 32 == 4294967296)\n";
          wl o "  in\n";
          if dt = "Empty" then begin
            wl o "  let h = HST.get () in\n";
            wl o "  [@inline_let] let _ = LL.valid_facts LL.parse_empty h input (pos `U32.add` %dul) in\n" taglen;
          end;
          wl o "  LL.finalize_dsum_case_unknown %s_sum %s_repr_serializer %s_repr_writer parse_%s_cases %s (unknown_%s_as_enum_key v) input pos\n\n" n tn tn n dp tn
       | _ -> ()
       end
  end

and compile_vldata o i is_private n ty li elem_li lenty len_len_min len_len_max smin smax =
  let (min, max) = li.min_len, li.max_len in
  let fits_in_bounds = smin <= elem_li.min_len && elem_li.max_len <= smax in
  let need_validator = is_private || need_validator li.meta li.min_len li.max_len in
  let need_jumper = is_private || need_jumper li.min_len li.max_len in
  if fits_in_bounds then
   begin
    w i "type %s = %s\n\n" n (compile_type ty);
    write_api o i is_private li.meta n min max;
    w o "let %s_parser' =\n" n;
    w o "  LP.parse_vlgen %d %d %s %s\n\n" smin smax (pcombinator_length_header_name lenty smin smax) (scombinator_name ty);
    let kind_eq = sprintf "(LP.get_parser_kind %s_parser' == %s_parser_kind)" n n in
    w o "let %s_kind_eq : squash %s = assert_norm %s\n\n" n kind_eq kind_eq;
    w o "let %s_parser = %s_parser'\n\n" n n;
    w o "let %s_serializer =\n" n;
    w o "  LP.serialize_vlgen %d %d %s %s\n\n" smin smax (scombinator_length_header_name lenty smin smax) (scombinator_name ty);
    write_bytesize o is_private n;
    wh o "let %s_parser32 =\n" n;
    wh o "  LP.parse32_vlgen %d %dul %d %dul %s %s %s\n\n" smin smin smax smax (pcombinator32_length_header_name lenty smin smax) (scombinator_name ty) (pcombinator32_name ty);
    wh o "let %s_serializer32 =\n" n;
    wh o "  LP.serialize32_vlgen %d %d %s %s\n\n" smin smax (scombinator32_length_header_name lenty smin smax) (scombinator32_name ty);
    wh o "let %s_size32 =\n" n;
    wh o "  LP.size32_vlgen %d %d %s %s\n\n" smin smax (size32_length_header_name lenty smin smax) (size32_name ty);
    if need_validator then (
      wl o "let %s_validator =\n" n;
      wl o "  LL.validate_vlgen %d %dul %d %dul %s %s %s %s\n\n" smin smin smax smax (validator_length_header_name lenty smin smax) (reader_length_header_name lenty smin smax) (scombinator_name ty) (validator_name ty);
    );
    if need_jumper then (
      let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
      wl o "let %s_jumper%s =\n\n" n jumper_annot;
      wl o "  LL.jump_vlgen %d %d %s %s %s %s\n\n" smin smax (jumper_length_header_name lenty smin smax) (reader_length_header_name lenty smin smax) (scombinator_name ty) (jumper_name ty)
    );
    (* accessor *)
    if ty <> "Empty" && ty <> "Fail" then begin
      wl i "val %s_gaccessor : LL.gaccessor %s_parser %s (LL.clens_id %s)\n\n" n n (pcombinator_name ty) (compile_type ty);
      wl o "let %s_gaccessor = LL.gaccessor_vlgen_payload %d %d %s %s\n\n" n smin smax (pcombinator_length_header_name lenty smin smax) (scombinator_name ty);
      wl i "val %s_accessor : LL.accessor %s_gaccessor\n\n" n n;
      wl o "let %s_accessor = LL.accessor_vlgen_payload %d %d %s %s\n\n" n smin smax (jumper_length_header_name lenty smin smax) (scombinator_name ty);
      ()
    end;
    (* TODO: intro lemmas *)
   ()
   end
  else
   begin
    let sizef =
      if basic_type ty then sprintf "Seq.length (LP.serialize %s x)" (scombinator_name ty)
      else bytesize_call ty "x" in
    w i "type %s = x:%s{let l = %s in %d <= l /\\ l <= %d}\n\n" n (compile_type ty) sizef smin smax;
    write_api o i is_private li.meta n min max;
    w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d %s\n\n" n smin smax (scombinator_name ty);
    w o "inline_for_extraction let synth_%s (x: %s') : Tot %s =\n" n n n;
    w o "  [@inline_let] let _ = %s in x\n\n" (bytesize_eq_call ty "x");
    w o "inline_for_extraction let synth_%s_recip (x: %s) : Tot %s' =\n" n n n;
    w o "  [@inline_let] let _ = %s in x\n\n" (bytesize_eq_call ty "x");
    w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
    w o "  LP.parse_bounded_vlgen %d %d %s %s\n\n" smin smax (pcombinator_length_header_name lenty smin smax) (scombinator_name ty);
    let kind_eq = sprintf "(LP.get_parser_kind %s'_parser == %s_parser_kind)" n n in
    w o "let %s_kind_eq : squash %s = assert_norm %s\n\n" n kind_eq kind_eq;
    w o "let %s_parser = LP.parse_synth %s'_parser synth_%s\n\n" n n n;
    w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
    w o "  LP.serialize_bounded_vlgen %d %d %s %s\n\n" smin smax (scombinator_length_header_name lenty smin smax) (scombinator_name ty);
    w o "let %s_serializer = LP.serialize_synth _ synth_%s %s'_serializer synth_%s_recip ()\n\n" n n n n;
    write_bytesize o is_private n;
    wh o "inline_for_extraction noextract let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
    wh o "  LP.parse32_bounded_vlgen %d %dul %d %dul %s %s %s\n\n" smin smin smax smax (pcombinator32_length_header_name lenty smin smax) (scombinator_name ty) (pcombinator32_name ty);
    wh o "let %s_parser32 = LP.parse32_synth' _ synth_%s %s'_parser32 ()\n\n" n n n;
    wh o "inline_for_extraction noextract let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
    wh o "  LP.serialize32_bounded_vlgen %d %d %s %s\n\n" smin smax (scombinator32_length_header_name lenty smin smax) (scombinator32_name ty);
    wh o "let %s_serializer32 = LP.serialize32_synth' _ synth_%s _ %s'_serializer32 synth_%s_recip ()\n\n" n n n n;
    wh o "inline_for_extraction noextract let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
    wh o "  LP.size32_bounded_vlgen %d %d %s %s\n\n" smin smax (size32_length_header_name lenty smin smax) (size32_name ty);
    wh o "let %s_size32 = LP.size32_synth' _ synth_%s _ %s'_size32 synth_%s_recip ()\n\n" n n n n;
    if need_validator then (
      wl o "inline_for_extraction let %s'_validator : LL.validator %s'_parser =\n" n n;
      wl o "  LL.validate_bounded_vlgen %d %dul %d %dul %s %s %s %s\n\n" smin smin smax smax (validator_length_header_name lenty smin smax) (reader_length_header_name lenty smin smax) (scombinator_name ty) (validator_name ty);
      wl o "let %s_validator = LL.validate_synth %s'_validator synth_%s ()\n\n" n n n
    );
    if need_jumper then (
      wl o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser =\n" n n;
      wl o "  LL.jump_bounded_vlgen %d %d %s %s %s %s\n\n" smin smax (jumper_length_header_name lenty smin smax) (reader_length_header_name lenty smin smax) (scombinator_name ty) (jumper_name ty);
      let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
      wl o "let %s_jumper%s = LL.jump_synth %s'_jumper synth_%s ()\n\n" n jumper_annot n n
    );
    (* TODO: intro lemmas *)
    (* accessor *)
    wl i "noextract let %s_clens : LL.clens %s %s = {\n" n n (compile_type ty);
    wl i "  LL.clens_cond = (fun _ -> True);\n";
    wl i "  LL.clens_get = (fun (x: %s) -> (x <: %s));\n" n (compile_type ty);
    wl i "}\n\n";
    wl i "val %s_gaccessor : LL.gaccessor %s_parser %s %s_clens\n\n" n n (pcombinator_name ty) n;
    let write_accessor g compose_needs_unit jumper_or_parser =
      wl o "let %s_%saccessor =\n" n g;
      wl o "  LL.%saccessor_ext\n" g;
      wl o "    (LL.%saccessor_compose\n" g;
      wl o "      (LL.%saccessor_synth %s'_parser synth_%s synth_%s_recip ())\n" g n n n;
      wl o "      (LL.%saccessor_bounded_vlgen_payload %d %d %s %s)\n" g smin smax jumper_or_parser (scombinator_name ty);
      (if compose_needs_unit then wl o "      ()\n");
      wl o "    )\n";
      wl o "    %s_clens\n" n;
      wl o "    ()\n\n";
      () in
    write_accessor "g" false (pcombinator_length_header_name lenty smin smax);
    wl i "val %s_accessor : LL.accessor %s_gaccessor\n\n" n n;
    write_accessor "" true (jumper_length_header_name lenty smin smax);
    ()
   end;
  (* TODO: lemma about bytesize *)
  ()

and compile_typedef o i tn fn (ty:type_t) vec def al =
  let n = if tn = "" then String.uncapitalize_ascii fn else tn^"_"^fn in
  let qname = if tn = "" then String.uncapitalize_ascii fn else tn^"@"^fn in
  let is_private = has_attr al "private" in
  let elem_li = sizeof ty in
  let li = get_leninfo qname in
  let need_validator = is_private || need_validator li.meta li.min_len li.max_len in
  let need_jumper = is_private || need_jumper li.min_len li.max_len in
  let (ty, vec) =
    (* Rewriting for some implifications, eg opaque+vldata=vlbytes *)
    match ty, vec with
    | _, VectorFixedCount k ->
      if li.min_len = li.max_len then (ty, VectorFixed li.max_len)
      else failwith "Can't declare array of variable length elements"
    | TypeSimple(t), VectorVldata vl when SM.mem (compile_type t) !erased ->
      let (len_len_min, len_len_max, max_len) = basic_bounds vl in
      TypeSimple("opaque"),
      VectorRange(max 0 (li.min_len-len_len_min),
                  min max_len (max 0 (li.max_len-len_len_max)),
                  Some vl)
    | TypeSimple("opaque"), VectorVldata vl ->
      let (_, _, max_len) = basic_bounds vl in
      TypeSimple("opaque"), VectorRange(0, max_len, Some vl)
    | _ -> ty, vec in
  match ty with
  | TypeIfeq _ -> failwith "Unsupported if-then-else, must to appear in a struct after a tag"
  | TypeSelect _ -> failwith "Unsupported select, must appear in a struct after an enum tag"
  | TypeSimple ty ->
    match vec with
    (* Type aliasing *)
    | VectorNone ->
      w i "type %s = %s\n\n" n (compile_type ty);
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "noextract let %s_parser = %s\n\n" n (pcombinator_name ty);
      w o "noextract let %s_serializer = %s\n\n" n (scombinator_name ty);
      write_bytesize o is_private n;
      wh o "let %s_parser32 = %s\n\n" n (pcombinator32_name ty);
      wh o "let %s_serializer32 = %s\n\n" n (scombinator32_name ty);
      wh o "let %s_size32 = %s\n\n" n (size32_name ty);
      (if need_validator then
        wl o "let %s_validator = %s\n\n" n (validator_name ty));
      (if need_jumper then
         let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
         wl o "let %s_jumper%s = %s\n\n" n jumper_annot (jumper_name ty));
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %s) [SMTPat (%s_bytesize x)]\n\n" n n n (bytesize_call ty "x") n;
      w o "let %s_bytesize_eqn x = %s\n\n" n (bytesize_eq_call ty "x");
      if ty <> "Empty" && ty <> "Fail"
      then begin
          w i "val %s_parser_serializer_eq (_: unit) : Lemma (%s_parser == %s /\\ %s_serializer == %s)\n\n" n n (pcombinator_name ty) n (scombinator_name ty);
          w o "let %s_parser_serializer_eq _ = ()\n\n" n
        end;
      ()

    (* Should be rewritten during normalization *)
    | VectorFixedCount _
    | VectorSymbolic _ -> failwith "not supported"

    | VectorCount(low, high, repr) ->
      let repr_t = match repr with None -> "uint32" | Some t -> t in
      w i "inline_for_extraction noextract let min_count = %d\ninline_for_extraction noextract let max_count = %d\n" low high;
      w i "type %s = l:list %s{%d <= L.length l /\\ L.length l <= %d}\n\n" n (compile_type ty) low high;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "let %s_parser' = LP.parse_vclist %d %d %s %s\n\n" n low high (pcombinator_name repr_t) (pcombinator_name ty);
      w o "private let kind_eq : squash (LP.get_parser_kind %s_parser' == %s_parser_kind) = _ by (FStar.Tactics.trefl ())\n\n" n n;
      w o "private let type_eq : squash (%s == LL.vlarray %s %d %d) = _ by (FStar.Tactics.trefl ())\n\n" n (compile_type ty) low high;
      w o "let %s_parser = %s_parser'\n" n n;
      w o "let %s_serializer = LL.serialize_vclist %d %d %s %s\n\n" n low high (scombinator_name repr_t) (scombinator_name ty);
      write_bytesize o is_private n;
      wh o "let %s_parser32 = LP.parse32_vclist %dul %dul %s %s\n\n" n low high (pcombinator32_name repr_t) (pcombinator32_name ty);
      wh o "let %s_serializer32 =\n  [@inline_let] let _ = assert_norm (LP.serialize32_vclist_precond %d %d (LP.get_parser_kind %s) (LP.get_parser_kind %s)) in\n" n low high (pcombinator_name repr_t) (pcombinator_name ty);
      wh o "  LP.serialize32_vclist %d %d %s %s\n\n" low high (scombinator32_name repr_t) (scombinator32_name ty);
      wh o "let %s_size32 =\n  [@inline_let] let _ = assert_norm (LP.serialize32_vclist_precond %d %d (LP.get_parser_kind %s) (LP.get_parser_kind %s)) in\n" n low high (pcombinator_name repr_t) (pcombinator_name ty);
      wh o "  LP.size32_vclist %d %d %s %s\n\n" low high (size32_name repr_t) (size32_name ty);
      wl o "let %s_validator = LL.validate_vclist %dul %dul %s %s %s\n\n" n low high (validator_name repr_t) (leaf_reader_name repr_t) (validator_name ty);
      let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
      wl o "let %s_jumper%s =\n" n jumper_annot;
      wl o "  LL.jump_vclist %d %d %s %s %s\n\n" low high (jumper_name repr_t) (leaf_reader_name repr_t) (jumper_name ty);
      (* finalizer, count, i-th accessor TODO *)
      ()

    | VectorVldata (("asn1_len" | "asn1_len8") as lenty) -> (* TODO: generalize once parse_bounded_integer is refactored into a parser to bounded_int32 in LowParse *)
       let (len_len_min, len_len_max, smax) = basic_bounds lenty in
       compile_vldata o i is_private n ty li elem_li lenty len_len_min len_len_max 0 smax

    | VectorVldata "bitcoin_varint" -> failwith "VectorVldata bitcoin_varint is unsupported for now"

    | VectorVldata vl ->
      let (len_len_min, len_len_max, smax) = basic_bounds vl in
      let (min, max) = li.min_len, li.max_len in
      let fits_in_bounds = elem_li.max_len <= smax in
      let needs_synth = not fits_in_bounds in
      if fits_in_bounds then
       begin
        w i "type %s = %s\n\n" n (compile_type ty);
        write_api o i is_private li.meta n min max;
        w o "let %s_parser =\n" n;
        w o "  LP.parse_bounded_vldata %d %d %s\n\n" 0 smax (pcombinator_name ty);
        w o "let %s_serializer =\n" n;
        w o "  LP.serialize_bounded_vldata %d %d %s\n\n" 0 smax (scombinator_name ty);
        write_bytesize o is_private n;
        wh o "let %s_parser32 =\n" n;
        wh o "  LP.parse32_bounded_vldata %d %dul %d %dul %s\n\n" 0 0 smax smax (pcombinator32_name ty);
        wh o "let %s_serializer32 =\n" n;
        wh o "  LP.serialize32_bounded_vldata %d %d %s\n\n" 0 smax (scombinator32_name ty);
        wh o "let %s_size32 =\n" n;
        wh o "  LP.size32_bounded_vldata %d %d %s %dul\n\n" 0 smax (size32_name ty) (log256 smax);
        if need_validator then (
          wl o "let %s_validator =\n" n;
          wl o "  LL.validate_bounded_vldata %d %d %s ()\n\n" 0 smax (validator_name ty);
        );
        if need_jumper then (
          let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
          wl o "let %s_jumper%s =\n\n" n jumper_annot;
          wl o "  LL.jump_bounded_vldata %d %d %s ()\n\n" 0 smax (pcombinator_name ty)
        );
        (* accessor *)
        if ty <> "Empty" && ty <> "Fail" then
         begin
          wl i "val %s_gaccessor : LL.gaccessor %s_parser %s (LL.clens_id %s)\n\n" n n (pcombinator_name ty) (compile_type ty);
          wl o "let %s_gaccessor = LL.gaccessor_bounded_vldata_payload %d %d %s\n\n" n 0 smax (pcombinator_name ty);
          wl i "val %s_accessor : LL.accessor %s_gaccessor\n\n" n n;
          wl o "let %s_accessor = LL.accessor_bounded_vldata_payload %d %d %s\n\n" n 0 smax (pcombinator_name ty);
          ()
         end;
        (* finalizer *)
        begin match ty with
        | "Fail" -> () (* impossible *)
        | "Empty" ->
            wl i "val %s_finalize (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : HST.Stack unit\n" n;
            wl i "  (requires (fun h ->\n";
            wl i "    U32.v pos + %d <= U32.v input.LL.len /\\\n" len_len_max;
            wl i "    LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h /\\\n" len_len_max;
            wl i "    LL.live_slice h input\n";
            wl i "  ))\n";
            wl i "  (ensures (fun h _ h' ->\n";
            wl i "    B.modifies (LL.loc_slice_from_to input pos (pos `U32.add` %dul)) h h' /\\\n" len_len_max;
            wl i "    LL.valid_pos %s_parser h' input pos (pos `U32.add` %dul)\n" n len_len_max;
            wl i "  ))\n\n";
            wl o "let %s_finalize #_ #_ input pos =\n" n;
            wl o "  let h = HST.get () in\n";
            wl o "  [@inline_let] let _ = LL.valid_facts LL.parse_empty h input (pos `U32.add` %dul) in\n" len_len_max;
            wl o "  LL.finalize_bounded_vldata %d %d LL.parse_empty input pos (pos `U32.add` %dul) \n\n" 0 smax len_len_max
        | _ ->
            wl i "val %s_finalize (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) (pos' : U32.t) : HST.Stack unit\n" n;
            wl i "  (requires (fun h ->\n";
            wl i "    U32.v pos + %d <= U32.v input.LL.len /\\\n" len_len_max;
            wl i "    LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h /\\\n" len_len_max;
            wl i "    LL.valid_pos %s h input (pos `U32.add` %dul) pos'\n" (pcombinator_name ty) len_len_max;
            wl i "  ))\n";
            wl i "  (ensures (fun h _ h' ->\n";
            wl i "    B.modifies (LL.loc_slice_from_to input pos (pos `U32.add` %dul)) h h' /\\\n" len_len_max;
            wl i "    LL.valid_content_pos %s_parser h' input pos (LL.contents %s h input (pos `U32.add` %dul)) pos'\n" n (pcombinator_name ty) len_len_max;
            wl i "  ))\n\n";
            wl o "let %s_finalize #_ #_ input pos pos' =\n" n;
            wl o "  LL.finalize_bounded_vldata %d %d %s input pos pos'\n\n" 0 smax (pcombinator_name ty)
        end;
        ()
       end
      else
       begin
        let sizef =
          if basic_type ty then sprintf "Seq.length (LP.serialize %s x)" (scombinator_name ty)
          else bytesize_call ty "x" in
        w i "type %s = x:%s{let l = %s in %d <= l /\\ l <= %d}\n\n" n (compile_type ty) sizef 0 smax;
        w i "val check_%s_bytesize (x: %s) : Tot (b: bool {b == (let l = %s in %d <= l && l <= %d)})\n\n" n (compile_type ty) sizef 0 smax;
        w o "let check_%s_bytesize x =\n" n;
        w o "  [@inline_let] let _ = %s in\n" (bytesize_eq_call (compile_type ty) "x");
        w o "  let l = %s x in\n" (size32_name ty);
        w o "  %dul `U32.lte` l && l `U32.lte` %dul\n\n" 0 smax;
        write_api o i is_private li.meta n min max;
        w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d %s\n\n" n 0 smax (scombinator_name ty);
        w o "inline_for_extraction let synth_%s (x: %s') : Tot %s =\n" n n n;
        w o "  [@inline_let] let _ = %s in x\n\n" (bytesize_eq_call ty "x");
        w o "inline_for_extraction let synth_%s_recip (x: %s) : Tot %s' =\n" n n n;
        w o "  [@inline_let] let _ = %s in x\n\n" (bytesize_eq_call ty "x");
        w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
        w o "  LP.parse_bounded_vldata_strong %d %d %s\n\n" 0 smax (scombinator_name ty);
        w o "let %s_parser = LP.parse_synth %s'_parser synth_%s\n\n" n n n;
        w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
        w o "  LP.serialize_bounded_vldata_strong %d %d %s\n\n" 0 smax (scombinator_name ty);
        w o "let %s_serializer = LP.serialize_synth _ synth_%s %s'_serializer synth_%s_recip ()\n\n" n n n n;
        write_bytesize o is_private n;
        wh o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
        wh o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul %s %s\n\n" 0 0 smax smax (scombinator_name ty) (pcombinator32_name ty);
        wh o "let %s_parser32 = LP.parse32_synth' _ synth_%s %s'_parser32 ()\n\n" n n n;
        wh o "inline_for_extraction noextract let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
        wh o "  LP.serialize32_bounded_vldata_strong %d %d %s\n\n" 0 smax (scombinator32_name ty);
        wh o "let %s_serializer32 = LP.serialize32_synth' _ synth_%s _ %s'_serializer32 synth_%s_recip ()\n\n" n n n n;
        wh o "inline_for_extraction noextract let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
        wh o "  LP.size32_bounded_vldata_strong %d %d %s %dul\n\n" 0 smax (size32_name ty) (log256 smax);
        wh o "let %s_size32 = LP.size32_synth' _ synth_%s _ %s'_size32 synth_%s_recip ()\n\n" n n n n;
        if need_validator then (
          wl o "inline_for_extraction let %s'_validator : LL.validator %s'_parser =\n" n n;
          wl o "  LL.validate_bounded_vldata_strong %d %d %s %s ()\n\n" 0 smax (scombinator_name ty) (validator_name ty);
          wl o "let %s_validator = LL.validate_synth %s'_validator synth_%s ()\n\n" n n n
        );
        if need_jumper then (
          wl o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser =\n" n n;
          wl o "  LL.jump_bounded_vldata_strong %d %d %s ()\n\n" 0 smax (scombinator_name ty);
          let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
          wl o "let %s_jumper%s = LL.jump_synth %s'_jumper synth_%s ()\n\n" n jumper_annot n n
        );
        (* finalizer *)
        if ty = "Empty" || ty = "Fail" then failwith "vldata empty/fail should have been in the 'bounds OK' case";
        wl i "val %s_finalize (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) (pos'  : U32.t) : HST.Stack unit\n"  n;
        wl i "  (requires (fun h ->\n" ;
        wl i "     U32.v pos + %d < 4294967296 /\\ (\n" len_len_max;
        wl i "     let pos_payload = pos `U32.add` %dul in\n" len_len_max;
        wl i "     LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h /\\\n"  len_len_max;
        wl i "     LL.valid_pos %s h input pos_payload pos' /\\ (\n" (pcombinator_name ty);
        wl i "     let len_payload = U32.v pos' - U32.v pos_payload in\n";
        wl i "     let x = LL.contents %s h input pos_payload in\n" (pcombinator_name ty);
        wl i "     let len_ser = %s in\n" (bytesize_call ty "x");
        wl i "     ((%d <= len_payload /\\ len_payload <= %d) \\/ (%d <= len_ser /\\ len_ser <= %d))\n" 0 smax 0 smax;
        wl i "  ))))\n";
        wl i "  (ensures (fun h _ h' ->\n";
        wl i "    let x = LL.contents %s h input (pos `U32.add` %dul) in\n" (pcombinator_name ty) len_len_max;
        wl i "    let len_ser = %s in\n" (bytesize_call ty "x");
        wl i "    B.modifies (LL.loc_slice_from_to input pos (pos `U32.add` %dul)) h h' /\\\n" len_len_max;
        wl i "    %d <= len_ser /\\ len_ser <= %d /\\\n" 0 smax;
        wl i "    LL.valid_content_pos %s_parser h' input pos x pos'\n" n;
        wl i "  ))\n\n";
        wl o "let %s_finalize #_ #_ input pos pos' =\n" n;
        wl o "  let h = HST.get () in\n";
        wl o "  [@inline_let] let _ =\n";
        wl o "    let x = LL.contents %s h input (pos `U32.add` %dul) in\n" (pcombinator_name ty) len_len_max;
        wl o "    %s\n" (bytesize_eq_call ty "x");
        wl o "  in\n";
        wl o "  LL.finalize_bounded_vldata_strong %d %d %s input pos pos';\n" 0 smax (scombinator_name ty);
        wl o "  let h = HST.get () in\n";
        wl o "  LL.valid_synth h %s'_parser synth_%s input pos\n\n" n n;
        (* accessor *)
        wl i "noextract let %s_clens : LL.clens %s %s = {\n" n n (compile_type ty);
        wl i "  LL.clens_cond = (fun _ -> True);\n";
        wl i "  LL.clens_get = (fun (x: %s) -> (x <: %s));\n" n (compile_type ty);
        wl i "}\n\n";
        wl i "val %s_gaccessor : LL.gaccessor %s_parser %s %s_clens\n\n" n n (pcombinator_name ty) n;
        let write_accessor g compose_needs_unit =
          wl o "let %s_%saccessor =\n" n g;
          wl o "  LL.%saccessor_ext\n" g;
          wl o "    (LL.%saccessor_compose\n" g;
          wl o "      (LL.%saccessor_synth %s'_parser synth_%s synth_%s_recip ())\n" g n n n;
          wl o "      (LL.%saccessor_bounded_vldata_strong_payload %d %d %s)\n" g 0 smax (scombinator_name ty);
          (if compose_needs_unit then wl o "      ()\n");
          wl o "    )\n";
          wl o "    %s_clens\n" n;
          wl o "    ()\n\n";
          ()
        in
        write_accessor "g" false;
        wl i "val %s_accessor : LL.accessor %s_gaccessor\n\n" n n;
        write_accessor "" true;
        ()
       end;
      (* lemma about bytesize *)
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + %s) [SMTPat (%s_bytesize x)]\n\n" n n n li.len_len (bytesize_call ty "x") n;
      w o "let %s_bytesize_eqn x =\n" n;
      (if needs_synth then w o "  LP.serialize_synth_eq _ synth_%s %s'_serializer synth_%s_recip () x;\n" n n n);
      w o "  %s\n\n" (bytesize_eq_call ty "x");
      ()

    (* Fixed-length bytes *)
    | VectorFixed k when (compile_type ty = "U8.t") ->
      w i "type %s = lbytes %d\n\n" n k;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "noextract let %s_parser = LP.parse_flbytes %d\n\n" n k;
      w o "noextract let %s_serializer = LP.serialize_flbytes %d\n\n" n k;
      write_bytesize o is_private n;
      wh o "let %s_parser32 = LP.parse32_flbytes %d %dul\n\n" n k k;
      wh o "let %s_serializer32 = LP.serialize32_flbytes %d\n\n" n k;
      wh o "let %s_size32 = LP.size32_constant %s_serializer %dul ()\n\n" n n k;
      (* validator and jumper not needed unless private, we are total constant size *)
      if is_private then
       begin
        wl o "let %s_validator = LL.validate_flbytes %d %dul\n\n" n k k;
        wl o "let %s_jumper : LL.jumper %s_parser = LL.jump_flbytes %d %dul\n\n" n n k k
       end;
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == BY.length x) [SMTPat (%s_bytesize x)]\n\n" n n n n;
      w o "let %s_bytesize_eqn x = ()\n\n" n;
      (* intro *)
      wl i "val %s_intro (h: HS.mem) (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : Lemma\n" n;
      wl i "  (requires (\n";
      wl i "    LL.live_slice h input /\\\n";
      wl i "    U32.v pos + %d <= U32.v input.LL.len\n" k;
      wl i "  ))\n";
      wl i "  (ensures (\n";
      wl i "    LL.valid_content_pos %s_parser h input pos (BY.hide (LL.bytes_of_slice_from_to h input pos (pos `U32.add` %dul))) (pos `U32.add` %dul)\n" n k k;
      wl i "  ))\n\n";
      wl o "let %s_intro h #_ #_ input pos =\n" n;
      wl o "  LL.valid_flbytes_intro h %d input pos\n\n" k;
      (* elim *)
      wl i "val %s_elim (h: HS.mem) (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : Lemma\n" n;
      wl i "  (requires (LL.valid %s_parser h input pos))\n" n;
      wl i "  (ensures (\n";
      wl i "    U32.v pos + %d <= U32.v input.LL.len /\\\n" k;
      wl i "    LL.valid_content_pos %s_parser h input pos (BY.hide (LL.bytes_of_slice_from_to h input pos (pos `U32.add` %dul))) (pos `U32.add` %dul)\n" n k k;
      wl i "  ))\n\n";
      wl o "let %s_elim h #_ #_ input pos =\n" n;
      wl o "  LL.valid_flbytes_elim h %d input pos\n\n" k;
      ()

    (* Fixed length list *)
    | VectorFixed k when elem_li.min_len = elem_li.max_len ->
      w i "unfold let %s_pred (l:list %s) (n:nat) : GTot Type0 = L.length l == n\n" n (compile_type ty);
      w i "type %s = l:list %s{%s_pred l %d}\n\n" n (compile_type ty) n li.min_count;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "type %s' = LP.array %s %d\n\n" n (compile_type ty) li.min_count;
      w o "private let %s_eq () : Lemma (%s' == %s) =\n" n n n;
      w o "  assert(%s'==%s) by (FStar.Tactics.norm [delta_only [`%%(LP.array); `%%(%s); `%%(%s')]]; FStar.Tactics.trefl ())\n\n" n n n n;
      w o "noextract let %s'_parser = LP.parse_array %s %d %d\n\n" n (scombinator_name ty) k li.min_count;
      w o "let %s_parser = %s_eq(); LP.coerce (LP.parser %s_parser_kind %s) %s'_parser\n\n" n n n n n;
      w o "noextract let %s'_serializer = LP.serialize_array %s %d %d ()\n\n" n (scombinator_name ty) k li.min_count;
      w o "let %s_serializer = %s_eq(); LP.coerce (LP.serializer %s_parser) %s'_serializer\n\n" n n n n;
      write_bytesize o is_private n;
      wh o "inline_for_extraction let %s'_parser32 = LP.parse32_array %s %s %d %dul %d ()\n\n"
        n (scombinator_name ty) (pcombinator32_name ty) k k li.min_count;
      wh o "let %s_parser32 = %s_eq(); LP.coerce (LP.parser32 %s_parser) %s'_parser32\n\n" n n n n;
      wh o "inline_for_extraction noextract let %s'_serializer32 =\n" n;
      wh o "  LP.serialize32_array #_ #_ #_ #%s %s %d %d ()\n\n" (scombinator_name ty) (scombinator32_name ty) k li.min_count;
      wh o "let %s_serializer32 = %s_eq(); LP.coerce (LP.serializer32 %s_serializer) %s'_serializer32\n\n" n n n n;
      wh o "let %s_size32 = LP.size32_array %s %d %dul %d ()\n" n (scombinator_name ty) k k li.min_count;
      (if need_validator then
        wl o "let %s_validator = LL.validate_array %s %s %d %dul %d ()\n\n" n (scombinator_name ty) (validator_name ty) k k li.min_count);
      (* jumper not needed unless private, we are constant size *)
      (if is_private then
        wl o "let %s_jumper : LL.jumper %s_parser = LL.jump_array %s %d %dul %d ()\n\n" n n (scombinator_name ty) k k li.min_count);
      wl i "noextract let clens_%s_nth (i: nat { i < %d } ) : LL.clens %s %s = {\n" n li.min_count n (compile_type ty);
      wl i "  LL.clens_cond = (fun _ -> True);\n";
      wl i "  LL.clens_get = (fun (l: %s) -> L.index l i);\n" n;
      wl i "}\n\n";
      wl i "val %s_nth_ghost (i: nat {i < %d}) : LL.gaccessor %s_parser %s (clens_%s_nth i)\n\n" n li.max_count n (pcombinator_name ty) n;
      wl o "let %s_nth_ghost i = LL.array_nth_ghost %s %d %d i\n\n" n (scombinator_name ty) li.max_len li.max_count;
      wl i "inline_for_extraction val %s_nth (i: U32.t { U32.v i < %d } ) : LL.accessor (%s_nth_ghost (U32.v i))\n\n" n li.max_count n;
      wl o "let %s_nth i = LL.array_nth %s %d %d i\n\n" n (scombinator_name ty) li.max_len li.max_count;
      (* intro lemma *)
      wl i "val %s_intro (h: HS.mem) (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos pos' : U32.t) : Lemma\n" n;
      wl i "  (requires (\n";
      wl i "     LL.valid_list %s h input pos pos' /\\\n" (pcombinator_name ty);
      wl i "     (L.length (LL.contents_list %s h input pos pos') == %d \\/ U32.v pos' - U32.v pos == %d)\n" (pcombinator_name ty) li.max_count li.max_len;
      wl i "  ))\n";
      wl i "  (ensures (\n";
      wl i "    let x = LL.contents_list %s h input pos pos' in\n" (pcombinator_name ty);
      wl i "    L.length x = %d /\\\n" li.max_count;
      wl i "    U32.v pos' - U32.v pos == %d /\\\n" li.max_len;
      wl i "    LL.valid_content_pos %s_parser h input pos x pos'\n" n;
      wl i "  ))\n\n";
      wl o "let %s_intro h #_ #_ input pos pos' = %s_eq (); LL.valid_list_valid_array %s %d %dul %d () h input pos pos'\n\n" n n (scombinator_name ty) li.max_len li.max_len li.max_count;
      (* elim lemma *)
      wl i "val %s_elim (h: HS.mem) (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : Lemma\n" n;
      wl i "  (requires (LL.valid %s_parser h input pos))\n" n;
      wl i "  (ensures (\n";
      wl i "    let pos' = LL.get_valid_pos %s_parser h input pos in\n" n;
      wl i "    U32.v pos' - U32.v pos == %d /\\\n" li.max_len;
      wl i "    LL.valid_list %s h input pos pos' /\\\n" (pcombinator_name ty);
      wl i "    LL.contents_list %s h input pos pos' == LL.contents %s_parser h input pos\n" (pcombinator_name ty) n;
      wl i "  ))\n";
      wl o "let %s_elim h #_ #_ input pos = %s_eq (); LL.valid_array_valid_list %s %d %dul %d () h input pos\n\n" n n (scombinator_name ty) li.max_len li.max_len li.max_count;
      (* lemmas about bytesize *)
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == L.length x `FStar.Mul.op_Star` %d) [SMTPat (%s_bytesize x)]\n\n" n n n elem_li.min_len n;
      w o "let %s_bytesize_eqn x =\n" n;
      w o "  assert_norm (LP.fldata_array_precond %s %d %d == true);\n" (pcombinator_name ty) li.max_len li.max_count;
      w o "  LP.length_serialize_array %s %d %d () x\n\n"(scombinator_name ty) li.max_len li.max_count;
      ()

    (* Fixed bytelen list of variable length elements *)
    | VectorFixed(k) ->
      w i "noextract val %s_list_bytesize: list %s -> GTot nat\n\n" n (compile_type ty);
      w o "let %s_list_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s) x)\n\n" n (scombinator_name ty);
      w i "type %s = l:list %s{%s_list_bytesize l == %d}\n\n" n (compile_type ty) n k;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "type %s' = LP.parse_fldata_strong_t (LP.serialize_list _ %s) %d\n\n" n (scombinator_name ty) k;
      w o "let %s_eq () : Lemma (%s' == %s) = assert_norm (%s' == %s)\n\n" n n n n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_fldata_strong (LP.serialize_list _ %s) %d\n\n" (scombinator_name ty) k;
      w o "let %s_parser = %s_eq (); LP.coerce (LP.parser %s_parser_kind %s) %s'_parser\n\n" n n n n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_fldata_strong (LP.serialize_list _ %s) %d\n\n" (scombinator_name ty) k;
      w o "let %s_serializer = %s_eq () ; LP.coerce (LP.serializer %s_parser) %s'_serializer\n\n" n n n n;
      write_bytesize o is_private n;
      wh o "inline_for_extraction noextract let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      wh o "  LP.parse32_fldata_strong (LP.serialize_list _ %s) (LP.parse32_list %s) %d %dul\n\n" (scombinator_name ty) (pcombinator32_name ty) k k;
      wh o "let %s_parser32 = %s_eq (); LP.coerce (LP.parser32 %s_parser) %s'_parser32\n\n" n n n n;
      wh o "inline_for_extraction noextract let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      wh o "  LP.serialize32_fldata_strong (LP.partial_serialize32_list _ %s %s ()) %d\n\n" (scombinator_name ty) (scombinator32_name ty) k;
      wh o "let %s_serializer32 = %s_eq (); LP.coerce (LP.serializer32 %s_serializer) %s'_serializer32\n\n" n n n n;
      wh o "inline_for_extraction noextract let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      wh o "  LP.size32_fldata_strong (LP.serialize_list _ %s) %d %dul\n\n" (scombinator_name ty) k k;
      wh o "let %s_size32 = %s_eq (); LP.coerce (LP.size32 %s_serializer) %s'_size32\n\n" n n n n;
      wl o "inline_for_extraction let %s'_validator : LL.validator %s'_parser =\n" n n;
      wl o "  LL.validate_fldata_strong (LL.serialize_list _ %s) (LL.validate_list %s ()) %d %dul\n\n" (scombinator_name ty) (validator_name ty) k k;
      wl o "let %s_validator = %s_eq (); LP.coerce (LL.validator %s_parser) %s'_validator\n\n" n n n n;
      (* jumper not needed unless private, we are constant size *)
      if is_private then
       begin
        wl o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser =\n" n n;
        wl o "  LL.jump_fldata_strong (LL.serialize_list _ %s) %d %dul\n\n" (scombinator_name ty) k k;
        wl o "let %s_jumper : LL.jumper %s_parser = %s_eq (); LP.coerce (LL.jumper %s_parser) %s'_jumper\n\n" n n n n n
       end;
      ()

    (* Variable length bytes *)
    | VectorRange (low, high, repr)
      when compile_type ty = "U8.t" &&
        (match repr with None -> true
        | Some t -> let (_,lm,_) = basic_bounds t in lm = log256 high) ->
      w i "inline_for_extraction noextract let min_len = %d\ninline_for_extraction noextract let max_len = %d\n" low high;
      w i "type %s = b:bytes{%d <= length b /\\ length b <= %d}\n\n" n low high;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "noextract let %s_parser = LP.parse_bounded_vlbytes %d %d\n\n" n low high;
      w o "noextract let %s_serializer = LP.serialize_bounded_vlbytes %d %d\n\n" n low high;
      write_bytesize o is_private n;
      wh o "let %s_parser32 = LP.parse32_bounded_vlbytes %d %dul %d %dul\n\n" n low low high high;
      wh o "let %s_serializer32 = LP.serialize32_bounded_vlbytes %d %d\n\n" n low high;
      wh o "let %s_size32 = LP.size32_bounded_vlbytes %d %d\n\n" n low high;
      if need_validator then
        wl o "let %s_validator = LL.validate_bounded_vlbytes %d %d\n\n" n low high;
      if need_jumper then begin
        let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
        wl o "let %s_jumper%s = LL.jump_bounded_vlbytes %d %d\n\n" n jumper_annot low high
      end;
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + BY.length x) [SMTPat (%s_bytesize x)]\n\n" n n n li.len_len n;
      w o "let %s_bytesize_eqn x = LP.length_serialize_bounded_vlbytes %d %d x\n\n" n low high;
      (* length *)
      wl i "val %s_length (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : HST.Stack U32.t\n" n;
      wl i "  (requires (fun h -> LL.valid %s_parser h input pos))\n" n;
      wl i "  (ensures (fun h res h' ->\n";
      wl i "    let x = LL.contents %s_parser h input pos in\n" n;
      wl i "    B.modifies B.loc_none h h' /\\\n";
      wl i "    U32.v pos + %d + U32.v res == U32.v (LL.get_valid_pos %s_parser h input pos) /\\\n" li.len_len n;
      wl i "    res == BY.len x /\\\n";
      wl i "    LL.bytes_of_slice_from_to h input (pos `U32.add` %dul) ((pos `U32.add` %dul) `U32.add` res) == BY.reveal x\n" li.len_len li.len_len;
      wl i "  ))\n\n";
      wl o "let %s_length #_ #_ input pos =\n" n;
      wl o "  [@inline_let] let _ = assert_norm (%s == LP.parse_bounded_vlbytes_t %d %d) in\n" n low high;
      wl o "  LL.bounded_vlbytes_payload_length %d %d input pos\n\n" low high;
      (* finalizer *)
      wl i "val %s_finalize (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) (len: U32.t) : HST.Stack U32.t\n\n" n;
      wl i "  (requires (fun h ->\n";
      wl i "    LL.live_slice h input /\\\n";
      wl i "    %d <= U32.v len /\\ U32.v len <= %d /\\\n" low high;
      wl i "    U32.v pos + %d + U32.v len <= U32.v input.LL.len /\\\n" li.len_len;
      wl i "    LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h\n" li.len_len;
      wl i "  ))\n";
      wl i "  (ensures (fun h pos' h' ->\n";
      wl i "    let pos_payload = pos `U32.add` %dul in\n" li.len_len;
      wl i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
      wl i "    LL.valid_content_pos %s_parser h' input pos (BY.hide (LL.bytes_of_slice_from_to h input pos_payload (pos_payload `U32.add` len))) pos' /\\\n" n;
      wl i "    U32.v pos' == U32.v pos_payload + U32.v len\n";
      wl i "  ))\n\n";
      wl o "let %s_finalize #_ #_ input pos len =\n" n;
      wl o "  [@inline_let] let _ = assert_norm (%s == LP.parse_bounded_vlbytes_t %d %d) in\n" n low high;
      wl o "  LL.finalize_bounded_vlbytes %d %d input pos len\n\n" low high;
      ()

    (* Variable length bytes where the size of the length is explicit *)
    | VectorRange (low, high, repr) when (compile_type ty = "U8.t") ->
      let trepr = match repr with Some t -> t | None -> failwith "Missing vlbytes size repr (QD bug?)" in
      let (_, repr, _) = basic_bounds trepr in
      w i "inline_for_extraction noextract let min_len = %d\ninline_for_extraction noextract let max_len = %d\n" low high;
      w i "type %s = b:bytes{%d <= length b /\\ length b <= %d}\n\n" n low high;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "noextract let %s_parser = LP.parse_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      w o "noextract let %s_serializer = LP.serialize_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      write_bytesize o is_private n;
      wh o "let %s_parser32 = LP.parse32_bounded_vlbytes' %d %dul %d %dul %d\n\n" n low low high high repr;
      wh o "let %s_serializer32 = LP.serialize32_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      wh o "let %s_size32 = LP.size32_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      if need_validator then
        wl o "let %s_validator = LL.validate_bounded_vlbytes' %d %d %d\n\n" n low high repr;
      if need_jumper then begin
        let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
        wl o "let %s_jumper%s = LL.jump_bounded_vlbytes' %d %d %d\n\n" n jumper_annot low high repr
      end;
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + BY.length x) [SMTPat (%s_bytesize x)]\n\n" n n n repr n;
      w o "let %s_bytesize_eqn x = LP.length_serialize_bounded_vlbytes' %d %d %d x\n\n" n low high repr;
      (* length *)
      wl i "val %s_length (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : HST.Stack U32.t\n" n;
      wl i "  (requires (fun h -> LL.valid %s_parser h input pos))\n" n;
      wl i "  (ensures (fun h res h' ->\n";
      wl i "    let x = LL.contents %s_parser h input pos in\n" n;
      wl i "    B.modifies B.loc_none h h' /\\\n";
      wl i "    U32.v pos + %d + U32.v res == U32.v (LL.get_valid_pos %s_parser h input pos) /\\\n" repr n;
      wl i "    res == BY.len x /\\\n";
      wl i "    LL.bytes_of_slice_from_to h input (pos `U32.add` %dul) ((pos `U32.add` %dul) `U32.add` res) == BY.reveal x\n" repr repr;
      wl i "  ))\n\n";
      wl o "let %s_length #_ #_ input pos =\n" n;
      wl o "  [@inline_let] let _ = assert_norm (%s == LP.parse_bounded_vlbytes_t %d %d) in\n" n low high;
      wl o "  LL.bounded_vlbytes'_payload_length %d %d %d input pos\n\n" low high repr;
      (* finalizer *)
      wl i "val %s_finalize (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) (len: U32.t) : HST.Stack U32.t\n\n" n;
      wl i "  (requires (fun h ->\n";
      wl i "    LL.live_slice h input /\\\n";
      wl i "    %d <= U32.v len /\\ U32.v len <= %d /\\\n" low high;
      wl i "    U32.v pos + %d + U32.v len <= U32.v input.LL.len /\\\n" repr;
      wl i "    LL.writable input.LL.base (U32.v pos) (U32.v pos + %d) h\n" repr;
      wl i "  ))\n";
      wl i "  (ensures (fun h pos' h' ->\n";
      wl i "    let pos_payload = pos `U32.add` %dul in\n" repr;
      wl i "    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\\\n";
      wl i "    LL.valid_content_pos %s_parser h' input pos (BY.hide (LL.bytes_of_slice_from_to h input pos_payload (pos_payload `U32.add` len))) pos' /\\\n" n;
      wl i "    U32.v pos' == U32.v pos_payload + U32.v len\n";
      wl i "  ))\n\n";
      wl o "let %s_finalize #_ #_ input pos len =\n" n;
      wl o "  [@inline_let] let _ = assert_norm (%s == LP.parse_bounded_vlbytes_t %d %d) in\n" n low high;
      wl o "  LL.finalize_bounded_vlbytes' %d %d %d input pos len\n\n" low high repr;
      ()

    (* Variable length list of fixed-length elements *)
    | VectorRange (low, high, _) when elem_li.min_len = elem_li.max_len ->
      w i "inline_for_extraction noextract let min_count = %d\ninline_for_extraction noextract let max_count = %d\n" li.min_count li.max_count;
      w i "type %s = l:list %s{%d <= L.length l /\\ L.length l <= %d}\n\n" n (compile_type ty) li.min_count li.max_count;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "private let pre : squash (LP.vldata_vlarray_precond %d %d %s %d %d == true) = _ by (FStar.Tactics.trefl ())\n\n" low high (pcombinator_name ty) li.min_count li.max_count;
      w o "let %s_parser =\n" n;
      w o "  LP.parse_vlarray %d %d %s %d %d ()\n\n" low high (scombinator_name ty) li.min_count li.max_count;
      w o "let %s_serializer =\n" n;
      w o "  LP.serialize_vlarray %d %d %s %d %d ()\n\n" low high (scombinator_name ty) li.min_count li.max_count;
      write_bytesize o is_private n;
      wh o "let %s_parser32 =\n" n;
      wh o "  LP.parse32_vlarray %d %dul %d %dul %s %s %d %d ()\n\n" low low high high (scombinator_name ty) (pcombinator32_name ty) li.min_count li.max_count;
      wh o "let %s_serializer32 =\n" n;
      wh o "  LP.serialize32_vlarray %d %d #_ #_ #_ #%s %s %d %d ()\n\n" low high (scombinator_name ty) (scombinator32_name ty) li.min_count li.max_count;
      wh o "let %s_size32 =\n" n;
      wh o "  [@inline_let] let _ = assert_norm (LP.vldata_vlarray_precond %d %d %s %d %d == true) in\n" low high (pcombinator_name ty) li.min_count li.max_count;
      wh o "  LP.size32_vlarray %d %d %s %d %d () %dul %dul\n\n" low high (scombinator_name ty) li.min_count li.max_count li.len_len elem_li.min_len;
      if need_validator then begin
        wl o "let %s_validator =\n" n;
        wl o " LL.validate_vlarray %d %d %s %s %d %d () %dul\n\n" low high (scombinator_name ty) (validator_name ty) li.min_count li.max_count li.len_len
      end;
      if need_jumper then begin
        let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
        wl o "let %s_jumper%s =\n" n jumper_annot;
        wl o " LL.jump_vlarray %d %d %s %d %d () %dul\n\n" low high (scombinator_name ty) li.min_count li.max_count li.len_len
      end;
      (* finalizer *)
      wl i "inline_for_extraction val finalize_%s (#rrel: _) (#rel: _) (sl: LL.slice rrel rel) (pos pos' : U32.t) : HST.Stack unit\n" n;
      wl i "(requires (fun h ->\n";
      wl i "  U32.v pos + %d < 4294967296 /\\\n" li.len_len;
      wl i "  LL.writable sl.LL.base (U32.v pos) (U32.v pos + %d) h /\\\n" li.len_len;
      wl i "  LL.valid_list %s h sl (pos `U32.add` %dul) pos' /\\ (\n" (pcombinator_name ty) li.len_len;
      wl i "  let count = L.length (LL.contents_list %s h sl (pos `U32.add` %dul) pos') in\n" (pcombinator_name ty) li.len_len;
      wl i "  let len = U32.v pos' - (U32.v pos + %d) in\n" li.len_len;
      wl i "  ((%d <= len /\\ len <= %d) \\/ (%d <= count /\\ count <= %d))\n" low high li.min_count li.max_count;
      wl i ")))\n";
      wl i "(ensures (fun h _ h' ->\n";
      wl i "  B.modifies (LL.loc_slice_from_to sl pos (pos `U32.add` %dul)) h h' /\\ (\n" li.len_len;
      wl i "  let l = LL.contents_list %s h sl (pos `U32.add` %dul) pos' in\n" (pcombinator_name ty) li.len_len;
      wl i "  %d <= L.length l /\\ L.length l <= %d /\\\n" li.min_count li.max_count;
      wl i "  LL.valid_content_pos %s_parser h' sl pos l pos'\n" n;
      wl i ")))\n\n";
      wl o "let _ : squash (%s == LL.vlarray %s %d %d) = _ by (FStar.Tactics.trefl ())\n\n" n (compile_type ty) li.min_count li.max_count;
      wl o "let finalize_%s #_ #_ sl pos pos' =\n" n;
      wl o "  LL.finalize_vlarray %d %d %s %d %d sl pos pos'\n\n" low high (scombinator_name ty) li.min_count li.max_count;
      (* length (elem count) and elim *)
      wl i "val %s_count (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : HST.Stack U32.t\n" n;
      wl i "  (requires (fun h -> LL.valid %s_parser h input pos))\n" n;
      wl i "  (ensures (fun h res h' ->\n";
      wl i "    let x = LL.contents %s_parser h input pos in\n" n;
      wl i "    let pos' = LL.get_valid_pos %s_parser h input pos in\n" n;
      wl i "    B.modifies B.loc_none h h' /\\\n";
      wl i "    U32.v res == L.length x /\\\n";
      wl i "    U32.v pos' == U32.v pos + %d + (U32.v res `FStar.Mul.op_Star` %d) /\\\n" li.len_len elem_li.min_len;
      wl i "    LL.valid_list %s h input (pos `U32.add` %dul) pos' /\\\n" (pcombinator_name ty) li.len_len;
      wl i "    LL.contents_list %s h input (pos `U32.add` %dul) pos' == x\n" (pcombinator_name ty) li.len_len;
      wl i "  ))\n";
      wl o "let %s_count #_ #_ input pos = LL.vlarray_list_length %d %d %s %d %d input pos\n\n" n low high (scombinator_name ty) li.min_count li.max_count;
      (* nth *)
      wl i "noextract let %s_clens_nth (i: nat) : Tot (LL.clens %s %s) = {\n" n n (compile_type ty);
      wl i "  LL.clens_cond = (fun (l: %s) -> i < L.length l);\n" n;
      wl i "  LL.clens_get = (fun (l: %s) -> L.index l i);\n" n;
      wl i "}\n\n";
      wl i "val %s_nth_ghost (i: nat) : Tot (LL.gaccessor %s_parser %s (%s_clens_nth i))\n\n" n n (pcombinator_name ty) n;
      wl o "let %s_nth_ghost i = LL.vlarray_nth_ghost %d %d %s %d %d i\n\n" n low high (scombinator_name ty) li.min_count li.max_count;
      wl i "val %s_nth (i: U32.t) : Tot (LL.accessor (%s_nth_ghost (U32.v i)))\n\n" n n;
      wl o "let %s_nth i = LL.vlarray_nth %d %d %s %d %d i\n\n" n low high (scombinator_name ty) li.min_count li.max_count;
      (* lemmas about bytesize *)
      w i "val %s_bytesize_eqn (x: %s) : Lemma (%s_bytesize x == %d + (L.length x `FStar.Mul.op_Star` %d)) [SMTPat (%s_bytesize x)]\n\n" n n n li.len_len elem_li.min_len n;
      w o "let %s_bytesize_eqn x = LP.length_serialize_vlarray %d %d %s %d %d () x\n\n" n low high (scombinator_name ty) li.min_count li.max_count;
      ()

    (* Variable length list of variable length elements *)
    | VectorRange(low, high, _) ->
      let (min, max) = (li.min_len-li.len_len), (li.max_len-li.len_len) in
      w i "noextract val %s_list_bytesize: list %s -> GTot nat\n\n" n (compile_type ty);
      w o "let %s_list_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s) x)\n\n" n (scombinator_name ty);
      w i "type %s = l:list %s{let x = %s_list_bytesize l in %d <= x /\\ x <= %d}\n\n" n (compile_type ty) n min max;
      w i "val %s_list_bytesize_nil : squash (%s_list_bytesize [] == 0)\n\n" n n;
      w o "let %s_list_bytesize_nil = LP.serialize_list_nil %s %s\n\n" n (pcombinator_name ty) (scombinator_name ty);
      w i "val %s_list_bytesize_cons (x: %s) (y: list %s) : Lemma (%s_list_bytesize (x :: y) == %s + %s_list_bytesize y) [SMTPat (%s_list_bytesize (x :: y))]\n\n" n (compile_type ty) (compile_type ty) n (bytesize_call ty "x") n n;
      w o "let %s_list_bytesize_cons x y = LP.serialize_list_cons %s %s x y; %s\n\n" n (pcombinator_name ty) (scombinator_name ty) (bytesize_eq_call ty "x");
      w i "val %s_list_bytesize_eq (l: list %s) : Lemma (%s_list_bytesize l == LL.serialized_list_length %s l)\n\n" n (compile_type ty) n (scombinator_name ty);
      w o "let %s_list_bytesize_eq l = LL.serialized_list_length_eq_length_serialize_list %s l\n\n" n (scombinator_name ty);
      w i "val check_%s_list_bytesize (l: list %s) : Tot (b: bool {b == (let x = %s_list_bytesize l in %d <= x && x <= %d)})\n\n" n (compile_type ty) n min max;
      w o "let check_%s_list_bytesize l =\n" n;
      w o "  let x = LP.size32_list %s () l in\n" (size32_name ty);
      w o "  %dul `U32.lte` x && x `U32.lte` %dul\n\n" min max;
      write_api o i is_private li.meta n li.min_len li.max_len;
      w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d (LP.serialize_list _ %s)\n\n" n min max (scombinator_name ty);
      w o "inline_for_extraction let synth_%s (x: %s') : Tot %s = x\n\n" n n n;
      w o "inline_for_extraction let synth_%s_recip (x: %s) : Tot %s' = x\n\n" n n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_bounded_vldata_strong %d %d (LP.serialize_list _ %s)\n\n" min max (scombinator_name ty);
      w o "let %s_parser = %s'_parser `LP.parse_synth` synth_%s \n\n" n n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_bounded_vldata_strong %d %d (LP.serialize_list _ %s)\n\n" min max (scombinator_name ty);
      w o "let %s_serializer = LP.serialize_synth _ synth_%s %s'_serializer synth_%s_recip ()\n\n" n n n n;
      write_bytesize o is_private n;
      wh o "inline_for_extraction noextract let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      wh o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul (LP.serialize_list _ %s) (LP.parse32_list %s)\n\n" min min max max (scombinator_name ty) (pcombinator32_name ty);
      wh o "let %s_parser32 = LP.parse32_synth' _ synth_%s %s'_parser32 ()\n\n" n n n;
      wh o "inline_for_extraction noextract let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      wh o "  LP.serialize32_bounded_vldata_strong %d %d (LP.partial_serialize32_list _ %s %s ())\n\n" min max (scombinator_name ty) (scombinator32_name ty);
      wh o "let %s_serializer32 = LP.serialize32_synth' _ synth_%s _ %s'_serializer32 synth_%s_recip ()\n\n" n n n n;
      wh o "inline_for_extraction noextract let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      wh o "  LP.size32_bounded_vldata_strong %d %d (LP.size32_list %s ()) %dul\n\n" min max (size32_name ty) li.len_len;
      wh o "let %s_size32 = LP.size32_synth' _ synth_%s _ %s'_size32 synth_%s_recip ()\n\n" n n n n;
      if need_validator then begin
        wl o "inline_for_extraction let %s'_validator : LL.validator %s'_parser =\n" n n;
        wl o "  LL.validate_bounded_vldata_strong %d %d (LP.serialize_list _ %s) (LL.validate_list %s ()) ()\n\n" min max (scombinator_name ty) (validator_name ty);
        wl o "let %s_validator = LL.validate_synth %s'_validator synth_%s ()\n\n" n n n
      end;
      if need_jumper then begin
        wl o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser =\n" n n;
        wl o "  LL.jump_bounded_vldata_strong %d %d (LP.serialize_list _ %s) ()\n\n" min max (scombinator_name ty);
        let jumper_annot = if is_private then sprintf " : LL.jumper %s_parser" n else "" in
        wl o "let %s_jumper%s = LL.jump_synth %s'_jumper synth_%s ()\n\n" n jumper_annot n n
      end;
      (* finalizer *)
      wl i "val finalize_%s (#rrel: _) (#rel: _) (sl: LL.slice rrel rel) (pos pos' : U32.t) : HST.Stack unit\n" n;
      wl i "(requires (fun h ->\n";
      wl i "  U32.v pos + %d < 4294967296 /\\\n" li.len_len;
      wl i "  LL.writable sl.LL.base (U32.v pos) (U32.v pos + %d) h /\\\n" li.len_len;
      wl i "  LL.valid_list %s h sl (pos `U32.add` %dul) pos' /\\ (\n" (pcombinator_name ty) li.len_len;
      wl i "  let len = U32.v pos' - (U32.v pos + %d) in\n" li.len_len;
      wl i "  let len_ser = %s_list_bytesize (LL.contents_list %s h sl (pos `U32.add` %dul) pos') in\n" n (pcombinator_name ty) li.len_len;
      wl i "  ((%d <= len /\\ len <= %d) \\/ (%d <= len_ser /\\ len_ser <= %d))\n" low high low high;
      wl i ")))\n";
      wl i "(ensures (fun h _ h' ->\n";
      wl i "  B.modifies (LL.loc_slice_from_to sl pos (pos `U32.add` %dul)) h h' /\\ (\n" li.len_len;
      wl i "  let l = LL.contents_list %s h sl (pos `U32.add` %dul) pos' in\n" (pcombinator_name ty) li.len_len;
      wl i "  %s_list_bytesize l == U32.v pos' - (U32.v pos + %d) /\\\n" n li.len_len;
      wl i "  LL.valid_content_pos %s_parser h' sl pos l pos'\n" n;
      wl i ")))\n\n";
      wl o "let finalize_%s #_ #_ sl pos pos' =\n" n;
      wl o "  LL.finalize_bounded_vldata_strong_list %d %d %s sl pos pos';\n" low high (scombinator_name ty);
      wl o "  let h = HST.get () in\n";
      wl o "  LL.valid_synth h %s'_parser synth_%s sl pos\n\n" n n;
      (* elim *)
      wl i "val %s_elim (h: HS.mem) (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : Lemma\n" n;
      wl i "  (requires (LL.valid %s_parser h input pos))\n" n;
      wl i "  (ensures (\n";
      wl i "    let pos' = LL.get_valid_pos %s_parser h input pos in\n" n;
      wl i "    U32.v pos + %d <= U32.v pos' /\\ (\n" li.len_len;
      wl i "    let pos1 = pos `U32.add` %dul in\n" li.len_len;
      wl i "    LL.valid_list %s h input pos1 pos' /\\\n" (pcombinator_name ty);
      wl i "    LL.contents_list %s h input pos1 pos' == LL.contents %s_parser h input pos\n" (pcombinator_name ty) n;
      wl i "  )))\n\n";
      wl o "let %s_elim h #_ #_ input pos =\n" n;
      wl o "  LL.valid_synth h %s'_parser synth_%s input pos;\n" n n;
      wl o "  LL.valid_bounded_vldata_strong_list_valid_list %d %d %s %s input pos h\n\n" low high (pcombinator_name ty) (scombinator_name ty);
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
    | TypeSimple ty, VectorNone -> (fn0, ty)
    | _ ->
      let n' = sprintf "%s_%s" n fn in
      let p = Typedef (al, ty, fn, vec, def) in
      let (o', i') = open_files n' in
      compile o' i' n p;
      w i "(* Type of field %s*)\ninclude %s\n\n" fn (module_name n');
      w o "(* Type of field %s*)\nopen %s\n\n" fn (module_name n');
      (* compile_typedef o i n fn ty vec def ("private"::al); *)
      (fn0, n')) fl in

  (* we assume that the 0 and 1 cases have already normalized by `compile` *)
  assert (List.length fields >= 2);
  
  (* application type *)
    w i "type %s = {\n" n;
    List.iter (fun (fn, ty) ->
      w i "  %s : %s;\n" fn (compile_type ty)) fields;
    w i "}\n\n";

  (* Tuple type for nondep_then combination *)
  let tfields = List.fold_left btree_insert (TLeaf (List.hd fields)) (List.tl fields) in
  let tuple =
    btree_fold
      (fun s _ (_, ty) -> sprintf "%s%s" s (compile_type ty))
      (fun s -> sprintf "%s(" s)
      (fun s -> sprintf "%s & " s)
      (fun s -> sprintf "%s)" s)
      (fun _ -> ())
      (fun _ -> ())
      ""
      ()
      tfields
  in
  w o "type %s' = %s\n\n" n tuple;

  (* synthethizer for tuple type *)
  let synth_arg =
    btree_fold
      (fun s _ (fn, _) -> sprintf "%s%s" s fn)
      (fun s -> sprintf "%s(" s)
      (fun s -> sprintf "%s," s)
      (fun s -> sprintf "%s)" s)
      (fun _ -> ())
      (fun _ -> ())
      ""
      ()
      tfields
  in
  let synth_body = List.fold_left (fun acc (fn, ty) -> sprintf "%s    %s = %s;\n" acc fn fn) "" fields in
  w o "inline_for_extraction let synth_%s (x: %s') : %s =\n" n n n;
  w o "  match x with %s -> {\n" synth_arg;
  w o "%s" synth_body;
  w o "  }\n\n";
  
  let synth_recip_body =
    btree_fold
      (fun s _ (fn, _) -> sprintf "%sx.%s" s fn)
      (fun s -> sprintf "%s(" s)
      (fun s -> sprintf "%s," s)
      (fun s -> sprintf "%s)" s)
      (fun _ -> ())
      (fun _ -> ())
      ""
      ()
      tfields
  in
  w o "inline_for_extraction let synth_%s_recip (x: %s) : %s' = %s\n\n" n n n synth_recip_body;

  (* Write parser API *)
  write_api o i is_private li.meta n li.min_len li.max_len;

  (* synthetizer injectivity and inversion lemmas *)
  w o "let synth_%s_recip_inverse () : Lemma (LP.synth_inverse synth_%s_recip synth_%s) = ()\n\n" n n n;
  w o "let synth_%s_injective () : Lemma (LP.synth_injective synth_%s) =\n" n n;
  w o "  LP.synth_inverse_synth_injective synth_%s_recip synth_%s;\n" n n;
  w o "  synth_%s_recip_inverse ()\n\n" n;
  w o "let synth_%s_inverse () : Lemma (LP.synth_inverse synth_%s synth_%s_recip) =\n" n n n;
  w o "  assert_norm (LP.synth_inverse synth_%s synth_%s_recip)\n\n" n n;
  w o "let synth_%s_recip_injective () : Lemma (LP.synth_injective synth_%s_recip) =\n" n n;
  w o "  synth_%s_recip_inverse ();\n" n;
  w o "  LP.synth_inverse_synth_injective synth_%s synth_%s_recip\n\n" n n;

  (* main parser combinator type *)
  let combinator ret bind =
    btree_fold
      (fun s _ (_, ty) -> sprintf "%s%s" s (ret ty))
      (fun s -> sprintf "%s(" s)
      (fun s -> sprintf "%s `%s` " s bind)
      (fun s -> sprintf "%s)" s)
      (fun _ -> ())
      (fun _ -> ())
      ""
      ()
      tfields
  in
  let parser = combinator pcombinator_name "LP.nondep_then" in
  w o "noextract let %s'_parser : LP.parser _ %s' = %s\n\n" n n parser;

  w o "noextract let %s'_parser_kind = LP.get_parser_kind %s'_parser\n\n" n n;
  w o "let %s_parser =\n  synth_%s_injective ();\n  assert_norm (%s_parser_kind == %s'_parser_kind);\n" n n n n;
  w o "  %s'_parser `LP.parse_synth` synth_%s\n\n" n n;

  (* main serializer type *)
  let serializer = combinator scombinator_name "LP.serialize_nondep_then" in
  w o "noextract let %s'_serializer : LP.serializer %s'_parser = %s\n\n" n n serializer;
  w o "let %s_serializer =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize_synth _ synth_%s %s'_serializer synth_%s_recip ()\n\n" n n n;
  write_bytesize o is_private n;

  (* main parser32 *)
  let parser32 = combinator pcombinator32_name "LP.parse32_nondep_then" in
  wh o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser = %s\n\n" n n parser32;
  wh o "let %s_parser32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  wh o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  wh o "  LP.parse32_synth _ synth_%s (fun x -> synth_%s x) %s'_parser32 ()\n\n" n n n;

  (* serialize32 *)
  let serializer32 = combinator scombinator32_name "LP.serialize32_nondep_then" in
  wh o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer = %s\n\n" n n serializer32;
  wh o "let %s_serializer32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  wh o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  wh o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  wh o "  LP.serialize32_synth _ synth_%s _ %s'_serializer32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;

  let size32 = combinator size32_name "LP.size32_nondep_then" in
  wh o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer = %s\n\n" n n size32;
  wh o "let %s_size32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  wh o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  wh o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  wh o "  LP.size32_synth _ synth_%s _ %s'_size32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;

  (* validator *)
  if need_validator li.meta li.min_len li.max_len then
   begin
    let validator = combinator validator_name "LL.validate_nondep_then" in
    wl o "inline_for_extraction let %s'_validator : LL.validator %s'_parser = %s\n\n" n n validator;
    wl o "let %s_validator =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
    wl o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
    wl o "  LL.validate_synth %s'_validator synth_%s ()\n\n" n n
   end;

  (* jumper *)
  if need_jumper li.min_len li.max_len then
   begin
    let jumper = combinator jumper_name "LL.jump_nondep_then" in
    wl o "inline_for_extraction let %s'_jumper : LL.jumper %s'_parser = %s\n\n" n n jumper;
    wl o "let %s_jumper =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
    wl o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
    wl o "  LL.jump_synth %s'_jumper synth_%s ()\n\n" n n
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
  let rec bytesize accu = function
  | TLeaf (fn, ty) ->
       (accu, scombinator_name ty, sprintf "x.%s" fn)
  | TNode (_, left, right) ->
     let (accu1, sleft, argleft) = bytesize accu left in
     let (accu2, sright, argright) = bytesize accu1 right in
     let accu = sprintf "%s;\nLP.length_serialize_nondep_then %s %s %s %s" accu2 sleft sright argleft argright in
     let s = sprintf "(%s `LP.serialize_nondep_then` %s)" sleft sright in
     let arg = sprintf "(%s, %s)" argleft argright in
     (accu, s, arg)
  in
  let (body, _, _) = bytesize "" tfields in
  w o "let %s_bytesize_eqn x =\n" n;
  w o "  [@inline_let] let _ = synth_%s_injective () in\n" n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize_synth_eq _ synth_%s %s'_serializer synth_%s_recip () x%s" n n n body;
     List.iter
       (fun (fn, ty) ->
         let bseq = bytesize_eq_call ty (sprintf "x.%s" fn) in
         if bseq <> "()" then w o ";\n  %s" bseq
       )
       fields
     ;
     let seq_sum = List.fold_left
       (fun acc (fn, ty) ->
         let s = scombinator_name ty in
         let cur = sprintf "Seq.length (LP.serialize %s x.%s)" s fn in
         if acc = "" then cur else sprintf "%s + %s" acc cur
       ) "" fields in
     w o ";\n  assert(%s_bytesize x == %s)\n\n" n seq_sum;

  (* accessors for fields *)
     let gacc =
       btree_fold
         (fun output path (fn, ty) -> sprintf "%slet gaccessor'_%s_%s : LL.gaccessor %s'_parser %s _ = %s\n\n" output n fn n (pcombinator_name ty) path)
         (fun x -> x)
         (fun x -> x)
         (fun x -> x)
         (fun path -> sprintf "(LL.gaccessor_then_fst %s)" path)
         (fun path -> sprintf "(LL.gaccessor_then_snd %s)" path)
         ""
         (sprintf "(LL.gaccessor_id %s'_parser)" n)
         tfields
     in
     wl o "%s" gacc;
     let rec accessors (output: string) (path: string) = function
       | TLeaf (fn, ty) ->
          let output' = sprintf "%sinline_for_extraction noextract let accessor'_%s_%s : LL.accessor gaccessor'_%s_%s = %s\n\n" output n fn n fn path in
          (output', jumper_name ty)
       | TNode (_, left, right) ->
          let (output1, jumper1) = accessors output (sprintf "(LL.accessor_then_fst %s)" path) left in
          let (output2, jumper2) = accessors output1 (sprintf "(LL.accessor_then_snd %s %s)" path jumper1) right in
          (output2, sprintf "(%s `LL.jump_nondep_then` %s)" jumper1 jumper2)
     in
     let (acc, _) = accessors "" (sprintf "(LL.accessor_id %s'_parser)" n) tfields in
     wl o "%s" acc;
     wl o "noextract let clens_%s_%s' : LL.clens %s %s' = synth_%s_recip_inverse (); synth_%s_recip_injective (); LL.clens_synth synth_%s_recip synth_%s ()\n\n" n n n n n n n n;
     wl o "let gaccessor_%s_%s' : LL.gaccessor %s_parser %s'_parser clens_%s_%s' = synth_%s_inverse (); synth_%s_injective (); synth_%s_recip_inverse (); LL.gaccessor_synth %s'_parser synth_%s synth_%s_recip ()\n\n" n n n n n n n n n n n n;
     wl o "inline_for_extraction noextract let accessor_%s_%s' : LL.accessor gaccessor_%s_%s' = synth_%s_inverse (); synth_%s_injective (); synth_%s_recip_inverse (); LL.accessor_synth %s'_parser synth_%s synth_%s_recip ()\n\n" n n n n n n n n n n;
    (* write the lenses *)
    List.iter
      (fun (fn, ty) ->
        wl i "noextract let clens_%s_%s : LL.clens %s %s = {\n" n fn n (compile_type ty);
        wl i "  LL.clens_cond = (fun _ -> True);\n";
        wl i "  LL.clens_get = (fun x -> x.%s);\n" fn;
        wl i "}\n\n";
      )
      fields;
    (* write the accessors *)
    List.iter
      (fun (fn, ty) ->
        wl i "val gaccessor_%s_%s : LL.gaccessor %s_parser %s clens_%s_%s\n\n" n fn n (pcombinator_name ty) n fn;
        wl o "let gaccessor_%s_%s = LL.gaccessor_ext (gaccessor_%s_%s' `LL.gaccessor_compose` gaccessor'_%s_%s) clens_%s_%s ()\n\n" n fn n n n fn n fn;
        wl i "val accessor_%s_%s : LL.accessor gaccessor_%s_%s\n\n" n fn n fn;
        wl o "let accessor_%s_%s = LL.accessor_ext (LL.accessor_compose accessor_%s_%s' accessor'_%s_%s ()) clens_%s_%s ()\n\n" n fn n n n fn n fn
      )
      fields;

  (* valid intro lemma *)
  let rec valid ((count, (precond_l, precond_r, postcond), body) as accu) = function
    | TLeaf (fn, ty) ->
       let p = pcombinator_name ty in
       let count' = count + 1 in
       let letpos' = sprintf "  let pos%d = LL.get_valid_pos %s h input pos%d in\n" count' p count in
       let precond_l' = sprintf "%s  LL.valid %s h input pos%d /\\ (\n%s" precond_l p count letpos' in
       let precond_r' = sprintf "%s)" precond_r in
       let postcond' = sprintf "%s  let %s = LL.contents %s h input pos%d in\n%s" postcond fn p count letpos' in
       ((count', (precond_l', precond_r', postcond'), body), p)
    | TNode (_, left, right) ->
       let (accu1, pleft) = valid accu left in
       let ((count', cond', body2), pright) = valid accu1 right in
       let body' = sprintf "%s  LL.valid_nondep_then_intro h %s %s input pos%d;\n" body2 pleft pright count in
       let p' = sprintf "(%s `LP.nondep_then` %s)" pleft pright in
       ((count', cond', body'), p')
  in
  let ((count, (precond_l, precond_r, postcond), body), _) = valid (0, ("", "", ""), "") tfields in
  wl i "val %s_valid (h:HS.mem) (#rrel: _) (#rel: _) (input:LL.slice rrel rel) (pos0:U32.t) : Lemma\n  (requires (\n" n;
  wl i "%s  True\n  %s))\n" precond_l precond_r;
  wl i "  (ensures (\n";
  wl i "%s" postcond;
  wl i "  LL.valid_content_pos %s_parser h input pos0 ({\n" n;
  List.iter
    (fun (fn, _) ->
      wl i "      %s = %s;\n" fn fn;
    )
    fields;
  wl i "    }) pos%d))\n\n" count;
  wl o "let %s_valid h #_ #_ input pos0 =\n%s%s" n postcond body;
  wl o "  assert_norm (%s' == LP.get_parser_type %s'_parser);\n" n n;
  wl o "  assert_norm (%s_parser_kind == %s'_parser_kind);\n" n n;
  wl o "  synth_%s_injective ();\n" n;
  wl o "  LL.valid_synth_intro h %s'_parser synth_%s input pos0\n\n" n n;
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
        | TypeIfeq (itag, cst, tt, tf) ->
          let et = sprintf "%s_%s_true" sn n in
          let ef = sprintf "%s_%s_false" sn n in
          let (o, i) = open_files et in
          let (o', i') = open_files ef in
          compile o i "" (Typedef (al', TypeSimple tt, et, VectorVldata tagt, None));
          compile o' i' "" (Typedef (al', TypeSimple tf, ef, VectorVldata tagt, None));
          (al @ al', TypeIfeq(itag, cst, et, ef), n, VectorNone, None)
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

(* Hoist {... tag t; select(t){} ...} when other fields are present,
  also rewrites { ... tag t[x]; (if t = v then ttrue else tfalse) y ... *)
and normalize_select sn (fl:struct_field_t list)
  (acc:struct_field_t list) (acc':tag_select_t list) (acc'':ite_t list)
  : struct_field_t list * tag_select_t list * ite_t list =
  match fl with
  | [] -> List.rev acc, List.rev acc', List.rev acc''
  | (al, TypeSimple("opaque"), tagn, VectorFixed d, None)
    :: (al', TypeIfeq(tagn', tagv, tt, tf), ifn, vec, def)
    :: r when tagn = tagn' ->
    let etyp = sprintf "%s_%s" sn ifn in
    let ite : ite_t = (al, al', sn, ifn, tagn, d, tagv, tt, tf) in
    let f' = (al', TypeSimple etyp, ifn, vec, def) in
    normalize_select sn r (f'::acc) acc' (ite::acc'')
  | (al, TypeSimple(tagt), tagn, VectorNone, None)
    :: (al', TypeSelect (tagn', cases, def), seln, VectorNone, None)
    :: r when tagn = tagn' ->
    let etyp = sprintf "%s_%s" sn seln in
    let sel' = (al, al', etyp, tagn, seln, tagt, cases, def) in
    let f' = (al, TypeSimple etyp, seln, VectorNone, None) in
    normalize_select sn r (f'::acc) (sel'::acc') acc''
  | (_, TypeSelect (_, _, _), seln, _, _) :: t ->
    failwith (sprintf "Field %s contains an invalid select in struct %s" seln sn)
  | h :: t -> normalize_select sn t (h::acc) acc' acc''

(* Global type Substitution, this is use for staging sums on implicit tags *)
and subst_of (x:typ) = try SM.find x !subst with _ -> x
and apply_subst_t (t:type_t) =
  match t with
  | TypeSimple(ty) -> TypeSimple(subst_of ty)
  | TypeIfeq(tag, v, t, f) -> TypeIfeq(tag, v, subst_of t, subst_of f)
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
  w i "module LPI = LowParse.Spec.AllIntegers\n";
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
  w o "module LPI = LowParse.Spec.AllIntegers\n";
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
      match normalize_select n fl [] [] [] with
      | [_, TypeSimple etyp', seln', VectorNone, None], [], [al, al', sn, ifn, tagn, d, tagv, tt, tf] ->
        compile_ite o i n sn ifn tagn d tagv tt tf al
      | [_, TypeSimple etyp', seln', VectorNone, None], [al, al', etyp, tagn, seln, tagt, cases, def], [] ->
        if etyp' <> etyp || seln' <> seln then failwith "Invalid rewrite of a select (QD bug)";
        compile_select o i n seln tagn tagt al cases def al'
      | fl, sell, itel ->
        List.iter (fun (al, al', etyp, tagn, seln, tagt, cases, def) ->
          let p = Struct([], [(al, TypeSimple(tagt), tagn, VectorNone, None);
            (al', TypeSelect (tagn, cases, def), seln, VectorNone, None)], etyp) in
          let (o', i') = open_files etyp in
          compile o' i' "" p;
          w i "(* Internal select() for %s *)\ninclude %s\n\n" etyp (module_name etyp);
          w o "(* Internal select() for %s *)\nopen %s\n\n" etyp (module_name etyp);
        ) sell;
        List.iter (fun (al, al', sn, ifn, tagn, d, tagv, tt, tf) ->
          let etyp = sprintf "%s_%s" sn ifn in
          let p = Struct([], [(al, TypeSimple("opaque"), tagn, VectorFixed d, None);
            (al', TypeIfeq(tagn, tagv, tt, tf), ifn, VectorNone, None)], etyp) in
          let (o', i') = open_files etyp in
          compile o' i' "" p;
          w i "include %s\n\n" (module_name etyp);
          w o "open %s\n\n" (module_name etyp);
        ) itel;
        match fl with
        | [] -> compile_typedef o i tn n (TypeSimple "Empty") VectorNone None al
        | [(al, ty, _, vec, def)] -> compile_typedef o i tn n ty vec def al
        | _ -> compile_struct o i n fl al
  in close_files o i with e -> close_files o i; raise e

let rfc_generate_fstar (p:Rfc_ast.prog) =
  let aux (p:gemstone_t) =
	  let n = tname true p in
    let (o, i) = open_files n in
		compile o i "" p
	in List.iter aux p
