open Rfc_ast
open Interm_ast

(* p is assumed to be sorted, see rfc_ast_sort.ml *)

let rec enum_fields (e: enum_field_t list) (accu: (string * int) list) : (string * int) list = match e with
  | [] -> List.rev accu
  | EnumFieldSimple keyvalue :: q -> rfc_to_interm_enum_fields q (keyvalue :: accu)
  | _ :: q -> enum_fields q accu

let rec enum_repr_type (e: enum_field_t list) : integer_type =
  | [EnumFieldAnonymous max] ->
     begin match max with
     | 255 -> U8
     | 65535 -> U16
     | 4294967295 -> U32
     | _ -> failwith "Unsupported anonymous type"
     end
  | _ :: q -> enum_repr_type q
  | [] -> failwith "Last enum member is not anonymous"
            
let has_attr (a:attr list) (s:attr) = List.mem s a

let enum (attrs: attr list) (fields: enum_field_t list) : Interm_ast.enum = {
    enum_repr_type = enum_repr_type fields;
    enum_known_cases = enum_fields fields [];
    enum_is_open = has_attr attrs "open";
  }

let field_type_name (typ: string) (fd: string) : string =
  sprintf "%s_%s" ty fd

let local_id (name: string) =
  { ident_id = None; ident_id = name; }

let type_name (ty: string) : string =
  String.uncapitalize ty

exception Invalid_integer_type

let integer_type (ty: string) : integer_type = match ty with
  | "uint8" -> U8
  | "uint16" -> U16
  | "uint32" -> U32
  | _ -> raise Invalid_integer_type

let atomic_type (prefix: string) (ty: string) : atomic_type = match ty with
  | "opaque" -> failwith "opaque should not appear at standalone position"
  | "Empty" -> AtomicEmpty
  | _ ->
     begin try
         AtomicInt (integer_type ty)
       with Invalid_integer_type ->
         AtomicAlias { ident_modul = Some (sprintf "%s%s" prefix ty); ident_id = type_name ty }
     end

let length_max = function
  | U8 -> 255
  | U16 -> 65535
  | U32 -> 4294967295

let rec struct_fields
  (typ: string)
  (fields: struct_field_t list)
  (accu: (string * Interm_ast.struct_field_type) list)
  (def_accu: (string * def) list)
: (string * Interm_ast.struct_field_type) list * (string * def) list =
  match fields with
  | [] -> List.rev accu, def_accu
  | (_, TypeSimple tagt, tagn, VectorNone, None) ::
      (_, ty, n, VectorSymbolic k, None) :: r
       when tagn = k ->
     let length_type = integer_type tagt in
     let field_type = field_type_name typ n in
     begin match ty with
     | TypeSimple "opaque" ->
     | TypeSimple ty ->
       let def_accu' = (field_type, DefSimple (SimpleSingletonWithLength (atomic_type ty, length_type))) :: def_accu in
       let accu' = (n, AtomicAlias (local_id field_type)) :: accu in
       struct_fields r accu' def_accu'
     | 
         
                                                                             (*           
let struc (attrs: attr list) (fields: struct_field_t list) : Interm_ast.struct_type =
  
      

let rec prog (src: Rfc_ast.prog) (accu: Interm_ast.prog) : Interm_ast.prog =
  match src with
  | [] -> List.rev accu
  | Enum (attr, members, name) ->
    
