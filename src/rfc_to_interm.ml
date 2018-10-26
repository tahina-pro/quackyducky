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

let enum (attrs: attr list) (fields: enum_field_t list) (name: typ) : Interm_ast.enum = {
    enum_key_type = name;
    enum_repr_type = enum_repr_type fields;
    enum_known_cases = enum_fields fields [];
    enum_is_open = has_attr attrs "open";
  }

let rec struct_fields (fields: struct_field_t list) (accu: (string * Interm_ast.struct_field_type) list) : (string * Interm_ast.struct_field_type) list =
  match fields with
  | [] -> List.rev accu
  | (_, TypeSimple tagt, tagn, VectorNone, None) ::
      (_, ty, n, VectorSymbolic 
                                                                                        
let struc (attrs: attr list) (fields: struct_field_t list) : Interm_ast.struct_type =
  
      

      (*
let rec prog (src: Rfc_ast.prog) (accu: Interm_ast.prog) : Interm_ast.prog =
  match src with
  | [] -> List.rev accu
  | Enum (attr, members, name) ->
    
