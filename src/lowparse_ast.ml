open Interm_ast

type vldata_payload_type =
  | VldataAtomic of atomic_type
  | VldataList of atomic_type

type vldata_payload = {
    vldata_payload_type: vldata_payload_type;
    vldata_payload_min: int;
    vldata_payload_max: int;
    vldata_payload_fits: bool;
}

type simple_type =
  | SimpleAtomic of atomic_type
  | SimpleFLData of atomic_type
  | SimpleVLData of vldata_payload
  | SimpleFLArray of atomic_type * int
  | SimpleVLArray of atomic_type * int * int

type enum_type = {
    enum_type_repr_type: integer_type;
    enum_known_cases: (string * int) list;
    enum_unknown_key: string option;
}

type enum = {
    enum_key_type: ident;
    enum_repr_type: ident;
    enum_known_cases: (ident * int) list;
    enum_is_open: bool;
  }

type def_type =
  | DefSimple   of simple_type
  | DefStruct   of struct_type
  | DefEnum     of enum
  | DefEnumType of enum_type

type def = {
    sized_def_type: sized_def_type;
    sized_def_min: int;
    sized_def_max: int;
}

type def =
  | SizedDef of sized_def

type modul = def list

type prog = (string * modul) list
