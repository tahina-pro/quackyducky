type integer_type =
  | U8
  | U16
  | U32

type ident = {
    ident_modul: string option;
    ident_id: string;
}

type enum_type = {
    enum_repr_type: integer_type;
    enum_known_keys: (string * int) list;
    enum_unknown_key: string option;
    enum_known_cases: int list;
}

type enum = {
    enum_key_type: ident;
    enum_known_cases: ident list;
    enum_is_open: bool;
  }

type atomic_type =
  | AtomicInt of integer_type
  | AtomicEmpty
  | AtomicAlias of ident

type simple_type =
  | SimpleAtomic of atomic_type
  | SimpleFLBytes of int
  | SimpleVLBytes of (int * int)
  | SimpleSingletonWithLength of (atomic_type * integer_type)
  | SimpleVectorFixed of (atomic_type * int)
  | SimpleVectorRange of (atomic_type * int * int)
                       
type select = {
    select_tag_field_name: string;
    select_tag_enum_type: ident;
    select_tag_is_implicit: bool;
    select_payload_field_name: string;
    select_payload_cases: (ident * atomic_type) list;
    select_payload_default_case: atomic_type option;
  }

type struct_field_type =
  | StructSelect of string
  | StructSimple of atomic_type

type struct_type = (string * struct_field_type) list

type def_type =
  | DefSimple   of simple_type
  | DefStruct   of struct_type
  | DefEnumType of enum_type
  | DefEnum     of enum

type modul = def_type list

type prog = (string * modul) list
