type integer_type =
  | U8
  | U16
  | U32

type enum = {
    enum_key_type: string;
    enum_repr_type: integer_type;
    enum_known_cases: (string * int) list;
    enum_is_open: bool;
  }

type atomic_type =
  | AtomicInt of integer_type
  | AtomicEmpty
  | AtomicAlias of string

type simple_type =
  | SimpleAtomic of atomic_type
  | SimpleSingletonWithLength of (atomic_type * integer_type)
  | SimpleVectorFixed of (atomic_type * int)
  | SimpleVectorRange of (atomic_type * int * int)
                       
type select = {
    select_tag_field_name: string;
    select_tag_enum_type: string;
    select_tag_is_implicit: bool;
    select_payload_field_name: string;
    select_payload_length_field_type: option integer_type;
    select_payload_cases: (string * string) list;
    select_payload_default_case: string option;
  }

type struct_field_type =
  | StructSelect of select
  | StructSimple of simple_type

type struct_type = (string * struct_field_type) list

type def_type =
  | DefSimple   of simple_type
  | DefStruct   of struct_type
  | DefEnum     of enum

type prog = def_type list
