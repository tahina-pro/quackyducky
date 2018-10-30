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

type def_type =
  | DefSimple   of simple_type
  | DefStruct   of struct_type
  | DefEnum     of enum

type parser_kind = {
    parser_kind_min: int;
    parser_kind_max: int;
    parser_kind_metadata_total: bool;
  }
                 
type def = {
    def_type: def_type;
    def_parser_kind: parser_kind;
  }

type modul = (string * def) list

type prog = (string * modul) list


type ctxt = {
    ctxt_curmod: modul;
    ctxt_prog: prog;
  }
