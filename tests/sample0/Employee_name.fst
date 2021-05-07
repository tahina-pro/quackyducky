module Employee_name

(* This file has been automatically generated by EverParse. *)
open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LP = LowParse.Spec
module LS = LowParse.SLow
module LPI = LowParse.Spec.AllIntegers
module LL = LowParse.Low
module L = FStar.List.Tot
module B = LowStar.Buffer
module BY = FStar.Bytes
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module LWP = LowParse.Writers.Instances

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

noextract let employee_name_parser = LP.parse_bounded_vlbytes 1 255

noextract let employee_name_serializer = LP.serialize_bounded_vlbytes 1 255

let employee_name_bytesize (x:employee_name) : GTot nat = Seq.length (employee_name_serializer x)

let employee_name_bytesize_eq x = ()

let employee_name_parser32 = LS.parse32_bounded_vlbytes 1 1ul 255 255ul

let employee_name_serializer32 = LS.serialize32_bounded_vlbytes 1 255

let employee_name_size32 = LS.size32_bounded_vlbytes 1 255

let employee_name_validator = LL.validate_bounded_vlbytes 1 255

let employee_name_jumper = LL.jump_bounded_vlbytes 1 255

let employee_name_bytesize_eqn x = LP.length_serialize_bounded_vlbytes 1 255 x

let employee_name_length #_ #_ input pos =
  [@inline_let] let _ = assert_norm (employee_name == LP.parse_bounded_vlbytes_t 1 255) in
  LL.bounded_vlbytes_payload_length 1 255 input pos

let employee_name_finalize #_ #_ input pos len =
  [@inline_let] let _ = assert_norm (employee_name == LP.parse_bounded_vlbytes_t 1 255) in
  LL.finalize_bounded_vlbytes 1 255 input pos len

