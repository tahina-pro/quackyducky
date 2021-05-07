module Employee_name

(* This file has been automatically generated by EverParse. *)
open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LP = LowParse.Spec.Base
module LS = LowParse.SLow.Base
module LPI = LowParse.Spec.AllIntegers
module LL = LowParse.Low.Base
module L = FStar.List.Tot
module B = LowStar.Buffer
module BY = FStar.Bytes
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module LWP = LowParse.Writers.Combinators


inline_for_extraction noextract let min_len = 1
inline_for_extraction noextract let max_len = 255
type employee_name = b:bytes{1 <= length b /\ length b <= 255}

inline_for_extraction noextract let employee_name_parser_kind = LP.strong_parser_kind 2 256 None

noextract val employee_name_parser: LP.parser employee_name_parser_kind employee_name

noextract val employee_name_serializer: LP.serializer employee_name_parser

noextract val employee_name_bytesize (x:employee_name) : GTot nat

noextract val employee_name_bytesize_eq (x:employee_name) : Lemma (employee_name_bytesize x == Seq.length (LP.serialize employee_name_serializer x))

val employee_name_parser32: LS.parser32 employee_name_parser

val employee_name_serializer32: LS.serializer32 employee_name_serializer

val employee_name_size32: LS.size32 employee_name_serializer

val employee_name_validator: LL.validator employee_name_parser

val employee_name_jumper: LL.jumper employee_name_parser

inline_for_extraction noextract let lwp_employee_name = LWP.make_parser employee_name_parser employee_name_serializer employee_name_jumper
val employee_name_bytesize_eqn (x: employee_name) : Lemma (employee_name_bytesize x == 1 + BY.length x) [SMTPat (employee_name_bytesize x)]

val employee_name_length (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) : HST.Stack U32.t
  (requires (fun h -> LL.valid employee_name_parser h input pos))
  (ensures (fun h res h' ->
    let x = LL.contents employee_name_parser h input pos in
    B.modifies B.loc_none h h' /\
    U32.v pos + 1 + U32.v res == U32.v (LL.get_valid_pos employee_name_parser h input pos) /\
    res == BY.len x /\
    LL.bytes_of_slice_from_to h input (pos `U32.add` 1ul) ((pos `U32.add` 1ul) `U32.add` res) == BY.reveal x
  ))

val employee_name_finalize (#rrel: _) (#rel: _) (input: LL.slice rrel rel) (pos: U32.t) (len: U32.t) : HST.Stack U32.t

  (requires (fun h ->
    LL.live_slice h input /\
    1 <= U32.v len /\ U32.v len <= 255 /\
    U32.v pos + 1 + U32.v len <= U32.v input.LL.len /\
    LL.writable input.LL.base (U32.v pos) (U32.v pos + 1) h
  ))
  (ensures (fun h pos' h' ->
    let pos_payload = pos `U32.add` 1ul in
    B.modifies (LL.loc_slice_from_to input pos pos_payload) h h' /\
    LL.valid_content_pos employee_name_parser h' input pos (BY.hide (LL.bytes_of_slice_from_to h input pos_payload (pos_payload `U32.add` len))) pos' /\
    U32.v pos' == U32.v pos_payload + U32.v len
  ))

