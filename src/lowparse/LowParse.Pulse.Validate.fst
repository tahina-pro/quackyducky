module LowParse.Pulse.Validate
include LowParse.Pulse.Parse
module AP = LowParse.Pulse.ArrayPtr
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module U32 = FStar.UInt32

let validator_prop
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: AP.v byte)
  (v_err: U32.t)
  (res: SZ.t)
: Tot prop
= 
  SZ.v res <= AP.length (AP.array_of b) /\
  begin match parse p (AP.contents_of b), (U32.v v_err = 0) with
  | None, false -> True
  | Some (_, consumed), true ->
    SZ.v res == consumed
  | _ -> False
  end

let validate_pre
  (b: AP.v byte)
  (a: AP.t byte)
  (len: SZ.t)
  (err: ref U32.t)
: Tot vprop
= AP.arrayptr a b ** pts_to err 0ul ** pure (
    SZ.v len == AP.length (AP.array_of b)
  )

let validate_post
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: AP.v byte)
  (a: AP.t byte)
  (len: SZ.t)
  (err: ref U32.t)
  (res: SZ.t)
: Tot vprop
= AP.arrayptr a b ** exists_ (fun v_err ->
    pts_to err v_err ** pure (
    validator_prop p b v_err res
  ))


inline_for_extraction
let validator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= 
  (b: AP.v byte) ->
  (a: AP.t byte) ->
  (len: SZ.t) ->
  (err: ref U32.t) ->
  stt SZ.t
    (validate_pre b a len err)
    (fun res -> validate_post p b a len err res)

inline_for_extraction
let validate
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (a: AP.t byte)
  (len: SZ.t)
  (err: ref U32.t)
  (#b: AP.v byte)
: stt SZ.t
    (AP.arrayptr a b ** pts_to err 0ul ** pure (
    SZ.v len == AP.length (AP.array_of b)
  ))
    (fun res -> AP.arrayptr a b ** exists_ (fun v_err ->
        pts_to err v_err ** pure (
            validator_prop p b v_err res
        )
    ))
= v b a len err

[@CMacro]
let validator_error_not_enough_data : U32.t = 1ul

inline_for_extraction
```pulse
fn validate_total_constant_size0
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: (sz: SZ.t {
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.v sz /\
      k.parser_kind_metadata == Some ParserKindMetadataTotal
  }))
  (b: AP.v byte)
  (a: AP.t byte)
  (len: SZ.t)
  (err: ref U32.t)
  requires validate_pre b a len err
  returns res: SZ.t
  ensures validate_post p b a len err res
{
  let _lemma_call_1 = parser_kind_prop_equiv k p;
  unfold (validate_pre b a len err);
  if (SZ.lte sz len) {
    fold (validate_post p b a len err sz);
    sz
  } else {
    err := validator_error_not_enough_data;
    fold (validate_post p b a len err 0sz);
    0sz
  }
}
```

inline_for_extraction
let validate_total_constant_size
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: (sz: SZ.t {
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.v sz /\
      k.parser_kind_metadata == Some ParserKindMetadataTotal
  }))
: Tot (validator p)
= validate_total_constant_size0 p sz

inline_for_extraction
let ifthenelse_validate
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (cond: bool)
  (vtrue: (squash (cond == true) -> Tot (validator p)))
  (vfalse: (squash (cond == false) -> Tot (validator p)))
: Tot (validator p)
= fun b a len err ->
  if cond
  then vtrue () b a len err
  else vfalse () b a len err

inline_for_extraction
```pulse
fn r_write_if
  (#t: Type)
  (cond: bool)
  (r: ref t)
  (v': (squash (cond == true) -> t))
  (#v: Ghost.erased t)
  requires pts_to r v
  ensures pts_to r (if cond then v' () else v)
{
    if (cond) {
        r := v' ();
    }
}
```
