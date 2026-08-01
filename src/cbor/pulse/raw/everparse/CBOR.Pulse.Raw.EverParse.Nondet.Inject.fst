module CBOR.Pulse.Raw.EverParse.Nondet.Inject
#lang-pulse

(* Implementation of the record<->cbor injection helpers.  Lives in everparse/
   because it [friend]s [CBOR.Pulse.API.Nondet.Type] (to realize
   [cbor_nondet_t == cbor_raw], hence the raw [CBOR_Case_Array_Gen] constructor
   produces a [cbor_nondet_t]) and [CBOR.Pulse.Raw.Nondet] (to unfold
   [cbor_nondet_case]); both of those modules reference the everparse-only
   format modules. *)

friend CBOR.Pulse.API.Nondet.Type
friend CBOR.Pulse.Raw.Nondet

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Nondet.Type
open CBOR.Pulse.Raw.Nondet
open CBOR.Pulse.Raw.Type

module Raw = CBOR.Pulse.Raw.Type

(* [cbor_nondet_t == cbor_raw] and
   [cbor_nondet_case (CBOR_Case_Array_Gen _) == CaseArray] (both by [friend]), so
   the refinement of the result holds definitionally. *)
let array_gen arec = CBOR_Case_Array_Gen arec

let array_gen_recover x arec =
  (* [x == array_gen arec == CBOR_Case_Array_Gen arec] (array_gen unfolds
     in-module), so [x] is a [CBOR_Case_Array_Gen] node. *)
  let x' : (y: cbor_raw { CBOR_Case_Array_Gen? y }) = x in
  let CBOR_Case_Array_Gen v = x' in
  v

let array_gen_inj arec1 arec2 = ()
