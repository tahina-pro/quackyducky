module CBOR.Pulse.Raw.EverParse.Det.Inject
#lang-pulse

(* Implementation of the record<->cbor injection helpers.  Lives in everparse/
   because it [friend]s [CBOR.Pulse.API.Det.Common] (to unfold [cbor_det_case])
   and [CBOR.Pulse.API.Det.Type] (so that [cbor_det_t == cbor_raw], hence the
   raw [CBOR_Case_Array_Gen] constructor produces a [cbor_det_t]). *)

friend CBOR.Pulse.API.Det.Type
friend CBOR.Pulse.API.Det.Common

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Det.Type
open CBOR.Pulse.API.Det.Common
open CBOR.Pulse.Raw.Type

module Raw = CBOR.Pulse.Raw.Type

(* [cbor_det_t == cbor_raw] and [cbor_det_case (CBOR_Case_Array_Gen _) == CaseArray]
   (both by [friend]), so the refinement of the result holds definitionally. *)
let array_gen arec = CBOR_Case_Array_Gen arec

let array_gen_recover x arec =
  (* [x == array_gen arec == CBOR_Case_Array_Gen arec] (array_gen unfolds
     in-module), so [x] is a [CBOR_Case_Array_Gen] node. *)
  let x' : (y: cbor_raw { CBOR_Case_Array_Gen? y }) = x in
  let CBOR_Case_Array_Gen v = x' in
  v

let array_gen_inj arec1 arec2 = ()
