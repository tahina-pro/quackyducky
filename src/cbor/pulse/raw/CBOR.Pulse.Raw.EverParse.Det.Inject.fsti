module CBOR.Pulse.Raw.EverParse.Det.Inject
#lang-pulse

(* Layer-2 (raw/) interface of the record<->cbor injection helpers used by the
   Rust structural array builder ([CBOR.Pulse.API.Det.Rust]).

   Unlike the C API, whose array handle IS the adapter's [cbor_mixed_list_array]
   record, the Rust [cbor_det_array] type is a record wrapper
     [{ array: cbordet { CaseArray? (cbor_det_case array) } }]
   around a full deterministic-CBOR object.  To store a builder record [arec]
   (produced by [CBOR.Pulse.Raw.EverParse.Det.ArrayBuilder]) in that wrapper we
   must exhibit a [cbor_det_t] whose [cbor_det_case] is [CaseArray] -- concretely
   the raw [CBOR_Case_Array_Gen arec] node.  Proving
     [CaseArray? (cbor_det_case (CBOR_Case_Array_Gen arec))]
   requires unfolding [cbor_det_case], which lives in
   [CBOR.Pulse.API.Det.Common]; that module [friend]s the everparse-only module
   [CBOR.Pulse.Raw.EverParse.SizeComparison], so it can only be [friend]ed from
   the everparse/ build.  Hence this interface (consumable from raw/) is realized
   by an implementation in everparse/ that [friend]s [Det.Type] and [Det.Common].

   The interface is abstraction-safe: it mentions only [cbor_det_t] (abstract)
   and [cbor_mixed_list_array], never an equation across the [cbor_det_t] /
   [cbor_raw] boundary. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Det.Type
open CBOR.Pulse.API.Det.Common

module Raw = CBOR.Pulse.Raw.Type

(* Inject an array-builder record into a deterministic-CBOR object whose case is
   [CaseArray] (concretely the [CBOR_Case_Array_Gen arec] node). *)
val array_gen (arec: Raw.cbor_mixed_list_array)
: Tot (x: cbor_det_t { CaseArray? (cbor_det_case x) })

(* Recover the underlying record from an [array_gen] image.  The (erased) ghost
   witness [arec] pins which record was injected; the returned CONCRETE record
   equals it.  This lets [Rust] extract the builder record held inside a wrapper
   field [a.array] without exposing the [cbor_det_t]/[cbor_raw] boundary. *)
val array_gen_recover
  (x: cbor_det_t)
  (arec: Ghost.erased Raw.cbor_mixed_list_array)
: Pure Raw.cbor_mixed_list_array
    (requires (x == array_gen (Ghost.reveal arec)))
    (ensures (fun r -> r == Ghost.reveal arec /\ x == array_gen r))

(* [array_gen] is injective: needed to invert the wrapper-ownership predicate
   (which existentially quantifies the underlying record). *)
val array_gen_inj (arec1 arec2: Raw.cbor_mixed_list_array)
: Lemma
    (requires (array_gen arec1 == array_gen arec2))
    (ensures (arec1 == arec2))
