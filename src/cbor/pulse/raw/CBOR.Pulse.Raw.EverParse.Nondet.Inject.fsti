module CBOR.Pulse.Raw.EverParse.Nondet.Inject
#lang-pulse

(* Layer-2 (raw/) interface of the record<->cbor injection helpers used by the
   Rust structural array builder ([CBOR.Pulse.API.Nondet.Rust]).

   Unlike the C API, whose array handle IS the adapter's [cbor_mixed_list_array]
   record, the Rust [cbor_nondet_array] type is a record wrapper
     [{ array: cbornondet { CaseArray? (cbor_nondet_case array) } }]
   around a full nondeterministic-CBOR object.  To store a builder record [arec]
   (produced by [CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder]) in that wrapper
   we must exhibit a [cbor_nondet_t] whose [cbor_nondet_case] is [CaseArray] --
   concretely the raw [CBOR_Case_Array_Gen arec] node.  Proving
     [CaseArray? (cbor_nondet_case (CBOR_Case_Array_Gen arec))]
   requires unfolding [cbor_nondet_case], which lives in
   [CBOR.Pulse.Raw.Nondet]; that module (and [CBOR.Pulse.API.Nondet.Type], which
   realizes [cbor_nondet_t == cbor_raw]) references the everparse-only format
   modules, so it can only be [friend]ed from the everparse/ build.  Hence this
   interface (consumable from raw/) is realized by an implementation in
   everparse/ that [friend]s [CBOR.Pulse.API.Nondet.Type] and
   [CBOR.Pulse.Raw.Nondet].

   The interface is abstraction-safe: it mentions only [cbor_nondet_t] (abstract)
   and [cbor_mixed_list_array], never an equation across the [cbor_nondet_t] /
   [cbor_raw] boundary. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Nondet.Type
open CBOR.Pulse.Raw.Nondet

module Raw = CBOR.Pulse.Raw.Type

(* Inject an array-builder record into a nondeterministic-CBOR object whose case
   is [CaseArray] (concretely the [CBOR_Case_Array_Gen arec] node). *)
val array_gen (arec: Raw.cbor_mixed_list_array)
: Tot (x: cbor_nondet_t { CaseArray? (cbor_nondet_case x) })

(* Recover the underlying record from an [array_gen] image.  The (erased) ghost
   witness [arec] pins which record was injected; the returned CONCRETE record
   equals it.  This lets [Rust] extract the builder record held inside a wrapper
   field [a.array] without exposing the [cbor_nondet_t]/[cbor_raw] boundary. *)
val array_gen_recover
  (x: cbor_nondet_t)
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
