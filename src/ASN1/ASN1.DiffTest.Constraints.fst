module ASN1.DiffTest.Constraints

(* Differential testing (difftest/): SIZE and value constraints.
   Must agree with difftest/schemas/DiffConstraints.asn *)

open ASN1.Base
open ASN1.Syntax

(* Sized ::= OCTET STRING (SIZE (2..3)) *)
let sized
= mk_restricted_field asn1_octetstring
    (fun s -> let l = Seq.length s in 2 <= l && l <= 3)

(* Byte ::= INTEGER (0..255) *)
let byte = mk_restricted_field asn1_integer (fun x -> 0 <= x && x <= 255)

(* NonEmptySeqOf ::= SEQUENCE SIZE (1..MAX) OF INTEGER *)
let nonEmptySeqOf = asn1_nonempty_sequence_of asn1_integer

(* NonEmptySetOf ::= SET SIZE (1..MAX) OF INTEGER *)
let nonEmptySetOf = asn1_nonempty_set_of asn1_integer
