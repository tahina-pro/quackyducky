module ASN1.DiffTest

(* Name-based dispatch for differential testing (difftest/).
   [parse name b] is [None] if [name] is not a known "Module.Type",
   otherwise [Some r] where [r] is the number of bytes consumed by
   the parser, or [None] if it rejects. *)

open ASN1.Base
open ASN1.Spec.Interpreter
module LP = LowParse.Spec.Base

let consumed (#s: _) (k: asn1_k s) (b: bytes)
  : option nat
= match asn1_as_parser k b with
  | Some (_, n) -> Some n
  | None -> None

let parse (name: string) (b: bytes) : option (option nat)
= match name with
  | "DiffSmoke.Smoke" -> Some (consumed ASN1.DiffTest.Smoke.smoke b)
  | _ -> None
