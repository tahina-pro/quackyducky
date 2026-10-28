module ASN1.Pulse.Interpreter
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.ILC
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter
open ASN1.Pulse.Sequence

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module ILC = ASN1.Pulse.ILC
module Term = ASN1.Pulse.Terminal

(* Definitions tagged with this attribute are unfolded when specializing
   the interpreter to a given schema. *)
irreducible let asn1_pulse_attr : unit = ()

(* The subset of schemas currently supported *)

[@@asn1_pulse_attr]
let supported_terminal (k: asn1_terminal_k) : Tot bool =
  match k with
  | ASN1_BOOLEAN -> true
  | ASN1_OCTETSTRING -> true
  | ASN1_INTEGER bound -> bound < 65536
  | _ -> false

[@@asn1_pulse_attr]
let rec supported_content (k: asn1_content_k) : Tot bool (decreases k) =
  match k with
  | ASN1_TERMINAL k' -> supported_terminal k'
  | ASN1_SEQUENCE gitems -> supported_items (dsnd gitems)
  | _ -> false

and supported_k (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC _ k' -> supported_content k'
  | _ -> false

and supported_items (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> supported_dec dk && supported_items tl

and supported_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot bool (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> supported_k k
  | ASN1_OPTION_ILC k -> supported_k k
  | _ -> false

(* Static information about sequence items *)

[@@asn1_pulse_attr]
let rec all_defaultable (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ d _ _ tl -> not (PLAIN? d) && all_defaultable tl

let rec all_defaultable_correct (#i: _) (ls: asn1_gen_items_l i)
: Lemma
  (ensures (all_defaultable ls == Some? (generate_defaultable_items (asn1_sequence_as_parser ls))))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ tl -> all_defaultable_correct tl

[@@asn1_pulse_attr]
inline_for_extraction
let has_id_k (#s: _) (k: asn1_k s) (u: squash (supported_k k)) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match k with
  | ASN1_ILC id0 _ -> ILC.asn1_id_eq id id0

inline_for_extraction
fn validate_fail
  (#t: Type0) (#k: Ghost.erased parser_kind) (p: SB.parser k t)
  (u: squash (forall b . None? (SB.parse p b)))
: LPS.validator #t #k p
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  false
}

(* The interpreter *)

[@@asn1_pulse_attr]
inline_for_extraction
let validate_terminal (k: asn1_terminal_k) (u: squash (supported_terminal k))
: Tot (LPS.validator #(asn1_terminal_t k) #asn1_weak_parser_kind (asn1_terminal_as_parser k))
= match k with
  | ASN1_BOOLEAN -> Term.validate_boolean
  | ASN1_OCTETSTRING -> Term.validate_octetstring
  | ASN1_INTEGER bound ->
    SZ.fits_at_least_16 bound;
    Term.validate_integer (SZ.uint_to_t bound)

[@@asn1_pulse_attr]
inline_for_extraction
let rec validate_content (k: asn1_content_k) (u: squash (supported_content k))
: Tot (LPS.validator #(asn1_content_t k) #asn1_weak_parser_kind (asn1_content_as_parser k))
  (decreases %[k; 0])
= match k with
  | ASN1_TERMINAL k' -> validate_terminal k' ()
  | ASN1_SEQUENCE gitems ->
    LPS.validate_ext (validate_seq (dsnd gitems) () None) #asn1_weak_parser_kind (asn1_content_as_parser k)

and validate_k_twin (#s: _) (k: asn1_k s) (u: squash (supported_k k)) (id: asn1_id_t)
: Tot (LPS.validator #(asn1_t k) #asn1_strong_parser_kind (snd (asn1_as_parser_twin k) id))
  (decreases %[k; 0])
= match k with
  | ASN1_ILC id0 k' ->
    LPS.ifthenelse_validator (snd (asn1_as_parser_twin k) id) (ILC.asn1_id_eq id0 id)
      (fun _ -> LPS.validate_ext (ILC.validate_asn1_LC (validate_content k' ())) #asn1_strong_parser_kind (snd (asn1_as_parser_twin k) id))
      (fun _ -> validate_fail (snd (asn1_as_parser_twin k) id) ())

and validate_dec_twin (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (supported_dec dk)) (id: asn1_id_t)
: Tot (LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) id))
  (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k ->
    validate_item_twin_plain (asn1_decorated_as_parser_twin dk) id (validate_k_twin k () id)
  | ASN1_OPTION_ILC k ->
    validate_item_twin_option (asn1_decorated_as_parser_twin dk) id (validate_k_twin k () id)

and validate_seq (#i: _) (ls: asn1_gen_items_l i) (u: squash (supported_items ls)) (st: option asn1_id_t)
: Tot (LPS.validator #_ #asn1_weak_parser_kind (seq_p (asn1_sequence_as_parser ls) st))
  (decreases %[ls; 1])
= match ls with
  | ASN1_GEN_ITEMS_NIL -> validate_seq_nil st
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
    all_defaultable_correct ls;
    validate_seq_cons (asn1_sequence_as_parser ls) (all_defaultable ls) (validate_seq_body ls ()) st

and validate_seq_body (#i: _) (ls: asn1_gen_items_l i) (u: squash (supported_items ls /\ Cons? (asn1_sequence_as_parser ls))) (id: asn1_id_t)
: Tot (LPS.validator #_ #asn1_weak_parser_kind (seq_p (asn1_sequence_as_parser ls) (Some id)))
  (decreases %[ls; 0])
= match ls with
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    let hd = Ghost.hide (asn1_decorated_as_parser_twin dk) in
    match tl with
    | ASN1_GEN_ITEMS_NIL ->
      validate_seq_single_body hd id (validate_dec_twin dk () id)
    | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
      validate_seq_cons_cons_body hd (asn1_sequence_as_parser tl) id
        (has_id_dec dk () id)
        (PLAIN? d)
        (validate_dec_twin dk () id)
        (validate_seq tl ())

and has_id_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (supported_dec dk)) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
  (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k -> has_id_k k () id
  | ASN1_OPTION_ILC k -> has_id_k k () id

[@@asn1_pulse_attr]
inline_for_extraction
let validate_k (#s: _) (k: asn1_k s) (u: squash (supported_k k))
: Tot (LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k))
= match k with
  | ASN1_ILC id k' -> ILC.validate_asn1_ILC id (validate_content k' ())
