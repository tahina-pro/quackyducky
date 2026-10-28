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
module C = ASN1.Pulse.Constructed
module SO = ASN1.Pulse.SetOf
module Rs = ASN1.Pulse.Restrict
module SC = ASN1.Pulse.SetComp
module Any = ASN1.Pulse.Any
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* Definitions tagged with this attribute are unfolded when specializing
   the interpreter to a given schema. *)
irreducible let asn1_pulse_attr : unit = ()

[@@asn1_pulse_attr]
let rec items_len (#i: _) (ls: asn1_gen_items_l i) : Tot (n: nat { n == List.Tot.length (asn1_sequence_as_parser ls) }) (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> 0
  | ASN1_GEN_ITEMS_CONS _ _ _ _ tl -> 1 + items_len tl

(* The subset of schemas currently supported *)

[@@asn1_pulse_attr]
let rec supported_terminal (k: asn1_terminal_k) : Tot bool (decreases k) =
  match k with
  | ASN1_INTEGER bound -> bound < 65536
  | ASN1_PREFIXED_TERMINAL _ k' -> supported_terminal k'
  | _ -> true

[@@asn1_pulse_attr]
let supported_default (k: asn1_terminal_k) : Tot bool =
  ASN1_BOOLEAN? k || ASN1_NULL? k

[@@asn1_pulse_attr]
let supported_restriction (k: asn1_terminal_k) (r: asn1_restriction k) : Tot bool =
  match k with
  | ASN1_BOOLEAN -> RESTRICT_IN? r
  | ASN1_INTEGER bound -> bound < 65536 && Rs.int_restriction_ok r
  | ASN1_OCTETSTRING -> Rs.size_restriction_ok r
  | _ -> false

[@@asn1_pulse_attr]
let rec supported_content (k: asn1_content_k) : Tot bool (decreases k) =
  match k with
  | ASN1_TERMINAL k' -> supported_terminal k'
  | ASN1_RESTRICTED_TERMINAL k' r -> supported_restriction k' r
  | ASN1_SEQUENCE gitems -> supported_items (dsnd gitems)
  | ASN1_SEQUENCE_OF _ k' -> supported_k k'
  | ASN1_SET_OF _ k' -> supported_k k'
  | ASN1_SET _ items _ -> supported_items items && items_len items <= 64
  | ASN1_PREFIXED k' -> supported_k k'
  | _ -> false

and supported_k (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC _ k' -> supported_content k'
  | ASN1_CHOICE_ILC lc _ -> supported_lc lc
  | ASN1_ANY_ILC -> true

and supported_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot bool (decreases lc) =
  match lc with
  | [] -> true
  | (_, ck) :: tl -> supported_content ck && supported_lc tl

and supported_items (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> supported_dec dk && supported_items tl

and supported_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot bool (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> supported_k k
  | ASN1_OPTION_ILC k -> supported_k k
  | ASN1_DEFAULT_TERMINAL _ #k _ -> supported_default k
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k r _ -> ASN1_BOOLEAN? k && RESTRICT_IN? r
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
let rec has_id_lc (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id (Set.as_set' (List.Tot.map fst lc)) })
  (decreases lc)
= match lc with
  | [] -> false
  | (id', _) :: tl -> ILC.asn1_id_eq id id' || has_id_lc tl id

[@@asn1_pulse_attr]
inline_for_extraction
let has_id_k (#s: _) (k: asn1_k s) (u: squash (supported_k k)) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match k with
  | ASN1_ILC id0 _ -> ILC.asn1_id_eq id id0
  | ASN1_CHOICE_ILC lc _ -> has_id_lc lc id
  | ASN1_ANY_ILC -> true

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

[@@asn1_pulse_attr]
inline_for_extraction
let has_id_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (supported_dec dk)) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match dk with
  | ASN1_PLAIN_ILC k -> has_id_k k () id
  | ASN1_OPTION_ILC k -> has_id_k k () id
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 _ _ -> ILC.asn1_id_eq id id0
  | ASN1_DEFAULT_TERMINAL id0 _ -> ILC.asn1_id_eq id id0

(* SET { ... }: static component lookup and final check *)

(* Not unfolded at specialization: the normalizer does not unfold recursive
   calls in the branches of a stuck match, so the recursive call must be
   an argument. *)
inline_for_extraction
let pick (b: bool) (j: U32.t) (r: option U32.t) : Tot (o: option U32.t { o == (if b then Some j else r) }) =
  if b then Some j else r

[@@asn1_pulse_attr]
inline_for_extraction
let rec set_comp (#i: _) (ls: asn1_gen_items_l i) (u: squash (supported_items ls))
  (j: U32.t { U32.v j + items_len ls <= 64 }) (id: asn1_id_t)
: Tot (r: option U32.t { SC.opt_u32_v r == (match SC.comp_of_id (asn1_sequence_as_parser ls) id with None -> None | Some c -> Some (U32.v j + c)) })
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> None
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    pick (has_id_dec dk () id) j (set_comp tl () (U32.add j 1ul) id)

[@@asn1_pulse_attr]
inline_for_extraction
let rec set_final (#i: _) (ls: asn1_gen_items_l i)
  (j: U32.t { U32.v j + items_len ls <= 64 }) (m: U64.t)
: Tot (b: bool { b == SC.final_ok' (asn1_sequence_as_parser ls) (U32.v j) m })
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ d _ _ tl ->
    SC.test_bit_spec m j;
    (not (PLAIN? d) || SC.test_bit m j) && set_final tl (U32.add j 1ul) m

(* The interpreter *)

[@@asn1_pulse_attr]
inline_for_extraction
let validate_default_content (k: asn1_terminal_k) (defv: asn1_terminal_t k) (u: squash (supported_default k))
: Tot (LPS.validator #(asn1_content_t (C.default_content k defv)) #asn1_weak_parser_kind (asn1_content_as_parser (C.default_content k defv)))
= match k with
  | ASN1_BOOLEAN -> Rs.validate_boolean_neq defv
  | ASN1_NULL ->
    Classical.forall_intro C.default_null_fails;
    validate_fail (asn1_content_as_parser (C.default_content k defv)) ()

[@@asn1_pulse_attr]
inline_for_extraction
let validate_restricted (k: asn1_terminal_k) (r: asn1_restriction k) (u: squash (supported_restriction k r))
: Tot (LPS.validator #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)))
= match k with
  | ASN1_BOOLEAN ->
    let RESTRICT_IN l = r in
    Rs.validate_boolean_in l
  | ASN1_INTEGER bound ->
    SZ.fits_at_least_16 bound;
    Rs.validate_integer_restricted (SZ.uint_to_t bound) r
  | ASN1_OCTETSTRING -> Rs.validate_octetstring_size r

[@@asn1_pulse_attr]
inline_for_extraction
let validate_default_restricted_content (k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_terminal_t k { restriction_pred r defv }) (u: squash (ASN1_BOOLEAN? k && RESTRICT_IN? r))
: Tot (LPS.validator #(asn1_content_t (C.default_restricted_content k r defv)) #asn1_weak_parser_kind (asn1_content_as_parser (C.default_restricted_content k r defv)))
= match k with
  | ASN1_BOOLEAN ->
    let RESTRICT_IN l = r in
    Rs.validate_boolean_in_neq l defv

[@@asn1_pulse_attr]
inline_for_extraction
let rec validate_terminal (k: asn1_terminal_k) (u: squash (supported_terminal k))
: Tot (LPS.validator #(asn1_terminal_t k) #asn1_weak_parser_kind (asn1_terminal_as_parser k))
  (decreases k)
= match k with
  | ASN1_BOOLEAN -> Term.validate_boolean
  | ASN1_INTEGER bound ->
    SZ.fits_at_least_16 bound;
    Term.validate_integer (SZ.uint_to_t bound)
  | ASN1_BITSTRING -> Term.validate_bitstring
  | ASN1_OCTETSTRING -> Term.validate_octetstring
  | ASN1_UTF8STRING -> Term.validate_utf8
  | ASN1_PRINTABLESTRING -> Term.validate_printable
  | ASN1_IA5STRING -> Term.validate_ia5
  | ASN1_VISIBLESTRING -> Term.validate_visible
  | ASN1_BMPSTRING -> Term.validate_bmp
  | ASN1_UNIVERSALSTRING -> Term.validate_universal
  | ASN1_TELETEXSTRING -> Term.validate_raw_string k
  | ASN1_NUMERICSTRING -> Term.validate_numeric
  | ASN1_VIDEOTEXSTRING -> Term.validate_raw_string k
  | ASN1_GRAPHICSTRING -> Term.validate_raw_string k
  | ASN1_GENERALSTRING -> Term.validate_raw_string k
  | ASN1_OBJECTDESCRIPTOR -> Term.validate_raw_string k
  | ASN1_NULL -> Term.validate_null
  | ASN1_OID -> ASN1.Pulse.OID.validate_oid
  | ASN1_RELATIVE_OID -> ASN1.Pulse.OID.validate_relative_oid
  | ASN1_OID_IRI -> Term.validate_oid_iri
  | ASN1_RELATIVE_OID_IRI -> Term.validate_relative_oid_iri
  | ASN1_UTCTIME -> Term.validate_utctime
  | ASN1_GENERALIZEDTIME -> Term.validate_generalizedtime
  | ASN1_DATE -> Term.validate_date
  | ASN1_TIME_OF_DAY -> Term.validate_timeofday
  | ASN1_DATE_TIME -> Term.validate_datetime
  | ASN1_PREFIXED_TERMINAL id k' ->
    LPS.validate_weaken asn1_weak_parser_kind
      (ILC.validate_asn1_ILC id #(ASN1_TERMINAL k') #(asn1_terminal_as_parser k') (validate_terminal k' ()))

[@@asn1_pulse_attr]
inline_for_extraction
let rec validate_content (k: asn1_content_k) (u: squash (supported_content k))
: Tot (LPS.validator #(asn1_content_t k) #asn1_weak_parser_kind (asn1_content_as_parser k))
  (decreases %[k; 0])
= match k with
  | ASN1_TERMINAL k' -> validate_terminal k' ()
  | ASN1_RESTRICTED_TERMINAL k' r -> validate_restricted k' r ()
  | ASN1_SEQUENCE gitems ->
    LPS.validate_ext (validate_seq (dsnd gitems) () None) #asn1_weak_parser_kind (asn1_content_as_parser k)
  | ASN1_SEQUENCE_OF ne k' ->
    C.validate_sized_list ne (validate_k k' ())
  | ASN1_SET_OF ne k' ->
    SO.validate_sized_set ne (validate_k k' ())
  | ASN1_SET _ items _ ->
    ASN1.Spec.Conformance.items_tagged_intro items;
    LPS.validate_ext
      (SC.validate_set (Ghost.hide (asn1_sequence_as_parser items))
        (fun id -> set_comp items () 0ul id)
        (fun m -> set_final items 0ul m)
        (fun id -> validate_set_elem_twin items () id))
      #asn1_weak_parser_kind (asn1_content_as_parser k)
  | ASN1_PREFIXED k' ->
    LPS.validate_weaken asn1_weak_parser_kind (validate_k k' ())

and validate_k (#s: _) (k: asn1_k s) (u: squash (supported_k k))
: Tot (LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k))
  (decreases %[k; 1])
= match k with
  | ASN1_ILC id k' -> ILC.validate_asn1_ILC id (validate_content k' ())
  | ASN1_CHOICE_ILC lc pf ->
    C.asn1_choice_id_then lc pf;
    C.validate_id_then (asn1_as_parser k) (Ghost.hide (snd (asn1_as_parser_twin k))) (fun id -> validate_k_twin k () id) ()
  | ASN1_ANY_ILC -> Any.validate_any

and validate_k_twin (#s: _) (k: asn1_k s) (u: squash (supported_k k)) (id: asn1_id_t)
: Tot (LPS.validator #(asn1_t k) #asn1_strong_parser_kind (snd (asn1_as_parser_twin k) id))
  (decreases %[k; 0])
= match k with
  | ASN1_ILC id0 k' ->
    LPS.ifthenelse_validator (snd (asn1_as_parser_twin k) id) (ILC.asn1_id_eq id0 id)
      (fun _ -> LPS.validate_ext (ILC.validate_asn1_LC (validate_content k' ())) #asn1_strong_parser_kind (snd (asn1_as_parser_twin k) id))
      (fun _ -> validate_fail (snd (asn1_as_parser_twin k) id) ())
  | ASN1_CHOICE_ILC lc pf ->
    Classical.forall_intro (C.asn1_choice_twin_consumed lc pf id);
    validate_ext_consumed (validate_choice_payload lc () id) (snd (asn1_as_parser_twin k) id)
  | ASN1_ANY_ILC -> Any.validate_any_twin id

and validate_choice_payload (lc: list (asn1_id_t & asn1_content_k)) (u: squash (supported_lc lc)) (id: asn1_id_t)
: Tot (LPS.validator #_ #asn1_strong_parser_kind (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id))
  (decreases %[lc; 0])
= match lc with
  | [] -> validate_fail (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) ()
  | (id', ck) :: tl ->
    Classical.forall_intro (C.asn1_choice_payload_cons id' ck tl id);
    LPS.ifthenelse_validator (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) (ILC.asn1_id_eq id id')
      (fun _ -> validate_ext_consumed (ILC.validate_asn1_LC (validate_content ck ())) (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id))
      (fun _ -> validate_ext_consumed (validate_choice_payload tl () id) (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id))

and validate_dec_twin (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (supported_dec dk)) (id: asn1_id_t)
: Tot (LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) id))
  (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k ->
    validate_item_twin_plain (asn1_decorated_as_parser_twin dk) id (validate_k_twin k () id)
  | ASN1_OPTION_ILC k ->
    validate_item_twin_option (asn1_decorated_as_parser_twin dk) id (validate_k_twin k () id)
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    Classical.forall_intro (C.default_terminal_twin_consumed id0 #k defv id);
    LPS.ifthenelse_validator (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) id) (ILC.asn1_id_eq id0 id)
      (fun _ -> validate_ext_consumed (ILC.validate_asn1_LC (validate_default_content k defv ())) (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) id))
      (fun _ -> validate_fail (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) id) ())
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    Classical.forall_intro (C.default_restricted_twin_consumed id0 #k r defv id);
    LPS.ifthenelse_validator (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) id) (ILC.asn1_id_eq id0 id)
      (fun _ -> validate_ext_consumed (ILC.validate_asn1_LC (validate_default_restricted_content k r defv ())) (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) id))
      (fun _ -> validate_fail (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) id) ())

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

and validate_set_elem_twin (#i: _) (ls: asn1_gen_items_l i) (u: squash (supported_items ls)) (id: asn1_id_t)
: Tot (LPS.validator #_ #asn1_strong_parser_kind (ASN1.Spec.SetComponents.parse_set_elem_twin (asn1_sequence_as_parser ls) id))
  (decreases %[ls; 0])
= match ls with
  | ASN1_GEN_ITEMS_NIL -> validate_fail (ASN1.Spec.SetComponents.parse_set_elem_twin (asn1_sequence_as_parser ls) id) ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let p = ASN1.Spec.SetComponents.parse_set_elem_twin (asn1_sequence_as_parser ls) id in
    Classical.forall_intro (SC.set_elem_twin_cons_consumed (asn1_decorated_as_parser_twin dk) (asn1_sequence_as_parser tl) id);
    LPS.ifthenelse_validator p (has_id_dec dk () id)
      (fun _ -> validate_ext_consumed (validate_dec_twin dk () id) #_ #asn1_strong_parser_kind p)
      (fun _ -> validate_ext_consumed (validate_set_elem_twin tl () id) #_ #asn1_strong_parser_kind p)
