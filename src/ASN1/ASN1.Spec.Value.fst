module ASN1.Spec.Value

(* Generic ASN.1 DER values (for ANY), parsed with the length-delimited
   recursive combinator LowParse.Spec.RecursiveVLGen *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32
open ASN1.Spec.Content.BOOLEAN
open ASN1.Spec.Content.INTEGER
open ASN1.Spec.Content.BITSTRING
open ASN1.Spec.Content.OCTETSTRING
open ASN1.Spec.Content.UTF8STRING
open ASN1.Spec.Content.PRINTABLESTRING
open ASN1.Spec.Content.IA5STRING
open ASN1.Spec.Content.VISIBLESTRING
open ASN1.Spec.Content.BMPSTRING
open ASN1.Spec.Content.UNIVERSALSTRING
open ASN1.Spec.Content.NULL
open ASN1.Spec.Content.OIDU32
open ASN1.Spec.Content.TIME

module RV = LowParse.Spec.RecursiveVLGen
module U32 = FStar.UInt32

let asn1_any_identifier_kind = parse_filter_kind (and_then_kind parse_u8_kind parse_asn1_identifier_first_kind)

let parse_asn1_any_identifier : parser asn1_any_identifier_kind asn1_any_id_t
= let _ = lemma_parse_asn1_identifier_first_inj () in
  (parse_u8 `and_then` parse_asn1_identifier_first) `parse_filter` asn1_any_id_valid

let asn1_universal_terminal_parser (k : asn1_terminal_k) : asn1_weak_parser (asn1_terminal_t k) =
  match k with
  | ASN1_BOOLEAN -> weaken _ parse_asn1_boolean
  | ASN1_INTEGER bound -> weaken _ (parse_untagged_bounded_integer bound)
  | ASN1_BITSTRING -> parse_asn1_bitstring
  | ASN1_OCTETSTRING -> parse_asn1_octetstring
  | ASN1_UTF8STRING -> parse_asn1_utf8string
  | ASN1_PRINTABLESTRING -> parse_asn1_printablestring
  | ASN1_IA5STRING -> parse_asn1_ia5string
  | ASN1_VISIBLESTRING -> parse_asn1_visiblestring
  | ASN1_BMPSTRING -> parse_asn1_bmpstring
  | ASN1_UNIVERSALSTRING -> parse_asn1_universalstring
  | ASN1_TELETEXSTRING -> parse_asn1_octetstring
  | ASN1_NULL -> parse_asn1_null
  | ASN1_OID -> parse_asn1_OIDU32
  | ASN1_UTCTIME -> parse_asn1_UTCTIME
  | ASN1_GENERALIZEDTIME -> parse_asn1_GENERALIZEDTIME
  | ASN1_PREFIXED_TERMINAL _ _ -> fail_parser _ _

(* The contents of a primitive value *)
let parse_asn1_any_leaf (id : asn1_any_id_t) : asn1_weak_parser (asn1_any_leaf_t id) =
  match id with
  | MK_ASN1_ID UNIVERSAL _ v ->
    begin match asn1_universal_terminal v with
    | Some k -> asn1_universal_terminal_parser k
    | None -> parse_asn1_octetstring
    end
  | _ -> parse_asn1_octetstring

let synth_asn1_value
  (x : dtuple2 asn1_any_id_t (fun id -> RV.rec_vlgen_payload asn1_value (asn1_any_leaf_t id)))
: Tot asn1_value
= match x with
  | (| id, RV.RNode l |) -> ASN1_VALUE_CONSTRUCTED id l
  | (| id, RV.RLeaf v |) -> ASN1_VALUE_PRIMITIVE id v

let asn1_value_param : RV.rec_vlgen_param = {
  RV.t = asn1_value;
  RV.tag = asn1_any_id_t;
  RV.tag_kind = asn1_any_identifier_kind;
  RV.parse_tag = parse_asn1_any_identifier;
  RV.len_min = 0;
  RV.len_max = 4294967295;
  RV.len_kind = parse_asn1_length_u32_t_kind;
  RV.parse_len = parse_asn1_length_u32_t;
  RV.is_node = (fun (id : asn1_any_id_t) -> CONSTRUCTED? id.f);
  RV.leaf_t = asn1_any_leaf_t;
  RV.leaf_kind = asn1_weak_parser_kind;
  RV.leaf = parse_asn1_any_leaf;
  RV.synth_ = synth_asn1_value;
  RV.synth_inj = ();
}

let parse_asn1_value : asn1_strong_parser asn1_value
= weaken _ (RV.parse_rec_vlgen asn1_value_param)

(* The value parser, after its identifier has been read *)

let synth_asn1_value_twin
  (id : asn1_any_id_t)
  (x : RV.rec_vlgen_payload asn1_value (asn1_any_leaf_t id))
: Tot asn1_value
= synth_asn1_value (| id, x |)

let parse_asn1_value_twin (id : asn1_id_t) : asn1_strong_parser asn1_value
= if asn1_any_id_valid id
  then weaken _ (RV.rec_vlgen_payload_parser asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id `parse_synth` synth_asn1_value_twin id)
  else fail_parser _ _

let parse_asn1_value_twin_and_then_cases_injective ()
: Lemma (and_then_cases_injective parse_asn1_value_twin)
= and_then_cases_injective_intro parse_asn1_value_twin (fun id1 id2 b1 b2 ->
    if asn1_any_id_valid id1 && asn1_any_id_valid id2
    then begin
      parse_synth_eq (RV.rec_vlgen_payload_parser asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id1) (synth_asn1_value_twin id1) b1;
      parse_synth_eq (RV.rec_vlgen_payload_parser asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id2) (synth_asn1_value_twin id2) b2
    end
    else ()
  )
