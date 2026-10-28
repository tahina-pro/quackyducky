module ASN1.Pulse.Terminal
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.Content.BOOLEAN
open ASN1.Spec.Content.OCTETSTRING
open ASN1.Spec.Interpreter

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module LSB = LowParse.Pulse.SeqBytes
module I = ASN1.Pulse.Identifier

(* BOOLEAN *)

inline_for_extraction
fn vread_boolean (_: unit)
: vreader #asn1_boolean_t #parse_asn1_boolean_t_kind parse_asn1_boolean
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  lemma_parse_asn1_boolean_unfold (Seq.slice v (SZ.v offset) (Seq.length v));
  let r = I.vread_u8 input poffset;
  match r {
    None -> {
      None #asn1_boolean_t
    }
    Some x -> {
      if (is_valid_asn1_boolean x) {
        Some (decode_asn1_boolean x)
      } else {
        None #asn1_boolean_t
      }
    }
  }
}

inline_for_extraction
let validate_boolean
: LPS.validator #asn1_boolean_t #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BOOLEAN)
= LPS.validate_ext
    #_ #asn1_weak_parser_kind
    (validate_of_vreader (vread_weaken asn1_weak_parser_kind (vread_boolean ()) ()))
    #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BOOLEAN)

inline_for_extraction
let read_boolean
: PPB.leaf_reader #asn1_boolean_t #parse_asn1_boolean_t_kind parse_asn1_boolean
= leaf_read_of_vreader (vread_boolean ())

(* OCTET STRING *)

inline_for_extraction
let validate_octetstring
: LPS.validator #asn1_octetstring_t #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OCTETSTRING)
= LPS.validate_ext
    #_ #asn1_weak_parser_kind
    (LPS.validate_weaken asn1_weak_parser_kind (LSB.validate_seq_all_bytes ()))
    #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OCTETSTRING)

(* INTEGER (bounded): the content is the whole input *)

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_integer
  (bound: SZ.t { SZ.v bound > 0 })
: LPS.validator #(asn1_terminal_t (ASN1_INTEGER (SZ.v bound))) #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_INTEGER (SZ.v bound)))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let off = !poffset;
  pts_to_len input;
  let len = S.len input;
  let n = SZ.sub len off;
  if (SZ.gt n bound || n = 0sz) {
    false
  } else if (n = 1sz) {
    poffset := len;
    true
  } else {
    let c0 = input.(off);
    let c1 = input.(SZ.add off 1sz);
    if ((c0 = 0uy && U8.lt c1 128uy) || (c0 = 255uy && U8.lt 127uy c1)) {
      false
    } else {
      poffset := len;
      true
    }
  }
}

#pop-options
