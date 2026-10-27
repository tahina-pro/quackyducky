module ASN1.Spec.Conformance.Examples

(* The X.509 certificate and CRL schemas are well-formed, so their typed
   parsers accept exactly the generic DER values that conform to them. *)

open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.Conformance

let x509_certificate_wf () : Lemma (wf ASN1.X509.x509_certificate) =
  assert (wf ASN1.X509.x509_certificate == true)
    by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

let crl_wf () : Lemma (wf ASN1.CRL.cRLCertificateList) =
  assert (wf ASN1.CRL.cRLCertificateList == true)
    by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

let x509_certificate_conformance (b: bytes)
: Lemma
  (conformance_spec ASN1.X509.x509_certificate b)
= x509_certificate_wf ();
  conformance_correct ASN1.X509.x509_certificate b

let crl_conformance (b: bytes)
: Lemma
  (conformance_spec ASN1.CRL.cRLCertificateList b)
= crl_wf ();
  conformance_correct ASN1.CRL.cRLCertificateList b

(* The library schemas for EXTERNAL, EMBEDDED PDV and CHARACTER STRING *)

let external_wf () : Lemma (wf ASN1.UniversalTypes.asn1_external) =
  assert (wf ASN1.UniversalTypes.asn1_external == true)
    by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

let embedded_pdv_wf () : Lemma (wf ASN1.UniversalTypes.asn1_embedded_pdv) =
  assert (wf ASN1.UniversalTypes.asn1_embedded_pdv == true)
    by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

let character_string_wf () : Lemma (wf ASN1.UniversalTypes.asn1_character_string) =
  assert (wf ASN1.UniversalTypes.asn1_character_string == true)
    by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())
