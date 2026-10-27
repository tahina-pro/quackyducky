module ASN1.Spec.Value.Enc

(* The DER encoding of generic ASN.1 values, as a Tot function, and the
   proof that the bytes consumed by the ANY parser are exactly the encoding
   of the value it returns *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.SeqBytes
open LowParse.Tot.List

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.LengthU32
open ASN1.Spec.Value

module RV = LowParse.Spec.RecursiveVLGen
module LPDER = LowParse.Spec.DER
module LPB = LowParse.Spec.BoundedInt
module E = FStar.Endianness
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Seq = FStar.Seq

(* Lengths (X.690 8.1.3, 10.1) *)

let enc_len (y: U32.t) : Tot bytes =
  let x = LPDER.tag_of_der_length32_impl y in
  let s1 = Seq.create 1 x in
  if x `U8.lt` 128uy
  then s1
  else if x = 129uy
  then s1 `Seq.append` Seq.create 1 (Cast.uint32_to_uint8 y)
  else s1 `Seq.append` E.n_to_be (LPB.log256' (U32.v y)) (U32.v y)

let enc_len_eq (y: U32.t)
: Lemma
  (enc_len y == serialize serialize_asn1_length_u32_t y)
= LPDER.serialize_bounded_der_length32_unfold 0 4294967295 y;
  let x = LPDER.tag_of_der_length32_impl y in
  if x `U8.lt` 128uy || x = 129uy
  then Seq.lemma_eq_elim (enc_len y) (serialize serialize_asn1_length_u32_t y)
  else begin
    LPB.serialize_bounded_integer_spec (LPB.log256' (U32.v y)) y;
    Seq.lemma_eq_elim (enc_len y) (serialize serialize_asn1_length_u32_t y)
  end

let parse_enc_len (y: U32.t) (suffix: bytes)
: Lemma
  (parse parse_asn1_length_u32_t (enc_len y `Seq.append` suffix) == Some (y, Seq.length (enc_len y)))
= enc_len_eq y;
  parse_strong_prefix #parse_asn1_length_u32_t_kind parse_asn1_length_u32_t (enc_len y) (enc_len y `Seq.append` suffix)

let parse_len_consumed (b: bytes)
: Lemma
  (match parse parse_asn1_length_u32_t b with
   | Some (y, c) -> Seq.slice b 0 c == enc_len y
   | None -> True)
= match parse parse_asn1_length_u32_t b with
  | Some (y, c) ->
    let e = enc_len y in
    parse_enc_len y Seq.empty;
    Seq.append_empty_r e;
    parse_injective #parse_asn1_length_u32_t_kind parse_asn1_length_u32_t b e;
    Seq.lemma_eq_elim (Seq.slice e 0 (Seq.length e)) e
  | None -> ()

let enc_len_nat (n: nat) : Tot bytes =
  if n < 4294967296 then enc_len (U32.uint_to_t n) else Seq.empty

(* Values *)

let rec asn1_value_enc (v: asn1_value) : Tot bytes (decreases v) =
  match v with
  | ASN1_VALUE_PRIMITIVE id b ->
    asn1_id_enc id `Seq.append` (enc_len_nat (Seq.length b) `Seq.append` b)
  | ASN1_VALUE_CONSTRUCTED id l ->
    let c = asn1_value_list_enc l in
    asn1_id_enc id `Seq.append` (enc_len_nat (Seq.length c) `Seq.append` c)

and asn1_value_list_enc (l: list asn1_value) : Tot bytes (decreases l) =
  match l with
  | [] -> Seq.empty
  | v :: q -> asn1_value_enc v `Seq.append` asn1_value_list_enc q

let parse_any_identifier_consumed (b: bytes)
: Lemma
  (match parse parse_asn1_any_identifier b with
   | Some (id, c) -> Seq.slice b 0 c == asn1_id_enc id /\ parse parse_asn1_identifier_U32 b == Some ((id <: asn1_id_t), c)
   | None -> (match parse parse_asn1_identifier_U32 b with Some (id, _) -> asn1_any_id_valid id == false | None -> True))
= lemma_parse_asn1_identifier_first_inj ();
  parse_filter_eq (parse_u8 `and_then` parse_asn1_identifier_first) asn1_any_id_valid b;
  parse_asn1_identifier_U32_consumed b

let pv = RV.parse_rec_vlgen asn1_value_param

let parse_asn1_any_leaf_eq (id: asn1_any_id_t) (b: bytes)
: Lemma
  (parse (parse_asn1_any_leaf id) b == (if asn1_any_leaf_ok id b then Some (b, Seq.length b) else None))
= parse_synth_eq (parse_seq_all_bytes `parse_filter` asn1_any_leaf_ok id) (synth_asn1_any_leaf id) b;
  parse_filter_eq parse_seq_all_bytes (asn1_any_leaf_ok id) b;
  parse_seq_all_bytes_correct ()

(* The contents of a value, after its header *)
let rec_vlgen_body_eq (id: asn1_any_id_t) (b: bytes)
: Lemma
  (parse (RV.rec_vlgen_body asn1_value_param pv id) b == (
    if CONSTRUCTED? id.f
    then match parse (tot_parse_list pv) b with
      | Some (l, c) -> Some (RV.RNode l, c)
      | None -> None
    else if asn1_any_leaf_ok id b then Some (RV.RLeaf b, Seq.length b) else None))
= if CONSTRUCTED? id.f
  then tot_parse_synth_eq (tot_parse_list pv) (RV.RNode #asn1_value #asn1_octetstring_t) b
  else begin
    tot_parse_synth_eq (parse_asn1_any_leaf id) (RV.RLeaf #asn1_value #asn1_octetstring_t) b;
    parse_asn1_any_leaf_eq id b
  end

let slice_3 (b: bytes) (c1 c2 len: nat)
: Lemma
  (requires (c1 + c2 + len <= Seq.length b))
  (ensures (Seq.slice b 0 (c1 + c2 + len) == Seq.slice b 0 c1 `Seq.append` (Seq.slice (Seq.slice b c1 (Seq.length b)) 0 c2 `Seq.append` Seq.slice b (c1 + c2) (c1 + c2 + len))))
= Seq.lemma_eq_elim (Seq.slice b 0 (c1 + c2 + len)) (Seq.slice b 0 c1 `Seq.append` (Seq.slice (Seq.slice b c1 (Seq.length b)) 0 c2 `Seq.append` Seq.slice b (c1 + c2) (c1 + c2 + len)))

let slice_2 (b: bytes) (n: nat)
: Lemma
  (requires (n <= Seq.length b))
  (ensures (b == Seq.slice b 0 n `Seq.append` Seq.slice b n (Seq.length b)))
= Seq.lemma_eq_elim b (Seq.slice b 0 n `Seq.append` Seq.slice b n (Seq.length b))

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec parse_asn1_value_consumed (b: bytes)
: Lemma
  (ensures (match parse pv b with
   | Some (v, n) -> Seq.slice b 0 n == asn1_value_enc v
   | None -> True))
  (decreases %[Seq.length b; 0])
= RV.parse_rec_vlgen_eq asn1_value_param b;
  match parse pv b with
  | None -> ()
  | Some (v, n) ->
    parse_any_identifier_consumed b;
    let Some (id, c1) = parse parse_asn1_any_identifier b in
    let b1 = Seq.slice b c1 (Seq.length b) in
    parse_len_consumed b1;
    let Some (len, c2) = parse parse_asn1_length_u32_t b1 in
    let hs = c1 + c2 in
    parser_kind_prop_equiv asn1_any_identifier_kind parse_asn1_any_identifier;
    assert (c1 > 0);
    assert (RV.rec_vlgen_header asn1_value_param b == Some (id, hs, U32.v len));
    assert (hs + U32.v len <= Seq.length b /\ n == hs + U32.v len);
    let ct = Seq.slice b hs (hs + U32.v len) in
    rec_vlgen_body_eq id ct;
    assert (U32.uint_to_t (U32.v len) == len);
    if CONSTRUCTED? id.f
    then begin
      parse_asn1_value_list_consumed ct;
      let Some (l, _) = parse (tot_parse_list pv) ct in
      assert (v == ASN1_VALUE_CONSTRUCTED id l)
    end else begin
      assert (v == ASN1_VALUE_PRIMITIVE id ct)
    end;
    slice_3 b c1 c2 (U32.v len)

and parse_asn1_value_list_consumed (b: bytes)
: Lemma
  (ensures (match parse (tot_parse_list pv) b with
   | Some (l, n) -> n == Seq.length b /\ b == asn1_value_list_enc l
   | None -> True))
  (decreases %[Seq.length b; 1])
= tot_parse_list_eq pv b;
  if Seq.length b = 0
  then Seq.lemma_eq_elim b Seq.empty
  else match parse pv b with
  | None -> ()
  | Some (v, n) ->
    if n = 0 then ()
    else begin
      parse_asn1_value_consumed b;
      let b' = Seq.slice b n (Seq.length b) in
      parse_asn1_value_list_consumed b';
      parser_kind_prop_equiv (parse_list_kind true) (tot_parse_list pv);
      slice_2 b n
    end
#pop-options

let parse_asn1_value_consumed' (b: bytes)
: Lemma
  (match parse parse_asn1_value b with
   | Some (v, n) -> Seq.slice b 0 n == asn1_value_enc v
   | None -> True)
= parse_asn1_value_consumed b
