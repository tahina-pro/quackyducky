module CBOR.Pulse.Raw.EverParse.Serialized.Rust
#lang-pulse
friend CBOR.Pulse.Raw.Format.Match
friend CBOR.Pulse.Raw.EverParse.Serialized.Base

module Read = CBOR.Pulse.Raw.EverParse.Serialized.Base
module Format = CBOR.Pulse.Raw.EverParse.Format

fn cbor_match_string_intro_aux (_: unit) : cbor_match_string_intro_aux_t #_ Match.cbor_match_string =
  (typ: _)
  (len: _)
  (input: _)
  (#pm: _)
  (#v: _)
{
    S.pts_to_len input;
    let res : Match.cbor_string = {
      cbor_string_type = typ;
      cbor_string_size = len.size;
      cbor_string_ptr = input;
      cbor_string_perm = pm;
    };
    Match.cbor_match_string_intro_aux input res (String typ len v);
    res
}

fn cbor_read
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
  requires
    pts_to_serialized serialize_raw_data_item input #pm v
  returns res: cbor_serialized_raw Match.cbor_string Match.cbor_serialized
  ensures
      cbor_serialized_raw_match Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged 1.0R res v **
      Trade.trade
        (cbor_serialized_raw_match Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged 1.0R res v)
        (pts_to_serialized serialize_raw_data_item input #pm v)
{
  let mut ph = Read.dummy_header;
  let pc = Format.get_header_and_contents input ph;
  let h = !ph;
  let typ = ((get_header_initial_byte h).major_type);
  if (typ = cbor_major_type_uint64 || typ = cbor_major_type_neg_int64) {
    Trade.elim _ _;
    let i = get_int64_value v h;
    cbor_serialized_raw_match_int_intro_trade Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged (pts_to_serialized serialize_raw_data_item input #pm v) typ i
  }
  else if (typ = cbor_major_type_text_string || typ = cbor_major_type_byte_string) {
    let i = get_string_length v h;
    Format.get_string_payload pc v;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res = cbor_serialized_raw_match_string_intro (cbor_match_string_intro_aux ()) Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged typ i pc;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else if (typ = cbor_major_type_tagged) {
    let tag = get_tagged_tag v h;
    Format.get_tagged_payload pc v;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let rest : Match.cbor_serialized = {
      cbor_serialized_header = tag;
      cbor_serialized_payload = pc;
      cbor_serialized_perm = pm;
    };
    Read.cbor_match_serialized_tagged_intro_aux tag pc rest v;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res : cbor_serialized_raw Match.cbor_string Match.cbor_serialized = CBOR_SerializedCase_Serialized_Tagged rest;
    Trade.rewrite_with_trade
      (Match.cbor_match_serialized_tagged rest 1.0R v)
      (cbor_serialized_raw_match Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged 1.0R res v);
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else if (typ = cbor_major_type_array) {
    let len = get_array_length v h;
    Format.get_array_payload pc v;
    with n (v': LowParse.Spec.VCList.nlist n raw_data_item) . assert (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) pc #pm v');
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let resa : Match.cbor_serialized = {
      cbor_serialized_header = len;
      cbor_serialized_payload = pc;
      cbor_serialized_perm = pm;
    };
    Read.cbor_match_serialized_array_intro_aux len pc #n #v' #pm resa (Ghost.reveal v) ();
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res: cbor_serialized_raw Match.cbor_string Match.cbor_serialized = CBOR_SerializedCase_Serialized_Array resa;
    Trade.rewrite_with_trade
      (Match.cbor_match_serialized_array resa 1.0R v)
      (cbor_serialized_raw_match Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged 1.0R res v);
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else if (typ = cbor_major_type_map) {
    let len = get_map_length v h;
    Format.get_map_payload pc v;
    with n (v': LowParse.Spec.VCList.nlist n (raw_data_item & raw_data_item)) . assert (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) pc #pm v');
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let resa: Match.cbor_serialized = {
      cbor_serialized_header = len;
      cbor_serialized_payload = pc;
      cbor_serialized_perm = pm;
    };
    Read.cbor_match_serialized_map_intro_aux len pc #n #v' #pm resa (Ghost.reveal v) ();
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res : cbor_serialized_raw Match.cbor_string Match.cbor_serialized = CBOR_SerializedCase_Serialized_Map resa;
    Trade.rewrite_with_trade
      (Match.cbor_match_serialized_map resa 1.0R v)
      (cbor_serialized_raw_match Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged 1.0R res v);
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else {
    assert (pure (typ == cbor_major_type_simple_value));
    Trade.elim _ _;
    let i = get_simple_value v h;
    cbor_serialized_raw_match_simple_intro_trade Match.cbor_match_string Match.cbor_match_serialized_array Match.cbor_match_serialized_map Match.cbor_match_serialized_tagged (pts_to_serialized serialize_raw_data_item input #pm v) i
  }
}
