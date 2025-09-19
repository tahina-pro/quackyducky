module CBOR.Pulse.Raw.Format.Match.C
#lang-pulse
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.VCList
open LowParse.Pulse.C

let cbor_match_serialized_payload_array
  a len p r
= exists* n (r': nlist n raw_data_item) .
    pts_to_serialized (serialize_nlist n serialize_raw_data_item) a #p r' **
    pure (r == r' /\ SZ.v len == Seq.length (serialize (serialize_nlist n serialize_raw_data_item) r'))

let cbor_match_serialized_payload_map
  a len p r
= exists* n (r' : nlist n (raw_data_item & raw_data_item)) .
    pts_to_serialized (serialize_nlist n (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item)) a #p r' **
    pure (r == r' /\ SZ.v len == Seq.length (serialize (serialize_nlist n (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item)) r'))

let cbor_match_serialized_payload_tagged
  a len p r
= pts_to_serialized serialize_raw_data_item a #p r **
  pure (SZ.v len == Seq.length (serialize (serialize_raw_data_item) r))

ghost
fn cbor_match_serialized_payload_array_share
  a len p r
requires
    (cbor_match_serialized_payload_array a len p r)
ensures
    (
      cbor_match_serialized_payload_array a len (p /. 2.0R) r **
      cbor_match_serialized_payload_array a len (p /. 2.0R) r
    )

{
  unfold (cbor_match_serialized_payload_array a len p r);
  with n (r': nlist n raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n serialize_raw_data_item) a #p r');
  pts_to_serialized_share (serialize_nlist n serialize_raw_data_item) a;
  fold (cbor_match_serialized_payload_array a len (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_array a len (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_array_gather
  a len
  (p1: perm)
  (r1: list raw_data_item)
  (p2: perm)
  (r2: list raw_data_item)
requires
    (cbor_match_serialized_payload_array a len p1 r1 **
      cbor_match_serialized_payload_array a len p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_array a len (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_array a len p1 r1);
  with n1 (r1': nlist n1 raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) a #p1 r1');
  unfold (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) a #p1 r1');
  serialize_nlist_serialize_list n1 serialize_raw_data_item r1';
  unfold (cbor_match_serialized_payload_array a len p2 r2);
  with n2 (r2': nlist n2 raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) a #p2 r2');
  unfold (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) a #p2 r2');
  serialize_nlist_serialize_list n2 serialize_raw_data_item r2';
  A.gather a;
  serializer_injective _ (serialize_list _ serialize_raw_data_item) r1' r2';
  fold (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) a #(p1 +. p2) r1');
  fold (cbor_match_serialized_payload_array a len (p1 +. p2) r1);
}

ghost
fn cbor_match_serialized_payload_map_share
  a len
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
requires
    (cbor_match_serialized_payload_map a len p r)
ensures
    (
      cbor_match_serialized_payload_map a len (p /. 2.0R) r **
      cbor_match_serialized_payload_map a len (p /. 2.0R) r
    )
{
  unfold (cbor_match_serialized_payload_map a len p r);
  with n (r': nlist n (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a #p r');
  pts_to_serialized_share (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a;
  fold (cbor_match_serialized_payload_map a len (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_map a len (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_map_gather
  a len
  (p1: perm)
  (r1: list (raw_data_item & raw_data_item))
  (p2: perm)
  (r2: list (raw_data_item & raw_data_item))
requires
    (cbor_match_serialized_payload_map a len p1 r1 **
      cbor_match_serialized_payload_map a len p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_map a len (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_map a len p1 r1);
  with n1 (r1': nlist n1 (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a #p1 r1');
  unfold (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a #p1 r1');
  serialize_nlist_serialize_list n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) r1';
  unfold (cbor_match_serialized_payload_map a len p2 r2);
  with n2 (r2': nlist n2 (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a #p2 r2');
  unfold (pts_to_serialized (serialize_nlist n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a #p2 r2');
  serialize_nlist_serialize_list n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) r2';
  A.gather a;
  serializer_injective _ (serialize_list _ (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) r1' r2';
  fold (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a #(p1 +. p2) r1');
  fold (cbor_match_serialized_payload_map a len (p1 +. p2) r1);
}

ghost
fn cbor_match_serialized_payload_tagged_share
  a len
  (p: perm)
  (r: raw_data_item)
requires
    (cbor_match_serialized_payload_tagged a len p r)
ensures
    (
      cbor_match_serialized_payload_tagged a len (p /. 2.0R) r **
      cbor_match_serialized_payload_tagged a len (p /. 2.0R) r
    )
{
  unfold (cbor_match_serialized_payload_tagged a len p r);
  pts_to_serialized_share serialize_raw_data_item a;
  fold (cbor_match_serialized_payload_tagged a len (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_tagged a len (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_tagged_gather
  a len 
  (p1: perm)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
requires
    (cbor_match_serialized_payload_tagged a len p1 r1 **
      cbor_match_serialized_payload_tagged a len p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_tagged a len (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_tagged a len p1 r1);
  unfold (cbor_match_serialized_payload_tagged a len p2 r2);
  pts_to_serialized_gather serialize_raw_data_item a;
  fold (cbor_match_serialized_payload_tagged a len (p1 +. p2) r1);
}

fn cbor_match_serialized_payload_array_copy
  a len
  (p: perm)
  (r: Ghost.erased (list raw_data_item))
  a'
norewrite
requires
    (exists* v' . A.pts_to a' v' **
      cbor_match_serialized_payload_array a len p r **
      pure (Seq.length v' == SZ.v len)
    )
ensures
    (
      cbor_match_serialized_payload_array a len p r **
      cbor_match_serialized_payload_array a' len 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_array a' len 1.0R r)
        (exists* v' . pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )
{
  unfold (cbor_match_serialized_payload_array a len p r);
  with n r' . assert (
    pts_to_serialized (serialize_nlist n serialize_raw_data_item) a #p r'
  );
  pts_to_serialized_copy #(nlist n raw_data_item) #(parse_nlist_kind n parse_raw_data_item_kind) #(coerce_eq () (parse_nlist n parse_raw_data_item)) (coerce_eq () (serialize_nlist n serialize_raw_data_item <: serializer (parse_nlist n parse_raw_data_item))) a len a';
  fold (cbor_match_serialized_payload_array a len p r);
  fold (cbor_match_serialized_payload_array a' len 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_array a' len 1.0R r)
      (exists* v' . A.pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_array a' len 1.0R r);
    with n r' . assert (
      pts_to_serialized (serialize_nlist n serialize_raw_data_item) a' r'
    );
    unfold (pts_to_serialized (serialize_nlist n serialize_raw_data_item) a' r')
  };
}

fn cbor_match_serialized_payload_map_copy
  a len
  (p: perm)
  (r: Ghost.erased (list (raw_data_item & raw_data_item)))
  a'
norewrite
requires
    (exists* v' . A.pts_to a' v' **
      cbor_match_serialized_payload_map a len p r **
      pure (Seq.length v' == SZ.v len)
    )
ensures
    (
      cbor_match_serialized_payload_map a len p r **
      cbor_match_serialized_payload_map a' len 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_map a' len 1.0R r)
        (exists* v' . pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )
{
  unfold (cbor_match_serialized_payload_map a len p r);
  with n r' . assert (
    pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a #p r'
  );
  pts_to_serialized_copy #(nlist n (raw_data_item & raw_data_item)) #(parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) #(coerce_eq () (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item))) (coerce_eq () (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) <: serializer (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item)))) a len a';
  fold (cbor_match_serialized_payload_map a len p r);
  fold (cbor_match_serialized_payload_map a' len 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_map a' len 1.0R r)
      (exists* v' . A.pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_map a' len 1.0R r);
    with n r' . assert (
      pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a' r'
    );
    unfold (pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) a' r')
  };
}

fn cbor_match_serialized_payload_tagged_copy
  a len
  (p: perm)
  (r: Ghost.erased (raw_data_item))
  a'
norewrite
requires
    (exists* v' . A.pts_to a' v' **
      cbor_match_serialized_payload_tagged a len p r **
      pure (Seq.length v' == SZ.v len)
    )
ensures
    (
      cbor_match_serialized_payload_tagged a len p r **
      cbor_match_serialized_payload_tagged a' len 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_tagged a' len 1.0R r)
        (exists* v' . pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )
{
  unfold (cbor_match_serialized_payload_tagged a len p r);
  with r' . assert (
    pts_to_serialized (serialize_raw_data_item) a #p r'
  );
  pts_to_serialized_copy serialize_raw_data_item a len a';
  fold (cbor_match_serialized_payload_tagged a len p r);
  fold (cbor_match_serialized_payload_tagged a' len 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_tagged a' len 1.0R r)
      (exists* v' . A.pts_to a' v' ** pure (Seq.length v' == SZ.v len))
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_tagged a' len 1.0R r);
    with r' . assert (
      pts_to_serialized (serialize_raw_data_item) a' r'
    );
    unfold (pts_to_serialized (serialize_raw_data_item) a' r')
  };
}
