module LowParse.Spec.Array
include LowParse.Spec.VLGen
include LowParse.Spec.List

module Seq = FStar.Seq
module L = FStar.List.Tot
module M = LowParse.Math

module U32 = FStar.UInt32

open FStar.Mul // for Prims.op_Multiply

// arith lemmas must be called explicitly
#reset-options "--z3cliopt smt.arith.nl=false"

let array_pred (#t: Type) (n: nat) (s: list t) : GTot Type0 =
  L.length s == n

let fldata_array_precond
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (array_byte_size: nat)
  (elem_count: nat)
: GTot bool
= serialize_list_precond k &&
  k.parser_kind_high = Some k.parser_kind_low &&
  elem_count * k.parser_kind_low = array_byte_size

let fldata_to_array_correct
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (x: list t)
: Lemma
  (requires (
    fldata_array_precond p array_byte_size elem_count == true /\
    parse_fldata_strong_pred (serialize_list _ s) array_byte_size x
  ))
  (ensures (
    array_pred elem_count x
  ))
= let y = serialize (serialize_list _ s) x in
  assert (parse (parse_list p) y == Some (x, array_byte_size));
  assert (Seq.length y == array_byte_size);
  list_length_constant_size_parser_correct p y;
  M.mul_reg_r elem_count (L.length x) k.parser_kind_low

inline_for_extraction
let array (t: Type) (n: nat) = (l: list t { array_pred n l } )

inline_for_extraction
let fldata_to_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true
  })
  (x: parse_fldata_strong_t (serialize_list _ s) array_byte_size)
: Tot (array t elem_count)
= [@inline_let]
  let (x' : list t) = x in
  [@inline_let]
  let _ = fldata_to_array_correct s array_byte_size elem_count x' in
  x'

let fldata_to_array_inj
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true
  })
: Lemma
  (forall (x1 x2: parse_fldata_strong_t (serialize_list _ s) array_byte_size) . {:pattern (fldata_to_array s array_byte_size elem_count u x1); (fldata_to_array s array_byte_size elem_count u x2)}
    fldata_to_array s array_byte_size elem_count u x1 == 
    fldata_to_array s array_byte_size elem_count u x2 ==>
    x1 == x2)
= ()

inline_for_extraction
let parse_array_kind
  (array_byte_size: nat)
: Tot parser_kind
= parse_fldata_kind array_byte_size parse_list_kind

let parse_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
: Pure (parser (parse_array_kind array_byte_size) (array t elem_count))
  (requires (
    fldata_array_precond p array_byte_size elem_count == true
  ))
  (ensures (fun _ -> True))
= let (u : unit { fldata_array_precond p array_byte_size elem_count == true } ) = () in
  fldata_to_array_inj s array_byte_size elem_count u;
  parse_fldata_strong (serialize_list _ s) array_byte_size `parse_synth` (fldata_to_array s array_byte_size elem_count u)

let array_to_fldata_correct
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (x: list t)
: Lemma
  (requires (
    fldata_array_precond p array_byte_size elem_count == true /\
    array_pred elem_count x
  ))
  (ensures (
    parse_fldata_strong_pred (serialize_list _ s) array_byte_size x
  ))
= let y = serialize (serialize_list _ s) x in
  list_length_constant_size_parser_correct p y

inline_for_extraction
let array_to_fldata
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true
  })
  (x: array t elem_count)
: Tot (parse_fldata_strong_t (serialize_list _ s) array_byte_size)
= [@inline_let]
  let (x' : list t) = x in
  [@inline_let]
  let _ = array_to_fldata_correct s array_byte_size elem_count x' in
  x'

let array_to_fldata_to_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (u1 u2: unit {
    fldata_array_precond p array_byte_size elem_count == true
  })
: Lemma
  (forall (x: array t elem_count) . {:pattern (fldata_to_array s array_byte_size elem_count u1 (array_to_fldata s array_byte_size elem_count u2 x))}
    fldata_to_array s array_byte_size elem_count u1 (array_to_fldata s array_byte_size elem_count u2 x) == x)
= ()

let serialize_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true
  })
: Tot (serializer (parse_array s array_byte_size elem_count))
= fldata_to_array_inj s array_byte_size elem_count u;
  array_to_fldata_to_array s array_byte_size elem_count u u;
  serialize_synth
    _
    (fldata_to_array s array_byte_size elem_count u)
    (serialize_fldata_strong (serialize_list _ s) array_byte_size)
    (array_to_fldata s array_byte_size elem_count u)
    ()

let length_serialize_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true
  })
  (x: array t elem_count)
: Lemma
  (Seq.length (serialize (serialize_array s array_byte_size elem_count u) x) == L.length x `FStar.Mul.op_Star` k.parser_kind_low)
= 
  fldata_to_array_inj s array_byte_size elem_count u;
  array_to_fldata_to_array s array_byte_size elem_count u u;
  serialize_synth_eq
    _
    (fldata_to_array s array_byte_size elem_count u)
    (serialize_fldata_strong (serialize_list _ s) array_byte_size)
    (array_to_fldata s array_byte_size elem_count u)
    ()
    x
  ;
  list_length_constant_size_parser_correct p (serialize (serialize_list _ s) x)


let vlarray_pred (#t: Type) (min max: nat) (s: list t) : GTot Type0 =
    let l = L.length s in
    min <= l /\ l <= max

let vldata_vlarray_precond
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (elem_count_min: nat)
  (elem_count_max: nat)
: GTot bool
= (* constant-size serializable parser for elements *)
     serialize_list_precond k &&
     k.parser_kind_high = Some k.parser_kind_low &&
  (* vldata *)
     array_byte_size_min <= array_byte_size_max &&
     array_byte_size_max > 0 &&
     array_byte_size_max < 4294967296 &&
  (* vlarray *)
     elem_count_min <= elem_count_max &&
     0 < elem_count_max &&
  (* ceil (array_byte_size_min / k.parser_kind_low) = elem_count_min *)
     elem_count_min * k.parser_kind_low < array_byte_size_min + k.parser_kind_low &&
     array_byte_size_min <= elem_count_min * k.parser_kind_low &&
  (* floor (array_byte_size_max / k.parser_kind_low) = elem_count_max *)
     elem_count_max * k.parser_kind_low <= array_byte_size_max &&
     array_byte_size_max < elem_count_max * k.parser_kind_low + k.parser_kind_low

let vldata_vlarray_precond_parser_kind_low
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (elem_count_min: nat)
  (elem_count_max: nat)
: Lemma
  (requires (vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max))
  (ensures (k.parser_kind_low < 4294967296))
  [SMTPat (k.parser_kind_low); SMTPat (vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max)]
= M.lemma_mult_le_right k.parser_kind_low 1 elem_count_max

let vldata_to_vlarray_correct
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (x: list t)
: Lemma
  (requires (
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true /\
    parse_bounded_vldata_strong_pred array_byte_size_min array_byte_size_max (serialize_list _ s) x
  ))
  (ensures (
    vlarray_pred elem_count_min elem_count_max x
  ))
= let y = serialize (serialize_list _ s) x in
  let l = L.length x in
  assert (parse (parse_list p) y == Some (x, Seq.length y));
  list_length_constant_size_parser_correct p y;
  M.lt_mul_add_reg_r elem_count_min l k.parser_kind_low;
  M.lt_mul_add_reg_r l elem_count_max k.parser_kind_low

inline_for_extraction
let vlarray (t: Type) (min max: nat) =
  (l: list t { min <= L.length l /\ L.length l <= max } )

inline_for_extraction
let vldata_to_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
  (x: parse_bounded_vldata_strong_t array_byte_size_min array_byte_size_max (serialize_list _ s))
: Tot (vlarray t elem_count_min elem_count_max)
= [@inline_let]
  let x' : list t = x in
  [@inline_let]
  let _ = vldata_to_vlarray_correct array_byte_size_min array_byte_size_max s elem_count_min elem_count_max x' in
  x'

let vldata_to_vlarray_inj
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Lemma
  (forall (x1 x2: parse_bounded_vldata_strong_t array_byte_size_min array_byte_size_max (serialize_list _ s)) .
    {:pattern
      (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x1);
      (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x2)}
    vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x1 ==
    vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x2 ==>
    x1 == x2)
= ()

inline_for_extraction
let parse_vlarray_kind
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_min <= array_byte_size_max /\ array_byte_size_max > 0 /\ array_byte_size_max < 4294967296 } )
  (hk: parser_kind)
: Tot parser_kind
= parse_bounded_vlgen_kind hk array_byte_size_min array_byte_size_max parse_list_kind

let parse_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_min <= array_byte_size_max } )
  (#hk: parser_kind)
  (hp: parser hk (bounded_int32 array_byte_size_min array_byte_size_max))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Tot (parser (parse_vlarray_kind array_byte_size_min array_byte_size_max hk) (vlarray t elem_count_min elem_count_max))
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  parse_bounded_vlgen array_byte_size_min array_byte_size_max hp (serialize_list _ s)
  `parse_synth`
  vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u

let parse_vlarray_eq_some
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_min <= array_byte_size_max })
  (#hk: parser_kind)
  (hp: parser hk (bounded_int32 array_byte_size_min array_byte_size_max))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
  (input: bytes)
: Lemma
  (requires (
    Some? (parse (parse_vlarray array_byte_size_min array_byte_size_max hp s elem_count_min elem_count_max u) input)
  ))
  (ensures (
    let pi = parse hp input in
    Some? pi /\ (
    let Some (len, c_len) = pi in
    array_byte_size_min <= U32.v len /\ U32.v len <= array_byte_size_max /\ (
    let input1 = Seq.slice input c_len (Seq.length input) in
    U32.v len <= Seq.length input1 /\ (
    let input2 = Seq.slice input1 0 (U32.v len) in
    let pl = parse (parse_list p) input2 in
    Some? pl /\ (
    let Some (l, c_l) = pl in
    c_l == U32.v len /\
    vlarray_pred elem_count_min elem_count_max l /\
    parse (parse_vlarray array_byte_size_min array_byte_size_max hp s elem_count_min elem_count_max u) input == Some (l, c_len + c_l)
  ))))))
= 
  parser_kind_prop_equiv k p;
  vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ();
  parse_synth_eq (parse_bounded_vlgen array_byte_size_min array_byte_size_max hp (serialize_list _ s)) (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) input;
  parse_bounded_vlgen_unfold array_byte_size_min array_byte_size_max hp (serialize_list _ s) input;
  parser_kind_prop_equiv parse_list_kind (parse_list p)

let vlarray_to_vldata_correct
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (x: list t)
: Lemma
  (requires (
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true /\
    vlarray_pred elem_count_min elem_count_max x
  ))
  (ensures (
    parse_bounded_vldata_strong_pred array_byte_size_min array_byte_size_max (serialize_list _ s) x
  ))
= let y = serialize (serialize_list _ s) x in
  let l = L.length x in
  assert (parse (parse_list p) y == Some (x, Seq.length y));
  list_length_constant_size_parser_correct p y;
  M.lemma_mult_le_right k.parser_kind_low elem_count_min l;
  M.lemma_mult_le_right k.parser_kind_low l elem_count_max

inline_for_extraction
let vlarray_to_vldata
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
  (x: vlarray t elem_count_min elem_count_max)
: Tot (parse_bounded_vldata_strong_t array_byte_size_min array_byte_size_max (serialize_list _ s))
= [@inline_let]
  let x' : list t = x in
  [@inline_let]
  let _ = vlarray_to_vldata_correct array_byte_size_min array_byte_size_max s elem_count_min elem_count_max x' in
  x'

let vlarray_to_vldata_to_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Lemma
  (forall (x: vlarray t elem_count_min elem_count_max) .
    {:pattern
      (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
        (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x))
    }
    vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
      (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    == x)
= ()

let serialize_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_min <= array_byte_size_max })
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 array_byte_size_min array_byte_size_max))
  (hs: serializer hp { hk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Tot (serializer (parse_vlarray array_byte_size_min array_byte_size_max hp s elem_count_min elem_count_max u))
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  vlarray_to_vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  serialize_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (serialize_bounded_vlgen array_byte_size_min array_byte_size_max hs (serialize_list _ s))
    (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    ()

let length_serialize_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_min <= array_byte_size_max })
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 array_byte_size_min array_byte_size_max))
  (hs: serializer hp { hk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
  (x: vlarray t elem_count_min elem_count_max)
: Lemma
  ( let l = L.length x `FStar.Mul.op_Star` k.parser_kind_low in
    FStar.UInt.fits l 32 /\
    in_bounds array_byte_size_min array_byte_size_max (U32.uint_to_t l) /\
    Seq.length (serialize (serialize_vlarray array_byte_size_min array_byte_size_max hs s elem_count_min elem_count_max u) x) == Seq.length (serialize hs (U32.uint_to_t l)) + l)
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  vlarray_to_vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  serialize_synth_eq
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (serialize_bounded_vlgen array_byte_size_min array_byte_size_max hs (serialize_list _ s))
    (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    ()
    x
  ;
  serialize_bounded_vlgen_unfold array_byte_size_min array_byte_size_max hs (serialize_list _ s) x;
  list_length_constant_size_parser_correct p (serialize (serialize_list _ s) x)
