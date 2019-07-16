module LowParse.SLow.Array
include LowParse.SLow.FLData
include LowParse.SLow.VLGen
include LowParse.SLow.List
include LowParse.Spec.Array

module U32 = FStar.UInt32

inline_for_extraction
let parse32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t { U32.v array_byte_size32 == array_byte_size } )
  (elem_count: nat)
  (u : unit { fldata_array_precond p array_byte_size elem_count == true } )
: Tot (parser32 (parse_array s array_byte_size elem_count))
= [@inline_let]
  let _ =
    fldata_to_array_inj s array_byte_size elem_count u
  in
  parse32_synth
    _
    (fldata_to_array s array_byte_size elem_count u)
    (fun x -> fldata_to_array s array_byte_size elem_count u x)
    (parse32_fldata_strong
      (serialize_list _ s)
      (parse32_list p32)
      array_byte_size
      array_byte_size32
    )
    ()

inline_for_extraction
let serialize32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (array_byte_size: nat { array_byte_size < 4294967296 } )
  (elem_count: nat)
  (u : unit { fldata_array_precond p array_byte_size elem_count == true } )
: Tot (serializer32 (serialize_array s array_byte_size elem_count u))
= [@inline_let]
  let _ =
    fldata_to_array_inj s array_byte_size elem_count u
  in
  [@inline_let]
  let _ =
    array_to_fldata_to_array s array_byte_size elem_count u
  in
  serialize32_synth
    _
    (fldata_to_array s array_byte_size elem_count u)
    _
    (serialize32_fldata_strong
      (partial_serialize32_list _ _ s32 ())
      array_byte_size
    )
    (array_to_fldata s array_byte_size elem_count u)
    (fun x -> array_to_fldata s array_byte_size elem_count u x)
    ()

inline_for_extraction
let size32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t { U32.v array_byte_size32 == array_byte_size } )
  (elem_count: nat)
  (u : unit { fldata_array_precond p array_byte_size elem_count == true } )
: Tot (size32 (serialize_array s array_byte_size elem_count u))
= size32_constant (serialize_array s array_byte_size elem_count u) array_byte_size32 ()


inline_for_extraction
let parse32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_min32: U32.t { U32.v array_byte_size_min32 == array_byte_size_min } )
  (array_byte_size_max: nat { array_byte_size_min <= array_byte_size_max } )
  (array_byte_size_max32: U32.t { U32.v array_byte_size_max32 == array_byte_size_max } )
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 array_byte_size_min array_byte_size_max))
  (hp32: parser32 hp)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Tot (parser32 (parse_vlarray array_byte_size_min array_byte_size_max hp s elem_count_min elem_count_max u))
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  parse32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    (parse32_bounded_vlgen
      array_byte_size_min
      array_byte_size_min32
      array_byte_size_max
      array_byte_size_max32
      hp32
      (serialize_list _ s)
      (parse32_list p32)
    )
    ()

inline_for_extraction
let serialize32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_min <= array_byte_size_max })
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 array_byte_size_min array_byte_size_max))
  (#hs: serializer hp)
  (hs32: serializer32 hs { hk.parser_kind_subkind == Some ParserStrong /\ Some? hk.parser_kind_high /\ Some?.v hk.parser_kind_high + array_byte_size_max < 4294967296 } ) // size bound necessary for FStar.Bytes.concat
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Tot (serializer32 (serialize_vlarray array_byte_size_min array_byte_size_max hs s elem_count_min elem_count_max u))
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  [@inline_let]
  let _ =
    vlarray_to_vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  serialize32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    _
    (serialize32_bounded_vlgen
      array_byte_size_min
      array_byte_size_max
      hs32
      (partial_serialize32_list _ _ s32 ())
    )
    (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    ()

inline_for_extraction
let size32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_min <= array_byte_size_max } )
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 array_byte_size_min array_byte_size_max))
  (#hs: serializer hp)
  (hs32: size32 hs { hk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
  (elem_byte_size32: U32.t { U32.v elem_byte_size32 == k.parser_kind_low } )
: Tot (size32 (serialize_vlarray array_byte_size_min array_byte_size_max hs s elem_count_min elem_count_max u))
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  [@inline_let]
  let _ =
    vlarray_to_vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  size32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (serialize_bounded_vlgen
      array_byte_size_min
      array_byte_size_max
      hs
      (serialize_list _ s)
    )
    (size32_bounded_vlgen
      array_byte_size_min
      array_byte_size_max
      hs32
      (size32_list #_ #_ #_ #s (size32_constant s elem_byte_size32 ()) ())
    )
    (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    ()
