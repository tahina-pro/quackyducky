module LowParse.Low.Bytes
include LowParse.Spec.Bytes
include LowParse.Low.Combinators
include LowParse.Low.VLData
include LowParse.Low.Int

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module B = LowStar.Buffer
module BY = LowParse.Bytes32
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8

inline_for_extraction
let validate_flbytes
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz /\ sz <= U32.v validator_max_length } )
: Tot (validator (parse_flbytes sz))
= validate_total_constant_size (parse_flbytes sz) sz32 ()

inline_for_extraction
let jump_flbytes
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (jumper (parse_flbytes sz))
= jump_constant_size (parse_flbytes sz) sz32 ()

let valid_flbytes_intro
  (h: HS.mem)
  (sz: nat { sz < 4294967296 } )
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (U32.v pos + sz <= U32.v s.len /\ live_slice h s))
  (ensures (
    valid_content_pos (parse_flbytes sz) h s pos (BY.hide (B.as_seq h (B.gsub s.base pos (U32.uint_to_t sz)))) (pos `U32.add` U32.uint_to_t sz)
  ))
= valid_facts (parse_flbytes sz) h s pos

let valid_pos_flbytes_elim
  (h: HS.mem)
  (sz: nat { sz < 4294967296 } )
  (s: slice)
  (pos pos' : U32.t)
: Lemma
  (requires (valid_pos (parse_flbytes sz) h s pos pos'))
  (ensures (U32.v pos + sz == U32.v pos'))
  [SMTPat (valid_pos (parse_flbytes sz) h s pos pos')]
= valid_facts (parse_flbytes sz) h s pos

let valid_flbytes_elim
  (h: HS.mem)
  (sz: nat { sz < 4294967296 } )
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (valid (parse_flbytes sz) h s pos))
  (ensures (
    valid_content_pos (parse_flbytes sz) h s pos (BY.hide (B.as_seq h (B.gsub s.base pos (U32.uint_to_t sz)))) (pos `U32.add` U32.uint_to_t sz)
  ))
= valid_flbytes_intro h sz s pos

let clens_flbytes_slice
  (sz: nat)
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (clens (BY.lbytes sz) (BY.lbytes (U32.v to - U32.v from)))
= {
  clens_cond =  (fun _ -> True);
  clens_get = (fun (x: BY.lbytes sz) -> (BY.slice x from to <: BY.lbytes (U32.v to - U32.v from)));
}

let gaccessor_flbytes_slice
  (sz: nat { sz < 4294967296 } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (gaccessor (parse_flbytes sz) (parse_flbytes (U32.v to - U32.v from)) (clens_flbytes_slice sz from to))
= fun (input: bytes) -> (
  begin
    if Seq.length input < sz
    then (0, 0) // dummy
    else (U32.v from, U32.v to - U32.v from)
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_flbytes sz) (parse_flbytes (U32.v to - U32.v from)) (clens_flbytes_slice sz from to) input res )))

inline_for_extraction
let accessor_flbytes_slice
  (sz: nat { sz < 4294967296 } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (accessor (gaccessor_flbytes_slice sz from to))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_flbytes_slice sz from to) input pos in
  pos `U32.add` from

let clens_flbytes_get
  (sz: nat)
  (i: U32.t { U32.v i < sz } )
: Tot (clens (BY.lbytes sz) byte)
= {
  clens_cond =  (fun _ -> True);
  clens_get = (fun (x: BY.lbytes sz) -> (BY.get x i <: byte));
}

#push-options "--z3rlimit_factor 4"
let gaccessor_flbytes_get
  (sz: nat { sz < 4294967296 } )
  (i: U32.t { U32.v i < sz } )
: Tot (gaccessor (parse_flbytes sz) (parse_u8) (clens_flbytes_get sz i))
= fun (input: bytes) -> (
  begin
    let res =
      if Seq.length input <= U32.v i
      then (0, 0) // dummy
      else (U32.v i, 1)
    in
    let g () : Lemma
      (requires (gaccessor_pre (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input))
      (ensures (gaccessor_post (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input res))
    = parser_kind_prop_equiv (get_parser_kind parse_u8) parse_u8;
      assert (res == (U32.v i, 1));
      parse_u8_spec (Seq.slice input (U32.v i) (U32.v i + 1))
    in
    Classical.move_requires g ();
    res
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input res )))
#pop-options

inline_for_extraction
let accessor_flbytes_get
  (sz: nat { sz < 4294967296 } )
  (i: U32.t { U32.v i < sz } )
: Tot (accessor (gaccessor_flbytes_get sz i))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_flbytes_get sz i) input pos in
  pos `U32.add` i

(* Temporary: flbytes as leaf values *)

inline_for_extraction
let serialize32_flbytes
  (sz32: U32.t)
: Tot (serializer32 (serialize_flbytes (U32.v sz32)))
= fun (src: BY.lbytes (U32.v sz32)) (dst: buffer8) ->
  begin if sz32 <> 0ul
  then
    let dst' = B.sub dst 0ul sz32 in
    BY.store_bytes src dst'
  end;
  sz32

inline_for_extraction
let write_flbytes
  (sz32: U32.t)
: Tot (leaf_writer_strong (serialize_flbytes (U32.v sz32)))
= leaf_writer_strong_of_serializer32 (serialize32_flbytes sz32) ()

inline_for_extraction
let write_flbytes_weak
  (sz32: U32.t { U32.v sz32 < 4294967295 } )  // need to return that value if output buffer is too small
: Tot (leaf_writer_weak (serialize_flbytes (U32.v sz32)))
= leaf_writer_weak_of_strong_constant_size (write_flbytes sz32) sz32 ()

inline_for_extraction
let read_flbytes
  (sz32: U32.t)
: Tot (leaf_reader (parse_flbytes (U32.v sz32)))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_flbytes (U32.v sz32)) h input pos in
  BY.of_buffer sz32 (B.sub input.base pos sz32)

(* Equality test between a vlbytes and a constant lbytes *)

#push-options "--z3rlimit 32"

inline_for_extraction
let buffer_equals_bytes
  (const: BY.bytes)
  (b: buffer8)
  (pos: U32.t)
: HST.Stack bool
  (requires (fun h ->
    B.live h b /\
    U32.v pos + BY.length const <= B.length b
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    (res == true <==> B.as_seq h (B.gsub b pos (BY.len const)) == BY.reveal const)
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let len = BY.len const in
  let bi = B.alloca 0ul 1ul in
  let bres = B.alloca true 1ul in
  let h1 = HST.get () in
  [@inline_let] let inv (h: HS.mem) (stop: bool) : GTot Type0 =
      B.modifies (B.loc_union (B.loc_buffer bi) (B.loc_buffer bres)) h1 h /\ (
      let length = U32.v len in
      let i32 = (Seq.index (B.as_seq h bi) 0) in
      let i = U32.v i32 in
      let res = Seq.index (B.as_seq h bres) 0 in
      i <= length /\
      (stop == false ==> res == true) /\
      ((stop == true /\ res == true) ==> i == length) /\
      (res == true <==> B.as_seq h0 (B.gsub b pos i32) `Seq.equal` Seq.slice (BY.reveal const) 0 i)
    )
  in
  C.Loops.do_while
    inv
    (fun _ ->
      let i = B.index bi 0ul in
      if i = len
      then
        true
      else begin
        let i' = i `U32.add` 1ul in
        [@inline_let] let _ =
          let s1 = (B.as_seq h0 (B.gsub b pos i)) in
          let c1 = (B.get h0 b (U32.v pos + U32.v i)) in
          let s2 = (Seq.slice (BY.reveal const) 0 (U32.v i)) in
          let c2 = (BY.index const (U32.v i)) in
          assert (B.as_seq h0 (B.gsub b pos i') `Seq.equal` Seq.snoc s1 c1);
          assert (Seq.slice (BY.reveal const) 0 (U32.v i') `Seq.equal` Seq.snoc s2 c2);
          Classical.move_requires (Seq.lemma_snoc_inj s1 s2 c1) c2
        in
        let res = B.index b (pos `U32.add` i) = BY.get const i in
        B.upd bres 0ul res;
        B.upd bi 0ul i';
        not res
      end
    );
  let res = B.index bres 0ul in
  HST.pop_frame ();
  res

#pop-options

inline_for_extraction
let valid_slice_equals_bytes
  (const: BY.bytes)
  (input: slice)
  (pos: U32.t)
: HST.Stack bool
  (requires (fun h ->
    valid (parse_flbytes (BY.length const)) h input pos
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    (res == true <==> contents (parse_flbytes (BY.length const)) h input pos == const
  )))
= let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_flbytes (BY.length const)) h input pos in
  buffer_equals_bytes const input.base pos

inline_for_extraction
let validate_all_bytes
  ()
: Tot (validator parse_all_bytes)
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts parse_all_bytes h input pos in
  input.len

inline_for_extraction
let validate_bounded_vlbytes'
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (validator (parse_bounded_vlbytes' min max l))
= validate_synth
    (validate_bounded_vldata_strong' min max l serialize_all_bytes (validate_all_bytes ()))
    (synth_bounded_vlbytes min max)
    ()

inline_for_extraction
let validate_bounded_vlbytes
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
: Tot (validator (parse_bounded_vlbytes min max))
= validate_bounded_vlbytes' min max (log256' max)

inline_for_extraction
let jump_all_bytes
  ()
: Tot (jumper parse_all_bytes)
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts parse_all_bytes h input pos in
  input.len

inline_for_extraction
let jump_bounded_vlbytes'
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296  } )
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (jumper (parse_bounded_vlbytes' min max l))
= jump_synth
    (jump_bounded_vldata_strong' min max l serialize_all_bytes)
    (synth_bounded_vlbytes min max)
    ()

inline_for_extraction
let jump_bounded_vlbytes
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296  } )
: Tot (jumper (parse_bounded_vlbytes min max))
= jump_bounded_vlbytes' min max (log256' max)

let valid_exact_all_bytes_elim
  (h: HS.mem)
  (input: slice)
  (pos pos' : U32.t)
: Lemma
  (requires (valid_exact parse_all_bytes h input pos pos'))
  (ensures (
    let x = contents_exact parse_all_bytes h input pos pos' in
    let length = U32.v pos' - U32.v pos in
    BY.length x == length /\
    valid_content_pos (parse_flbytes length) h input pos x pos'
  ))
= valid_exact_equiv parse_all_bytes h input pos pos' ;
  contents_exact_eq parse_all_bytes h input pos pos' ;
  let length = U32.v pos' - U32.v pos in
  valid_facts (parse_flbytes length) h input pos ;
  assert (no_lookahead_on (parse_flbytes length) (B.as_seq h (B.gsub input.base pos (pos' `U32.sub` pos))) (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos))));
  assert (injective_postcond (parse_flbytes length) (B.as_seq h (B.gsub input.base pos (pos' `U32.sub` pos))) (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos))))

#push-options "--z3rlimit 32"

let valid_bounded_vlbytes'_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vlbytes' min max l) h input pos
  ))
  (ensures (
    let sz = l in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vlbytes' min max l) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    let x = contents (parse_bounded_vlbytes' min max l) h input pos in
    BY.len x == len_payload /\
    valid_pos (parse_bounded_vlbytes' min max l) h input pos (pos_payload `U32.add` len_payload) /\
    valid_content_pos (parse_flbytes (U32.v len_payload)) h input pos_payload x (pos_payload `U32.add` len_payload)
  ))))
= valid_synth h (parse_bounded_vlbytes_aux min max l) (synth_bounded_vlbytes min max) input pos;
  valid_bounded_vldata_strong'_elim h min max l serialize_all_bytes input pos;
  let sz = l in
  let len_payload = contents (parse_bounded_integer sz) h input pos in
  let pos_payload = pos `U32.add` U32.uint_to_t sz in
  valid_exact_all_bytes_elim h input pos_payload (pos_payload `U32.add` len_payload);
  ()

#pop-options

let valid_bounded_vlbytes_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vlbytes min max) h input pos
  ))
  (ensures (
    let sz = log256' max in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vlbytes min max) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    let x = contents (parse_bounded_vlbytes min max) h input pos in
    BY.len x == len_payload /\
    valid_pos (parse_bounded_vlbytes min max) h input pos (pos_payload `U32.add` len_payload) /\
    valid_content_pos (parse_flbytes (U32.v len_payload)) h input pos_payload x (pos_payload `U32.add` len_payload)
  ))))
= valid_bounded_vlbytes'_elim h min max (log256' max) input pos

let valid_bounded_vlbytes_elim_length
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vlbytes min max) h input pos
  ))
  (ensures (
    content_length (parse_bounded_vlbytes min max) h input pos == log256' max + BY.length (contents (parse_bounded_vlbytes min max) h input pos)
  ))
  [SMTPat (valid (parse_bounded_vlbytes min max) h input pos)]
= valid_bounded_vlbytes_elim h min max input pos

inline_for_extraction
let bounded_vlbytes'_payload_length
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (input: slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h -> valid (parse_bounded_vlbytes' min max l) h input pos))
  (ensures (fun h len h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + l + U32.v len <= U32.v input.len /\ (
    let x = contents (parse_bounded_vlbytes' min max l) h input pos in
    BY.len x == len /\
    valid_content_pos (parse_flbytes (U32.v len)) h input (pos `U32.add` U32.uint_to_t l) x (get_valid_pos (parse_bounded_vlbytes' min max l) h input pos) /\
    B.as_seq h (B.gsub input.base (pos `U32.add` U32.uint_to_t l) len) == BY.reveal x
  )))
= let h = HST.get () in
  [@inline_let] let _ = valid_bounded_vlbytes'_elim h min max l input pos in
  let len = read_bounded_integer l input pos in
  [@inline_let] let _ = valid_flbytes_elim h (U32.v len) input (pos `U32.add` U32.uint_to_t l) in
  len

inline_for_extraction
let bounded_vlbytes_payload_length
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h -> valid (parse_bounded_vlbytes min max) h input pos))
  (ensures (fun h len h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + log256' max + U32.v len <= U32.v input.len /\ (
    let x = contents (parse_bounded_vlbytes min max) h input pos in
    BY.len x == len /\
    valid_content_pos (parse_flbytes (U32.v len)) h input (pos `U32.add` U32.uint_to_t (log256' max)) x (get_valid_pos (parse_bounded_vlbytes min max) h input pos) /\
    B.as_seq h (B.gsub input.base (pos `U32.add` U32.uint_to_t (log256' max)) len) == BY.reveal x
  )))
= bounded_vlbytes'_payload_length min max (log256' max) input pos

(* Get the content buffer *)

#push-options "--z3rlimit 32"

inline_for_extraction
let get_vlbytes'_contents
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (input: slice)
  (pos: U32.t)
: HST.Stack buffer8
  (requires (fun h -> valid (parse_bounded_vlbytes' min max l) h input pos))
  (ensures (fun h b h' ->
    let x = contents (parse_bounded_vlbytes' min max l) h input pos in
    B.modifies B.loc_none h h' /\
    U32.v pos + l + BY.length x <= U32.v input.len /\
    b == B.gsub input.base (pos `U32.add` U32.uint_to_t l) (BY.len x) /\
    B.as_seq h b == BY.reveal x
  ))
= 
  let h = HST.get () in
  [@inline_let] let _ = valid_bounded_vlbytes'_elim h min max l input pos in
  let len = read_bounded_integer l input pos in
  [@inline_let] let _ = valid_facts (parse_flbytes (U32.v len)) h input (pos `U32.add` U32.uint_to_t l) in
  B.sub input.base (pos `U32.add` U32.uint_to_t l) len

#pop-options

inline_for_extraction
let get_vlbytes_contents
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
: HST.Stack buffer8
  (requires (fun h -> valid (parse_bounded_vlbytes min max) h input pos))
  (ensures (fun h b h' ->
    let l = log256' max in
    let x = contents (parse_bounded_vlbytes min max) h input pos in
    B.modifies B.loc_none h h' /\
    U32.v pos + l + BY.length x <= U32.v input.len /\
    b == B.gsub input.base (pos `U32.add` U32.uint_to_t l) (BY.len x) /\
    B.as_seq h b == BY.reveal x
  ))
= get_vlbytes'_contents min max (log256' max) input pos

(* In fact, the following accessors are not useful in practice,
   because users would need to have the flbytes parser combinator in
   their scope *)

let clens_vlbytes_cond
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (length: nat)
  (x: parse_bounded_vlbytes_t min max)
: GTot Type0
= BY.length x == length

let clens_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (length: nat)
: Tot (clens (parse_bounded_vlbytes_t min max) (BY.lbytes length))
= {
  clens_cond = (clens_vlbytes_cond min max length);
  clens_get = (fun (x: parse_bounded_vlbytes_t min max) -> (x <: Ghost (BY.lbytes length) (requires (clens_vlbytes_cond min max length x)) (ensures (fun _ -> True))));
}


#push-options "--z3rlimit 16 --max_fuel 2 --initial_fuel 2 --max_ifuel 6 --initial_ifuel 6"

let gaccessor_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (length: nat { length < 4294967296 } )
: Tot (gaccessor (parse_bounded_vlbytes' min max l) (parse_flbytes length) (clens_vlbytes min max length))
= fun (input: bytes) -> (begin
    let res = if Seq.length input = l + length
    then (l, length)
    else (0, 0)
    in
    let g () : Lemma
      (requires (gaccessor_pre (parse_bounded_vlbytes' min max l) (parse_flbytes length) (clens_vlbytes min max length) input))
      (ensures (gaccessor_post (parse_bounded_vlbytes' min max l) (parse_flbytes length) (clens_vlbytes min max length) input res))
    = parse_bounded_vlbytes_eq min max l input
    in
    Classical.move_requires g ();
    res
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_bounded_vlbytes' min max l) (parse_flbytes length) (clens_vlbytes min max length) input res)))

#pop-options

let gaccessor_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (length: nat { length < 4294967296 } )
: Tot (gaccessor (parse_bounded_vlbytes min max) (parse_flbytes length) (clens_vlbytes min max length))
= gaccessor_vlbytes' min max (log256' max) length

#push-options "--z3rlimit 64 --max_fuel 2 --initial_fuel 2 --max_ifuel 6 --initial_ifuel 6"

inline_for_extraction
let accessor_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (length: U32.t)
: Tot (accessor (gaccessor_vlbytes' min max l (U32.v length)))
= fun sl pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq h (gaccessor_vlbytes' min max l (U32.v length)) sl pos;
    valid_bounded_vlbytes'_elim h min max l sl pos;
    parse_bounded_vlbytes_eq min max l (B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)))
  in
  pos `U32.add` U32.uint_to_t l

#pop-options

inline_for_extraction
let accessor_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (length: U32.t)
: Tot (accessor (gaccessor_vlbytes min max (U32.v length)))
= accessor_vlbytes' min max (log256' max) length

let clens_vlbytes_slice
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= max } )
: Tot (clens (parse_bounded_vlbytes_t min max) (BY.lbytes (U32.v to - U32.v from)))
= {
  clens_cond =  (fun (x: parse_bounded_vlbytes_t min max) -> U32.v to <= BY.length x);
  clens_get = (fun (x: parse_bounded_vlbytes_t min max) -> (BY.slice x from to <: BY.lbytes (U32.v to - U32.v from)));
}

#push-options "--z3rlimit 16"

let gaccessor_vlbytes'_slice
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= max } )
: Tot (gaccessor (parse_bounded_vlbytes' min max l) (parse_flbytes (U32.v to - U32.v from)) (clens_vlbytes_slice min max from to))
= fun (input: bytes) -> (
  begin
    parse_bounded_vlbytes_eq min max l input;
    if Seq.length input < l + U32.v to
    then (0, 0) // dummy
    else (l + U32.v from, U32.v to - U32.v from)
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_bounded_vlbytes' min max l) (parse_flbytes (U32.v to - U32.v from)) (clens_vlbytes_slice min max from to) input res )))

let gaccessor_vlbytes_slice
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= max } )
: Tot (gaccessor (parse_bounded_vlbytes min max) (parse_flbytes (U32.v to - U32.v from)) (clens_vlbytes_slice min max from to))
= gaccessor_vlbytes'_slice min max (log256' max) from to

#pop-options


#push-options "--z3rlimit 50"

inline_for_extraction
let accessor_vlbytes'_slice
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= max } )
: Tot (accessor (gaccessor_vlbytes'_slice min max l from to))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_bounded_vlbytes' min max l) h input pos;
    parse_bounded_vlbytes_eq min max l (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
    slice_access_eq h (gaccessor_vlbytes'_slice min max l from to) input pos
  in
  pos `U32.add`  U32.uint_to_t l `U32.add` from

#pop-options

inline_for_extraction
let accessor_vlbytes_slice
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= max } )
: Tot (accessor (gaccessor_vlbytes_slice min max from to))
= accessor_vlbytes'_slice min max (log256' max) from to

let clens_vlbytes_get
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (i: U32.t)
: Tot (clens (parse_bounded_vlbytes_t min max) byte)
= {
  clens_cond =  (fun (x: parse_bounded_vlbytes_t min max) -> U32.v i < BY.length x);
  clens_get = (fun (x: parse_bounded_vlbytes_t min max) -> (BY.get x i <: byte));
}

#push-options "--z3rlimit 16"

let gaccessor_vlbytes'_get
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (i: U32.t)
: Tot (gaccessor (parse_bounded_vlbytes' min max l) (parse_u8) (clens_vlbytes_get min max i))
= fun (input: bytes) -> (
  begin
    let res =
      if Seq.length input <= l + U32.v i
      then (0, 0) // dummy
      else (l + U32.v i, 1)
    in
    let g () : Lemma
      (requires (gaccessor_pre (parse_bounded_vlbytes' min max l) parse_u8 (clens_vlbytes_get min max i) input))
      (ensures (gaccessor_post (parse_bounded_vlbytes' min max l) parse_u8 (clens_vlbytes_get min max i) input res))
    = parse_bounded_vlbytes_eq min max l input;
      parser_kind_prop_equiv (get_parser_kind parse_u8) parse_u8;
      assert (res == (l + U32.v i, 1));
      parse_u8_spec (Seq.slice input (l + U32.v i) (l + U32.v i + 1))
    in
    Classical.move_requires g ();
    res
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_bounded_vlbytes' min max l) parse_u8 (clens_vlbytes_get min max i) input res )))

inline_for_extraction
let accessor_vlbytes'_get
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (i: U32.t)
: Tot (accessor (gaccessor_vlbytes'_get min max l i))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_bounded_vlbytes' min max l) h input pos;
    parse_bounded_vlbytes_eq min max l (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
    slice_access_eq h (gaccessor_vlbytes'_get min max l i) input pos
  in
  pos `U32.add` U32.uint_to_t l `U32.add` i

#pop-options

let gaccessor_vlbytes_get
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (i: U32.t)
: Tot (gaccessor (parse_bounded_vlbytes min max) (parse_u8) (clens_vlbytes_get min max i))
= gaccessor_vlbytes'_get min max (log256' max) i

inline_for_extraction
let accessor_vlbytes_get
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
  (i: U32.t)
: Tot (accessor (gaccessor_vlbytes_get min max i))
= accessor_vlbytes'_get min max (log256' max) i

#push-options "--z3rlimit 128 --max_fuel 2 --initial_fuel 2 --max_ifuel 6 --initial_ifuel 6"

let valid_bounded_vlbytes'_intro
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (input: slice)
  (pos: U32.t)
  (len: U32.t)
: Lemma
  (requires (
    let sz = l in
    min <= U32.v len /\ U32.v len <= max /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len /\
    U32.v pos + sz <= 4294967295 /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid (parse_flbytes (U32.v len)) h input pos_payload
  )))
  (ensures (
    let sz = l in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_content_pos (parse_bounded_vlbytes' min max l) h input pos (contents (parse_flbytes (U32.v len)) h input pos_payload) (pos_payload `U32.add` len)
  ))
= valid_facts (parse_bounded_vlbytes' min max l) h input pos;
  parse_bounded_vlbytes_eq min max l (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
  let sz = l in
  valid_facts (parse_bounded_integer sz) h input pos;
  valid_facts (parse_flbytes (U32.v len)) h input (pos `U32.add` U32.uint_to_t sz)

#pop-options

let valid_bounded_vlbytes_intro
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
  (len: U32.t)
: Lemma
  (requires (
    let sz = log256' max in
    min <= U32.v len /\ U32.v len <= max /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len /\
    U32.v pos + sz <= 4294967295 /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid (parse_flbytes (U32.v len)) h input pos_payload
  )))
  (ensures (
    let sz = log256' max in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_content_pos (parse_bounded_vlbytes min max) h input pos (contents (parse_flbytes (U32.v len)) h input pos_payload) (pos_payload `U32.add` len)
  ))
= valid_bounded_vlbytes'_intro h min max (log256' max) input pos len

inline_for_extraction
let finalize_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (input: slice)
  (pos: U32.t)
  (len: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    let sz = l in
    live_slice h input /\
    min <= U32.v len /\ U32.v len <= max /\
    U32.v pos + sz + U32.v len <= U32.v input.len
  ))
  (ensures (fun h pos' h' ->
    let sz = l in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    B.modifies (loc_slice_from_to input pos pos_payload) h h' /\
    valid_content_pos (parse_bounded_vlbytes' min max l) h' input pos (BY.hide (B.as_seq h (B.gsub input.base pos_payload len))) pos' /\
    U32.v pos' == U32.v pos_payload + U32.v len
  ))
= [@inline_let]
  let sz = l in
  let pos_payload = write_bounded_integer sz len input pos in
  let h = HST.get () in
  [@inline_let] let _ =
    valid_flbytes_intro h (U32.v len) input pos_payload;
    valid_bounded_vlbytes'_intro h min max l input pos len
  in
  pos_payload `U32.add` len

inline_for_extraction
let finalize_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
  (len: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    let sz = log256' max in
    live_slice h input /\
    min <= U32.v len /\ U32.v len <= max /\
    U32.v pos + sz + U32.v len <= U32.v input.len
  ))
  (ensures (fun h pos' h' ->
    let sz = log256' max in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    B.modifies (loc_slice_from_to input pos pos_payload) h h' /\
    valid_content_pos (parse_bounded_vlbytes min max) h' input pos (BY.hide (B.as_seq h (B.gsub input.base pos_payload len))) pos' /\
    U32.v pos' == U32.v pos_payload + U32.v len
  ))
= finalize_bounded_vlbytes' min max (log256' max) input pos len
