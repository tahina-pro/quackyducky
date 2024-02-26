module LowParse.SteelST.BitSum
include LowParse.Spec.BitSum
include LowParse.SteelST.ValidateAndRead
include LowParse.SteelST.Write
include LowParse.SteelST.Combinators

inline_for_extraction
let validate_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (f: filter_bitsum'_t b)
  (d: destr_bitsum'_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: validate_and_read p)
: Pure (validate_and_read (parse_bitsum' b p))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= [@@inline_let]
  let _ = synth_bitsum'_injective b in
  rewrite_validate_and_read
    (validate_and_read_synth
      (validate_filter_and_read
        w
        (filter_bitsum' b)
        (fun x -> f x)
      )
      (synth_bitsum' b)
      (d
        cps_read_synth_cont
        (fun k cond iftrue iffalse pre t' post phi ->
          if cond
          then iftrue () pre t' post phi
          else iffalse () pre t' post phi
        )
        (fun k pre t' post phi -> phi k)
      )
      ()
    )
    _

inline_for_extraction
let read_and_jump_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (d: destr_bitsum'_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: read_and_jump p)
: Pure (read_and_jump (parse_bitsum' b p))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= [@@inline_let]
  let _ = synth_bitsum'_injective b in
  rewrite_read_and_jump
    (read_and_jump_synth
      (read_and_jump_filter
        w
        (filter_bitsum' b)
      )
      (synth_bitsum' b)
      (d
        cps_read_synth_cont
        (fun k cond iftrue iffalse pre t' post phi ->
          if cond
          then iftrue () pre t' post phi
          else iffalse () pre t' post phi
        )
        (fun k pre t' post phi -> phi k)
      )
      ()
    )
    _

inline_for_extraction
let jump_bitsum' 
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: jumper p)
: Tot (jumper (parse_bitsum' b p))
= [@@inline_let]
  let _ = synth_bitsum'_injective b in
  jump_synth
    (jump_filter
      w
      (filter_bitsum' b)
    )
    (synth_bitsum' b)
    ()

inline_for_extraction
let read_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (d: destr_bitsum'_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: cps_reader p)
: Tot (cps_reader (parse_bitsum' b p))
= [@@inline_let]
  let _ = synth_bitsum'_injective b in
  cps_read_synth
    (cps_read_filter
      r
      (filter_bitsum' b)
    )
    (synth_bitsum' b)
    (
      d
        cps_read_synth_cont
        (fun k cond iftrue iffalse pre t' post phi ->
          if cond
          then iftrue () pre t' post phi
          else iffalse () pre t' post phi
        )
        (fun k pre t' post phi -> phi k)
    )
    ()

inline_for_extraction
let write_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (sr: synth_bitsum'_recip_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: writer s)
: Tot (writer (serialize_bitsum' b s))
= fun x a ->
    serialize_bitsum'_eq b s x;
    synth_bitsum'_injective b;
    synth_bitsum'_recip_inverse b;
    Steel.ST.Util.noop ();
    let res = w (sr x) a in
    let _ = Steel.ST.GenElim.gen_elim () in
    let _ = intro_filter _ (filter_bitsum' b) a in
    let _ = intro_synth _ (synth_bitsum' b) a () in
    let _ = rewrite_aparse a (parse_bitsum' b p) in
    Steel.ST.Util.return res
