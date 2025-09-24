module CBOR.Pulse.Raw.Iterator.Gen
open CBOR.Pulse.Raw.Util
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch.Util
module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util

inline_for_extraction
let cbor_raw_iterator_init_from_slice_t
  (#cbor_raw_iterator: Type0)
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (cbor_raw_iterator_match: perm -> cbor_raw_iterator -> list elt_high -> slprop)
=
  (a: S.slice elt_low) ->
  (#pm: perm) ->
  (#pm': perm) ->
  (#l: Ghost.erased (list elt_high)) ->
  (#sq: Ghost.erased (Seq.seq elt_low)) ->
  stt cbor_raw_iterator
  (requires
  pts_to a #pm sq **
  PM.seq_list_match sq l (elt_match pm') **
  pure (FStar.UInt.fits (SZ.v (S.len a)) U64.n)
  )
  (ensures fun res -> exists* p .
  cbor_raw_iterator_match p res l **
     trade
       (cbor_raw_iterator_match p res l)
       (pts_to a #pm sq **
         PM.seq_list_match sq l (elt_match pm')
       )
  )

inline_for_extraction
let cbor_raw_iterator_init_from_serialized_t
  (#cbor_raw_serialized_iterator #cbor_raw_iterator: Type0)
  (#elt_high: Type0)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (cbor_raw_iterator_match: perm -> cbor_raw_iterator -> list elt_high -> slprop)
=
  (a: cbor_raw_serialized_iterator) ->
  (#pm: perm) ->
  (#l: Ghost.erased (list elt_high)) ->
  stt cbor_raw_iterator
  (requires
  ser_match pm a l
  )
  (ensures fun res -> exists* p .
  cbor_raw_iterator_match p res l **
     trade
       (cbor_raw_iterator_match p res l)
       (ser_match pm a l)
  )

inline_for_extraction
let cbor_raw_iterator_is_empty_t
  (#elt_high #cbor_raw_iterator: Type0)
  (cbor_raw_iterator_match: perm -> cbor_raw_iterator -> list elt_high -> slprop)
= (c: cbor_raw_iterator) ->
  (#pm: perm) ->
  (#r: Ghost.erased (list elt_high)) ->
  stt bool
  (requires
    cbor_raw_iterator_match pm c r
  )
  (ensures fun res ->
    cbor_raw_iterator_match pm c r **
    pure (res == Nil? r)
  )

inline_for_extraction
let cbor_raw_iterator_length_t
  (#elt_high #cbor_raw_iterator: Type0)
  (cbor_raw_iterator_match: perm -> cbor_raw_iterator -> list elt_high -> slprop)
=
  (c: cbor_raw_iterator) ->
  (#pm: perm) ->
  (#r: Ghost.erased (list elt_high)) ->
  stt U64.t
  (requires
    cbor_raw_iterator_match pm c r
  )
  (ensures fun res ->
    cbor_raw_iterator_match pm c r **
    pure ((U64.v res <: nat) == List.Tot.length r)
  )

inline_for_extraction
let cbor_raw_iterator_next_t
  (#cbor_raw_iterator: Type0)
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (cbor_raw_iterator_match: perm -> cbor_raw_iterator -> list elt_high -> slprop)
=
  (pi: R.ref (cbor_raw_iterator)) ->
  (#pm: perm) ->
  (#i: Ghost.erased cbor_raw_iterator) ->
  (#l: Ghost.erased (list elt_high)) ->
  stt elt_low
  (
    R.pts_to pi i **
    cbor_raw_iterator_match pm i l **
    pure (Cons? l)
  )
  (fun res -> exists* a p i' q .
    elt_match p res a **
    R.pts_to pi i' **
    cbor_raw_iterator_match pm i' q **
    trade
      (elt_match p res a ** cbor_raw_iterator_match pm i' q)
      (cbor_raw_iterator_match pm i l) **
    pure (Ghost.reveal l == a :: q)
  )

inline_for_extraction
let cbor_raw_iterator_truncate_t
  (#elt_high #cbor_raw_iterator: Type0)
  (cbor_raw_iterator_match: perm -> cbor_raw_iterator -> list elt_high -> slprop)
=
  (c: cbor_raw_iterator) ->
  (len: U64.t) ->
  (#pm: perm) ->
  (#r: Ghost.erased (list elt_high)) ->
  stt cbor_raw_iterator
  (requires
    cbor_raw_iterator_match pm c r **
    pure (U64.v len <= List.Tot.length r)
  )
  (ensures fun res ->
    cbor_raw_iterator_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)) **
    Trade.trade
      (cbor_raw_iterator_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)))
      (cbor_raw_iterator_match pm c r)
  )
