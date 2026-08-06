module CBOR.Spec.Raw.MapRemove

(* Pure spec lemma supporting a NONdeterministic CBOR map remove-by-key
   operation.  Given a valid map [Map len entries] and a valid key [rk],
   structurally removing every entry whose key is [raw_equiv] to [rk]
   corresponds, at the abstract [cbor_map] level, to
     [cbor_map_filter (fun kv -> not (fst kv = mk_cbor rk))].

   This is SOUND precisely because [raw_equiv] IS abstract ([mk_cbor])
   equality (see [mk_cbor_equiv]); the deterministic engine's STRUCTURAL
   ([cbor_compare = 0]) equality would be UNSOUND here, since a valid
   nondeterministic map may hold a NON-optimal key that is [raw_equiv] to
   -- but structurally different from -- the query key.

   Dual of [CBOR.Spec.Raw.MapPrepend.mk_cbor_map_prepend]. *)

open CBOR.Spec.Raw
open CBOR.Spec.API.Format

module R = CBOR.Spec.Raw.Base
module U = CBOR.Spec.Util
module U64 = FStar.UInt64
module L = FStar.List.Tot

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"

(* The [assoc] of the [mk_cbor]-mapped, key-filtered entry list, in terms of
   the [assoc] of the [mk_cbor]-mapped FULL entry list: removing the
   [raw_equiv]-class of [rk] at the raw level is exactly zeroing out the key
   [mk_cbor rk] at the abstract level. *)
let rec assoc_map_mk_cbor_filter
  (k: cbor) (rk: R.raw_data_item) (entries: list (R.raw_data_item & R.raw_data_item))
: Lemma
  (requires (
    L.for_all valid_raw_data_item (L.map fst entries) /\
    L.for_all valid_raw_data_item (L.map snd entries) /\
    valid_raw_data_item rk == true
  ))
  (ensures (
    L.assoc k (L.map mk_cbor_map_entry (L.filter (fun e -> not (raw_equiv (fst e) rk)) entries)) ==
    begin match L.assoc k (L.map mk_cbor_map_entry entries) with
    | None -> None
    | Some v -> if k = mk_cbor rk then None else Some v
    end
  ))
  (decreases entries)
= match entries with
  | [] -> ()
  | (ek, ev) :: q ->
    mk_cbor_equiv ek rk;
    assoc_map_mk_cbor_filter k rk q

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"

(* Main bridge lemma: the raw key-filtered map ([Map len' filtered]) has, as
   its abstract value, exactly the [cbor_map_filter] of the abstract source
   map by "key not equal to [mk_cbor rk]".

   Validity of the filtered map is a PRECONDITION (the caller -- the raw
   nondet wrapper -- already establishes it via filter-preserves-validity),
   mirroring how the caller supplies validity to [mk_cbor_map_prepend]. *)
let mk_cbor_map_remove
  (len: R.raw_uint64)
  (entries: R.nlist (R.raw_data_item & R.raw_data_item) (U64.v len.value))
  (rk: R.raw_data_item)
  (len': (l: R.raw_uint64 { U64.v l.value == L.length (L.filter (fun e -> not (raw_equiv (fst e) rk)) entries) }))
: Lemma
  (requires (
    valid_raw_data_item (R.Map len entries) == true /\
    valid_raw_data_item rk == true /\
    valid_raw_data_item (R.Map len' (L.filter (fun e -> not (raw_equiv (fst e) rk)) entries)) == true
  ))
  (ensures (
    CMap? (unpack (mk_cbor (R.Map len entries))) /\
    CMap? (unpack (mk_cbor (R.Map len' (L.filter (fun e -> not (raw_equiv (fst e) rk)) entries)))) /\
    (CMap?.c (unpack (mk_cbor (R.Map len' (L.filter (fun e -> not (raw_equiv (fst e) rk)) entries)))) <: cbor_map) ==
      cbor_map_filter (fun (kv: (cbor & cbor)) -> not (fst kv = mk_cbor rk))
        (CMap?.c (unpack (mk_cbor (R.Map len entries))))
  ))
= let filtered = L.filter (fun e -> not (raw_equiv (fst e) rk)) entries in
  mk_cbor_eq (R.Map len entries);
  mk_cbor_eq (R.Map len' filtered);
  valid_eq basic_data_model (R.Map len entries);
  valid_eq basic_data_model (R.Map len' filtered);
  let m_old = CMap?.c (unpack (mk_cbor (R.Map len entries))) in
  let m_new = CMap?.c (unpack (mk_cbor (R.Map len' filtered))) in
  let target = cbor_map_filter (fun (kv: (cbor & cbor)) -> not (fst kv = mk_cbor rk)) m_old in
  let aux (k: cbor) : Lemma (cbor_map_get m_new k == cbor_map_get target k) =
    list_assoc_map_mk_cbor_map_entry m_old entries () k;
    list_assoc_map_mk_cbor_map_entry m_new filtered () k;
    assoc_map_mk_cbor_filter k rk entries;
    cbor_map_get_filter (fun (kv: (cbor & cbor)) -> not (fst kv = mk_cbor rk)) m_old k
  in
  FStar.Classical.forall_intro aux;
  assert (cbor_map_equal m_new target);
  cbor_map_ext m_new target

#pop-options
