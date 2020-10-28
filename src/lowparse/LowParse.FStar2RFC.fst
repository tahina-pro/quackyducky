module LowParse.FStar2RFC

open LowParse.TacLib

(* Construct a sum type parser from a F* sum type *)

noextract
let get_name_and_ctors (s: term) : Tac (name & list ctor) =
  let e = top_env () in
  let typename = match inspect s with
  | Tv_FVar fv -> inspect_fv fv
  | _ -> fail "not a type name"
  in
  match lookup_typ e typename with
  | None -> fail "type not found"
  | Some se ->
    begin match inspect_sigelt se with
    | Sg_Inductive name _ _ _ constructors -> name, constructors
    | _ -> fail "not an inductive type"
    end

noextract
let name_eq (n1 n2: name) : Tot bool =
  (n1 `compare_name` n2) = FStar.Order.Eq

noextract
let typ_eq_name (t: typ) (n: name) : Tac bool =
  match inspect t with
  | Tv_FVar fv ->
    (inspect_fv fv `compare_name` n) = FStar.Order.Eq
  | _ -> false

noextract
let string_of_base_type (t: typ) : Tac string =
  if t `term_eq` (`FStar.UInt8.t)
  then "FStar.UInt8.t"
  else if t `term_eq` (`FStar.UInt16.t)
  then "FStar.UInt16.t"
  else if t `term_eq` (`FStar.UInt32.t)
  then "FStar.UInt32.t"
  else if t `term_eq` (`FStar.UInt64.t)
  then "FStar.UInt64.t"
  else fail "not a base type"

noextract
noeq
type constr_aux_t = {
  constr_aux_payload_typ: typ;
  constr_synth_pattern: pattern;
  constr_synth_args: list argv;
  constr_synth_recip_bvs: list bv;
  constr_synth_recip_body: term;
}

let get_fv (tm: term) : Tac fv =
  match inspect tm with
  | Tv_FVar fv -> fv
  | _ -> fail "not an fv"

let string_capitalize
  (x: string)
: Tot string
= if String.length x = 0
  then x
  else String.uppercase (String.sub x 0 1) ^ String.sub x 1 (String.length x - 1)

let y : string = _ by (let x = string_capitalize "abc" in exact (quote x))

noextract
let unfold_fv (t: term) : Tac term =
  let e = top_env () in
  let typename = match inspect t with
  | Tv_FVar fv -> inspect_fv fv
  | _ -> fail "not a type name"
  in
  match lookup_typ e typename with
  | None -> fail "type not found"
  | Some se ->
    begin match inspect_sigelt se with
    | Sg_Let _ _ _ _ def -> def
    | _ -> fail "not an inductive type"
    end

noextract
let rec string_index_of_from
  (x: string)
  (c: Char.char)
  (i: nat)
: Pure (option nat)
  (requires True)
  (ensures (fun y ->
    match y with
    | None -> True
    | Some y -> i <= y /\ y < String.length x
  ))
  (decreases (String.length x - i))
= if i >= String.length x
  then None
  else if String.index x i = c
  then Some i
  else string_index_of_from x c (i + 1)

noextract
let rec string_index_of_to
  (x: string)
  (c: Char.char)
  (i: nat)
: Pure (option nat)
  (requires i <= String.length x)
  (ensures (fun y ->
    match y with
    | None -> True
    | Some y -> y < i
  ))
  (decreases i)
= if i = 0
  then None
  else if String.index x (i - 1) = c
  then Some (i - 1)
  else string_index_of_to x c (i - 1)

let _ : unit = _ by (print (term_to_string (unfold_fv (`y))); exact (`()))

noextract
let rec mk_constr_aux (iname: name) (t: typ) : Tac constr_aux_t =
  if t `typ_eq_name` iname
  then {
    constr_aux_payload_typ = (`unit);
    constr_synth_recip_bvs = [];
    constr_synth_recip_body = (`());
    constr_synth_pattern = Pat_Constant C_Unit;
    constr_synth_args = [];
  }
  else match inspect t with
  | Tv_Arrow bv c ->
    let (bv, _) = inspect_binder bv in
    let arg_t = (inspect_bv bv).bv_sort in
    begin match inspect_comp c with
    | C_Total ret _ ->
      if ret `typ_eq_name` iname
      then
        let b = fresh_bv ret in
        let br = fresh_bv ret in
        {
          constr_aux_payload_typ = ret;
          constr_synth_recip_bvs = [b];
          constr_synth_recip_body = pack (Tv_BVar b);
          constr_synth_pattern = Pat_Var br;
          constr_synth_args = [pack (Tv_BVar br), Q_Explicit];
        }
      else
        let j = mk_constr_aux iname ret in
        let b = fresh_bv ret in
        let br = fresh_bv ret in
        {
          constr_aux_payload_typ = mk_app (`tuple2) [arg_t, Q_Explicit; j.constr_aux_payload_typ, Q_Explicit];
          constr_synth_recip_bvs = b :: j.constr_synth_recip_bvs;
          constr_synth_recip_body = mk_app (`Mktuple2) [
            ret, Q_Implicit;
            j.constr_aux_payload_typ, Q_Implicit;
            pack (Tv_BVar b), Q_Explicit;
            j.constr_synth_recip_body, Q_Explicit;
          ];
          constr_synth_pattern = Pat_Cons (get_fv (`Mktuple2)) [Pat_Var br, true; j.constr_synth_pattern, true];
          constr_synth_args = (pack (Tv_BVar br), Q_Explicit) :: j.constr_synth_args;
        }
    | _ -> fail "not a Tot constructor"
    end
  | _ -> fail "not an arrow constructor"

noextract
noeq
type constr_t = {
  constr_payload_typ: typ;
  constr_synth: term;
  constr_synth_recip: branch;
}

module L = FStar.List.Tot

noextract
let mk_constr (iname: name) (s: ctor) : Tac constr_t =
  let (name, typ) = s in
  let aux = mk_constr_aux iname typ in
  {
    constr_payload_typ = aux.constr_aux_payload_typ;
    constr_synth = (
      let b = fresh_bv aux.constr_aux_payload_typ in
      pack (Tv_Abs (mk_binder b) (
        pack (Tv_Match (pack (Tv_Var b)) [
          aux.constr_synth_pattern, mk_app (pack (Tv_FVar (pack_fv name))) aux.constr_synth_args
      ]))))
    ;
    constr_synth_recip = (
      let mp = L.map (fun x -> (Pat_Var x, true)) aux.constr_synth_recip_bvs in
      Pat_Cons (pack_fv name) mp,
      aux.constr_synth_recip_body
    );
  }

noextract
let rec mk_maps_aux (iname: name) (c: list ctor) : Tac unit =
  match c with
  | [] -> ()
  | a :: q ->
    let _ = mk_constr iname a in
    mk_maps_aux iname q

noextract
let mk_maps (s: typ) : Tac unit =
  let (name, ctors) = get_name_and_ctors s in
  mk_maps_aux name ctors

type t = | A | B of bool

let _ : unit = synth_by_tactic (fun _ ->
    mk_maps (`t);
    exact (`())
  )
