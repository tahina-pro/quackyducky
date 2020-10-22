module LowParse.Low.Tac.Sum
include LowParse.Low.Sum

open LowParse.TacLib

(* Tactic for accessor extensionality *)

noextract
let sum_accessor_ext (ty: term) : Tac unit =
      let thm = mk_app (`clens_eq_intro') [(ty, Q_Implicit)] in
      apply thm;
      iseq [
        (fun _ ->
          norm [delta; zeta; iota; primops];
          let x = intro () in
          destruct (binder_to_term x);
          to_all_goals (fun _ ->
            let eqn = intros_until_eq_hyp () in
            rewrite eqn;
            norm [delta; zeta; iota; primops];
            trivial ()
          )
        );
        (fun _ ->
          norm [delta; zeta; iota; primops];
          let x = intro () in
          destruct (binder_to_term x);
          to_all_goals (fun _ ->
            let eqn = intros_until_eq_hyp () in
            rewrite eqn;
            norm [delta; zeta; iota; primops];
            let u = intro () in
            smt ()
          )
        )
      ]

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
let typ_eq_name (t: typ) (n: name) : Tac bool =
  match inspect t with
  | Tv_FVar fv ->
    (inspect_fv fv `compare_name` n) = FStar.Order.Eq
  | _ -> false

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

(*

let subtype_equals
  (t0 t1 t2: Type)
  (x1: t1)
  (x2: t2)
: GTot Type0
= t1 `subtype_of` t0 /\ t2 `subtype_of` t0 /\ ((x1 <: t0) == (x2 <: t0))

noextract
let rec mk_enum_upto' (x: U8.t) : Tot (list (U8.t & U8.t)) (decreases (U8.v x)) =
  if x = 0uy
  then []
  else
    let y = x `U8.sub` 1uy in
    (y, y) :: mk_enum_upto' y

let rec for_all_memb
  (#a: eqtype)
  (f: (a -> Tot bool))
  (l: list a)
: Lemma
  (L.for_all f l <==> (forall x . L.mem x l ==> f x))
= match l with
  | [] -> ()
  | _ :: q -> for_all_memb f q

let rec mk_enum_upto_correct
  (x: U8.t)
: Lemma
  (ensures (
    let l = mk_enum_upto' x in
    let l1 = L.map fst l in
    let l2 = L.map snd l in
    L.noRepeats l1 /\
    L.noRepeats l2 /\
    L.for_all (U8.gt x) l1 /\
    L.for_all (U8.gt x) l2
  ))
  (decreases (U8.v x))
= if x = 0uy
  then ()
  else begin
    let y = x `U8.sub` 1uy in
    mk_enum_upto_correct y;
    let l = mk_enum_upto' y in
    let l1 = L.map fst l in
    let l2 = L.map snd l in
    for_all_memb (U8.gt y) l1;
    for_all_memb (U8.gt y) l2;
    for_all_memb (U8.gt x) l1;
    for_all_memb (U8.gt x) l2
  end

noextract
let mk_enum_upto (x: U8.t) : Tot (enum U8.t U8.t) =
  mk_enum_upto_correct x;
  mk_enum_upto' x

let rec mk_enum_upto_complete
  (x: U8.t)
  (y: U8.t)
: Lemma
  (requires (U8.v y < U8.v x))
  (ensures (
    let l = mk_enum_upto' x in
    let l1 = L.map fst l in
    let l2 = L.map snd l in
    L.mem y l1 /\ L.mem y l2
  ))
  (decreases (U8.v x))
= if U8.v y + 1 = U8.v x
  then ()
  else mk_enum_upto_complete (x `U8.sub` 1uy) y

inline_for_extraction
let mk_enum_upto_key
  (x: U8.t)
  (y: U8.t)
: Pure (enum_key (mk_enum_upto x))
  (requires (U8.v y < U8.v x))
  (ensures (fun z -> (z <: U8.t) == y))
= mk_enum_upto_complete x y;
  y

inline_for_extraction
let mk_enum_upto_repr
  (x: U8.t)
  (y: U8.t)
: Pure (enum_repr (mk_enum_upto x))
  (requires (U8.v y < U8.v x))
  (ensures (fun z -> (z <: U8.t) == y))
= mk_enum_upto_complete x y;
  y

let rec mk_enum_upto_key_repr'
  (x: U8.t)
  (y: U8.t)
: Lemma
  (requires (U8.v y < U8.v x))
  (ensures (
    L.assoc y (mk_enum_upto' x) == Some y
  ))
  (decreases (U8.v x))
= if U8.v y + 1 = U8.v x
  then ()
  else mk_enum_upto_key_repr' (x `U8.sub` 1uy) y

let mk_enum_upto_key_repr
  (x: U8.t)
  (y: U8.t)
: Lemma
  (requires (U8.v y < U8.v x))
  (ensures (
    enum_repr_of_key (mk_enum_upto x) (mk_enum_upto_key x y) == mk_enum_upto_repr x y
  ))
= mk_enum_upto_key_repr' x y

let mk_enum_upto_repr_key
  (x: U8.t)
  (y: U8.t)
: Lemma
  (requires (U8.v y < U8.v x))
  (ensures (
    enum_key_of_repr (mk_enum_upto x) (mk_enum_upto_repr x y) == mk_enum_upto_key x y
  ))
= mk_enum_upto_key_repr x y;
  enum_key_of_repr_of_key (mk_enum_upto x) (mk_enum_upto_key x y)

