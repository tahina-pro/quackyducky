module CBOR.Pulse.Raw.EverParse.Iterator.Mixed
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open LowParse.PulseParse.Iterator.Type
open LowParse.PulseParse.Iterator

module SZ = FStar.SizeT
module U64 = FStar.UInt64
module IO = LowParse.PulseParse.Iterator.IntOps
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module LPS = LowParse.Pulse.Base

(* Bridge: u64_ops.v reduces to U64.v. Two SMT patterns so the identity fires
   whether a query mentions [io.v x] (lib-style length facts) or [U64.v x]
   (concrete postconditions at the CBOR boundary). Needed because the branch
   result is upcast to the declared [U64.t] return type, dropping the
   definitional link to [IO.u64_ops]. *)
let u64_ops_v_eq (x: U64.t) : Lemma (IO.u64_ops.v x == U64.v x)
  [SMTPatOr [[SMTPat (IO.u64_ops.v x)]; [SMTPat (U64.v x)]]]
= ()

(* prefix-narrow identities *)
let list_narrow_zero (#a: Type) (l: list a) (n: nat)
: Lemma (list_narrow l 0 n == fst (List.Tot.splitAt n l))
= ()

let list_narrow_full (#a: Type) (l: list a)
: Lemma (list_narrow l 0 (List.Tot.length l) == l)
= list_narrow_zero l (List.Tot.length l);
  FStar.List.Pure.Properties.splitAt_length_total l

(* splitAt of an append, when the cut falls inside the first component. *)
let lemma_splitAt_append_left (#a: Type) (nn: nat) (la lb: list a)
  : Lemma
    (requires nn <= List.Tot.length la)
    (ensures fst (List.Tot.splitAt nn (List.Tot.append la lb)) == fst (List.Tot.splitAt nn la))
= let (lc, ld) = List.Tot.splitAt nn la in
  FStar.List.Pure.Properties.lemma_splitAt_append nn la;
  List.Tot.Properties.append_assoc lc ld lb;
  FStar.List.Pure.Properties.lemma_append_splitAt lc (List.Tot.append ld lb)

(* splitAt of an append, when the cut falls inside the second component. *)
let lemma_splitAt_append_right (#a: Type) (nn: nat) (la lb: list a)
  : Lemma
    (requires List.Tot.length la <= nn /\ nn <= List.Tot.length la + List.Tot.length lb)
    (ensures fst (List.Tot.splitAt nn (List.Tot.append la lb)) ==
             List.Tot.append la (fst (List.Tot.splitAt (nn - List.Tot.length la) lb)))
= let mm = nn - List.Tot.length la in
  let (lc, ld) = List.Tot.splitAt mm lb in
  FStar.List.Pure.Properties.lemma_splitAt_append mm lb;
  List.Tot.Properties.append_assoc la lc ld;
  List.Tot.Properties.append_length la lc;
  FStar.List.Pure.Properties.lemma_append_splitAt (List.Tot.append la lc) ld

(* Layer 1: generic iterator-level operations over the lowparse mixed-list
   `iterator` type, generic over the element vmatch and parser.  These
   provide the operations that lowparse does NOT provide (is_empty, length,
   share, gather, truncate).  All of them are permission-preserving; the
   1.0R normalization for truncate is done by the caller (Layer 2) that
   embeds a permission field in a record wrapper. *)

inline_for_extraction
fn iter_is_empty
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (i: iterator U64.t t)
  (#pm: perm) (#l: Ghost.erased (list u))
requires iterator_match vmatch IO.u64_ops p pm i l
returns res: bool
ensures iterator_match vmatch IO.u64_ops p pm i l ** pure (res == Nil? (Ghost.reveal l))
{
  match i {
    IBase bi -> {
      rewrite each i as (IBase #U64.t #t bi);
      unfold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi) l);
      base_mixed_list_match_length vmatch IO.u64_ops p pm bi l;
      // Hoist the length out of binary-operator-operand position: the extracted
      // (inline) length is a block-like `match`, which the krml Rust printer
      // cannot emit as an operand of `==`. A pure `let` is semantically identical.
      let blen = base_mixed_list_length IO.u64_ops bi;
      let res = IO.u64_ops.eq blen 0uL;
      fold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi) l);
      rewrite each (IBase #U64.t #t bi) as i;
      res
    }
    IPair bi ml -> {
      rewrite each i as (IPair #U64.t #t bi ml);
      unfold (iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l);
      with l1 l2. assert (base_mixed_list_match vmatch IO.u64_ops p pm bi l1 ** mixed_list_match vmatch IO.u64_ops p pm ml l2);
      base_mixed_list_match_length vmatch IO.u64_ops p pm bi l1;
      mixed_list_match_length vmatch IO.u64_ops p pm ml l2;
      List.Tot.Properties.append_length l1 l2;
      // Hoist (see IBase case above): keep the block-like match off `==`.
      let blen = base_mixed_list_length IO.u64_ops bi;
      let res = IO.u64_ops.eq blen 0uL;
      fold (iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l);
      rewrite each (IPair #U64.t #t bi ml) as i;
      res
    }
  }
}

inline_for_extraction
fn iter_length
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (i: iterator U64.t t)
  (#pm: perm) (#l: Ghost.erased (list u))
requires iterator_match vmatch IO.u64_ops p pm i l ** pure (FStar.UInt.fits (List.Tot.length (Ghost.reveal l)) 64)
returns res: U64.t
ensures iterator_match vmatch IO.u64_ops p pm i l ** pure ((U64.v res <: nat) == List.Tot.length (Ghost.reveal l))
{
  match i {
    IBase bi -> {
      rewrite each i as (IBase #U64.t #t bi);
      unfold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi) l);
      base_mixed_list_match_length vmatch IO.u64_ops p pm bi l;
      let res = base_mixed_list_length IO.u64_ops bi;
      fold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi) l);
      rewrite each (IBase #U64.t #t bi) as i;
      res
    }
    IPair bi ml -> {
      rewrite each i as (IPair #U64.t #t bi ml);
      unfold (iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l);
      with l1 l2. assert (base_mixed_list_match vmatch IO.u64_ops p pm bi l1 ** mixed_list_match vmatch IO.u64_ops p pm ml l2);
      base_mixed_list_match_length vmatch IO.u64_ops p pm bi l1;
      mixed_list_match_length vmatch IO.u64_ops p pm ml l2;
      List.Tot.Properties.append_length l1 l2;
      // Hoist BOTH lengths out of `+` operand position (block-like matches).
      let blen = base_mixed_list_length IO.u64_ops bi;
      let mlen = mixed_list_length IO.u64_ops ml;
      let res = IO.u64_ops.add blen mlen;
      fold (iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l);
      rewrite each (IPair #U64.t #t bi ml) as i;
      res
    }
  }
}

ghost
fn iter_share
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (vmatch_share: share_t vmatch)
  (i: iterator U64.t t)
  (#pm: perm) (#l: (list u))
requires iterator_match vmatch IO.u64_ops p pm i l
ensures iterator_match vmatch IO.u64_ops p (pm /. 2.0R) i l ** iterator_match vmatch IO.u64_ops p (pm /. 2.0R) i l
{
  match i {
    IBase bi -> {
      rewrite each i as (IBase #U64.t #t bi);
      unfold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi) l);
      base_mixed_list_match_share vmatch IO.u64_ops p pm bi l vmatch_share;
      fold (iterator_match vmatch IO.u64_ops p (pm /. 2.0R) (IBase #U64.t #t bi) l);
      fold (iterator_match vmatch IO.u64_ops p (pm /. 2.0R) (IBase #U64.t #t bi) l);
      rewrite each (IBase #U64.t #t bi) as i;
    }
    IPair bi ml -> {
      rewrite each i as (IPair #U64.t #t bi ml);
      unfold (iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l);
      with l1 l2. assert (base_mixed_list_match vmatch IO.u64_ops p pm bi l1 ** mixed_list_match vmatch IO.u64_ops p pm ml l2);
      base_mixed_list_match_share vmatch IO.u64_ops p pm bi l1 vmatch_share;
      mixed_list_match_share vmatch IO.u64_ops p pm ml l2 vmatch_share;
      fold (iterator_match vmatch IO.u64_ops p (pm /. 2.0R) (IPair #U64.t #t bi ml) l);
      fold (iterator_match vmatch IO.u64_ops p (pm /. 2.0R) (IPair #U64.t #t bi ml) l);
      rewrite each (IPair #U64.t #t bi ml) as i;
    }
  }
}

ghost
fn iter_gather
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (vmatch_gather: gather_t vmatch)
  (i: iterator U64.t t)
  (#pm1: perm) (#l1: (list u)) (#pm2: perm) (#l2: (list u))
requires iterator_match vmatch IO.u64_ops p pm1 i l1 ** iterator_match vmatch IO.u64_ops p pm2 i l2
ensures iterator_match vmatch IO.u64_ops p (pm1 +. pm2) i l1 ** pure (l1 == l2)
{
  match i {
    IBase bi -> {
      rewrite each i as (IBase #U64.t #t bi);
      unfold (iterator_match vmatch IO.u64_ops p pm1 (IBase #U64.t #t bi) l1);
      unfold (iterator_match vmatch IO.u64_ops p pm2 (IBase #U64.t #t bi) l2);
      base_mixed_list_match_gather vmatch IO.u64_ops p pm1 pm2 bi l1 l2 vmatch_gather;
      fold (iterator_match vmatch IO.u64_ops p (pm1 +. pm2) (IBase #U64.t #t bi) l1);
      rewrite each (IBase #U64.t #t bi) as i;
    }
    IPair bi ml -> {
      rewrite each i as (IPair #U64.t #t bi ml);
      unfold (iterator_match vmatch IO.u64_ops p pm1 (IPair #U64.t #t bi ml) l1);
      with la lb. assert (base_mixed_list_match vmatch IO.u64_ops p pm1 bi la ** mixed_list_match vmatch IO.u64_ops p pm1 ml lb);
      unfold (iterator_match vmatch IO.u64_ops p pm2 (IPair #U64.t #t bi ml) l2);
      with lc ld. assert (base_mixed_list_match vmatch IO.u64_ops p pm2 bi lc ** mixed_list_match vmatch IO.u64_ops p pm2 ml ld);
      base_mixed_list_match_gather vmatch IO.u64_ops p pm1 pm2 bi la lc vmatch_gather;
      mixed_list_match_gather vmatch IO.u64_ops p pm1 pm2 ml lb ld vmatch_gather;
      List.Tot.Properties.append_length la lb;
      List.Tot.Properties.append_length lc ld;
      fold (iterator_match vmatch IO.u64_ops p (pm1 +. pm2) (IPair #U64.t #t bi ml) l1);
      rewrite each (IPair #U64.t #t bi ml) as i;
    }
  }
}

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
inline_for_extraction
fn iter_truncate
  (#t #u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
  (i: iterator U64.t t)
  (n: U64.t)
  (#pm: perm) (#l: Ghost.erased (list u))
requires iterator_match vmatch IO.u64_ops p pm i l ** pure (U64.v n <= List.Tot.length (Ghost.reveal l))
returns res: iterator U64.t t
ensures exists* pm'.
  iterator_match vmatch IO.u64_ops p pm' res (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))) **
  Trade.trade
    (iterator_match vmatch IO.u64_ops p pm' res (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))))
    (iterator_match vmatch IO.u64_ops p pm i l)
{
  match i {
    IBase bi -> {
      rewrite each i as (IBase #U64.t #t bi);
      unfold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi) l);
      base_mixed_list_match_length vmatch IO.u64_ops p pm bi l;
      rewrite (base_mixed_list_match vmatch IO.u64_ops p pm bi l)
        as (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l);
      let bi' = base_mixed_list_narrow_n vmatch IO.u64_ops p j 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l 0uL n;
      list_narrow_zero (Ghost.reveal l) (U64.v n);
      rewrite (base_mixed_list_match vmatch IO.u64_ops p pm bi' (list_narrow (Ghost.reveal l) (U64.v 0uL - 0) (U64.v n)))
        as (base_mixed_list_match vmatch IO.u64_ops p pm bi' (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))));
      fold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))));
      intro (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))) @==>
             iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi) l)
        #(Trade.trade (base_mixed_list_match vmatch IO.u64_ops p pm bi' (list_narrow (Ghost.reveal l) (U64.v 0uL - 0) (U64.v n)))
                      (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l))
        fn _ {
          unfold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))));
          rewrite (base_mixed_list_match vmatch IO.u64_ops p pm bi' (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))))
            as (base_mixed_list_match vmatch IO.u64_ops p pm bi' (list_narrow (Ghost.reveal l) (U64.v 0uL - 0) (U64.v n)));
          elim_trade _ _;
          rewrite (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l)
            as (base_mixed_list_match vmatch IO.u64_ops p pm bi l);
          fold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi) l);
        };
      rewrite each (IBase #U64.t #t bi) as i;
      IBase #U64.t #t bi'
    }
    IPair bi ml -> {
      rewrite each i as (IPair #U64.t #t bi ml);
      unfold (iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l);
      with l1 l2. assert (base_mixed_list_match vmatch IO.u64_ops p pm bi l1 ** mixed_list_match vmatch IO.u64_ops p pm ml l2);
      base_mixed_list_match_length vmatch IO.u64_ops p pm bi l1;
      List.Tot.Properties.append_length l1 l2;
      // Hoist the base length out of the `<=` operand (and reuse it in CASE B's
      // `-`): block-like matches cannot be binary operands in extracted Rust.
      let blen = base_mixed_list_length IO.u64_ops bi;
      if (IO.u64_ops.lte n blen) {
        // CASE A: the truncation point falls within the base; result is IBase bi'
        rewrite (base_mixed_list_match vmatch IO.u64_ops p pm bi l1)
          as (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l1);
        let bi' = base_mixed_list_narrow_n vmatch IO.u64_ops p j 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l1 0uL n;
        list_narrow_zero l1 (U64.v n);
        lemma_splitAt_append_left (U64.v n) l1 l2;
        rewrite (base_mixed_list_match vmatch IO.u64_ops p pm bi' (list_narrow l1 (U64.v 0uL - 0) (U64.v n)))
          as (base_mixed_list_match vmatch IO.u64_ops p pm bi' (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))));
        fold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))));
        intro (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))) @==>
               iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l)
          #(Trade.trade (base_mixed_list_match vmatch IO.u64_ops p pm bi' (list_narrow l1 (U64.v 0uL - 0) (U64.v n)))
                        (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l1)
            ** mixed_list_match vmatch IO.u64_ops p pm ml l2
            ** pure (Ghost.reveal l == List.Tot.append l1 l2 /\
                     (base_mixed_list_length IO.u64_ops bi == 0uL ==> mixed_list_length IO.u64_ops ml == 0uL) /\
                     U64.v n <= List.Tot.length l1))
          fn _ {
            unfold (iterator_match vmatch IO.u64_ops p pm (IBase #U64.t #t bi') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))));
            list_narrow_zero l1 (U64.v n);
            lemma_splitAt_append_left (U64.v n) l1 l2;
            rewrite (base_mixed_list_match vmatch IO.u64_ops p pm bi' (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))))
              as (base_mixed_list_match vmatch IO.u64_ops p pm bi' (list_narrow l1 (U64.v 0uL - 0) (U64.v n)));
            elim_trade _ _;
            rewrite (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l1)
              as (base_mixed_list_match vmatch IO.u64_ops p pm bi l1);
            fold (iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l);
          };
        rewrite each (IPair #U64.t #t bi ml) as i;
        IBase #U64.t #t bi'
      } else {
        // CASE B: the truncation point extends into the tail; result is IPair bi ml'
        mixed_list_match_length vmatch IO.u64_ops p pm ml l2;
        let mlen = IO.u64_ops.sub n blen;
        rewrite (mixed_list_match vmatch IO.u64_ops p pm ml l2)
          as (mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (mixed_list_length IO.u64_ops ml)) pm ml l2);
        let ml' = mixed_list_narrow_n vmatch IO.u64_ops p j 0 (U64.v (mixed_list_length IO.u64_ops ml)) pm ml l2 0uL mlen vmatch_share vmatch_gather;
        rewrite (base_mixed_list_match vmatch IO.u64_ops p pm bi l1)
          as (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l1);
        base_mixed_list_match_n_share vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) pm bi l1 vmatch_share;
        // keep one copy as base_mixed_list_match_n (spare, for the reverse trade), convert the
        // other to base_mixed_list_match so the fold below is unambiguous.
        rewrite (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) (pm /. 2.0R) bi l1)
          as (base_mixed_list_match vmatch IO.u64_ops p (pm /. 2.0R) bi l1);
        list_narrow_zero l2 (U64.v mlen);
        lemma_splitAt_append_right (U64.v n) l1 l2;
        fold (iterator_match vmatch IO.u64_ops p (pm /. 2.0R) (IPair #U64.t #t bi ml') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))));
        intro (iterator_match vmatch IO.u64_ops p (pm /. 2.0R) (IPair #U64.t #t bi ml') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))) @==>
               iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l)
          #(base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) (pm /. 2.0R) bi l1
            ** Trade.trade (mixed_list_match vmatch IO.u64_ops p (pm /. 2.0R) ml' (list_narrow l2 (U64.v 0uL - 0) (U64.v mlen)))
                           (mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (mixed_list_length IO.u64_ops ml)) pm ml l2)
            ** pure (Ghost.reveal l == List.Tot.append l1 l2 /\
                     (base_mixed_list_length IO.u64_ops bi == 0uL ==> mixed_list_length IO.u64_ops ml == 0uL) /\
                     List.Tot.length l1 == U64.v (base_mixed_list_length IO.u64_ops bi) /\
                     U64.v (base_mixed_list_length IO.u64_ops bi) <= U64.v n /\
                     U64.v n <= List.Tot.length l1 + List.Tot.length l2 /\
                     U64.v mlen == U64.v n - U64.v (base_mixed_list_length IO.u64_ops bi)))
          fn _ {
            unfold (iterator_match vmatch IO.u64_ops p (pm /. 2.0R) (IPair #U64.t #t bi ml') (fst (List.Tot.splitAt (U64.v n) (Ghost.reveal l))));
            with la lb. assert (base_mixed_list_match vmatch IO.u64_ops p (pm /. 2.0R) bi la ** mixed_list_match vmatch IO.u64_ops p (pm /. 2.0R) ml' lb);
            rewrite (base_mixed_list_match vmatch IO.u64_ops p (pm /. 2.0R) bi la)
              as (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) (pm /. 2.0R) bi la);
            base_mixed_list_match_n_gather vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) (pm /. 2.0R) (pm /. 2.0R) bi la l1 vmatch_gather;
            rewrite (base_mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (base_mixed_list_length IO.u64_ops bi)) ((pm /. 2.0R) +. (pm /. 2.0R)) bi la)
              as (base_mixed_list_match vmatch IO.u64_ops p pm bi l1);
            list_narrow_zero l2 (U64.v mlen);
            lemma_splitAt_append_right (U64.v n) l1 l2;
            List.Tot.Properties.append_length_inv_head l1 lb l1 (list_narrow l2 (U64.v 0uL - 0) (U64.v mlen));
            rewrite (mixed_list_match vmatch IO.u64_ops p (pm /. 2.0R) ml' lb)
              as (mixed_list_match vmatch IO.u64_ops p (pm /. 2.0R) ml' (list_narrow l2 (U64.v 0uL - 0) (U64.v mlen)));
            elim_trade _ _;
            rewrite (mixed_list_match_n vmatch IO.u64_ops p 0 (U64.v (mixed_list_length IO.u64_ops ml)) pm ml l2)
              as (mixed_list_match vmatch IO.u64_ops p pm ml l2);
            fold (iterator_match vmatch IO.u64_ops p pm (IPair #U64.t #t bi ml) l);
          };
        rewrite each (IPair #U64.t #t bi ml) as i;
        IPair #U64.t #t bi ml'
      }
    }
  }
}
#pop-options
