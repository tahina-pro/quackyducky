module EverParse3d.InputStream.Buffer
open EverParse3d.InputStream.Buffer.Aux

(* Implementation for single buffers *)

let t = t

let _get_read
  (x: t)
  (h: HS.mem)
: Ghost (Seq.seq U8.t)
  (requires (_live x h))
  (ensures (fun y -> Ghost.reveal x.g_all == y `Seq.append` _get_remaining x h))
=
  let i = U32.v (B.deref h x.pos) in
  Seq.lemma_split x.g_all i;
  Seq.slice x.g_all 0 i

let _is_prefix_of
  (x y: t)
: Tot prop
= x.buf == y.buf /\
  U32.v x.len <= U32.v y.len /\
  x.pos == y.pos /\
  x.g_all_buf == y.g_all_buf /\
  Ghost.reveal x.g_all == Seq.slice (Ghost.reveal y.g_all) 0 (U32.v x.len)

let _get_suffix
  (x y: t)
: Ghost (Seq.seq U8.t)
  (requires (x `_is_prefix_of` y))
  (ensures (fun _ -> True))
= Seq.slice (Ghost.reveal y.g_all) (U32.v x.len) (U32.v y.len)

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false"
#restart-solver

let _is_prefix_of_prop
  (x: t)
  (y: t)
  (h: HS.mem)
: Lemma
  (requires (
    _live x h /\
    x `_is_prefix_of` y
  ))
  (ensures (
      _live y h /\
      _get_read y h `Seq.equal` _get_read x h /\
      _get_remaining y h `Seq.equal` (_get_remaining x h `Seq.append` _get_suffix x y)
  ))
= ()

open LowStar.BufferOps

#restart-solver

let inst = {

  live = _live;

  footprint = _footprint;

  live_not_unused_in = begin fun x h ->
    ()
  end;

  len_all = begin fun x ->
    x.len
  end;

  get_all = begin fun x ->
    Ghost.reveal x.g_all
  end;

  get_remaining = begin fun x h ->
    _get_remaining x h
  end;

  get_read = begin fun x h ->
    _get_read x h
  end;

  preserved = begin fun x l h h' ->
    ()
  end;
  
  has = begin fun x currentPosition n ->
    n `U32.lte` (x.len `U32.sub` currentPosition)
  end;

  read = begin fun x currentPosition n dst ->
    let h0 = HST.get () in
    let res = B.sub x.buf currentPosition n in
    x.pos *= currentPosition `U32.add` n;
    let h' = HST.get () in
    assert (Ghost.reveal (B.deref h' x.pos) == currentPosition `U32.add` n);
    res
  end;

  skip = begin fun x currentPosition n ->
    let h0 = HST.get () in
    x.pos *= currentPosition `U32.add` n;
    let h' = HST.get () in
    assert (Ghost.reveal (B.deref h' x.pos) == currentPosition `U32.add` n);
    ()
  end;

  empty = begin fun x _ ->
    let h0 = HST.get () in
    x.pos *= x.len;
    x.len
  end;

  is_prefix_of = _is_prefix_of;

  get_suffix = _get_suffix;

  is_prefix_of_prop = _is_prefix_of_prop;

  truncate = begin fun x currentPosition n ->
    {
      buf = x.buf;
      len = currentPosition `U32.add` n;
      pos = x.pos;
      g_all = Ghost.hide (Seq.slice (Ghost.reveal x.g_all) 0 (U32.v currentPosition + U32.v n));
      g_all_buf = x.g_all_buf;
      prf = ();
    }
  end;
}

#pop-options
