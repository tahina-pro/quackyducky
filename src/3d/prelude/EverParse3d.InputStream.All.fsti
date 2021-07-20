module EverParse3d.InputStream.All
include EverParse3d.InputStream.Base

(* These are defined in some EverParse3d.InputStream.fst defined in a subdirectory. The include path determines which one is used *)

inline_for_extraction
noextract
val t : Type0

[@@FStar.Tactics.Typeclasses.tcinstance]
inline_for_extraction
noextract
val inst : input_stream_inst t

module LP = LowParse.Low.Base
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

inline_for_extraction noextract
val lift_reader
  (#k: LP.parser_kind)
  (#u: _)
  (#p: LP.parser k u)
  (r: LP.leaf_reader p)
  (sz: U32.t)
  (sl: t)
: HST.Stack u
  (requires (fun h ->
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
    k.LP.parser_kind_low = U32.v sz /\
    live sl h /\
    Some? (LP.parse p (get_remaining sl h))
  ))
  (ensures (fun h res h' ->
    let s = get_remaining sl h in
    live sl h' /\
    B.modifies (footprint sl) h h' /\
    begin match LP.parse p s with
    | None -> False
    | Some (y, len) ->
      res == y /\
      get_remaining sl h' == Seq.slice s len (Seq.length s)
    end
  ))
