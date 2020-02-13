module LowParse.Low.Readable

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32

inline_for_extraction
noextract
val perm (#t: Type) (b: B.buffer t) : Tot Type0

val perm_gsub
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
: GTot (perm (B.gsub b offset length))

unfold
let coerce (#t1: Type) (x1: t1) (t2: Type { t1 == t2 }) : Tot (x2: t2 { x1 == x2 }) = x1

val perm_gsub_gsub
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (offset1: U32.t)
  (length1: U32.t { U32.v offset1 + U32.v length1 <= B.length b })
  (offset2: U32.t)
  (length2: U32.t { U32.v offset2 + U32.v length2 <= U32.v length1 })
: Lemma
  (perm_gsub (perm_gsub p offset1 length1) offset2 length2 == coerce (perm_gsub p (offset1 `U32.add` offset2) length2) (perm (B.gsub (B.gsub b offset1 length1) offset2 length2)))
  [SMTPat (perm_gsub (perm_gsub p offset1 length1) offset2 length2)]

val perm_gsub_zero_length
  (#t: Type) (#b: B.buffer t) (p: perm b)
: Lemma
  ( b == B.gsub b 0ul (B.len b) /\
    p == perm_gsub p 0ul (B.len b) )

val loc_perm
  (#t: Type) (#b: B.buffer t) (p: perm b)
: GTot B.loc

val loc_perm_prop
  (#t: Type) (#b: B.buffer t) (p: perm b)
: Lemma
  (B.address_liveness_insensitive_locs `B.loc_includes` loc_perm p)
  [SMTPat (loc_perm p)]

val loc_perm_gsub
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
: Lemma
  (loc_perm p `B.loc_includes` loc_perm (perm_gsub p offset length))
  [SMTPat (loc_perm (perm_gsub p offset length))]

val loc_includes_perm_gsub
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (offset1: U32.t)
  (length1: U32.t { U32.v offset1 + U32.v length1 <= B.length b })
  (offset2: U32.t)
  (length2: U32.t { U32.v offset2 + U32.v length2 <= B.length b })
: Lemma
  (requires (
    U32.v offset1 <= U32.v offset2 /\
    U32.v offset2 + U32.v length2 <= U32.v offset1 + U32.v length1
  ))
  (ensures (
    loc_perm (perm_gsub p offset1 length1) `B.loc_includes` loc_perm (perm_gsub p offset2 length2)
  ))
  [SMTPat (loc_perm (perm_gsub p offset1 length1) `B.loc_includes` loc_perm (perm_gsub p offset2 length2))]

val loc_disjoint_perm_gsub
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (offset1: U32.t)
  (length1: U32.t { U32.v offset1 + U32.v length1 <= B.length b })
  (offset2: U32.t)
  (length2: U32.t { U32.v offset2 + U32.v length2 <= B.length b })
: Lemma
  (requires (
    U32.v offset1 + U32.v length1 <= U32.v offset2 \/
    U32.v offset2 + U32.v length2 <= U32.v offset1
  ))
  (ensures (
    loc_perm (perm_gsub p offset1 length1) `B.loc_disjoint` loc_perm (perm_gsub p offset2 length2)
  ))
  [SMTPat (loc_perm (perm_gsub p offset1 length1) `B.loc_disjoint` loc_perm (perm_gsub p offset2 length2))]

val valid_perm
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
: GTot Type0

val valid_perm_gsub
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
: Lemma
  (requires (valid_perm h p))
  (ensures (valid_perm h (perm_gsub p offset length)))

val valid_perm_prop
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
: Lemma
  (requires (valid_perm h p))
  (ensures (B.live h b /\ B.loc_disjoint (B.loc_buffer b) (loc_perm p)))
  [SMTPat (valid_perm h p)]

val valid_perm_frame
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    valid_perm h p /\ B.modifies (l `B.loc_union` B.address_liveness_insensitive_locs) h h' /\ B.loc_disjoint l (loc_perm p)
  ))
  (ensures (valid_perm h' p))

val readable
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: GTot Type0

val readable_prop
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (readable h p from to))
  (ensures (valid_perm h p))
  [SMTPat (readable h p from to)]

val readable_weaken
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (from1: U32.t)
  (to1: U32.t)
  (from2: U32.t)
  (to2: U32.t { U32.v from1 <= U32.v from2 /\ U32.v from2 <= U32.v to2 /\ U32.v to2 <= U32.v to1 /\ U32.v to1 <= B.length b })
: Lemma
  (requires (readable h p from1 to1))
  (ensures (readable h p from2 to2))

val readable_merge
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (readable h p from mid /\ readable h p mid to))
  (ensures (readable h p from to))

val readable_gsub
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= U32.v length })
: Lemma
  (readable h (perm_gsub p offset length) from to <==> readable h p (offset `U32.add` from) (offset `U32.add` to))
  [SMTPat (readable h (perm_gsub p offset length) from to)]

val readable_frame
  (h: HS.mem)
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    readable h p from to /\ B.modifies l h h' /\ B.loc_disjoint l (loc_perm (perm_gsub p from (to `U32.sub` from)))
  ))
  (ensures (readable h' p from to)) 

inline_for_extraction
noextract
val sub
  (#t: Type) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
: HST.Stack (perm (B.gsub b offset length))
  (requires (fun h -> valid_perm h p))
  (ensures (fun h p' h' -> h' == h /\ p' == perm_gsub p offset length))

module LP = LowParse.Low.Base

inline_for_extraction
noextract
val read_with_perm
  (#k: LP.parser_kind)
  (#t: Type)
  (#p: LP.parser k t)
  (r: LP.leaf_reader p)
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (slp: perm sl.LP.base)
  (pos: U32.t)
: HST.Stack t
  (requires (fun h ->
    LP.valid p h sl pos /\
    readable h slp pos (LP.get_valid_pos p h sl pos)
  ))
  (ensures (fun h res h' ->
    B.modifies (loc_perm (perm_gsub slp pos (LP.get_valid_pos p h sl pos `U32.sub` pos))) h h' /\
    res == LP.contents p h sl pos
  ))
