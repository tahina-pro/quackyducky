module Lisp

val read_witness_from
  (from: (unit -> ML string))
: ML (Seq.seq int)
