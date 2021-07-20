module EverParse3d.InputStream.All
open EverParse3d.InputStream.Buffer
friend EverParse3d.InputStream.Buffer

module Aux = EverParse3d.InputStream.Buffer.Aux

let t = t

let inst = inst

let lift_reader #k #u #p r sz input =
  LP.parser_kind_prop_equiv k p;
  let h0 = HST.get () in
  let position = get_read_count input in
  LP.valid_facts p h0 (LP.make_slice input.Aux.buf input.Aux.len) position;
  let result = r (LP.make_slice input.Aux.buf input.Aux.len) position in
  skip input sz;
  result
