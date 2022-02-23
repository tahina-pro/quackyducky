module EverParse3d.InputStream.All

open EverParse3d.InputStream.FunPtr
module Aux = EverParse3d.InputStream.FunPtr.Type

let t = t

#set-options "--print_implicits"

let inst = {
  live = live;
  footprint = footprint;
  perm_footprint = perm_footprint;
  live_not_unused_in = live_not_unused_in;
  len_all = len_all;
  get_all = get_all;
  get_remaining = get_remaining;
  get_read = get_read;
  preserved = preserved;
  tlen = (fun _ -> unit);
  has_t = Aux.has_t;
  has = has;
  read_t = Aux.read_t;
  read = read;
  skip_t = Aux.skip_t;
  skip = skip;
  skip_if_success = skip_if_success;
  empty_t = Aux.empty_t;
  empty = empty;
  is_prefix_of = is_prefix_of;
  get_suffix = get_suffix;
  is_prefix_of_prop = is_prefix_of_prop;
  truncate = truncate;
  truncate_len = truncate_len;
}
