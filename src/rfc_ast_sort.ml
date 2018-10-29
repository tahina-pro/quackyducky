open Rfc_ast

let tname (p:gemstone_t) : string =
  let aux = function
		| Enum (_, _, n) -> n
		| Struct (_, _, n) -> n
    | Typedef (_, _, n, _, _) -> n
	in String.uncapitalize_ascii (aux p)

let dedup l =
  let r = ref [] in
  List.iter (fun x -> if not (List.mem x !r) then r := x::!r) l;
  List.rev !r

let tname (p:gemstone_t) : string =
  let aux = function
		| Enum (_, _, n) -> n
		| Struct (_, _, n) -> n
    | Typedef (_, _, n, _, _) -> n
	in String.uncapitalize_ascii (aux p)

let typedep = function
  | TypeSimple ty -> [ty]
  | TypeSelect (_, l, o) ->
    let l = List.map (fun (_, ty)->ty) l in
    match o with None -> l | Some ty -> ty :: l

let getdep (p:gemstone_t) : typ list =
  let tn = tname p in
  let dep =
    match p with
    | Enum (_, fl, n) ->
      ([]:typ list list)
    | Struct (_, fl, _) ->
      let dep = List.map (fun (al, ty, n, vec, def) ->
        typedep ty) fl in
      dep
    | Typedef (al, ty, n, vec, def) ->
      [typedep ty]
    in
  dedup (List.flatten dep)

let sort (p: prog) : prog =
  let deps = List.map (fun d -> (d, getdep d)) p in
  let deps_sorted =
    List.sort
      (fun (d1, dep1) (d2, dep2) ->
        let n1 = tname d1 in
        let n2 = tname d2 in
        if n1 = n2
        then 0
        else if List.mem n1 dep2
        then -1
        else if List.mem n2 dep1
        then 1
        else 0)
      deps
  in
  List.map fst deps_sorted
