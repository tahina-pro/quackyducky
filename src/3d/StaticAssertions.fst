(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain as copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module StaticAssertions
open FStar.All
open Ast
module B = Binding

noeq
type sizeof_assertion = {
  type_name : ident;
  size : int
}

noeq
type static_asserts = {
  includes : list string;
  sizeof_assertions : list sizeof_assertion
}

let empty_static_asserts = {
  includes = [];
  sizeof_assertions = []
}

let compute_static_asserts (env:TypeSizes.env_t) 
                           (r:option type_refinement)
  : ML static_asserts
  = match r with
    | None -> empty_static_asserts
    | Some r -> 
      let sizeof_assertions =
        r.type_map
        |> List.map
          (fun (i, jopt) ->
            let j =
              match jopt with
              | None -> i
              | Some j -> j
            in
            let t_j = with_dummy_range (Type_app j []) in
            match TypeSizes.size_of_typ env t_j with
            | TypeSizes.Fixed n
            | TypeSizes.WithVariableSuffix n ->
             { type_name = i;
               size = n }
            | _ -> 
              Ast.error 
                (Printf.sprintf
                  "Type %s is variable sized and cannot refine a C type %s"
                  j.v i.v)
                i.range)
      in
      {
        includes = r.Ast.includes;
        sizeof_assertions = sizeof_assertions
      }
