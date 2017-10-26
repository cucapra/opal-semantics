type node = string
type var = string
type world = string
type op = string

type sexp =
  | EmptySet
  | Cons of (sexp * sexp)
  | Var of (node * var)

type bool =
  | True
  | False
  | Equals of (sexp * sexp)
  | In of (sexp * sexp)
  | And of (bool * bool)
  | Or of (bool * bool)

type com =
  | Skip
  | Seq of (com * com)
  | If of (bool * com * com)
  | With of (node * com)
  | At of (node * com)
  | Hyp of (world * com)
  | Commit of world
  | Handle of (node * var * op * sexp * sexp * com)
  | Op of op

let cons2 func name l r =
  let ls = func l in
  let rs = func r in
  Printf.sprintf "(%s %s %s)" name ls rs

let rec output_coq_sexp = function
  | EmptySet -> "EmptySet"
  | Cons (l, r) -> cons2 output_coq_sexp "Cons" l r
  | Var (n, v) -> Printf.sprintf "(Var \"%s\" \"%s\")" n v

let rec output_coq_bool = function
  | True -> "True"
  | False -> "False"
  | Equals (l, r) -> cons2 output_coq_sexp "Equals" l r
  | In (l, r) -> cons2 output_coq_sexp "In" l r
  | And (l, r) -> cons2 output_coq_bool "And" l r
  | Or (l, r) -> cons2 output_coq_bool "Or" l r

let rec output_coq_com = function
  | Skip -> "Skip"
  | Seq (l, r) -> cons2 output_coq_com "Seq" l r
  | If (b, l, r) ->
     let bs = output_coq_bool b in
     let ls = output_coq_com l in
     let rs = output_coq_com r in
     Printf.sprintf "(If %s %s %s)" bs ls rs
  | With (n, c) ->
     let cs = output_coq_com c in
     Printf.sprintf "(With \"%s\" %s)" n cs
  | At (n, c) ->
     let cs = output_coq_com c in
     Printf.sprintf "(At \"%s\" %s)" n cs
  | Hyp (w, c) ->
     let cs = output_coq_com c in
     Printf.sprintf "(Hyp \"%s\" %s)" w cs
  | Commit w ->
     Printf.sprintf "(Commit \"%s\")" w
  | Handle (n, v, op, sh, sm, c) ->
     let shs = output_coq_sexp sh in
     let sms = output_coq_sexp sm in
     let cs = output_coq_com c in
     Printf.sprintf "(Handle \"%s\" \"%s\" \"%s\" %s %s %s)"
                   n v op shs sms cs
  | Op op ->
     Printf.sprintf "(Op \"%s\")" op
