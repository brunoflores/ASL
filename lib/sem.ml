let init_env = [ "+"; "-"; "*"; "/"; "=" ]
let global_env = ref init_env

type semval = Constval of int | Funval of (semval -> semval)

exception Illtyped
exception Semantbug of string

let init_semantics f =
  Funval
    (function
    | Constval n ->
        Funval (function Constval m -> Constval (f n m) | _ -> raise Illtyped)
    | _ -> raise Illtyped)

let caml_function = function
  | "+" -> ( + )
  | "-" -> ( - )
  | "*" -> ( * )
  | "/" -> ( / )
  | "=" -> fun n m -> if n = m then 1 else 0
  | s -> raise (Semantbug (Format.sprintf "Unknown primitive: %s" s))

let init_sem = List.map (fun x -> init_semantics (caml_function x)) init_env
let global_sem = ref init_sem

let rec nth n = function
  | [] -> raise (Failure "nth")
  | head :: tail -> if n = 1 then head else nth (n - 1) tail

let rec semant rho =
  let open Ast in
  let rec sem = function
    | Const n -> Constval n
    | Var n -> nth n rho
    | Cond (e1, e2, e3) -> (
        match sem e1 with
        | Constval 0 -> sem e3
        | Constval _ -> sem e2
        | _ -> raise Illtyped)
    | Abs (_, e') -> Funval (fun x -> semant (x :: rho) e')
    | App (e1, e2) -> (
        match sem e1 with Funval f -> f (sem e2) | _ -> raise Illtyped)
  in
  sem

let semantics = function
  | Some (Ast.Decl (s, e)) ->
      let result = semant !global_sem e in
      global_env := s :: !global_env;
      global_sem := result :: !global_sem;
      Format.printf "ASL value of %s is %s\n" s
        (match result with
        | Constval n -> string_of_int n
        | Funval _ -> "<fun>")
  | None -> ()
