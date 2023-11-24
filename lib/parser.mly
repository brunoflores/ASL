%{

open Ast

exception Unbound of string

let binding_depth s rho =
  let rec bind n = function
    | [] -> raise (Unbound s)
    | head :: tail -> if s=head
		      then Var n
		      else bind (n+1) tail
  in bind 1 rho

(*
let init_env = ["+"; "-"; "*"; "/"; "="]
type ctx = string list
*)

%}

%token <int> INT
%token <string> IDENT
%token LET
%token BE
%token IF
%token THEN
%token ELSE
%token FI
%token SEMIC
%token LAMBDA
%token DOT
%token LPAR
%token RPAR
%token EOF

%start <top_asl option> top

%%

top:
  | EOF
    { None }
  | LET; x = IDENT; BE; e = expression; SEMIC; EOF
    { Some (Decl (x, e))  }
  | e = expression; SEMIC; EOF
    { Some (Decl ("it", e)) }

expression:
  | e = expr
    { let e', _ = e [] in e' }

expr:
  | LAMBDA; x = IDENT; DOT; e = expr
    { fun ctx ->
        let e', ctx' = e (x :: ctx) in
        Abs (x, e'), ctx' }
  | x = IDENT
    { fun ctx ->
        try binding_depth x ctx, ctx
        with Unbound s ->
	  failwith @@ Format.sprintf "ASL Parsing: Unbound identifier: %s" s }
  | n = INT
    { fun ctx ->
        Const n, ctx }
