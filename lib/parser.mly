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
    { let e', _ = e !Sem.global_env in e' }

apps:
  | e = atom
    { fun ctx ->
        let e', ctx' = e ctx in
        (e', ctx') }
  | e1 = atom; e2 = atom
    { fun ctx ->
        let e1', _ = e1 ctx in
        let e2', _ = e2 ctx in
	App (e1', e2'), ctx }
  | e1 = atom; e2 = atom; es = apps
    { fun ctx ->
        let e1', _ = e1 ctx in
        let e2', _ = e2 ctx in
	let es', _ = es ctx in
	App ((App (e1', e2')), es'), ctx }

expr:
  | LAMBDA; x = IDENT; DOT; e = expr
    { fun ctx ->
        let e', ctx' = e (x :: ctx) in
        Abs (x, e'), ctx' }
  | e = apps
    { fun ctx ->
        let e', ctx' = e ctx in
	e', ctx' }

atom:
  | x = IDENT
    { fun ctx ->
        try binding_depth x ctx, ctx
        with Unbound s ->
	  failwith @@ Format.sprintf "ASL Parsing: Unbound identifier: %s" s }
  | n = INT
    { fun ctx ->
        Const n, ctx }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr; FI
    { fun ctx ->
        let e1', _ = e1 ctx in
        let e2', _ = e2 ctx in
	let e3', _ = e3 ctx in
        Cond (e1', e2', e3'), ctx }
  | LPAR; e = expr; RPAR
    { fun ctx ->
        let e', ctx' = e ctx in (e', ctx') }
