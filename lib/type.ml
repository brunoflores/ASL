type asl_type =
  | Unknown
  | Number
  | TypeVar of vartype
  | Arrow of asl_type * asl_type

and vartype = { index : int; mutable value : asl_type }
and asl_type_scheme = Forall of int list * asl_type

exception Typingbug of string
exception Typeclash of asl_type * asl_type

let new_vartype, reset_vartypes =
  let counter = ref 0 in
  ( (function
    | () ->
        counter := !counter + 1;
        { index = !counter; value = Unknown }),
    function () -> counter := 0 )

let rec shorten t =
  match t with
  | TypeVar { value = Unknown; _ } -> t
  | TypeVar { value = TypeVar { value = Unknown; _ } as tv; _ } -> tv
  | TypeVar ({ value = TypeVar tv1; _ } as tv2) ->
      tv2.value <- tv1.value;
      shorten t
  | TypeVar { value = t'; _ } -> t'
  | Unknown -> raise (Typingbug "shorten")
  | t' -> t'

let occurs { index = n; _ } =
  let rec occrec = function
    | TypeVar { index = m; _ } -> n = m
    | Number -> false
    | Arrow (t1, t2) -> occrec t1 || occrec t2
    | Unknown -> raise (Typingbug "occurs")
  in
  occrec

let rec unify (tau1, tau2) =
  match (shorten tau1, shorten tau2) with
  | ( TypeVar ({ index = n; value = Unknown } as tv1),
      (TypeVar { index = m; value = Unknown } as t2) ) ->
      if n <> m then tv1.value <- t2
  | t1, (TypeVar ({ value = Unknown; _ } as tv) as t2) ->
      if not (occurs tv t1) then tv.value <- t1 else raise (Typeclash (t1, t2))
  | (TypeVar ({ value = Unknown; _ } as tv) as t1), t2 ->
      if not (occurs tv t2) then tv.value <- t2 else raise (Typeclash (t1, t2))
  | Number, Number -> ()
  | Arrow (t1, t2), Arrow (t'1, t'2) ->
      unify (t1, t'1);
      unify (t2, t'2)
  | t1, t2 -> raise (Typeclash (t1, t2))

let init_typing_env =
  List.map
    (function _ -> Forall ([], Arrow (Number, Arrow (Number, Number))))
    Sem.init_env

let global_typing_env = ref init_typing_env

let vars_of_type tau =
  let rec vars vs = function
    | Number -> vs
    | TypeVar { index = n; value = Unknown } ->
        if List.mem n vs then vs else n :: vs
    | TypeVar { value = t; _ } -> vars vs t
    | Arrow (t1, t2) -> vars (vars vs t1) t2
    | Unknown -> raise (Typingbug "vars_of_type")
  in
  vars [] tau

(* [unknowns_of_type (bv, t)] returns the list of variables occuring in [t] that
   do not appear in [bv]. *)
let unkowns_of_type (bv, t) = Lib.subtract (vars_of_type t) bv

(* The set of unknowns of a type environment is the union of the unknowns
   of each type. *)
let unknowns_of_type_env env =
  List.flatten
    (List.map (function Forall (gv, t) -> unkowns_of_type (gv, t)) env)

let generalise_type (gamma, tau) =
  let module IntSet = Set.Make (Int) in
  let genvars =
    IntSet.of_list
    @@ Lib.subtract (vars_of_type tau) (unknowns_of_type_env gamma)
  in
  Forall (IntSet.fold List.cons genvars [], tau)

let gen_instance (Forall (gv, tau)) =
  let unknowns = List.map (function n -> (n, TypeVar (new_vartype ()))) gv in
  let rec ginstance = function
    | TypeVar { index = n; value = Unknown } as t -> (
        try List.assoc n unknowns with Not_found -> t)
    | TypeVar { value = t; _ } -> ginstance t
    | Number -> Number
    | Arrow (t1, t2) -> Arrow (ginstance t1, ginstance t2)
    | Unknown -> raise (Typingbug "gen_instance")
  in
  ginstance tau

(* Each rule corresponds to a typing inference rule. *)
let rec asl_typing_expr gamma =
  let rec type_rec = function
    | Ast.Const _ -> Number
    | Var n ->
        let sigma =
          try List.nth gamma n with Failure _ -> raise (Typingbug "Unbound")
        in
        gen_instance sigma
    | Cond (e1, e2, e3) ->
        unify (Number, type_rec e1);
        let t2 = type_rec e2 in
        let t3 = type_rec e3 in
        unify (t2, t3);
        t3
    | App (Abs (_x, e2), e1) ->
        (* LET case *)
        let t1 = type_rec e1 in
        let sigma = generalise_type (gamma, t1) in
        asl_typing_expr (sigma :: gamma) e2
    | App (e1, e2) ->
        let u = TypeVar (new_vartype ()) in
        unify (type_rec e1, Arrow (type_rec e2, u));
        u
    | Abs (_x, e) ->
        let u = TypeVar (new_vartype ()) in
        let s = Forall ([], u) in
        Arrow (u, asl_typing_expr (s :: gamma) e)
  in
  type_rec

(* Compute a decent name for type variables. *)
let tvar_name n =
  let rec name_of n =
    let q, r = (n / 26, n mod 26) in
    let s = String.make 1 (char_of_int (96 + r)) in
    if q = 0 then s else name_of q ^ s
  in
  "'" ^ name_of n

(* A printing function for type schemes. *)
let print_type_scheme (Forall (gv, t)) =
  let names =
    let rec names_of = function
      | _n, [] -> []
      | n, _ :: lv -> tvar_name n :: names_of (n + 1, lv)
    in
    names_of (1, gv)
  in
  let tvar_names = List.combine (List.rev gv) names in
  let rec print_rec = function
    | TypeVar { index = n; value = Unknown } ->
        let name =
          try List.assoc n tvar_names
          with Not_found -> raise (Typingbug "Non generic variable")
        in
        print_string name
    | TypeVar { value = t; _ } -> print_rec t
    | Number -> print_string "Number"
    | Arrow (t1, t2) ->
        print_string "(";
        print_rec t1;
        print_string " -> ";
        print_rec t2;
        print_string ")"
    | Unknown -> raise (Typingbug "print_type_scheme")
  in
  print_rec t
