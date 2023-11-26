type instruction =
  | Quote of int (* Integer constants *)
  | Plus (* Arithmetic operations *)
  | Minus
  | Divide
  | Equal
  | Times
  | Nth of int (* Variable accesses *)
  | Branch of instruction list * instruction list (* Conditional execution *)
  | Push (* Pushes onto the stack *)
  | Swap (* Exchange top of stack and register *)
  | Clos of instruction list (* Builds a closure with current environment *)
  | Apply (* Function application *)
[@@deriving show, eq]

type instr_list = instruction list [@@deriving show, eq]

type obj =
  | Constant of int
  | Closure of obj * obj
  | Address of instruction list
  | Environment of obj list

type state = {
  mutable reg : obj;
  mutable pc : instruction list;
  mutable stack : obj list;
}

(* Operational semantics of CAM *)
(* The effect of an instruction is to change the state configuration. *)
exception CAMbug of string
exception CAMend of obj

let step state =
  match state with
  | { pc = Quote n :: code; _ } ->
      state.reg <- Constant n;
      state.pc <- code
  | { pc = Plus :: code; reg = Constant m; stack = Constant n :: s } ->
      state.reg <- Constant (n + m);
      state.stack <- s;
      state.pc <- code
  | { pc = Minus :: code; reg = Constant m; stack = Constant n :: s } ->
      state.reg <- Constant (n - m);
      state.stack <- s;
      state.pc <- code
  | { pc = Times :: code; reg = Constant m; stack = Constant n :: s } ->
      state.reg <- Constant (n * m);
      state.stack <- s;
      state.pc <- code
  | { pc = Divide :: code; reg = Constant m; stack = Constant n :: s } ->
      state.reg <- Constant (n / m);
      state.stack <- s;
      state.pc <- code
  | { pc = Equal :: code; reg = Constant m; stack = Constant n :: s } ->
      state.reg <- Constant (if n = m then 1 else 0);
      state.stack <- s;
      state.pc <- code
  | { pc = Branch (code1, code2) :: code; reg = Constant m; stack = r :: s } ->
      state.reg <- r;
      state.stack <- Address code :: s;
      state.pc <- (if m = 0 then code2 else code1)
  | { pc = Push :: code; reg = r; stack = s } ->
      state.stack <- r :: s;
      state.pc <- code
  | { pc = Swap :: code; reg = r1; stack = r2 :: s } ->
      state.reg <- r2;
      state.stack <- r1 :: s;
      state.pc <- code
  | { pc = Clos code1 :: code; reg = r; _ } ->
      state.reg <- Closure (Address code1, r);
      state.pc <- code
  | { pc = []; stack = Address code :: s; _ } ->
      state.stack <- s;
      state.pc <- code
  | {
   pc = Apply :: code;
   reg = v;
   stack = Closure (Address code1, Environment e) :: s;
  } ->
      state.reg <- Environment (v :: e);
      state.stack <- Address code :: s;
      state.pc <- code1
  | { pc = []; reg = v; stack = [] } -> raise (CAMend v)
  | { pc = (Plus | Minus | Times | Divide | Equal) :: _; stack = _ :: _; _ } ->
      raise (CAMbug "IllTyped")
  | { pc = Nth n :: code; reg = Environment e; _ } ->
      state.reg <-
        (try List.nth e n with Failure _ -> raise (CAMbug "IllTyped"));
      state.pc <- code
  | _ -> raise (CAMbug "Wrong configuration")

(** The compilation scheme:

  * The code of a constant is [Quote];

  * A variable is compile as an access to the appropriate component of the
    current environment ([Nth]);

  * Conditional expression will save the current environment ([Push]),
    evaluate the condition part, and, according to the boolean value obtained,
    select the appropriate code to execute ([Branch]);

  * Application will save the environment on the stack ([Push]), execute
    the function part of the application, then exchange the functional value and
    the saved environment ([Swap]), evaluate the argument and, finally,
    apply the functional value (which is at the top of the stack) to
    the argument held in the register with the [Apply] instruction;

  * Abstraction simply consists in building a clusure representing the
    functional value: the closure is composed of the code of the function
    and the current environment. *)
let rec code_of = function
  | Ast.Const n -> [ Quote n ]
  | Var n -> [ Nth n ]
  | Cond (e1, e2, e3) ->
      (Push :: code_of e1) @ [ Branch (code_of e2, code_of e3) ]
  | App (e1, e2) -> (Push :: code_of e1) @ [ Swap ] @ code_of e2 @ [ Apply ]
  | Abs (_, e) -> [ Clos (code_of e) ]

let init_cam_env =
  let basic_instruction = function
    | "+" -> Plus
    | "-" -> Minus
    | "*" -> Times
    | "/" -> Divide
    | "=" -> Equal
    | s -> raise (CAMbug (Format.sprintf "Unknown primitive: %s" s))
  in
  List.map
    (function
      | s ->
          let code =
            [ Clos (Push :: Nth 2 :: Swap :: Nth 1 :: [ basic_instruction s ]) ]
          in
          Closure (Address code, Environment []))
    Sem.init_env

let global_cam_env = ref init_cam_env

let test_it ast instrs =
  let code = code_of ast in
  if not (equal_instr_list code instrs) then (
    print_endline
    @@ Format.sprintf "\nwant: %s\ngot: %s\n\n" (show_instr_list instrs)
         (show_instr_list code);
    raise (Failure ""))
  else ()

let%test_unit _ =
  let ast = Ast.Const 1 in
  let instrs = [ Quote 1 ] in
  test_it ast instrs

let%test_unit _ =
  let instrs =
    [ Push; Push; Nth 6; Swap; Quote 1; Apply; Swap; Quote 2; Apply ]
  in
  let ast = Ast.App (App (Var 6, Const 1), Const 2) in
  test_it ast instrs

let%test_unit _ =
  let instrs =
    [
      Push;
      Clos [ Nth 1 ];
      Swap;
      Push;
      Clos [ Nth 1 ];
      Swap;
      Quote 0;
      Apply;
      Apply;
    ]
  in
  let ast = Ast.App (Abs ("x", Var 1), App (Abs ("x", Var 1), Const 0)) in
  test_it ast instrs

let%test_unit _ =
  let instrs =
    [
      Push;
      Push;
      Nth 6;
      Swap;
      Quote 1;
      Apply;
      Swap;
      Push;
      Quote 0;
      Branch ([ Quote 2 ], [ Quote 3 ]);
      Apply;
    ]
  in
  let ast = Ast.App (App (Var 6, Const 1), Cond (Const 0, Const 2, Const 3)) in
  test_it ast instrs

(* The main function for executing compiled ASL manages the global environment
   until execution has succeeded. *)
let run (Ast.Decl (s, e)) =
  let open Type in
  (* Typing *)
  Type.reset_vartypes ();
  let tau =
    try asl_typing_expr !global_typing_env e with
    | Typeclash (t1, t2) ->
        let vars = vars_of_type t1 @ vars_of_type t2 in
        print_string "ASL Type clash between ";
        print_type_scheme (Forall (vars, t1));
        print_string " and ";
        print_type_scheme (Forall (vars, t2));
        raise (Failure "ASL typing")
    | Ast.Unbound s -> raise (Typingbug ("Unbound: " ^ s))
  in
  let sigma = generalise_type (!global_typing_env, tau) in
  (* Printing type information *)
  print_string "ASL Type of ";
  print_string s;
  print_string " is ";
  print_type_scheme sigma;
  print_newline ();
  (* Compiling *)
  let code = code_of e in
  let state = { reg = Environment !global_cam_env; pc = code; stack = [] } in
  (* Executing *)
  let result =
    try
      while true do
        step state
      done;
      state.reg
    with CAMend v -> v
  in
  (* Updating environments *)
  Sem.global_env := s :: !Sem.global_env;
  global_typing_env := sigma :: !global_typing_env;
  global_cam_env := result :: !global_cam_env;
  (* Printing result *)
  (match result with
  | Constant n -> print_int n
  | Closure _ -> print_string "<funval>"
  | _ -> raise (CAMbug "Wrong state configuration"));
  print_newline ()
