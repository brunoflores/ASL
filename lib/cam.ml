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
