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
