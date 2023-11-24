type asl =
  | CONST of int
  | Var of int
  | Cond of asl * asl * asl
  | App of asl * asl
  | Abs of string * asl

let () = print_endline "Hello, World!"
