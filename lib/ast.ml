type asl =
  | Const of int
  | Var of int
  | Cond of asl * asl * asl
  | App of asl * asl
  | Abs of string * asl

and top_asl = Decl of string * asl
