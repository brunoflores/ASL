let subtract l1 l2 =
  match l2 with
  | [] -> l1
  | l2 ->
      let rec subtract_l2 = function
        | [] -> []
        | head :: tail ->
            if List.mem head l2 then subtract_l2 tail
            else head :: subtract_l2 tail
      in
      subtract_l2 l1
