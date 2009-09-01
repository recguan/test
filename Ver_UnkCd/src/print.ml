open Type

let rec print_exp ex =
  match ex with
    | Var v -> v
    | LVar v -> v
    | SVar v -> v
    | Ref ex -> "[" ^ (print_exp ex) ^ "]"
    | Nil -> "nil" 

let print_pure pr =
  match pr with
    | Eq (ex_1, ex_2) -> (print_exp ex_1) ^ "==" ^ (print_exp ex_2) ^ " "
    | Neq (ex_1, ex_2) -> (print_exp ex_1) ^ "!=" ^ (print_exp ex_2) ^ " "
    | PTop -> "PT "

let print_sep sp =
  match sp with
    | Point (ex_1, ex_2) -> (print_exp ex_1) ^ "|->" ^ (print_exp ex_2) ^ " "
    | Lseg (ex_1, ex_2) -> "lseg(" ^ (print_exp ex_1) ^ "," ^ (print_exp ex_2) ^ ") "
    | Emp -> "emp "
    | Junk -> "junk "
    | STop -> "ST "
