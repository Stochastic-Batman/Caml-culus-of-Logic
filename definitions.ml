type propositional_expr = 
        | Var of string
        | Neg of propositional_expr
        | And of propositional_expr * propositional_expr
        | Or of propositional_expr * propositional_expr
        | Implies of propositional_expr * propositional_expr
        | Equivalence of propositional_expr * propositional_expr
  
  
let rec is_valid_propositional_expr e =
        match e with
                | Var _ -> true
                | Neg expr -> is_valid_propositional_expr expr
                | And (expr1, expr2) -> is_valid_propositional_expr expr1 && is_valid_propositional_expr expr2
                | Or (expr1, expr2) -> is_valid_propositional_expr expr1 && is_valid_propositional_expr expr2
                | Implies (expr1, expr2) -> is_valid_propositional_expr expr1 && is_valid_propositional_expr expr2
                | Equivalence (expr1, expr2) -> is_valid_propositional_expr expr1 && is_valid_propositional_expr expr2
  
  
let rec string_of_propositional_expr e =
        match e with
                | Var v -> v
                | Neg expr -> "¬" ^ "(" ^ (string_of_propositional_expr expr) ^ ")"
                | And (e1, e2) -> "(" ^ (string_of_propositional_expr e1) ^ " ∧ " ^ (string_of_propositional_expr e2) ^ ")"
                | Or (e1, e2) -> "(" ^ (string_of_propositional_expr e1) ^ " ∨ " ^ (string_of_propositional_expr e2) ^ ")"
                | Implies (e1, e2) -> "(" ^ (string_of_propositional_expr e1) ^ " → " ^ (string_of_propositional_expr e2) ^ ")"
                | Equivalence (e1, e2) -> "(" ^ (string_of_propositional_expr e1) ^ " ↔ " ^ (string_of_propositional_expr e2) ^ ")"
