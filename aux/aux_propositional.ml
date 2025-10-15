open Definitions


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


let string_of_propositional_sequent seq =
        let aux lst = 
                if lst = [] then "∅"
                else String.concat ", " (List.map string_of_propositional_expr lst)
        in
        (aux seq.antecedent) ^ " ⟶ " ^ (aux seq.consequent)


let rec negate_propositional_expr expr = 
        match expr with
                | Var e -> Neg (Var e)
                | Neg e -> e
                | And (e1, e2) -> Or (negate_propositional_expr e1, negate_propositional_expr e2)
                | Or (e1, e2) -> And (negate_propositional_expr e1, negate_propositional_expr e2)
                | Implies (e1, e2) -> And (e1, negate_propositional_expr e2)
                | Equivalence (e1, e2) -> Or (And (e1, negate_propositional_expr e2), And (negate_propositional_expr e1, e2))


let rec distribute_or_over_and e1 e2 =
        match e1, e2 with
                | And (a, b), c -> And (distribute_or_over_and a c, distribute_or_over_and b c)
                | a, And (b, c) -> And (distribute_or_over_and a b, distribute_or_over_and a c)
                | _ -> Or (e1, e2)


let rec distribute_and_over_or e1 e2 =
        match e1, e2 with
                | Or (a, b), c -> Or (distribute_and_over_or a c, distribute_and_over_or b c)
                | a, Or (b, c) -> Or (distribute_and_over_or a b, distribute_and_over_or a c)
                | _ -> And (e1, e2)


let cnf_clauses expr =
        let rec extract_clause e =
                match e with
                | Or (e1, e2) ->
                        let clause1 = extract_clause e1 in
                        let clause2 = extract_clause e2 in
                        clause1 @ clause2
                | Var v -> [Var v]
                | Neg (Var v) -> [Neg (Var v)]
                | _ -> [e]  (* Fallback for unexpected cases, but this should not happen in the first place *)
        in
        let rec collect_clauses e acc =
                match e with
                | And (e1, e2) ->
                        let acc1 = collect_clauses e1 acc in
                        collect_clauses e2 acc1
                | _ ->  (* Fallback for unexpected cases, but this should not happen in the first place *)
                        let clause = extract_clause e in
                        clause :: acc
        in
        List.rev (collect_clauses expr [])


let are_complementary e1 e2 =
        match e1, e2 with
        | Var v1, Neg (Var v2) -> v1 = v2
        | Neg (Var v1), Var v2 -> v1 = v2
        | _ -> false


let remove_literal c x = List.filter (fun el -> el <> x) c


let contains_literal c x = List.exists (fun el -> el = x) c


let remove_duplicates c =
        let rec aux seen = function
                | [] -> List.rev seen
                | h :: t -> if List.mem h seen then aux seen t else aux (h :: seen) t
        in
        aux [] c
