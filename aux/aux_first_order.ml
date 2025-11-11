open Definitions

(* Term utilities *)

let rec vars_of_term_first_order = function
    | FOVar v -> [v]
    | FOConst _ -> []
    | FOFunc(_, terms) -> List.flatten (List.map vars_of_term_first_order terms)

let rec subst_in_term_first_order (subst: substitution_first_order) = function
    | FOVar v -> (try List.assoc v subst with Not_found -> FOVar v)
    | FOConst c -> FOConst c
    | FOFunc(f, terms) -> FOFunc(f, List.map (subst_in_term_first_order subst) terms)

let rec occurs_in_first_order v = function
    | FOVar v' -> v = v'
    | FOConst _ -> false
    | FOFunc(_, terms) -> List.exists (occurs_in_first_order v) terms

(* Formula utilities *)

let rec free_vars_first_order = function
    | FOAtomic(_, terms) -> List.flatten (List.map vars_of_term_first_order terms)
    | FONeg f -> free_vars_first_order f
    | FOAnd(f1, f2) -> free_vars_first_order f1 @ free_vars_first_order f2
    | FOOr(f1, f2) -> free_vars_first_order f1 @ free_vars_first_order f2
    | FOImplies(f1, f2) -> free_vars_first_order f1 @ free_vars_first_order f2
    | FOEquiv(f1, f2) -> free_vars_first_order f1 @ free_vars_first_order f2
    | FOForall(x, f) -> List.filter (fun v -> v <> x) (free_vars_first_order f)
    | FOExists(x, f) -> List.filter (fun v -> v <> x) (free_vars_first_order f)

let rec bound_vars_first_order = function
    | FOAtomic _ -> []
    | FONeg f -> bound_vars_first_order f
    | FOAnd(f1, f2) -> bound_vars_first_order f1 @ bound_vars_first_order f2
    | FOOr(f1, f2) -> bound_vars_first_order f1 @ bound_vars_first_order f2
    | FOImplies(f1, f2) -> bound_vars_first_order f1 @ bound_vars_first_order f2
    | FOEquiv(f1, f2) -> bound_vars_first_order f1 @ bound_vars_first_order f2
    | FOForall(x, f) -> x :: bound_vars_first_order f
    | FOExists(x, f) -> x :: bound_vars_first_order f

let is_closed_first_order formula = free_vars_first_order formula = []

let rec subst_in_formula_first_order (subst: substitution_first_order) = function
    | FOAtomic(p, terms) -> FOAtomic(p, List.map (subst_in_term_first_order subst) terms)
    | FONeg f -> FONeg (subst_in_formula_first_order subst f)
    | FOAnd(f1, f2) ->
        FOAnd(subst_in_formula_first_order subst f1, subst_in_formula_first_order subst f2)
    | FOOr(f1, f2) ->
        FOOr(subst_in_formula_first_order subst f1, subst_in_formula_first_order subst f2)
    | FOImplies(f1, f2) ->
        FOImplies(subst_in_formula_first_order subst f1, subst_in_formula_first_order subst f2)
    | FOEquiv(f1, f2) ->
        FOEquiv(subst_in_formula_first_order subst f1, subst_in_formula_first_order subst f2)
    | FOForall(x, f) ->
        let subst' = List.filter (fun (v, _) -> v <> x) subst in
        FOForall(x, subst_in_formula_first_order subst' f)
    | FOExists(x, f) ->
        let subst' = List.filter (fun (v, _) -> v <> x) subst in
        FOExists(x, subst_in_formula_first_order subst' f)

(* String conversions *)

let rec string_of_term_first_order = function
    | FOVar v -> v
    | FOConst c -> c
    | FOFunc(f, []) -> f ^ "()"
    | FOFunc(f, terms) -> f ^ "(" ^ String.concat ", " (List.map string_of_term_first_order terms) ^ ")"

let rec string_of_formula_first_order = function
    | FOAtomic(p, []) -> p
    | FOAtomic(p, terms) -> p ^ "(" ^ String.concat ", " (List.map string_of_term_first_order terms) ^ ")"
    | FONeg f -> "¬" ^ string_of_formula_first_order f
    | FOAnd(f1, f2) -> "(" ^ string_of_formula_first_order f1 ^ " ∧ " ^ string_of_formula_first_order f2 ^ ")"
    | FOOr(f1, f2) -> "(" ^ string_of_formula_first_order f1 ^ " ∨ " ^ string_of_formula_first_order f2 ^ ")"
    | FOImplies(f1, f2) -> "(" ^ string_of_formula_first_order f1 ^ " → " ^ string_of_formula_first_order f2 ^ ")"
    | FOEquiv(f1, f2) -> "(" ^ string_of_formula_first_order f1 ^ " ↔ " ^ string_of_formula_first_order f2 ^ ")"
    | FOForall(x, f) -> "∀" ^ x ^ ". " ^ string_of_formula_first_order f
    | FOExists(x, f) -> "∃" ^ x ^ ". " ^ string_of_formula_first_order f


let compose_substitutions_first_order subst1 subst2 =
    let applied_subst1 = List.map (fun (x, t) -> (x, subst_in_term_first_order subst2 t)) subst1 in
    let subst2_filtered = List.filter (fun (x, _) -> not (List.mem_assoc x subst1)) subst2 in
    applied_subst1 @ subst2_filtered
