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



(* Formula classification for first-order tableaux *)

let is_fo_alpha_formula = function
    | FOAnd(_, _) -> true
    | FONeg(FOOr(_, _)) -> true
    | FONeg(FOImplies(_, _)) -> true
    | FOEquiv(_, _) -> true
    | _ -> false



let is_fo_beta_formula = function
    | FOOr(_, _) -> true
    | FOImplies(_, _) -> true
    | FONeg(FOAnd(_, _)) -> true
    | FONeg(FOEquiv(_, _)) -> true
    | _ -> false



let is_fo_gamma_formula = function
    | FOForall(_, _) -> true
    | FONeg(FOExists(_, _)) -> true
    | _ -> false



let is_fo_delta_formula = function
    | FOExists(_, _) -> true
    | FONeg(FOForall(_, _)) -> true
    | _ -> false



let is_fo_literal = function
    | FOAtomic(_, _) -> true
    | FONeg(FOAtomic(_, _)) -> true
    | _ -> false



(* Get components for FO formulas *)
let get_fo_alpha_components = function
    | FOAnd(f1, f2) -> [f1; f2]
    | FONeg(FOOr(f1, f2)) -> [FONeg f1; FONeg f2]
    | FONeg(FOImplies(f1, f2)) -> [f1; FONeg f2]
    | FOEquiv(f1, f2) -> [FOImplies(f1, f2); FOImplies(f2, f1)]
    | _ -> []



let get_fo_beta_components = function
    | FOOr(f1, f2) -> [f1; f2]
    | FOImplies(f1, f2) -> [FONeg f1; f2]
    | FONeg(FOAnd(f1, f2)) -> [FONeg f1; FONeg f2]
    | FONeg(FOEquiv(f1, f2)) -> [FONeg(FOImplies(f1, f2)); FONeg(FOImplies(f2, f1))]
    | _ -> []



(* Check for complementary literals in FO *)
let are_fo_complementary_literals lit1 lit2 =
    match (lit1, lit2) with
    | (FOAtomic(p1, _), FONeg(FOAtomic(p2, _))) 
    | (FONeg(FOAtomic(p2, _)), FOAtomic(p1, _)) ->
        p1 = p2
    | _ -> false



(* Check if a FO branch can be closed *)
let can_close_fo_branch formulas =
    let rec check_pairwise = function
        | [] -> false
        | h::t ->
            List.exists (fun f -> are_fo_complementary_literals h f) t 
            || check_pairwise t
    in
    check_pairwise formulas



(* Check if all formulas are FO literals *)
let all_fo_formulas_are_literals formulas =
    List.for_all is_fo_literal formulas



(* Generate fresh constant name *)
let fresh_const base used_consts =
    let rec fresh n =
        let const_name = base ^ string_of_int n in
        if List.mem const_name used_consts then
            fresh (n + 1)
        else
            const_name
    in
    fresh 0



(* Generate fresh variable name *)
let fresh_var base used_vars =
    let rec fresh n =
        let var_name = base ^ string_of_int n in
        if List.mem var_name used_vars then
            fresh (n + 1)
        else
            var_name
    in
    fresh 0
