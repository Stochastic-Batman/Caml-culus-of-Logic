open Definitions
open Aux_first_order


(* Unification Algorithm *)

let rec unify equations =
    match equations with
    | [] -> Unifiable []
    | (s, t) :: rest ->
        if s = t then
            unify rest
        else
            match (s, t) with
            | (FOVar x, t) when not (occurs_in_first_order x t) ->
                let subst = [(x, t)] in
                let rest_subst = List.map (fun (s', t') ->
                    (subst_in_term_first_order subst s', subst_in_term_first_order subst t')) rest
                in
                (match unify rest_subst with
                 | Unifiable subst' -> Unifiable (compose_substitutions_first_order subst subst')
                 | NotUnifiable msg -> NotUnifiable msg)
            | (t, FOVar x) when not (occurs_in_first_order x t) -> unify ((FOVar x, t) :: rest)
            | (FOFunc(f, args1), FOFunc(g, args2)) when f = g && List.length args1 = List.length args2 -> 
                let new_equations = List.combine args1 args2 @ rest in unify new_equations
            | _ -> NotUnifiable ("Cannot unify " ^ string_of_term_first_order s ^ " with " ^ string_of_term_first_order t)


(* Most General Unifier (MGU) *)

let mgu terms1 terms2 =
    if List.length terms1 <> List.length terms2 then NotUnifiable "Different number of terms"
    else let equations = List.combine terms1 terms2 in unify equations


(* Unification with occurs check *)

let unify_with_occurs_check equations =
    let rec unify_aux equations subst =
        match equations with
        | [] -> Unifiable subst
        | (s, t) :: rest ->
            let s_subst = subst_in_term_first_order subst s in
            let t_subst = subst_in_term_first_order subst t in
            if s_subst = t_subst then
                unify_aux rest subst
            else
                match (s_subst, t_subst) with
                | (FOVar x, t') when not (occurs_in_first_order x t') ->
                    let new_subst = compose_substitutions_first_order subst [(x, t')] in
                    let rest_subst = List.map (fun (s', t') ->
                        (subst_in_term_first_order [(x, t')] s', subst_in_term_first_order [(x, t')] t')) rest
                    in
                    unify_aux rest_subst new_subst
                | (t', FOVar x) when not (occurs_in_first_order x t') -> unify_aux ((FOVar x, t') :: rest) subst
                | (FOFunc(f, args1), FOFunc(g, args2)) when f = g && List.length args1 = List.length args2 -> 
                    let new_equations = List.combine args1 args2 @ rest in unify_aux new_equations subst
                | _ -> NotUnifiable ("Cannot unify " ^ string_of_term_first_order s_subst ^ " with " ^ string_of_term_first_order t_subst)
    in
    unify_aux equations []


(* Pattern matching (one-way unification) *)

let pattern_match pattern target =
    match (pattern, target) with
    | (FOVar x, t) -> Unifiable [(x, t)]
    | (FOConst c1, FOConst c2) when c1 = c2 -> Unifiable []
    | (FOFunc(f1, args1), FOFunc(f2, args2)) when f1 = f2 && List.length args1 = List.length args2 -> 
        let equations = List.combine args1 args2 in unify equations
    | _ -> NotUnifiable "Pattern does not match"


let are_unifiable s t = match unify [(s, t)] with Unifiable _ -> true | NotUnifiable _ -> false
