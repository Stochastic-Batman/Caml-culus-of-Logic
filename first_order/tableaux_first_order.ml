open Definitions
open Aux_first_order


let create_initial_st_node formula =
    {
        st_formulas = [formula];
        st_marked = false;
        st_node_type = FOLiteral;
        st_free_vars = [];
        st_skolem_counter = 0;
    }


let apply_st_alpha_rule node alpha_formula =
    let components = get_fo_alpha_components alpha_formula in
    let new_formulas = 
        List.filter (fun f -> f <> alpha_formula) node.st_formulas @ components
    in
    { node with st_formulas = new_formulas }


let apply_st_beta_rule node beta_formula =
    let components = get_fo_beta_components beta_formula in
    match components with
    | [comp1; comp2] ->
        let node1 = 
            { node with 
                st_formulas = List.filter (fun f -> f <> beta_formula) node.st_formulas @ [comp1] 
            }
        in
        let node2 = 
            { node with 
                st_formulas = List.filter (fun f -> f <> beta_formula) node.st_formulas @ [comp2] 
            }
        in
        [node1; node2]
    | _ -> [node]


let apply_st_gamma_rule node gamma_formula ground_term =
    match gamma_formula with
    | FOForall(x, f) ->
        let new_formula = subst_in_formula_first_order [(x, FOConst ground_term)] f in
        let new_formulas = gamma_formula :: node.st_formulas @ [new_formula] in
        { node with st_formulas = new_formulas }
    | FONeg(FOExists(x, f)) ->
        let new_formula = FONeg (subst_in_formula_first_order [(x, FOConst ground_term)] f) in
        let new_formulas = gamma_formula :: node.st_formulas @ [new_formula] in
        { node with st_formulas = new_formulas }
    | _ -> node


let apply_st_delta_rule node delta_formula =
    let new_const = fresh_const "c" (List.map (function FOConst c -> c | _ -> "") 
        (List.flatten (List.map (function FOAtomic(_, terms) -> terms | _ -> []) node.st_formulas))) in
    match delta_formula with
    | FOExists(x, f) ->
        let new_formula = subst_in_formula_first_order [(x, FOConst new_const)] f in
        let new_formulas = List.filter (fun f -> f <> delta_formula) node.st_formulas @ [new_formula] in
        { node with st_formulas = new_formulas; st_skolem_counter = node.st_skolem_counter + 1 }
    | FONeg(FOForall(x, f)) ->
        let new_formula = FONeg (subst_in_formula_first_order [(x, FOConst new_const)] f) in
        let new_formulas = List.filter (fun f -> f <> delta_formula) node.st_formulas @ [new_formula] in
        { node with st_formulas = new_formulas; st_skolem_counter = node.st_skolem_counter + 1 }
    | _ -> node


(* Find decomposable formula for FO semantic tableaux *)
let find_st_decomposable_formula formulas =
    let rec find = function
        | [] -> None
        | h::t ->
            if is_fo_alpha_formula h then Some (h, FOAlpha)
            else if is_fo_beta_formula h then Some (h, FOBeta)
            else if is_fo_gamma_formula h then Some (h, FOGamma)
            else if is_fo_delta_formula h then Some (h, FODelta)
            else find t
    in
    find formulas


let semantic_tableaux_first_order formula =
    let rec expand_branch branch ground_terms =
        if can_close_fo_branch branch.st_formulas then
            FOTableauClosed
        else if all_fo_formulas_are_literals branch.st_formulas then
            FOTableauOpen None
        else
            match find_st_decomposable_formula branch.st_formulas with
            | None -> FOTableauUnknown
            | Some (decomposable, typ) ->
                match typ with
                | FOAlpha ->
                    let new_branch = apply_st_alpha_rule branch decomposable in
                    expand_branch new_branch ground_terms
                | FOBeta ->
                    let new_branches = apply_st_beta_rule branch decomposable in
                    (match expand_branch (List.hd new_branches) ground_terms with
                    | FOTableauClosed -> 
                        expand_branch (List.nth new_branches 1) ground_terms
                    | result -> result)
                | FOGamma ->
                    if ground_terms = [] then
                        let new_const = fresh_const "a" [] in
                        let new_branch = apply_st_gamma_rule branch decomposable new_const in
                        expand_branch new_branch (new_const::ground_terms)
                    else
                        let new_branch = apply_st_gamma_rule branch decomposable (List.hd ground_terms) in
                        expand_branch new_branch ground_terms
                | FODelta ->
                    let new_branch = apply_st_delta_rule branch decomposable in
                    let new_const = match decomposable with
                        | FOExists(_, _) | FONeg(FOForall(_, _)) ->
                            let rec find_const = function
                                | FOAtomic(_, [FOConst c]) -> c
                                | FOAtomic(_, _) -> ""
                                | FONeg f -> find_const f
                                | _ -> ""
                            in
                            find_const (List.hd (List.rev new_branch.st_formulas))
                        | _ -> ""
                    in
                    expand_branch new_branch (if new_const <> "" then new_const::ground_terms else ground_terms)
                | _ -> FOTableauUnknown
    in
    
    let initial_branch = create_initial_st_node formula in
    expand_branch initial_branch []


(* Free Variable Tableaux *)

let create_fv_tableau_branch formula =
    {
        fvt_formulas = [formula];
        fvt_free_vars = [];
        fvt_constraints = [];
        fvt_skolem_counter = 0;
        fvt_closed = false;
    }


let fv_apply_alpha_rule branch alpha_formula =
    let components = get_fo_alpha_components alpha_formula in
    { branch with fvt_formulas = components @ branch.fvt_formulas }


let fv_apply_beta_rule branch beta_formula =
    let components = get_fo_beta_components beta_formula in
    match components with
    | [comp1; comp2] ->
        let branch1 = { branch with fvt_formulas = comp1 :: branch.fvt_formulas } in
        let branch2 = { branch with fvt_formulas = comp2 :: branch.fvt_formulas } in
        [branch1; branch2]
    | _ -> [branch]


let fv_apply_gamma_rule branch gamma_formula =
    let new_var = fresh_var "X" branch.fvt_free_vars in
    match gamma_formula with
    | FOForall(x, f) ->
        let new_formula = subst_in_formula_first_order [(x, FOVar new_var)] f in
        { branch with 
            fvt_formulas = gamma_formula :: new_formula :: branch.fvt_formulas;
            fvt_free_vars = new_var :: branch.fvt_free_vars;
        }
    | FONeg(FOExists(x, f)) ->
        let new_formula = FONeg (subst_in_formula_first_order [(x, FOVar new_var)] f) in
        { branch with 
            fvt_formulas = gamma_formula :: new_formula :: branch.fvt_formulas;
            fvt_free_vars = new_var :: branch.fvt_free_vars;
        }
    | _ -> branch


let fv_apply_delta_rule branch delta_formula =
    match delta_formula with
    | FOExists(x, f) ->
        let skolem_func = 
            if branch.fvt_free_vars = [] then
                FOConst ("c_" ^ string_of_int branch.fvt_skolem_counter)
            else
                let args = List.map (fun v -> FOVar v) branch.fvt_free_vars in
                FOFunc("f_" ^ string_of_int branch.fvt_skolem_counter, args)
        in
        let new_formula = subst_in_formula_first_order [(x, skolem_func)] f in
        { branch with 
            fvt_formulas = new_formula :: branch.fvt_formulas;
            fvt_skolem_counter = branch.fvt_skolem_counter + 1;
        }
    | FONeg(FOForall(x, f)) ->
        let skolem_func = 
            if branch.fvt_free_vars = [] then
                FOConst ("c_" ^ string_of_int branch.fvt_skolem_counter)
            else
                let args = List.map (fun v -> FOVar v) branch.fvt_free_vars in
                FOFunc("f_" ^ string_of_int branch.fvt_skolem_counter, args)
        in
        let new_formula = FONeg (subst_in_formula_first_order [(x, skolem_func)] f) in
        { branch with 
            fvt_formulas = new_formula :: branch.fvt_formulas;
            fvt_skolem_counter = branch.fvt_skolem_counter + 1;
        }
    | _ -> branch


let find_fv_unifiable_pair formulas =
    let rec find_pair = function
        | [] -> None
        | h::t ->
            match h with
            | FOAtomic(p1, terms1) ->
                let rec check_rest = function
                    | [] -> None
                    | f::rest ->
                        match f with
                        | FONeg(FOAtomic(p2, terms2)) when p1 = p2 -> 
                            Some ((terms1, terms2), (h, f))
                        | _ -> check_rest rest
                in
                check_rest t
            | FONeg(FOAtomic(p1, terms1)) ->
                let rec check_rest = function
                    | [] -> None
                    | f::rest ->
                        match f with
                        | FOAtomic(p2, terms2) when p1 = p2 -> 
                            Some ((terms1, terms2), (h, f))
                        | _ -> check_rest rest
                in
                check_rest t
            | _ -> find_pair t
    in
    find_pair formulas


let free_variable_tableaux formula =
    let rec expand_branch branch =
        if branch.fvt_closed then
            FOFVTableauClosed
        else if all_fo_formulas_are_literals branch.fvt_formulas then
            match find_fv_unifiable_pair branch.fvt_formulas with
            | Some ((terms1, terms2), (lit1, lit2)) ->
                let can_unify = 
                    try
                        let _ = List.combine terms1 terms2 in true
                    with _ -> false
                in
                if can_unify then
                    FOFVTableauClosed
                else
                    FOFVTableauOpen None
            | None -> FOFVTableauOpen None
        else
            match find_st_decomposable_formula branch.fvt_formulas with
            | None -> FOFVTableauUnknown
            | Some (decomposable, typ) ->
                match typ with
                | FOAlpha ->
                    let new_branch = fv_apply_alpha_rule branch decomposable in
                    expand_branch new_branch
                | FOBeta ->
                    let new_branches = fv_apply_beta_rule branch decomposable in
                    (match expand_branch (List.hd new_branches) with
                    | FOFVTableauClosed -> 
                        expand_branch (List.nth new_branches 1)
                    | result -> result)
                | FOGamma ->
                    let new_branch = fv_apply_gamma_rule branch decomposable in
                    expand_branch new_branch
                | FODelta ->
                    let new_branch = fv_apply_delta_rule branch decomposable in
                    expand_branch new_branch
                | _ -> FOFVTableauUnknown
    in
    
    let initial_branch = create_fv_tableau_branch formula in
    expand_branch initial_branch


(* Top-level proving functions *)

let prove_by_semantic_tableaux formula =
    match semantic_tableaux_first_order (FONeg formula) with
    | FOTableauClosed -> true
    | _ -> false



let prove_by_free_variable_tableaux formula =
    match free_variable_tableaux (FONeg formula) with
    | FOFVTableauClosed -> true
    | _ -> false
