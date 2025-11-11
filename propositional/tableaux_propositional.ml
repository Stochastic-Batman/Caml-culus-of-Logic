open Definitions
open Aux_propositional

let is_alpha_formula (expr : propositional_expr) : bool =
    match expr with
    | Neg (Neg _) -> true
    | And (_, _) -> true
    | Neg (Or (_, _)) -> true
    | Neg (Implies (_, _)) -> true
    | Equivalence (_, _) -> true
    | _ -> false


let is_beta_formula (expr : propositional_expr) : bool =
    match expr with
    | Or (_, _) -> true
    | Neg (And (_, _)) -> true
    | Implies (_, _) -> true
    | Neg (Equivalence (_, _)) -> true
    | _ -> false


let get_alpha_components (expr : propositional_expr) : propositional_expr list =
    match expr with
    | Neg (Neg e) -> [e]
    | And (e1, e2) -> [e1; e2]
    | Neg (Or (e1, e2)) -> [Neg e1; Neg e2]
    | Neg (Implies (e1, e2)) -> [e1; Neg e2]
    | Equivalence (e1, e2) -> [Implies (e1, e2); Implies (e2, e1)]
    | _ -> []


let get_beta_components (expr : propositional_expr) : propositional_expr list =
    match expr with
    | Or (e1, e2) -> [e1; e2]
    | Neg (And (e1, e2)) -> [Neg e1; Neg e2]
    | Implies (e1, e2) -> [Neg e1; e2]
    | Neg (Equivalence (e1, e2)) -> [Neg (Implies (e1, e2)); Neg (Implies (e2, e1))]
    | _ -> []


let has_complementary_literals (formulas : propositional_expr list) : bool =
    let rec check_complementary = function
        | [] -> false
        | h :: t ->
            match h with
            | Var v -> List.exists (function Neg (Var v') when v = v' -> true | _ -> false) t
            | Neg (Var v) -> List.exists (function Var v' when v = v' -> true | _ -> false) t
            | _ -> check_complementary t
    in
    check_complementary formulas


let has_formula_and_negation (formulas : propositional_expr list) : bool =
    let rec check_contradiction = function
        | [] -> false
        | h :: t ->
            List.exists (fun f -> f = negate_propositional_expr h) t || check_contradiction t
    in
    check_contradiction formulas


let can_close_node (formulas : propositional_expr list) : bool = 
    has_complementary_literals formulas || has_formula_and_negation formulas


let all_formulas_are_literals (formulas : propositional_expr list) : bool =
    List.for_all (function
        | Var _ -> true
        | Neg (Var _) -> true
        | _ -> false
    ) formulas


let extract_valuation_from_branch (formulas : propositional_expr list) : (string * bool) list =
    let rec extract_vals acc = function
        | [] -> acc
        | Var v :: t -> 
            if not (List.mem_assoc v acc) then
                extract_vals ((v, true) :: acc) t
            else
                extract_vals acc t
        | Neg (Var v) :: t -> 
            if not (List.mem_assoc v acc) then
                extract_vals ((v, false) :: acc) t
            else
                extract_vals acc t
        | _ :: t -> extract_vals acc t
    in
    List.rev (extract_vals [] formulas)


(* Semantic Tableaux *)

let create_initial_node (formula : propositional_expr) : tableau_node_propositional = {
    formulas = [formula];
    marked = false;
    node_type = Literal
}


let apply_alpha_rule (node : tableau_node_propositional) (alpha_formula : propositional_expr) : tableau_node_propositional =
    let components = get_alpha_components alpha_formula in
    let new_formulas = 
        List.filter (fun f -> f <> alpha_formula) node.formulas @ components
    in
    { node with formulas = new_formulas }


let apply_beta_rule (node : tableau_node_propositional) (beta_formula : propositional_expr) : tableau_node_propositional list =
    let components = get_beta_components beta_formula in
    match components with
    | [comp1; comp2] ->
        let node1_formulas = 
            List.filter (fun f -> f <> beta_formula) node.formulas @ [comp1]
        in
        let node2_formulas = 
            List.filter (fun f -> f <> beta_formula) node.formulas @ [comp2]
        in
        [
            { formulas = node1_formulas; marked = false; node_type = Beta };
            { formulas = node2_formulas; marked = false; node_type = Beta }
        ]
    | _ -> [node]  (* Should not happen for valid beta formulas *)


let rec find_decomposable_formula (formulas : propositional_expr list) : (propositional_expr * tableau_node_type_propositional) option =
    match formulas with
    | [] -> None
    | h :: t ->
        if is_alpha_formula h then Some (h, Alpha)
        else if is_beta_formula h then Some (h, Beta)
        else find_decomposable_formula t


let semantic_tableaux_propositional (formula : propositional_expr) : tableau_result_propositional =
    let rec build_tableaux (nodes : tableau_node_propositional list) : tableau_result_propositional =
        match nodes with
        | [] -> TableauUnknown
        | node :: rest ->
            if node.marked then
                build_tableaux rest
            else if can_close_node node.formulas then
                (* Mark as closed and continue *)
                build_tableaux ({ node with marked = true } :: rest)
            else if all_formulas_are_literals node.formulas then
                (* All formulas are literals and no contradiction - mark as open *)
                TableauOpen (extract_valuation_from_branch node.formulas)
            else
                match find_decomposable_formula node.formulas with
                | None ->
                    (* No more formulas to decompose but not all literals - this shouldn't happen *)
                    TableauUnknown
                | Some (decomposable_formula, formula_type) ->
                    if formula_type = Alpha then
                        let new_node = apply_alpha_rule node decomposable_formula in
                        build_tableaux (new_node :: rest)
                    else
                        let new_nodes = apply_beta_rule node decomposable_formula in
                        (* For beta rules, process both branches *)
                        match build_tableaux (List.hd new_nodes :: rest) with
                        | TableauClosed -> 
                            (* If first branch closes, check second branch *)
                            build_tableaux (List.nth new_nodes 1 :: rest)
                        | result -> result
    in
    
    let initial_node = create_initial_node formula in
    build_tableaux [initial_node]


(* Analytic Tableaux *)

let analytic_apply_alpha_rule (node : tableau_node_propositional) (alpha_formula : propositional_expr) : tableau_node_propositional =
    let components = get_alpha_components alpha_formula in
    { node with formulas = components }  (* Don't keep other formulas *)


let analytic_apply_beta_rule (node : tableau_node_propositional) (beta_formula : propositional_expr) : tableau_node_propositional list =
    let components = get_beta_components beta_formula in
    match components with
    | [comp1; comp2] ->
        [
            { formulas = [comp1]; marked = false; node_type = Beta };
            { formulas = [comp2]; marked = false; node_type = Beta }
        ]
    | _ -> [node]  (* Should not happen for valid beta formulas *)


let analytic_tableaux_propositional (formula : propositional_expr) : tableau_result_propositional =
    let rec build_analytic_tableaux (branch_nodes : tableau_node_propositional list) : tableau_result_propositional =
        match branch_nodes with
        | [] -> TableauUnknown
        | nodes ->
            (* Check if current branch can be closed *)
            let all_formulas = List.concat (List.map (fun n -> n.formulas) nodes) in
            
            if can_close_node all_formulas then
                TableauClosed
            else if List.for_all (fun n -> all_formulas_are_literals n.formulas) nodes then
                (* All formulas are literals and no contradiction - branch is open *)
                TableauOpen (extract_valuation_from_branch all_formulas)
            else
                (* Find next formula to decompose in the branch *)
                let decomposable_option = 
                    List.fold_left (fun acc node ->
                        match acc with
                        | Some _ -> acc
                        | None -> find_decomposable_formula node.formulas
                    ) None nodes
                in
                
                match decomposable_option with
                | None ->
                    (* No more formulas to decompose - branch is open *)
                    TableauOpen (extract_valuation_from_branch all_formulas)
                | Some (decomposable_formula, formula_type) ->
                    (* Find the node containing this formula *)
                    let node_index = 
                        List.find_index (fun node -> 
                            List.mem decomposable_formula node.formulas
                        ) nodes
                    in
                    
                    match node_index with
                    | None -> TableauUnknown
                    | Some index ->
                        let target_node = List.nth nodes index in
                        let remaining_nodes = 
                            List.mapi (fun i node -> if i = index then None else Some node) nodes
                            |> List.filter_map (fun x -> x)
                        in
                        
                        if formula_type = Alpha then
                            let new_node = analytic_apply_alpha_rule target_node decomposable_formula in
                            build_analytic_tableaux (new_node :: remaining_nodes)
                        else
                            let new_nodes = analytic_apply_beta_rule target_node decomposable_formula in
                            (* For beta rules, we need to create two separate branches *)
                            let branch1_result = build_analytic_tableaux (List.hd new_nodes :: remaining_nodes) in
                            match branch1_result with
                            | TableauClosed -> 
                                build_analytic_tableaux (List.nth new_nodes 1 :: remaining_nodes)
                            | result -> result
    in
    
    let initial_node = create_initial_node formula in
    build_analytic_tableaux [initial_node]


let complete_semantic_tableaux_propositional (formula : propositional_expr) : tableau_result_propositional =
    semantic_tableaux_propositional formula


(* Top-level proving functions *)

let prove_by_tableaux (formula : propositional_expr) : bool =
    match complete_semantic_tableaux_propositional (negate_propositional_expr formula) with
    | TableauClosed -> true   (* ¬F is unsatisfiable, so F is valid *)
    | TableauOpen _ -> false  (* ¬F is satisfiable, so F is not valid *)
    | TableauUnknown -> false


let is_unsatisfiable_tableaux (formula : propositional_expr) : bool =
    match complete_semantic_tableaux_propositional formula with
    | TableauClosed -> true
    | TableauOpen _ -> false
    | TableauUnknown -> false
