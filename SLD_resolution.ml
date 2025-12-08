open Definitions
open Unification_first_order


(* Convert SLD terms to first-order terms for unification *)
let rec term_sld_to_fo = function 
    | SLD_Var v -> FOVar v 
    | SLD_Const c -> FOConst c 
    | SLD_Func(f, args) -> FOFunc(f, List.map term_sld_to_fo args)

(* Convert first-order terms back to SLD terms *)
let rec term_fo_to_sld = function
    | FOVar v -> SLD_Var v
    | FOConst c -> SLD_Const c
    | FOFunc(f, args) -> SLD_Func(f, List.map term_fo_to_sld args)

(* Convert first-order substitution to SLD substitution *)
let subst_fo_to_sld subst = 
    List.map (fun (v, t) -> (v, term_fo_to_sld t)) subst

let atom_sld_to_fo (pred, terms) = FOAtomic(pred, List.map term_sld_to_fo terms)

let rec apply_substitution_sld subst = function
    | SLD_Var v -> (try List.assoc v subst with Not_found -> SLD_Var v)
    | SLD_Const c -> SLD_Const c
    | SLD_Func(f, args) -> SLD_Func(f, List.map (apply_substitution_sld subst) args)

let apply_substitution_atom_sld subst (pred, terms) = 
    (pred, List.map (apply_substitution_sld subst) terms)

let apply_substitution_goal_sld subst goal = 
    List.map (apply_substitution_atom_sld subst) goal

(* Most General Unifier for SLD terms - returns substitution_sld directly *)
let mgu_sld (pred1, terms1) (pred2, terms2) =
    if pred1 <> pred2 then
        None
    else
        let fo_terms1 = List.map term_sld_to_fo terms1 in
        let fo_terms2 = List.map term_sld_to_fo terms2 in
        match mgu fo_terms1 fo_terms2 with
        | Unifiable subst -> Some (subst_fo_to_sld subst)
        | NotUnifiable _ -> None

(* Rename variables in a clause to avoid conflicts *)
let rename_variables clause counter =
    let rec rename_term subst counter = function
        | SLD_Var v ->
            let new_name = v ^ "_" ^ string_of_int !counter in
            incr counter;
            (SLD_Var new_name, (v, SLD_Var new_name) :: subst)
        | SLD_Const c -> (SLD_Const c, subst)
        | SLD_Func(f, args) ->
            let (new_args, subst_acc) =
                List.fold_left (fun (acc_args, acc_subst) t ->
                    let (new_t, new_subst) = rename_term acc_subst counter t in
                    (new_t :: acc_args, new_subst)
                ) ([], subst) args in
            (SLD_Func(f, List.rev new_args), subst_acc)
    in
    
    let rename_atom subst counter (pred, terms) =
        let (new_terms, new_subst) =
            List.fold_left (fun (acc_terms, acc_subst) t ->
                let (new_t, updated_subst) = rename_term acc_subst counter t in
                (new_t :: acc_terms, updated_subst)
            ) ([], subst) terms in
        ((pred, List.rev new_terms), new_subst)
    in
    
    let counter_ref = ref counter in
    let (new_head, subst1) = rename_atom [] counter_ref clause.head in
    let (new_body, _) =
        List.fold_left (fun (acc_body, acc_subst) atom ->
            let (new_atom, new_subst) = rename_atom acc_subst counter_ref atom in
            (new_atom :: acc_body, new_subst)
        ) ([], subst1) clause.body in
    
    { head = new_head; body = List.rev new_body }, !counter_ref

(* Helper functions for List.take and List.drop *)
let rec take n lst =
    match (n, lst) with
    | (0, _) | (_, []) -> []
    | (n, hd :: tl) -> hd :: take (n - 1) tl

let rec drop n lst =
    match (n, lst) with
    | (0, _) -> lst
    | (_, []) -> []
    | (n, _ :: tl) -> drop (n - 1) tl

(* One SLD resolution step *)
let sld_step program goal selected_index =
    if selected_index >= List.length goal then None
    else
        let selected_atom = List.nth goal selected_index in
        let rec try_clauses clauses =
            match clauses with
            | [] -> None
            | clause :: rest_clauses ->
                let renamed_clause, _ = rename_variables clause 0 in
                match mgu_sld selected_atom renamed_clause.head with
                | Some mgu ->
                    (* Apply mgu to the body of the clause *)
                    let new_body = apply_substitution_goal_sld mgu renamed_clause.body in
                    
                    (* Apply mgu to the rest of the goal (except selected) *)
                    let before_selected = take selected_index goal in
                    let after_selected = drop (selected_index + 1) goal in
                    let rest_goal = before_selected @ after_selected in
                    let new_rest_goal = apply_substitution_goal_sld mgu rest_goal in
                    
                    (* New goal = clause body + rest of goal *)
                    let new_goal = new_body @ new_rest_goal in
                    
                    Some {
                        goal = goal;
                        selected_atom = selected_atom;
                        clause_used = renamed_clause;
                        mgu = Some mgu;
                        new_goal = new_goal
                    }
                | None -> try_clauses rest_clauses
        in
        try_clauses program

(* SLD resolution with leftmost selection rule *)
let rec sld_resolution program goal max_depth derivation =
    if max_depth <= 0 then Infinite
    else if goal = [] then
        Success ([], List.rev derivation)  (* Empty goal means success *)
    else
        (* Leftmost selection rule *)
        match sld_step program goal 0 with
        | None -> Failure (List.rev derivation)  (* No matching clause *)
        | Some step ->
            sld_resolution program step.new_goal (max_depth - 1) (step :: derivation)

(* Main SLD resolution function *)
let sld_query program query max_depth = sld_resolution program query max_depth []

(* Extract answer substitution from successful derivation *)
let extract_answer derivation =
    let rec combine_substitutions substs =
        match substs with
        | [] -> []
        | sub :: rest ->
            let combined_rest = combine_substitutions rest in
            (* Apply current substitution to the rest, then combine *)
            let updated_rest = List.map (fun (v, t) -> (v, apply_substitution_sld sub t)) combined_rest in
            sub @ updated_rest
    in
    
    let mgus = List.fold_left (fun acc step ->
        match step.mgu with
        | Some mgu -> mgu :: acc
        | None -> acc
    ) [] derivation in
    
    combine_substitutions (List.rev mgus)

(* Pretty printing *)
let rec string_of_term_sld = function
    | SLD_Var v -> v
    | SLD_Const c -> c
    | SLD_Func(f, []) -> f ^ "()"
    | SLD_Func(f, args) ->
        f ^ "(" ^ String.concat ", " (List.map string_of_term_sld args) ^ ")"

let string_of_atom_sld (pred, terms) =
    if terms = [] then pred
    else pred ^ "(" ^ String.concat ", " (List.map string_of_term_sld terms) ^ ")"

let string_of_goal_sld goal = "← " ^ String.concat ", " (List.map string_of_atom_sld goal)

let string_of_clause_sld clause =
    string_of_atom_sld clause.head ^
    (if clause.body = [] then "" 
     else " ← " ^ String.concat ", " (List.map string_of_atom_sld clause.body))

let string_of_substitution_sld subst = 
    String.concat ", " (List.map (fun (v, t) -> v ^ " = " ^ string_of_term_sld t) subst)

let string_of_sld_result = function
    | Success (subst, _) -> 
        if subst = [] then "Success (no substitutions needed)"
        else "Success with substitution: " ^ string_of_substitution_sld subst
    | Failure _ -> "Failure"
    | Infinite -> "Infinite (max depth reached)"
