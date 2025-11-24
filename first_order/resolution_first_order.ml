open Definitions
open Aux_first_order
open Unification_first_order
open Clausification_first_order



type clause = formula_first_order list


let rename_variables clause counter =
    let rec rename_formula formula map counter =
        match formula with
        | FOAtomic(p, terms) -> 
            let new_terms = List.map (rename_term map) terms in
            (FOAtomic(p, new_terms), counter)
        | FONeg f -> 
            let (f', counter') = rename_formula f map counter in
            (FONeg f', counter')
        | FOAnd(f1, f2) -> 
            let (f1', counter1) = rename_formula f1 map counter in
            let (f2', counter2) = rename_formula f2 map counter1 in
            (FOAnd(f1', f2'), counter2)
        | FOOr(f1, f2) -> 
            let (f1', counter1) = rename_formula f1 map counter in
            let (f2', counter2) = rename_formula f2 map counter1 in
            (FOOr(f1', f2'), counter2)
        | FOImplies(f1, f2) -> 
            let (f1', counter1) = rename_formula f1 map counter in
            let (f2', counter2) = rename_formula f2 map counter1 in
            (FOImplies(f1', f2'), counter2)
        | FOEquiv(f1, f2) -> 
            let (f1', counter1) = rename_formula f1 map counter in
            let (f2', counter2) = rename_formula f2 map counter1 in
            (FOEquiv(f1', f2'), counter2)
        | FOForall(x, f) -> 
            let new_x = "v" ^ string_of_int counter in
            let new_map = (x, FOVar new_x) :: map in
            let (f', counter') = rename_formula f new_map (counter + 1) in
            (FOForall(new_x, f'), counter')
        | FOExists(x, f) -> 
            let new_x = "v" ^ string_of_int counter in
            let new_map = (x, FOVar new_x) :: map in
            let (f', counter') = rename_formula f new_map (counter + 1) in
            (FOExists(new_x, f'), counter')
    
    and rename_term map = function
        | FOVar v -> (try List.assoc v map with Not_found -> FOVar v)
        | FOConst c -> FOConst c
        | FOFunc(f, terms) -> FOFunc(f, List.map (rename_term map) terms)
    
    in
    let renamed_clause = ref [] in
    let current_counter = ref counter in
    List.iter (fun formula ->
        let (renamed, new_counter) = rename_formula formula [] !current_counter in
        renamed_clause := renamed :: !renamed_clause;
        current_counter := new_counter
    ) clause;
    (List.rev !renamed_clause, !current_counter)


let standardize_apart clauses =
    let rec standardize clauses counter acc =
        match clauses with
        | [] -> List.rev acc
        | clause :: rest ->
            let (renamed_clause, new_counter) = rename_variables clause counter in
            standardize rest new_counter (renamed_clause :: acc)
    in
    standardize clauses 0 []


let is_positive_literal = function
    | FOAtomic _ -> true
    | FONeg (FOAtomic _) -> false
    | _ -> false


let get_atom = function
    | FOAtomic(p, terms) -> (p, terms)
    | FONeg (FOAtomic(p, terms)) -> (p, terms)
    | _ -> failwith "Not a literal"


let are_complementary_literals lit1 lit2 =
    match (lit1, lit2) with
    | (FOAtomic(p1, terms1), FONeg (FOAtomic(p2, terms2)))
    | (FONeg (FOAtomic(p1, terms1)), FOAtomic(p2, terms2)) ->
        if p1 = p2 then
            match unify [(FOFunc(p1, terms1), FOFunc(p2, terms2))] with
            | Unifiable _ -> true
            | NotUnifiable _ -> false
        else false
    | _ -> false


let find_resolvents clause1 clause2 =
    let resolvents = ref [] in
    
    for i = 0 to List.length clause1 - 1 do
        let lit1 = List.nth clause1 i in
        for j = 0 to List.length clause2 - 1 do
            let lit2 = List.nth clause2 j in
            if are_complementary_literals lit1 lit2 then
                match (lit1, lit2) with
                | (FOAtomic(p1, terms1), FONeg (FOAtomic(p2, terms2)))
                | (FONeg (FOAtomic(p1, terms1)), FOAtomic(p2, terms2)) ->
                    (match unify [(FOFunc(p1, terms1), FOFunc(p2, terms2))] with
                    | Unifiable subst ->
                        let remaining1 = List.mapi (fun idx lit -> if idx = i then None else Some lit) clause1 
                                      |> List.filter_map (fun x -> x) in
                        let remaining2 = List.mapi (fun idx lit -> if idx = j then None else Some lit) clause2 
                                      |> List.filter_map (fun x -> x) in
                        
                        let apply_subst_to_clause clause =
                            List.map (subst_in_formula_first_order subst) clause
                        in
                        
                        let new_clause = apply_subst_to_clause (remaining1 @ remaining2) in
                        let simplified_clause = List.fold_left (fun acc lit ->
                            if List.exists (are_complementary_literals lit) acc then acc
                            else lit :: acc
                        ) [] new_clause in
                        
                        resolvents := List.rev simplified_clause :: !resolvents
                    | NotUnifiable _ -> ())
                | _ -> ()
        done
    done;
    
    !resolvents


let is_tautology clause =
    let rec check_complementary = function
        | [] -> false
        | h :: t ->
            List.exists (fun lit -> are_complementary_literals h lit) t || check_complementary t
    in
    check_complementary clause


let remove_tautologies clauses =
    List.filter (fun clause -> not (is_tautology clause)) clauses


let subsumes clause1 clause2 =
    List.for_all (fun lit1 -> List.exists (fun lit2 -> lit1 = lit2) clause2) clause1


let remove_subsumed clauses =
    let rec remove_subs acc = function
        | [] -> List.rev acc
        | h :: t ->
            if List.exists (fun c -> subsumes c h && c != h) (acc @ t) then
                remove_subs acc t
            else
                remove_subs (h :: acc) t
    in
    remove_subs [] clauses


let resolution_first_order formula =
    let clauses = clausify formula in
    let standardized_clauses = standardize_apart clauses in
    
    let rec resolution_procedure active passive =
        if List.mem [] active then Unsatisfiable
        else if passive = [] then Satisfiable
        else
            let current = List.hd passive in
            let new_passive = List.tl passive in
            
            let new_resolvents = ref [] in
            
            List.iter (fun active_clause ->
                let resolvents = find_resolvents current active_clause in
                new_resolvents := resolvents @ !new_resolvents
            ) active;
            
            let filtered_resolvents = 
                !new_resolvents 
                |> remove_tautologies
                |> remove_subsumed
                |> List.filter (fun r -> not (List.mem r active) && not (List.mem r new_passive))
            in
            
            if List.mem [] filtered_resolvents then Unsatisfiable
            else
                resolution_procedure 
                    (current :: active)
                    (new_passive @ filtered_resolvents)
    in
    
    try
        resolution_procedure [] standardized_clauses
    with _ -> Unknown


let resolution_clauses clauses =
    let standardized_clauses = standardize_apart clauses in
    
    let rec resolution_procedure active passive =
        if List.mem [] active then Unsatisfiable
        else if passive = [] then Satisfiable
        else
            let current = List.hd passive in
            let new_passive = List.tl passive in
            
            let new_resolvents = ref [] in
            
            List.iter (fun active_clause ->
                let resolvents = find_resolvents current active_clause in
                new_resolvents := resolvents @ !new_resolvents
            ) active;
            
            let filtered_resolvents = 
                !new_resolvents 
                |> remove_tautologies
                |> remove_subsumed
                |> List.filter (fun r -> not (List.mem r active) && not (List.mem r new_passive))
            in
            
            if List.mem [] filtered_resolvents then Unsatisfiable
            else
                resolution_procedure 
                    (current :: active)
                    (new_passive @ filtered_resolvents)
    in
    
    try
        resolution_procedure [] standardized_clauses
    with _ -> Unknown


let is_valid_resolution formula =
    match resolution_first_order (FONeg formula) with
        | Unsatisfiable -> true
        | Satisfiable -> false
        | Unknown -> false
