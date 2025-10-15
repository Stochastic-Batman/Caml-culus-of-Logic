open Definitions
open Aux_propositional  (* cnf_clauses are imported from aux_propositional.ml *)
open Nf
open Examples


(* Resolution *)

let resolution_preprocessing e = cnf (negate_propositional_expr e)


let resolvent c1 c2 x =
        if contains_literal c1 x && contains_literal c2 (negate_propositional_expr x) then
                let c1' = remove_literal c1 x in
                let c2' = remove_literal c2 (negate_propositional_expr x) in
                Some (c1' @ c2')
        else
                None


let find_resolvents c1 c2 =  (* Find all possible resolvents between two clauses *)
        let rec find_lit_resolvents clause1 acc =
                match clause1 with
                | [] -> acc
                | h :: t ->
                        let complementary_resolvents = 
                                List.filter_map (fun x -> if are_complementary h x then resolvent c1 c2 h else None) c2
                        in
                        find_lit_resolvents t (complementary_resolvents @ acc)
        in
        find_lit_resolvents c1 []


let simplify_clause c =  (* Simplify clause by removing duplicates and tautologies *)
        let no_duplicates = remove_duplicates c in
        let is_tautology =  (* Check for tautology: if both a literal and its negation are present *)
                List.exists (fun el -> List.exists (are_complementary el) no_duplicates) no_duplicates
        in
        if is_tautology then [] else no_duplicates



let resolution_propositional proposition =
        let rec resolution_procedure clauses processed_pairs =
                if List.mem [] clauses then false  (* Unsat - empty clause found *)
                else
                        let all_pairs =  (* Check if there are no unresolved clashing clauses *)
                                let rec generate_pairs = function
                                        | [] -> []
                                        | h :: t ->  (List.map (fun c -> (h, c)) t) @ (generate_pairs t)
                                in
                                generate_pairs clauses
                        in

                        let unresolved_pairs = List.filter (fun pair -> not (List.mem pair processed_pairs)) all_pairs
                        in

                        if unresolved_pairs = [] then true  (* Sat - no more resolvents to compute *)
                        else
                                let (c1, c2) = List.hd unresolved_pairs
                                in
                                let new_processed_pairs = (c1, c2) :: processed_pairs
                                in
                                let resolvents = find_resolvents c1 c2
                                in
                                let non_trivial_resolvents = List.filter (fun r -> r <> [])  (List.map simplify_clause resolvents)
                                in
                                let unique_resolvents =
                                        let rec remove_dups seen = function
                                                        | [] -> List.rev seen
                                                        | h :: t ->
                                                                if List.mem h seen then remove_dups seen t
                                                                else remove_dups (h :: seen) t
                                        in
                                        remove_dups [] non_trivial_resolvents
                                in
                                let new_clauses = List.filter (fun r -> not (List.mem r clauses)) unique_resolvents
                                in
                                if new_clauses = [] then resolution_procedure clauses new_processed_pairs
                                else resolution_procedure (clauses @ new_clauses) new_processed_pairs
        in

        let preprocessed = resolution_preprocessing proposition
        in
        let initial_clauses = cnf_clauses preprocessed
        in
        let simplified_clauses = List.map simplify_clause initial_clauses
        in
        let unique_clauses =
                let rec remove_dups seen = function
                        | [] -> List.rev seen
                        | h :: t ->
                                if List.mem h seen then remove_dups seen t
                                else remove_dups (h :: seen) t
                in
                remove_dups [] simplified_clauses
        in
        let result = resolution_procedure unique_clauses [] in
        result
