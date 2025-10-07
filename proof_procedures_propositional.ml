open Definitions
open Aux_propositional  (* cnf_clauses are imported from aux_propositional.ml *)
open Nf
open Examples


(* Resolution *)

let resolution_preprocessing e = cnf (negate_propositional_expr e)


let are_complementary e1 e2 =
        match e1, e2 with
        | Var v1, Neg (Var v2) -> v1 = v2
        | Neg (Var v1), Var v2 -> v1 = v2
        | _ -> false


let remove_literal c x = List.filter (fun el -> el <> x) c


let contains_literal c x = List.exists (fun el -> el = x) c


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


let remove_duplicates c =
        let rec aux seen = function
                | [] -> List.rev seen
                | h :: t -> if List.mem h seen then aux seen t else aux (h :: seen) t
        in
        aux [] c


let simplify_clause c =  (* Simplify clause by removing duplicates and tautologies *)
        let no_duplicates = remove_duplicates c in
        let is_tautology =  (* Check for tautology: if both a literal and its negation are present *)
                List.exists (fun el -> List.exists (are_complementary el) no_duplicates) no_duplicates
        in
        if is_tautology then [] else no_duplicates
