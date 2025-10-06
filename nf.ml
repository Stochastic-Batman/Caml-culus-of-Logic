open Definitions
open Aux_propositional
open Examples   


let rec nnf e = 
    match e with
        | Equivalence (e1, e2) -> nnf (And (Implies(e1, e2), Implies(e2, e1)))
        | Implies (e1, e2) -> nnf (Or (Neg e1, e2))
        | Or (e1, e2) -> Or (nnf e1, nnf e2)
        | And (e1, e2) -> And (nnf e1, nnf e2)
        | Neg (Implies (e1, e2)) -> nnf (And (e1, Neg e2))
        | Neg (Equivalence (e1, e2)) -> nnf (Or (And (e1, Neg e2), And (Neg e1, e2)))
        | Neg (And (e1, e2)) -> Or (nnf (Neg e1), nnf (Neg e2))
        | Neg (Or (e1, e2)) -> And (nnf (Neg e1), nnf (Neg e2))
        | Neg (Neg e) -> nnf e
        | Neg (Var e) -> Neg (Var e)
        | Var _ -> e 


let rec cnf e =
    match nnf e with
        | And (e1, e2) -> And (cnf e1, cnf e2)
        | Or (And (f, g), h) -> cnf (And (Or (f, h), Or (g, h)))
        | Or (h, And (f, g)) -> cnf (And (Or (h, f), Or (h, g)))
        | Or (e1, e2) -> Or (cnf e1, cnf e2)
        | x -> x


let rec dnf e =
    match nnf e with
        | Or (e1, e2) -> Or (dnf e1, dnf e2)
        | And (Or (f, g), h) -> dnf (Or (And (f, h), And (g, h)))
        | And (h, Or (f, g)) -> dnf (Or (And (h, f), And (h, g)))
        | And (e1, e2) -> And (dnf e1, dnf e2)
        | x -> x


let run_nf_tests () = 
    Printf.printf "nnf of %s: %s\n" (string_of_propositional_expr expr1) (string_of_propositional_expr (nnf expr1));
    Printf.printf "nnf of %s: %s\n" (string_of_propositional_expr expr2) (string_of_propositional_expr (nnf expr2));
    Printf.printf "nnf of %s: %s\n" (string_of_propositional_expr expr3) (string_of_propositional_expr (nnf expr3));
    Printf.printf "nnf of %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (nnf expr4));
    Printf.printf "negation of %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (negate_propositional_expr expr4));
    Printf.printf "cnf of %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (cnf expr4));
    Printf.printf "dnf of %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (dnf expr4));

let _ = run_proof_procedures_propositional_tests ()
