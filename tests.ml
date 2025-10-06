open Definitions
open Aux_propositional
open Nf
open Proof_procedures_propositional
open Examples


let run_nf_tests () = 
    Printf.printf "=== Propositional Logic : Normal Form Tests ===\n";
    Printf.printf "NNF of %s: %s\n" (string_of_propositional_expr expr1) (string_of_propositional_expr (nnf expr1));
    Printf.printf "NNF of %s: %s\n" (string_of_propositional_expr expr2) (string_of_propositional_expr (nnf expr2));
    Printf.printf "NNF of %s: %s\n" (string_of_propositional_expr expr3) (string_of_propositional_expr (nnf expr3));
    Printf.printf "NNF of %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (nnf expr4));
    Printf.printf "Negation of %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (negate_propositional_expr expr4));
    Printf.printf "CNF of %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (cnf (nnf expr4)));
    Printf.printf "DNF of %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (dnf (nnf expr4)));
    Printf.printf "\n"


let run_proof_procedures_propositional_tests () =
    Printf.printf "=== Propositional Logic : Proof Procedure Tests ===\n";
    Printf.printf "Preprocessed %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (resolution_preprocessing expr4));
    Printf.printf "\n"


let run_all_tests () =
    run_nf_tests ();
    run_proof_procedures_propositional_tests ()


let () = run_all_tests ()
