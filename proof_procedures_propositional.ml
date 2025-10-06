open Definitions
open Aux_propositional
open Nf
open Examples


let resolution_preprocessing e = cnf (negate_propositional_expr e)

let run_proof_procedures_propositional_tests () =
        Printf.printf "Preprocessed %s: %s\n" (string_of_propositional_expr expr4) (string_of_propositional_expr (resolution_preprocessing expr4))

let _ = run_proof_procedures_propositional_tests ()
