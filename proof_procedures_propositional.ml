open Definitions
open Aux_propositional
open Nf
open Examples


let resolution_preprocessing e = cnf (negate_propositional_expr e)

