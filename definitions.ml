type propositional_expr = 
        | Var of string
        | Neg of propositional_expr
        | And of propositional_expr * propositional_expr
        | Or of propositional_expr * propositional_expr
        | Implies of propositional_expr * propositional_expr
        | Equivalence of propositional_expr * propositional_expr


type propositional_sequent = {
        antecedent : propositional_expr list;
        consequent : propositional_expr list
}


type propositional_sequent_proof_result = 
        | Proved 
        | Failed of propositional_expr list
