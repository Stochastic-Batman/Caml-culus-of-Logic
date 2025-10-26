(* Propositional Logic *)
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


type tableau_node_propositional = {
        formulas : propositional_expr list;
        marked : bool;
        node_type : tableau_node_type_propositional
} and tableau_node_type_propositional = Alpha | Beta | Literal


type tableau_branch_propositional = tableau_node_propositional list


type tableau_tree_propositional =
        | Leaf of tableau_node_propositional
        | Branch of tableau_node_propositional * tableau_tree_propositional list


type tableau_result_propositional =
        | TableauClosed
        | TableauOpen of (string * bool) list  (* satisfying valuation *)
        | TableauUnknown


type tableau_mark_propositional = Closed | Open | Unmarked
