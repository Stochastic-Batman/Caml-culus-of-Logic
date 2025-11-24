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


(* First-Order Logic *)

(* In definitions.ml, change the first-order logic types to use different names *)

type term_first_order =
    | FOVar of string
    | FOConst of string
    | FOFunc of string * term_first_order list

type formula_first_order =
    | FOAtomic of string * term_first_order list
    | FONeg of formula_first_order
    | FOAnd of formula_first_order * formula_first_order
    | FOOr of formula_first_order * formula_first_order
    | FOImplies of formula_first_order * formula_first_order
    | FOEquiv of formula_first_order * formula_first_order
    | FOForall of string * formula_first_order
    | FOExists of string * formula_first_order

type substitution_first_order = (string * term_first_order) list

type equation_first_order = term_first_order * term_first_order

type unification_problem_first_order = equation_first_order list

type unification_result_first_order = Unifiable of substitution_first_order | NotUnifiable of string

type clause_first_order = formula_first_order list

type cnf_first_order = clause_first_order list

type structure_first_order = {
    domain: string list;
    functions: (string * (string list -> string)) list;
    predicates: (string * (string list -> bool)) list;
}

type interpretation_first_order = {
    structure: structure_first_order;
    variable_assignment: (string -> string); (* Maps variables to domain elements *)
}

(* First-Order Resolution *)

type resolution_result = Unsatisfiable | Satisfiable | Unknown
