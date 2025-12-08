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

(* First-Order Semantic Tableaux *)

type fo_semantic_tableau_node = {
    st_formulas : formula_first_order list;
    st_marked : bool;
    st_node_type : fo_tableau_node_type;
    st_free_vars : string list;
    st_skolem_counter : int;
} and fo_tableau_node_type = FOAlpha | FOBeta | FOGamma | FODelta | FOLiteral

(* For free variable tableaux *)
type fo_fv_tableau_branch = {
    fvt_formulas : formula_first_order list;
    fvt_free_vars : string list;
    fvt_constraints : (term_first_order * term_first_order) list;
    fvt_skolem_counter : int;
    fvt_closed : bool;
}

type fo_tableau_result = FOTableauClosed | FOTableauOpen of structure_first_order option | FOTableauUnknown

type fo_fv_tableau_result = FOFVTableauClosed | FOFVTableauOpen of structure_first_order option | FOFVTableauUnknown


(* First-Order Sequent Calculus *)

type sequent_calculus_FO_sequent = {
    fo_antecedent : formula_first_order list;
    fo_consequent : formula_first_order list
}

type sequent_calculus_FO_proof_result = ProvedFO | FailedFO of string

(* For tracking constants and substitutions during proof *)
type sequent_calculus_FO_proof_state = {
    sequent : sequent_calculus_FO_sequent;
    depth : int;
    max_depth : int;
    next_constant_index : int;
    used_constants : string list;
    ground_terms : term_first_order list;
}

(* Logic Programming (SLD Resolution) *)

type term_sld = SLD_Var of string | SLD_Const of string | SLD_Func of string * term_sld list

type atom_sld = string * term_sld list  (* predicate name and arguments *)

type clause_sld = { head: atom_sld; body: atom_sld list }

type goal_sld = atom_sld list

type substitution_sld = (string * term_sld) list

type sld_step = {
    goal: goal_sld;
    selected_atom: atom_sld;
    clause_used: clause_sld;
    mgu: substitution_sld option;
    new_goal: goal_sld
}

type sld_derivation = sld_step list

type sld_result = Success of substitution_sld * sld_derivation | Failure of sld_derivation | Infinite

type program_sld = clause_sld list
