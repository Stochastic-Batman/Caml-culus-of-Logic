open Definitions
open Aux_propositional
open Examples


let rec nnf e = 
        match e with
                | Var _ -> e
                | Neg e' -> (match e' with
                        | Var v -> Neg (Var v)
                        | Neg e1 -> nnf e1
                        | And (e1, e2) -> nnf (Or (Neg e1, Neg e2))
                        | Or (e1, e2) -> nnf (And (Neg e1, Neg e2))
                        | Implies (e1, e2) -> nnf (And (e1, Neg e2))
                        | Equivalence (e1, e2) -> nnf (Or (And (e1, Neg e2), And (Neg e1, e2))))
                | And (e1, e2) -> And (nnf e1, nnf e2)
                | Or (e1, e2) -> Or (nnf e1, nnf e2)
                | Implies (e1, e2) -> nnf (Or (Neg e1, e2))
                | Equivalence (e1, e2) -> nnf (And (Implies(e1, e2), Implies(e2, e1)))


(* distribute_or_over_and & distribute_and_over_or are from aux_propositional.ml *)

let rec cnf e =
        let e_nnf = nnf e in
        match e_nnf with
                | And (e1, e2) -> And (cnf e1, cnf e2)
                | Or (e1, e2) -> distribute_or_over_and (cnf e1) (cnf e2)
                | _ -> e_nnf


let rec dnf e =
        let e_nnf = nnf e in
        match e_nnf with
                | Or (e1, e2) -> Or (dnf e1, dnf e2)
                | And (e1, e2) -> distribute_and_over_or (dnf e1) (dnf e2)
                | _ -> e_nnf
