open Definitions


(* Propositional Logic *)

let expr1 = And (Var "A", Neg (Var "B"))
let expr2 = Implies (Var "A", Var "C")
let expr3 = Neg (And (Var "A", Var "B"))
let expr4 = Implies (And (Var "p", Implies (Var "q", Var "r")), Var "s")
let expr5 = And (Or (Var "A", Var "B"), Or (Neg (Var "A"), Var "C"))
let expr6 = And (Var "p", Neg (Var "p"))

let tableaux_expr1 = Implies (Implies (Var "p", Var "q"), Implies (Neg (Var "q"), Neg (Var "p")))
let tableaux_expr2 = And (Implies (Var "p", Var "q"), Implies (Neg (Var "p"), Neg (Var "q")))
let tableaux_expr3 = And (Or (Var "p", Var "q"), And (Neg (Var "p"), Neg (Var "q")))
let tableaux_expr4 = Implies (Var "A", Var "A")
let tableaux_expr5 = And (Var "A", Neg (Var "A"))
