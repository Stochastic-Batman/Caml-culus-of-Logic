open Definitions


(* Propositional Logic *)

let expr1 = And (Var "A", Neg (Var "B"))
let expr2 = Implies (Var "A", Var "C")
let expr3 = Neg (And (Var "A", Var "B"))
let expr4 = Implies (And (Var "p", Implies (Var "q", Var "r")), Var "s")
let expr5 = And (Or (Var "A", Var "B"), Or (Neg (Var "A"), Var "C"))
let expr6 = And (Var "p", Neg (Var "p"))
