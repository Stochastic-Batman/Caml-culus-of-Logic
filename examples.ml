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


(* First-Order Logic *)

let term1_first_order = FOVar "x"
let term2_first_order = FOConst "a"
let term3_first_order = FOFunc("f", [FOVar "x"; FOConst "b"])
let term4_first_order = FOFunc("g", [FOFunc("f", [FOVar "y"]); FOConst "c"])

let formula1_first_order = FOAtomic("P", [FOVar "x"])
let formula2_first_order = FOAtomic("Q", [FOConst "a"; FOVar "y"])
let formula3_first_order = FOAnd(FOAtomic("P", [FOVar "x"]), FOAtomic("Q", [FOVar "x"]))
let formula4_first_order = FOForall("x", FOAtomic("P", [FOVar "x"]))
let formula5_first_order = FOExists("y", FOAtomic("Q", [FOConst "a"; FOVar "y"]))
let formula6_first_order = FOForall("x", FOExists("y", FOAtomic("R", [FOVar "x"; FOVar "y"])))
let formula7_first_order = FOImplies(FOForall("x", FOAtomic("Human", [FOVar "x"])), FOExists("y", FOAnd(FOAtomic("Mortal", [FOVar "y"]), FOAtomic("Human", [FOVar "y"]))))
let formula8_first_order = FOForall("x", FOImplies(FOAtomic("Man", [FOVar "x"]), FOAtomic("Mortal", [FOVar "x"])))
let formula9_first_order = FOAnd(FOAtomic("Man", [FOConst "socrates"]), FOForall("x", FOImplies(FOAtomic("Man", [FOVar "x"]), FOAtomic("Mortal", [FOVar "x"]))))

let unification_example1 = (FOVar "x", FOConst "a")
let unification_example2 = (FOVar "x", FOVar "y")
let unification_example3 = (FOFunc("f", [FOVar "x"]), FOFunc("f", [FOConst "a"]))
let unification_example4 = (FOFunc("f", [FOVar "x"; FOConst "b"]), FOFunc("f", [FOConst "a"; FOVar "y"]))

let clausify_example1 = FOForall("x", FOExists("y", FOAtomic("Loves", [FOVar "x"; FOVar "y"])))
let clausify_example2 = FOImplies(FOForall("x", FOAtomic("Man", [FOVar "x"])), FOExists("y", FOAnd(FOAtomic("Mortal", [FOVar "y"]), FOAtomic("Man", [FOVar "y"]))))
let clausify_example3 = FOForall("x", FOImplies(FOAnd(FOAtomic("Human", [FOVar "x"]), FOAtomic("Male", [FOVar "x"])), FOAtomic("Man", [FOVar "x"])))

let resolution_example1 = FOForall("x", FOAtomic("P", [FOVar "x"]))
let resolution_example2 = FOExists("x", FONeg (FOAtomic("P", [FOVar "x"])))
let resolution_example3 = FOImplies(FOForall("x", FOAtomic("Man", [FOVar "x"])), FOAtomic("Man", [FOConst "socrates"]))
let resolution_example4 = FOAnd(FOForall("x", FOImplies(FOAtomic("Man", [FOVar "x"]), FOAtomic("Mortal", [FOVar "x"]))), FOAtomic("Man", [FOConst "socrates"]))
let resolution_example5 = FOForall("x", FOExists("y", FOAtomic("Loves", [FOVar "x"; FOVar "y"])))

let resolution_unsat1 = FOAnd(FOForall("x", FOAtomic("P", [FOVar "x"])), FOExists("x", FONeg (FOAtomic("P", [FOVar "x"]))))
let resolution_unsat2 = FOAnd(FOAnd(FOForall("x", FOImplies(FOAtomic("Man", [FOVar "x"]), FOAtomic("Mortal", [FOVar "x"]))), FOAtomic("Man", [FOConst "socrates"])), FONeg (FOAtomic("Mortal", [FOConst "socrates"])))


(* Semantic Tableaux Examples for First-Order Logic *)
let tableaux_fo_expr1 = FOForall("x", FOAtomic("P", [FOVar "x"]))
let tableaux_fo_expr2 = FOExists("x", FOAtomic("P", [FOVar "x"]))
let tableaux_fo_expr3 = FOImplies(
    FOForall("x", FOImplies(FOAtomic("Human", [FOVar "x"]), FOAtomic("Mortal", [FOVar "x"]))),
    FOImplies(FOAtomic("Human", [FOConst "socrates"]), FOAtomic("Mortal", [FOConst "socrates"]))
)
let tableaux_fo_expr4 = FOAnd(
    FOForall("x", FOAtomic("P", [FOVar "x"])),
    FONeg(FOAtomic("P", [FOConst "a"]))
)
let tableaux_fo_expr5 = FOImplies(
    FOExists("x", FOForall("y", FOAtomic("Loves", [FOVar "x"; FOVar "y"]))),
    FOForall("y", FOExists("x", FOAtomic("Loves", [FOVar "x"; FOVar "y"])))
)


(* Free Variable Tableaux Examples *)

let fv_tableaux_expr1 = FOForall("x", FOAtomic("P", [FOVar "x"]))
let fv_tableaux_expr2 = FOExists("x", FOAnd(
    FOAtomic("P", [FOVar "x"]),
    FONeg(FOAtomic("P", [FOVar "x"]))
))
let fv_tableaux_expr3 = FOImplies(
    FOAnd(
        FOForall("x", FOImplies(FOAtomic("Human", [FOVar "x"]), FOAtomic("Mortal", [FOVar "x"]))),
        FOAtomic("Human", [FOConst "socrates"])
    ),
    FOAtomic("Mortal", [FOConst "socrates"])
)
let fv_tableaux_expr4 = FOExists("x", FOForall("y", FOAtomic("R", [FOVar "x"; FOVar "y"])))
let fv_tableaux_expr5 = FOImplies(
    FOForall("x", FOAtomic("P", [FOVar "x"])),
    FOExists("y", FOAtomic("P", [FOVar "y"]))
)

(* Three provable examples for First-Order Sequent Calculus *)

let sequent_calculus_FO_example1 =
    FOImplies(
        FOForall("x", FOAtomic("P", [FOVar "x"])),
        FOAtomic("P", [FOConst "a"])
    )
(* ∀x P(x) → P(a) - Universal instantiation *)


let sequent_calculus_FO_example2 =
    FOImplies(
        FOAtomic("P", [FOConst "a"]),
        FOExists("x", FOAtomic("P", [FOVar "x"]))
    )
(* P(a) → ∃x P(x) - Existential generalization *)


let sequent_calculus_FO_example3 =
    FOImplies(
        FOAnd(
            FOForall("x",
                FOImplies(
                    FOAtomic("Man", [FOVar "x"]),
                    FOAtomic("Mortal", [FOVar "x"])
                )
            ),
            FOAtomic("Man", [FOConst "socrates"])
        ),
        FOAtomic("Mortal", [FOConst "socrates"])
    )
(* (∀x Man(x)→Mortal(x) ∧ Man(socrates)) → Mortal(socrates) - Socrates mortality *)

