open Definitions
open Aux_first_order


(* PNF: Prenex Normal Form *)

let rec pnf formula =
    match formula with
    | FONeg f ->
        (match f with
         | FOForall(x, f') -> FOExists(x, pnf (FONeg f'))
         | FOExists(x, f') -> FOForall(x, pnf (FONeg f'))
         | _ -> let f_pnf = pnf f in FONeg f_pnf)
    | FOAnd(f1, f2) ->
        let f1_pnf = pnf f1 in
        let f2_pnf = pnf f2 in
        (match f1_pnf, f2_pnf with
         | FOForall(x1, f1'), FOForall(x2, f2') -> FOForall(x1, FOForall(x2, FOAnd(f1', f2')))
         | FOExists(x1, f1'), FOExists(x2, f2') -> FOExists(x1, FOExists(x2, FOAnd(f1', f2')))
         | FOForall(x, f'), _ -> FOForall(x, FOAnd(f', f2_pnf))
         | FOExists(x, f'), _ -> FOExists(x, FOAnd(f', f2_pnf))
         | _, FOForall(x, f') -> FOForall(x, FOAnd(f1_pnf, f'))
         | _, FOExists(x, f') -> FOExists(x, FOAnd(f1_pnf, f'))
         | _ -> FOAnd(f1_pnf, f2_pnf))
    | FOOr(f1, f2) ->
        let f1_pnf = pnf f1 in
        let f2_pnf = pnf f2 in
        (match f1_pnf, f2_pnf with
         | FOForall(x1, f1'), FOForall(x2, f2') -> FOForall(x1, FOForall(x2, FOOr(f1', f2')))
         | FOExists(x1, f1'), FOExists(x2, f2') -> FOExists(x1, FOExists(x2, FOOr(f1', f2')))
         | FOForall(x, f'), _ -> FOForall(x, FOOr(f', f2_pnf))
         | FOExists(x, f'), _ -> FOExists(x, FOOr(f', f2_pnf))
         | _, FOForall(x, f') -> FOForall(x, FOOr(f1_pnf, f'))
         | _, FOExists(x, f') -> FOExists(x, FOOr(f1_pnf, f'))
         | _ -> FOOr(f1_pnf, f2_pnf))
    | FOImplies(f1, f2) -> pnf (FOOr(FONeg f1, f2))
    | FOEquiv(f1, f2) -> pnf (FOAnd(FOImplies(f1, f2), FOImplies(f2, f1)))
    | FOForall(x, f) -> FOForall(x, pnf f)
    | FOExists(x, f) -> FOExists(x, pnf f)
    | _ -> formula

let skolem_counter = ref 0

let fresh_skolem_function () = incr skolem_counter; "sk" ^ string_of_int !skolem_counter

let rec skolemize formula =
    let rec skolemize_aux formula bound_vars =
        match formula with
        | FOExists(x, f) ->
            let skolem_func =
                if bound_vars = [] then
                    FOConst (fresh_skolem_function ())
                else
                    FOFunc(fresh_skolem_function (), List.map (fun v -> FOVar v) bound_vars)
            in
            let subst = [(x, skolem_func)] in
            skolemize_aux (subst_in_formula_first_order subst f) bound_vars
        | FOForall(x, f) -> FOForall(x, skolemize_aux f (x :: bound_vars))
        | FOAnd(f1, f2) -> FOAnd(skolemize_aux f1 bound_vars, skolemize_aux f2 bound_vars)
        | FOOr(f1, f2) -> FOOr(skolemize_aux f1 bound_vars, skolemize_aux f2 bound_vars)
        | FOImplies(f1, f2) -> FOImplies(skolemize_aux f1 bound_vars, skolemize_aux f2 bound_vars)
        | FOEquiv(f1, f2) -> FOEquiv(skolemize_aux f1 bound_vars, skolemize_aux f2 bound_vars)
        | _ -> formula
    in
    skolemize_aux formula []

let rec remove_universals formula =
    match formula with
    | FOForall(_, f) -> remove_universals f
    | _ -> formula

let rec to_nnf formula =
    match formula with
    | FONeg (FONeg f) -> to_nnf f
    | FONeg (FOAnd(f1, f2)) -> FOOr(to_nnf (FONeg f1), to_nnf (FONeg f2))
    | FONeg (FOOr(f1, f2)) -> FOAnd(to_nnf (FONeg f1), to_nnf (FONeg f2))
    | FONeg (FOImplies(f1, f2)) -> FOAnd(to_nnf f1, to_nnf (FONeg f2))
    | FONeg (FOEquiv(f1, f2)) -> FOOr(FOAnd(to_nnf f1, to_nnf (FONeg f2)), FOAnd(to_nnf (FONeg f1), to_nnf f2))
    | FONeg (FOForall(x, f)) -> FOExists(x, to_nnf (FONeg f))
    | FONeg (FOExists(x, f)) -> FOForall(x, to_nnf (FONeg f))
    | FOAnd(f1, f2) -> FOAnd(to_nnf f1, to_nnf f2)
    | FOOr(f1, f2) -> FOOr(to_nnf f1, to_nnf f2)
    | FOImplies(f1, f2) -> FOOr(to_nnf (FONeg f1), to_nnf f2)
    | FOEquiv(f1, f2) -> FOAnd(FOOr(to_nnf (FONeg f1), to_nnf f2), FOOr(to_nnf (FONeg f2), to_nnf f1))
    | FOForall(x, f) -> FOForall(x, to_nnf f)
    | FOExists(x, f) -> FOExists(x, to_nnf f)
    | _ -> formula

let rec distribute f1 f2 =
    match f1, f2 with
    | FOAnd(a, b), c -> FOAnd(distribute a c, distribute b c)
    | a, FOAnd(b, c) -> FOAnd(distribute a b, distribute a c)
    | _ -> FOOr(f1, f2)

let rec to_cnf formula =
    match formula with
    | FOAnd(f1, f2) -> FOAnd(to_cnf f1, to_cnf f2)
    | FOOr(f1, f2) -> distribute (to_cnf f1) (to_cnf f2)
    | _ -> formula

let rec extract_clauses formula =
    match formula with
    | FOAnd(f1, f2) -> extract_clauses f1 @ extract_clauses f2
    | _ -> [formula]

let rec disjunction_to_literals formula =
    match formula with
    | FOOr(f1, f2) -> disjunction_to_literals f1 @ disjunction_to_literals f2
    | _ -> [formula]

let clausify formula =
    let pnf_formula = pnf formula in
    let skolemized = skolemize pnf_formula in
    let no_quantifiers = remove_universals skolemized in
    let nnf_formula = to_nnf no_quantifiers in
    let cnf_formula = to_cnf nnf_formula in
    let clause_list = extract_clauses cnf_formula in
    List.map disjunction_to_literals clause_list
