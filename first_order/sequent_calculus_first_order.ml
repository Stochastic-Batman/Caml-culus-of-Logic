open Definitions

(* Gentzen System G for first-order logic *)

let get_new_constant state =
	let c = "c" ^ string_of_int state.next_constant_index in
	(c, {
		state with
		next_constant_index = state.next_constant_index + 1;
		used_constants = c :: state.used_constants;
		ground_terms = FOConst c :: state.ground_terms
	})


let add_ground_term term state = { state with ground_terms = term :: state.ground_terms }


let substitute_in_formula formula (var, term) =
	let rec subst f =
		match f with
		| FOAtomic (p, args) ->
			FOAtomic (p, List.map (subst_term (var, term)) args)
		| FONeg f1 -> FONeg (subst f1)
		| FOAnd (f1, f2) -> FOAnd (subst f1, subst f2)
		| FOOr (f1, f2) -> FOOr (subst f1, subst f2)
		| FOImplies (f1, f2) -> FOImplies (subst f1, subst f2)
		| FOEquiv (f1, f2) -> FOEquiv (subst f1, subst f2)
		| FOForall (x, f1) ->
			if x = var then f else FOForall (x, subst f1)
		| FOExists (x, f1) ->
			if x = var then f else FOExists (x, subst f1)
	and subst_term sub t =
		match t with
		| FOVar x -> if x = var then term else FOVar x
		| FOConst c -> FOConst c
		| FOFunc (fn, args) -> FOFunc (fn, List.map (subst_term sub) args)
	in
	subst formula


let is_axiom seq =
	List.exists
		(fun a ->
			List.exists
				(fun c ->
					match (a, c) with
					| FOAtomic (p1, args1), FOAtomic (p2, args2) -> p1 = p2 && args1 = args2
					| _ -> false)
				seq.fo_consequent)
		seq.fo_antecedent

(* Left rules *)

let and_left state f =
	match f with
	| FOAnd (e1, e2) ->
		let new_antecedent =
			e1 :: e2 :: List.filter (fun x -> x <> f) state.sequent.fo_antecedent
		in
		[
			{
				state with
				sequent =
					{
						fo_antecedent = new_antecedent;
						fo_consequent = state.sequent.fo_consequent;
					};
			};
		]
	| _ -> []


let or_left state f =
	match f with
	| FOOr (e1, e2) ->
		let filtered = List.filter (fun x -> x <> f) state.sequent.fo_antecedent in
		[
			{
				state with
				sequent =
					{
						fo_antecedent = e1 :: filtered;
						fo_consequent = state.sequent.fo_consequent;
					};
			};
			{
				state with
				sequent =
					{
						fo_antecedent = e2 :: filtered;
						fo_consequent = state.sequent.fo_consequent;
					};
			};
		]
	| _ -> []


let implies_left state f =
	match f with
	| FOImplies (e1, e2) ->
		let filtered = List.filter (fun x -> x <> f) state.sequent.fo_antecedent in
		[
			{
				state with
				sequent =
					{
						fo_antecedent = filtered;
						fo_consequent = e1 :: state.sequent.fo_consequent;
					};
			};
			{
				state with
				sequent =
					{
						fo_antecedent = e2 :: filtered;
						fo_consequent = state.sequent.fo_consequent;
					};
			};
		]
	| _ -> []


let neg_left state f =
	match f with
	| FONeg e ->
		let filtered = List.filter (fun x -> x <> f) state.sequent.fo_antecedent in
		[
			{
				state with
				sequent =
					{
						fo_antecedent = filtered;
						fo_consequent = e :: state.sequent.fo_consequent;
					};
			};
		]
	| _ -> []


(* Right rules *)

let and_right state f =
	match f with
	| FOAnd (e1, e2) ->
		let filtered = List.filter (fun x -> x <> f) state.sequent.fo_consequent in
		[
			{
				state with
				sequent =
					{
						fo_antecedent = state.sequent.fo_antecedent;
						fo_consequent = e1 :: filtered;
					};
			};
			{
				state with
				sequent =
					{
						fo_antecedent = state.sequent.fo_antecedent;
						fo_consequent = e2 :: filtered;
					};
			};
		]
	| _ -> []


let or_right state f =
	match f with
	| FOOr (e1, e2) ->
		let filtered = List.filter (fun x -> x <> f) state.sequent.fo_consequent in
		[
			{
				state with
				sequent =
					{
						fo_antecedent = state.sequent.fo_antecedent;
						fo_consequent = e1 :: e2 :: filtered;
					};
			};
		]
	| _ -> []


let implies_right state f =
	match f with
	| FOImplies (e1, e2) ->
		let filtered = List.filter (fun x -> x <> f) state.sequent.fo_consequent in
		[
			{
				state with
				sequent =
					{
						fo_antecedent = e1 :: state.sequent.fo_antecedent;
						fo_consequent = e2 :: filtered;
					};
			};
		]
	| _ -> []


let neg_right state f =
	match f with
	| FONeg e ->
		let filtered = List.filter (fun x -> x <> f) state.sequent.fo_consequent in
		[
			{
				state with
				sequent =
					{
						fo_antecedent = e :: state.sequent.fo_antecedent;
						fo_consequent = filtered;
					};
			};
		]
	| _ -> []


(* Quantifier rules *)

let forall_left state f =
	match f with
	| FOForall (x, body) ->
		state.ground_terms
		|> List.map (fun term ->
				let new_formula = substitute_in_formula body (x, term) in
				let new_antecedent =
					new_formula :: f :: List.filter (fun x -> x <> f) state.sequent.fo_antecedent
				in
				{
					state with
					sequent =
						{
							fo_antecedent = new_antecedent;
							fo_consequent = state.sequent.fo_consequent;
						};
				})
	| _ -> []


let exists_left state f =
	match f with
	| FOExists (x, body) ->
		let c, new_state = get_new_constant state in
		let new_formula = substitute_in_formula body (x, FOConst c) in
		let new_antecedent =
			new_formula :: List.filter (fun x -> x <> f) new_state.sequent.fo_antecedent
		in
		[
			{
				new_state with
				sequent =
					{
						fo_antecedent = new_antecedent;
						fo_consequent = new_state.sequent.fo_consequent;
					};
			};
		]
	| _ -> []


let forall_right state f =
	match f with
	| FOForall (x, body) ->
		let c, new_state = get_new_constant state in
		let new_formula = substitute_in_formula body (x, FOConst c) in
		let new_consequent =
			new_formula :: List.filter (fun x -> x <> f) new_state.sequent.fo_consequent
		in
		[
			{
				new_state with
				sequent =
					{
						fo_antecedent = new_state.sequent.fo_antecedent;
						fo_consequent = new_consequent;
					};
			};
		]
	| _ -> []


let exists_right state f =
	match f with
	| FOExists (x, body) ->
		state.ground_terms
		|> List.map (fun term ->
				let new_formula = substitute_in_formula body (x, term) in
				let new_consequent =
					new_formula :: f :: List.filter (fun x -> x <> f) state.sequent.fo_consequent
				in
				{
					state with
					sequent =
						{
							fo_antecedent = state.sequent.fo_antecedent;
							fo_consequent = new_consequent;
						};
				})
	| _ -> []


(* Main proof procedure *)

let rec prove_sequent state =
	if state.depth > state.max_depth then
		FailedFO (Printf.sprintf "Max depth %d exceeded" state.max_depth)
	else if is_axiom state.sequent then
		ProvedFO
	else
		(* Collect all formulas that can be reduced *)
		let left_formulas = state.sequent.fo_antecedent in
		let right_formulas = state.sequent.fo_consequent in

		(* Try propositional rules first *)
		let try_propositional_rule state formula rule_func =
			let new_states = rule_func state formula in
			if new_states <> [] then
				let results =
					List.map
						(fun s -> prove_sequent { s with depth = state.depth + 1 })
						new_states
				in
				if List.for_all (function ProvedFO -> true | _ -> false) results then
					ProvedFO
				else
					FailedFO "Propositional rule failed"
			else
				FailedFO "No propositional rule applicable"
		in

		(* Try left propositional rules *)
		let left_prop_result =
			List.fold_left
				(fun acc f ->
					match acc with
					| ProvedFO -> ProvedFO
					| FailedFO _ -> (
						match f with
						| FOAnd _ -> try_propositional_rule state f and_left
						| FOOr _ -> try_propositional_rule state f or_left
						| FOImplies _ -> try_propositional_rule state f implies_left
						| FONeg _ -> try_propositional_rule state f neg_left
						| _ -> FailedFO "Not a propositional formula"))
				(FailedFO "No left propositional formula")
				left_formulas
		in

		if left_prop_result = ProvedFO then ProvedFO
		else
			(* Try right propositional rules *)
			let right_prop_result =
				List.fold_left
					(fun acc f ->
						match acc with
						| ProvedFO -> ProvedFO
						| FailedFO _ -> (
							match f with
							| FOAnd _ -> try_propositional_rule state f and_right
							| FOOr _ -> try_propositional_rule state f or_right
							| FOImplies _ -> try_propositional_rule state f implies_right
							| FONeg _ -> try_propositional_rule state f neg_right
							| _ -> FailedFO "Not a propositional formula"))
					(FailedFO "No right propositional formula")
					right_formulas
			in

			if right_prop_result = ProvedFO then ProvedFO
			else
				(* Try quantifier rules *)
				let try_quantifier_rule state formula rule_func =
					let new_states = rule_func state formula in
					if new_states <> [] then
						let results =
							List.map
								(fun s -> prove_sequent { s with depth = state.depth + 1 })
								new_states
						in
						if List.for_all (function ProvedFO -> true | _ -> false) results then
							ProvedFO
						else
							FailedFO "Quantifier rule failed"
					else
						FailedFO "No quantifier rule applicable"
				in

				(* Try left quantifier rules *)
				let left_quant_result =
					List.fold_left
						(fun acc f ->
							match acc with
							| ProvedFO -> ProvedFO
							| FailedFO _ -> (
								match f with
								| FOForall _ -> try_quantifier_rule state f forall_left
								| FOExists _ -> try_quantifier_rule state f exists_left
								| _ -> FailedFO "Not a quantifier formula"))
						(FailedFO "No left quantifier formula")
						left_formulas
				in

				if left_quant_result = ProvedFO then ProvedFO
				else
					(* Try right quantifier rules *)
					let right_quant_result =
						List.fold_left
							(fun acc f ->
								match acc with
								| ProvedFO -> ProvedFO
								| FailedFO _ -> (
									match f with
									| FOForall _ ->
										try_quantifier_rule state f forall_right
									| FOExists _ ->
										try_quantifier_rule state f exists_right
									| _ -> FailedFO "Not a quantifier formula"))
							(FailedFO "No right quantifier formula")
							right_formulas
					in

					if right_quant_result = ProvedFO then ProvedFO
					else FailedFO "No rules applicable and not an axiom"

(* Top-level functions *)

let extract_ground_terms formula =
	let rec extract_from_term acc =
		function
		| FOVar _ -> acc
		| FOConst c -> FOConst c :: acc
		| FOFunc (fn, args) ->
			let term = FOFunc (fn, args) in
			term :: List.fold_left extract_from_term acc args
	in
	let rec extract acc =
		function
		| FOAtomic (_, args) -> List.fold_left extract_from_term acc args
		| FONeg f -> extract acc f
		| FOAnd (f1, f2)
		| FOOr (f1, f2)
		| FOImplies (f1, f2)
		| FOEquiv (f1, f2) ->
			extract (extract acc f1) f2
		| FOForall (_, f)
		| FOExists (_, f) -> extract acc f
	in
	let terms = extract [] formula in
	List.sort_uniq compare terms


let prove_formula_FO formula =
	let ground_terms = extract_ground_terms formula in
	let initial_state =
		{
			sequent = { fo_antecedent =  []; fo_consequent = [ formula ] };
			depth = 0;
			max_depth = 100;
			next_constant_index = 1;
			used_constants = [];
			ground_terms = ground_terms;
		}
	in
	prove_sequent initial_state


let prove_sequent_top_FO seq =
	let ground_terms =
		List.fold_left
			(fun acc f -> extract_ground_terms f @ acc)
			[]
			(seq.fo_antecedent @ seq.fo_consequent)
	in
	let initial_state =
		{
			sequent = seq;
			depth = 0;
			max_depth = 100;
			next_constant_index = 1;
			used_constants = [];
			ground_terms = ground_terms;
		}
	in
	prove_sequent initial_state


let is_valid_sequent_calculus_FO formula = match prove_formula_FO formula with ProvedFO -> true | FailedFO _ -> false


(* Helper for string representation *)

let rec string_of_term_first_order_FO t =
    match t with
    | FOVar x -> x
    | FOConst c -> c
    | FOFunc (f, args) ->
        match args with
        | [] -> f
        | _ ->
            f ^ "(" ^
            (String.concat ", " (List.map string_of_term_first_order_FO args))
            ^ ")"


let string_of_sequent_calculus_FO_sequent seq =
	let string_of_formula_list lst =
		String.concat ", "
			(List.map
				(fun f ->
					let rec to_str f =
						match f with
						| FOAtomic (p, args) ->
							p
							^ "("
							^ String.concat ", "
								(List.map string_of_term_first_order_FO args)
							^ ")"
						| FONeg f1 -> "¬" ^ to_str f1
						| FOAnd (f1, f2) ->
							"(" ^ to_str f1 ^ " ∧ " ^ to_str f2 ^ ")"
						| FOOr (f1, f2) ->
							"(" ^ to_str f1 ^ " ∨ " ^ to_str f2 ^ ")"
						| FOImplies (f1, f2) ->
							"(" ^ to_str f1 ^ " → " ^ to_str f2 ^ ")"
						| FOEquiv (f1, f2) ->
							"(" ^ to_str f1 ^ " ↔ " ^ to_str f2 ^ ")"
						| FOForall (x, f1) -> "∀" ^ x ^ "." ^ to_str f1
						| FOExists (x, f1) -> "∃" ^ x ^ "." ^ to_str f1
					in
					to_str f)
				lst)
	in
	string_of_formula_list seq.fo_antecedent ^ " ⟶ "
	^ string_of_formula_list seq.fo_consequent

