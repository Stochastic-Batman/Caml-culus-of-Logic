open Definitions
open Aux_propositional


(* Gentzen System G' rules *)

(* Axiom rule *)
let is_axiom seq = List.exists (fun a -> List.exists (fun c -> a = c) seq.consequent) seq.antecedent

(* Left rules *)
let and_left seq f = match f with
	| And(e1, e2) ->
		[{ antecedent = e1 :: e2 :: (List.filter (fun x -> x <> f) seq.antecedent);
		consequent = seq.consequent }]
	| _ -> []


let or_left seq f = match f with
	| Or(e1, e2) ->
		[{ antecedent = e1 :: (List.filter (fun x -> x <> f) seq.antecedent); consequent = seq.consequent };
		{ antecedent = e2 :: (List.filter (fun x -> x <> f) seq.antecedent); consequent = seq.consequent }]
	| _ -> []


let implies_left seq f = match f with
	| Implies(e1, e2) ->
		[{ antecedent = List.filter (fun x -> x <> f) seq.antecedent;
		consequent = e1 :: seq.consequent };
		{ antecedent = e2 :: (List.filter (fun x -> x <> f) seq.antecedent);
		consequent = seq.consequent }]
	| _ -> []


let neg_left seq f = match f with
	| Neg(e) ->
		[{ antecedent = List.filter (fun x -> x <> f) seq.antecedent;
		consequent = e :: seq.consequent }]
	| _ -> []


(* Right rules *)
let and_right seq f = match f with
	| And(e1, e2) ->
		[{ antecedent = seq.antecedent;
		consequent = e1 :: (List.filter (fun x -> x <> f) seq.consequent) };
		{ antecedent = seq.antecedent;
		consequent = e2 :: (List.filter (fun x -> x <> f) seq.consequent) }]
	| _ -> []


let or_right seq f = match f with
	| Or(e1, e2) ->
		[{ antecedent = seq.antecedent;
		consequent = e1 :: e2 :: (List.filter (fun x -> x <> f) seq.consequent) }]
	| _ -> []


let implies_right seq f = match f with
	| Implies(e1, e2) ->
		[{ antecedent = e1 :: seq.antecedent;
		consequent = e2 :: (List.filter (fun x -> x <> f) seq.consequent) }]
	| _ -> []


let neg_right seq f = match f with
	| Neg(e) ->
		[{ antecedent = e :: seq.antecedent;
		consequent = List.filter (fun x -> x <> f) seq.consequent }]
	| _ -> []


let rec prove_sequent seq depth max_depth =
	if depth > max_depth then Failed []  (* Prevent infinite recursion *)
	else if is_axiom seq then Proved
	else
		let apply_rule rule_func formula = rule_func seq formula in

		(* Try left rules first *)
		let left_formulas = seq.antecedent in
		let left_results = List.concat_map (fun f ->
			match f with
			| And(_,_) -> apply_rule and_left f
			| Or(_,_) -> apply_rule or_left f
			| Implies(_,_) -> apply_rule implies_left f
			| Neg(_) -> apply_rule neg_left f
			| _ -> []
		) left_formulas in

		if left_results <> [] then
			let sub_results = List.map (fun sub_seq -> prove_sequent sub_seq (depth + 1) max_depth) left_results in
			if List.for_all (function Proved -> true | _ -> false) sub_results then Proved
			else Failed []
		else
			(* Try right rules *)
			let right_formulas = seq.consequent in
			let right_results = List.concat_map (fun f ->
				match f with
				| And(_,_) -> apply_rule and_right f
				| Or(_,_) -> apply_rule or_right f
				| Implies(_,_) -> apply_rule implies_right f
				| Neg(_) -> apply_rule neg_right f
				| _ -> []
			) right_formulas in

			if right_results <> [] then
				let sub_results = List.map (fun sub_seq -> prove_sequent sub_seq (depth + 1) max_depth) right_results in
				if List.for_all (function Proved -> true | _ -> false) sub_results then Proved
				else Failed []
			else
				Failed []  (* No rules apply and not an axiom *)

(* Top-level function to prove a formula *)
let prove_formula formula =
	let initial_sequent = { antecedent = []; consequent = [formula] } in
	prove_sequent initial_sequent 0 1000  (* Max depth 1000 *)

(* Test if a formula is valid using sequent calculus *)
let is_valid_sequent_calculus formula =
	match prove_formula formula with
	| Proved -> true
	| Failed _ -> false

(* Function to prove a general sequent *)
let prove_sequent_top seq =
	prove_sequent seq 0 1000
