# 🐫 Caml-culus of Logic

Implementation of selected concepts from propositional logic, first-order logic, logic programming, probabilistic logic programming, and fuzzy logic programming.

### Definitions and AUX Modules

The file `definitions.ml` contains the foundational type definitions and auxiliary functions utilized by subsequent implementations. This module serves as the core dependency for multiple files. The files with prefix `aux_` are a collection of auxiliary functions for their respective modules (for example, `aux_propositional.ml` contains auxiliary functions for propositional logic).


## Propositional Logic

### Normal Forms

The module `nf.ml` implements recursive transformation algorithms for propositional logic expressions. It provides methods to convert expressions into three canonical forms: Negative Normal Form (NNF), Conjunctive Normal Form (CNF) and Disjunctive Normal Form (DNF).

To execute the examples included in `nf.ml`:

```
ocamlc -c definitions.ml
ocamlc -c aux_propositional.ml
ocamlc -c examples.ml
ocamlc -c nf.ml
ocamlc -o nf definitions.cmo aux_propositional.cmo examples.cmo nf.cmo
./nf
```

## Proof Procedures

`proof_procedures_propositional.ml` implements the following proof methods:
1. Resolution
2. Sequent Calculus (not yet implemented)
3. Tableaux (not yet implemented)

```
ocamlc -c definitions.ml
ocamlc -c aux_propositional.ml
ocamlc -c examples.ml
ocamlc -c nf.ml
ocamlc -c proof_procedures_propositional.ml
ocamlc -o proof_procedures_propositional definitions.cmo aux_propositional.cmo examples.cmo nf.cmo proof_procedures_propositional.cmo
./proof_procedures_propositional
```
