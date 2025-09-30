# 🐫 Caml-culus of Logic

Implementation of selected concepts from propositional logic, first-order logic, logic programming, probabilistic logic programming, and fuzzy logic programming.

## Definitions Module

The file `definitions.ml` contains the foundational type definitions and auxiliary functions utilized by subsequent implementations. This module serves as the core dependency for multiple files.

## Normal Forms Implementation

The module `nf.ml` implements recursive transformation algorithms for propositional logic expressions. It provides methods to convert expressions into three canonical forms: Negative Normal Form (NNF), Conjunctive Normal Form (CNF) and Disjunctive Normal Form (DNF).

To execute the examples included in `nf.ml`:

```
ocamlc -c definitions.ml
ocamlc -c nf.ml
ocamlc -o nf definitions.cmo nf.cmo
./nf
```
