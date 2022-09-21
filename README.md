# A Computational Cantor-Bernstein and Myhill's Isomorphism Theorem in Constructive Type Theory (Proof Pearl)

## Description

The three files containing the theorems are:

- `Basic/Myhill.v` with the Myhill Isomorphism Theorem and CB as consequence
- `Basic/CB_PHP.v` with CB using a computational pigeonhole principle
- `Basic/CB.v` with CB using list enumerators

## Compilation

```sh
opam switch create cantor_bernstein_myhill --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations.1.3+8.16
make
```
