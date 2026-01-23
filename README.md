# Synthetic Computability Theory in Coq

## Meta

## Description

This library contains results on synthetic computability theory.

- Equivalence proofs for various axioms of synthetic computability in `Axioms/Equivalence.v`
- Rice's theorem in `Basic/Rice.v`
- Myhill's isomorphism theorem in `Basic/Myhill.v`
- The existence of simple and hypersimple predicates in `ReducibilityDegrees.summary_reducibility_degrees.v`
- A proof that nonrandom numbers defined via Kolmogorov Complexity form a simple predicate in `KolmogorovComplexity/Kolmogorov_gen.v`
- A definition of oracle computability and Turing reducibility in `TuringReducibility/OracleComputability.v`
- A proof of Post's theorem (`PT`) in `TuringReducibility/SemiDec.v`
- A proof of Post's theorem about the arithmetical hierarchy in `PostsTheorem/PostsTheorem.v`
- A proof of the Kleene-Post theorem in `PostsTheorem/KleenePostTheorem.v`
- A solution to Post's problem in `PostsProblem`

## Installation

```sh
opam switch create coq-synthetic-computability --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.9.0.0 rocq-equations coq-stdpp
cd theories
make
make install
```

To build the part of the development relying on models of computation, in addition you have to 

```sh
opam install coq-library-undecidability
make models
make install-models
```
