# The Kleene-Post and Post's Theorem in the Calculus of Inductive Constructions

## Meta

- Author(s):
  - Yannick Forster
  - Dominik Kirst
  - Niklas Mück
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.17
- Additional dependencies: 
  - the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp)
  - for the syntactic arithmetical hierarchy, the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability)
- Coq namespace: `SyntheticComputability`

## Description

- A proof of Post's theorem about the arithmetical hierarchy in `PostsTheorem/PostsTheorem.v`
- A proof of the Kleene-Post theorem in `PostsTheorem/KleenePostTheorem.v`

## Installation

```sh
opam switch create coq-synthetic-computability --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.17.0 coq-equations.1.3+8.17 coq-stdpp.1.8.0
cd theories
make
```

To build the part of the development dealing with the syntactic arithmetical hierarchy (Appendix A), do:

```sh
opam install coq-library-undecidability.1.1+8.17
make models
```
