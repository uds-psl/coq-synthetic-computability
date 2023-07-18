# Synthetic Computability Theory in Coq

## Meta

- Author(s):
  - Yannick Forster
  - Felix Jahn
  - Dominik Kirst
  - Fabian Kunze
  - Nils Lauermann
  - Niklas Mück
- Maintainer:
  - Yannick Forster ([**@yforster**](https://github.com/yfrster))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.17
- Additional dependencies: 
  - the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp)
  - optionally, the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability)
- Coq namespace: `SyntheticComputability`
- Related publication(s):
  - [Church’s Thesis and Related Axioms in Coq’s Type Theory](https://drops.dagstuhl.de/opus/volltexte/2021/13455/) doi:[10.4230/LIPIcs.CSL.2021.21](https://doi.org/10.4230/LIPIcs.CSL.2021.21)
  - [Parametric Church’s Thesis: Synthetic Computability Without Choice](https://arxiv.org/abs/2112.11781) doi:[10.1007/978-3-030-93100-1_6](https://doi.org/10.1007/978-3-030-93100-1_6)
  - [Computability in Constructive Type Theory](https://ps.uni-saarland.de/~forster/thesis.php) doi:[10.22028/D291-35758 ](https://dx.doi.org/10.22028/D291-35758)
  - [Synthetic Kolmogorov Complexity in Coq](https://drops.dagstuhl.de/opus/volltexte/2022/16721/) doi:[10.4230/LIPIcs.ITP.2022.12](https://doi.org/10.4230/LIPIcs.ITP.2022.12)
  - [Constructive and Synthetic Reducibility Degrees: Post's Problem for Many-One and Truth-Table Reducibility in Coq](https://doi.org/10.4230/LIPIcs.CSL.2023.21) doi:[10.4230/LIPIcs.CSL.2023.21](https://doi.org/10.4230/LIPIcs.CSL.2023.21)
  - [A Computational Cantor-Bernstein and Myhill's Isomorphism Theorem in Constructive Type Theory (Proof Pearl)](https://hal.inria.fr/hal-03891390/file/myhill-cantor-cpp23.pdf) doi:[10.1145/3573105.3575690](https://doi.org/10.1145/3573105.3575690)

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

## Installation

```sh
opam switch create coq-synthetic-computability --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.17 coq-stdpp.1.8.0
cd theories
make
make install
```

To build the part of the development relying on models of computation, in addition you have to 

```sh
opam install coq-library-undecidability.1.1+8.17
make models
make install-models
```
