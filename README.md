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
- Compatible Coq versions: 8.15.2
- Additional dependencies: 
  - the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp)
  - optionally, the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability)
- Coq namespace: `SyntheticComputability``
- Related publication(s):
  - [Computability in Constructive Type Theory](https://ps.uni-saarland.de/~forster/thesis.php) doi:[10.22028/D291-35758 ](https://dx.doi.org/10.22028/D291-35758)
  - [Synthetic Kolmogorov Complexity in Coq](https://hal.inria.fr/hal-03596267)

## Description

This library contains results on synthetic computability theory.

- Equivalence proofs for various axioms of synthetic computability in `Axioms/Equivalence.v`
- Rice's theorem in `Basic/Rice.v`
- Myhill's isomorphism theorem in `Basic/Myhill.v`
- The existence of simple and hypersimple predicates in `ReducibilityDegrees.summary_reducibility_degrees.v`
- A proof that nonrandom numbers defined via Kolmogorov Complexity form a simple predicate in `KolmogorovComplexity/Kolmogorov_gen.v`

## Installation

```sh
opam switch create coq-synthetic-computability --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.15.3 stdpp
make
make install
```

