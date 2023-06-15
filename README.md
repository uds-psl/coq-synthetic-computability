# Oracle Computability and Turing Reducibility in the Calculus of Inductive Constructions

## Meta

- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.17.0
- Additional dependencies:
  - the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp)
- Coq namespace: `SyntheticComputability`

## Installation

```sh
opam switch create coq-synthetic-computability --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.17 coq-stdpp.1.8.0
make
make install
```
