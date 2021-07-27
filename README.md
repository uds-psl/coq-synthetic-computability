# Computability in Constructive Type Theory

This is the Coq mechanisation of part I of "Computability in Constructive Type Theory", the PhD thesis of Yannick Forster.

## How to compile the code

You need `The Coq Proof Assistant, version 8.13.2`, the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp), the [Smpl](https://github.com/uds-psl/smpl) package, the [MetaCoq](metacoq.github.io/) package and the [Equations](https://mattam82.github.io/Coq-Equations/) package installed.

Afterwards, you can type `make`.

## How to install Coq

The easiest way to install Coq and required libraries is via `opam` (version `2`).
```
opam switch create coq-synthetic-computability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.13.2 coq-equations.1.2.3+8.13 coq-stdpp.1.5.0 coq-metacoq-template.1.0~beta2+8.13 coq-smpl
```
