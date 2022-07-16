# Constructive and Synthetic Reducibility Degrees - Post's Problem for Many-one and Truth-table Reducibility in Coq

This repository contains the Coq code accompanying the paper "Constructive and Synthetic Reducibility Degrees - Post's Problem for Many-one and Truth-table Reducibility in Coq" by Yannick Forster and Felix Jahn.

It is a selection of files on the `main` branch of this repository to ease reviewing. The central theorems of the paper are proved in `ReducibilityDegrees/summary_reducibility_degrees.v`.

You need `The Coq Proof Assistant, version 8.15.2` and the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp) installed.
The easiest way to install is via opam as follows:

```sh
opam switch create coq-synthetic-computability --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.15.2 coq-stdpp
```

Afterwards, this project can be build by issuing `make`, html files are created using `make html`.
