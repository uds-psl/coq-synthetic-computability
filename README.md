# Synthetic Kolmogorov Complexity in Coq

This is the Coq mechanisation of the paper draft *Synthetic Kolmogorov Complexity in Coq* by Yannick Forster, Fabian Kunze, and Nils Lauermann.
The relevant file is [`Synthetic/Kolmogorov_gen.v`](./Synthetic/Kolmogorov_gen.v), all other files are taken from the development accompanying the paper [*A Constructive and Synthetic Theory of Reducibility: Myhill’s Isomorphism Theorem and Post’s Problem for Many-one and Truth-table Reducibility in Coq*](https://www.ps.uni-saarland.de/Publications/documents/ForsterEtAl_2020_Synthetic-Reducibility-in-Coq.pdf) by Yannick Forster, Felix Jahn, and Gert Smolka.

## How to compile the code

You need `The Coq Proof Assistant, version 8.13.2`, the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp), and the [Equations](https://mattam82.github.io/Coq-Equations/) package installed.

Afterwards, you can type `make`.

## How to install Coq

The easiest way to install Coq and required libraries is via `opam` (version `2`).
```
opam switch create coq-synthetic-computability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.13.2 coq-equations.1.2.3+8.13 coq-stdpp.1.5.0 
```
