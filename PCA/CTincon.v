From SyntheticComputability Require Import CT baire_cantor.

Variable ϕ : nat -> nat -> nat -> option nat.
Hypothesis mono : (forall c x : nat, partial.monotonic (ϕ c x)).

Definition CTs :=
  forall f : nat -> nat, {c |  forall x : nat, exists n : nat, ϕ c x n = Some (f x)}.

Definition genmod :=
  exists M, forall F : (nat -> nat) -> nat -> nat, modulus (M F) F.

Goal CTs -> genmod.
Proof.
  intros CT. unshelve eexists.
  - intros F f x.
    pose (G := fun n => 
