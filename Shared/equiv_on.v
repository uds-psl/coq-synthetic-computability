Require Import ssreflect Setoid.

Class equiv_on (T : Type) :=
  {
    equiv_rel : T -> T -> Prop;
    equiv_rel_is_equiv : Equivalence equiv_rel
  }.
Arguments equiv_rel _ {_} _ _.
Existing Instance equiv_rel_is_equiv.

Notation "a ≡{ T } b" := (@equiv_rel T _ a b) (at level 70).

Instance ext_equiv {A B} `{equiv_on B} : equiv_on (A -> B).
Proof.
  exists (fun (f1 : A -> B) (f2 : A -> B) => forall x, f1 x ≡{B} f2 x).
  split.
  - move => ? ?. reflexivity.
  - move => x y ? z. now symmetry.
  - move => x y z ? ? a. now transitivity (y a).
Defined.

Instance nat_equiv : equiv_on nat := {| equiv_rel := eq |}.
Instance bool_equiv : equiv_on bool := {| equiv_rel := eq |}.
Instance Prop_equiv : equiv_on Prop := {| equiv_rel := iff |}.

Definition surjection_wrt {A} {B} (e : equiv_on B) (f : A -> B) :=
  forall b, exists a, f a ≡{B} b.

Instance equiv_ran {A B} : equiv_on (A -> option B) | 100.
Proof.
  exists (fun f1 f2 => forall x, (exists n, f1 n = Some x) <-> (exists n, f2 n = Some x)).
  split; red.
  - reflexivity.
  - intros x y H1 z. now rewrite H1.
  - intros f1 f2 f3 H1 H2 x.
    now rewrite H1 H2.
Defined.

Notation "f ≡{ran} g" := (@equiv_rel _  equiv_ran f g) (at level 80).
