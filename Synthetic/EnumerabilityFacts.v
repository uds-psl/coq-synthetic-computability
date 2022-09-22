From SyntheticComputability.Synthetic Require Import DecidabilityFacts.
From SyntheticComputability.Shared Require Export embed_nat mu_nat.
Require Import List Morphisms Lia.
Export EmbedNatNotations.

(** ** Enumerability  *)

Definition enumeratorᵗ' X f := forall x : X, exists n : nat, f n = Some x.
Notation enumeratorᵗ f X := (enumeratorᵗ' X f).
Definition enumerableᵗ X := exists f : nat -> option X, enumeratorᵗ f X.

Definition retraction' {X} {Y} (I : X -> Y) R := forall x : X, R (I x) = Some x.
Notation retraction I R X Y := (@retraction' X Y I R).

Definition retract X Y := exists I R, retraction I R X Y.
Definition datatype X := retract X nat.

Definition injective {X Y} (f : X -> Y) :=
  forall x1 x2, f x1 = f x2 -> x1 = x2.

Lemma retraction_injective X Y I R :
  retraction I R X Y ->
  injective I.
Proof.
  intros HR x1 x2 H % (f_equal R).
  rewrite !HR in H. congruence.
Qed.

Lemma retraction_discrete X Y I R :
  retraction I R X Y -> discrete Y -> discrete X.
Proof.
  intros HR [f Hf].
  exists (fun '(x1, x2) => f (I x1, I x2)).
  intros [x1 x2]. unfold decider, reflects in *.
  rewrite <- Hf.
  split.
  - now intros ->.
  - intros H % (f_equal R). rewrite !HR in H. congruence.
Qed.

Lemma retraction_enumerable X Y I R :
  retraction I R X Y -> enumerableᵗ Y -> enumerableᵗ X.
Proof.
  intros HR [f Hf].
  exists (fun n => match f n with Some x => R x | None => None end).
  intros x. destruct (Hf (I x)) as [n Hn].
  exists n. rewrite Hn. eapply HR.
Qed.

Lemma enumerator_retraction X d e :
  decider d (eq_on X) -> enumeratorᵗ e X -> {I | retraction I e X nat}.
Proof.
  intros Hd He.
  destruct (decider_AC _ (fun x n => if e n is Some y then d (x, y) else false)) as [f Hf].
  - intros x. destruct (He x) as [n Hn]; exists n; rewrite Hn; now eapply Hd.
  - exists f. intros x.
    specialize (Hf x). destruct (e (f x)); try congruence.
    eapply Hd in Hf. congruence.
Qed.

Lemma retraction_decider_eq X I R :
  retraction I R X nat -> decider (fun '(x,y)=> Nat.eqb (I x) (I y)) (eq_on X).
Proof.
  intros H [x y].
  red. rewrite PeanoNat.Nat.eqb_eq.
  split.
  - congruence.
  - intros H1 % (f_equal R). rewrite !H in H1. congruence.
Qed.

Lemma datatype_discrete X :
  datatype X -> discrete X.
Proof.
  intros (I & R & H). eapply ex_intro, retraction_decider_eq, H.
Qed.

Lemma retraction_enumerator X I R :
  retraction I R X nat -> enumeratorᵗ R X.
Proof.
  intros H x. exists (I x). now rewrite H.
Qed.

Lemma datatype_enumerable X :
  datatype X -> enumerableᵗ X.
Proof.
  intros (I & R & H). eapply ex_intro, retraction_enumerator, H.
Qed.

Lemma enumerable_discrete_datatype X :
  discrete X -> enumerableᵗ X -> datatype X.
Proof.
  intros [d Hd] [e He].
  pose proof (enumerator_retraction _ _ _ Hd He) as (I & H).
  now exists I, e.
Qed.  
