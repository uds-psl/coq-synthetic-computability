Require SyntheticComputability.Shared.Dec.
Require Import Setoid Morphisms.
Require Export SyntheticComputability.Synthetic.Definitions.
From SyntheticComputability.Shared Require Import mu_nat.

(** Dependently-typed deciders *)

Lemma decider_dec X (p : X -> Prop) f :
  decider f p -> forall x, Dec.dec (p x).
Proof.
  intros Hf x. specialize (Hf x). destruct (f x); firstorder congruence.
Qed.

Lemma dec_decider X p (d : forall x : X, Dec.dec (p x)) :
  decider (fun x => if d x then true else false) p.
Proof.
  intros x. destruct (d x); firstorder congruence.
Qed.

Lemma dec_decidable X p :
  (forall x : X, Dec.dec (p x)) -> decidable p.
Proof.
  intros d. eapply ex_intro, dec_decider.
Qed.

Lemma decidable_iff X p :
  decidable p <-> inhabited (forall x : X, Dec.dec (p x)).
Proof.
  split.
  - intros [f H]. econstructor. eapply decider_dec, H.
  - intros [f]. eapply dec_decidable, f.
Qed.

(** *** Discrete types  *)

Notation eq_on T := ((fun '(x,y) => x = y :> T)).

Definition discrete X := decidable (eq_on X).

Lemma decider_if X (D : forall x y : X, Dec.dec (x = y)) :
 decider (fun '(x,y) => if D x y then true else false) (eq_on X).
Proof.
  intros (x,y). red. destruct (D x y); firstorder congruence.
Qed.  

Lemma discrete_iff X :
  discrete X <-> inhabited (forall x y : X, Dec.dec (x=y)).
Proof.
  split.
  - intros [D] % decidable_iff. econstructor. intros x y; destruct (D (x,y)); firstorder.
  - intros [d]. eapply decidable_iff. econstructor. intros (x,y). eapply d.
Qed.
