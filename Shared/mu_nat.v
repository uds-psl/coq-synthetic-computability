
Require Import Lia.

Definition least p n k := n <= k /\ p k /\ forall i, n <= i -> p i -> k <= i.

Section WO.

  Variable f: nat -> bool.

  (* Guardedness predicate *)
  Inductive G (n: nat) : Prop :=
  | GI : (f n = false -> G (S n)) -> G n.

  Lemma G_sig n :
    G n -> { k | least (fun k => f k = true) n k }.
  Proof.
    induction 1 as [n _ IH].
    destruct (f n) eqn:H.
    - exists n. repeat split; eauto.
    - destruct (IH eq_refl) as (k & Hle & Hk & Hleast).
      exists k. repeat split.
      + lia.
      + exact Hk.
      + intros i Hi. inversion Hi.
        * congruence.
        * eapply Hleast; eauto. lia.
  Defined.

  Lemma G_zero n :
    G n -> G 0.
  Proof.
    induction n as [|n IH].
    - intros H. exact H.
    - intros H. apply IH. constructor. intros _. exact H.
  Defined.

  Theorem mu_nat :
    (exists n, f n = true) -> { n | least (fun n => f n = true) 0 n }.
  Proof.
    intros H. apply (G_sig 0).
    destruct H as [n H].  
    apply (G_zero n).
    constructor. rewrite H. discriminate.
  Defined.

End WO.

Definition mu_nat_dep : forall P : nat -> Prop,
(forall n : nat, {P n} + {~ P n}) -> (exists n : nat, P n) -> {n : nat | P n}.
Proof.
  intros P d Hn.
  edestruct (mu_nat (fun n => if d n then true else false)) as [n H].
  - abstract (destruct Hn as [n H]; exists n; destruct d; firstorder).
  - exists n. abstract (destruct H as (_ & H & _),  (d n); congruence).
Defined.  

Definition mu_nat_dep_least : forall P : nat -> Prop,
(forall n : nat, {P n} + {~ P n}) -> (exists n : nat, P n) -> {n : nat | least P 0 n}.
Proof.
  intros P d Hn.
  edestruct (mu_nat (fun n => if d n then true else false)) as [n H].
  - abstract (destruct Hn as [n H]; exists n; destruct d; firstorder).
  - exists n. destruct H as (? & ? & H1),  (d n); try congruence.
    firstorder try congruence. eapply H1. 2: destruct (d); firstorder. lia.
Defined.

Lemma mu_nat_dep_min P d H : forall m, m < proj1_sig (@mu_nat_dep P d H) -> ~ P m.
Proof.
  intros. unfold mu_nat_dep in *. destruct mu_nat as [n (H1 & H2 & H3)].
  cbn in H0. intros Hm.
  specialize (H3 m ltac:(lia)). destruct (d m); firstorder lia.
Qed.

Lemma mu_nat_dep_irrel P d H1 H2 : 
  proj1_sig (mu_nat_dep P d H1) = proj1_sig (mu_nat_dep P d H2).
Proof.
  match goal with [ |- ?L = ?R ] => 
    (assert (L < R \/ L = R \/ L > R) as [H | [H | H]] by lia)
  end.
  - eapply mu_nat_dep_min in H. repeat destruct mu_nat_dep; cbn in *; tauto.
  - eauto.
  - eapply mu_nat_dep_min in H. repeat destruct mu_nat_dep; cbn in *; tauto.
Qed.
