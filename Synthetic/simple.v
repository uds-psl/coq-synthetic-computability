Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.Shared.Pigeonhole.
Require Import SyntheticComputability.Shared.FinitenessFacts.
Require Import SyntheticComputability.Synthetic.reductions SyntheticComputability.Synthetic.truthtables.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts SyntheticComputability.Synthetic.EnumerabilityFacts SyntheticComputability.Synthetic.SemiDecidabilityFacts SyntheticComputability.Synthetic.ReducibilityFacts.
Require Import SyntheticComputability.Shared.ListAutomation.
Require Import List Arith.

Import ListNotations ListAutomationNotations.

Definition productive (p : nat -> Prop) := exists f : nat -> nat, forall c, (forall x, W c x -> p x) -> p (f c) /\ ~ W c (f c).

Lemma productive_nonenumerable p :
  productive p -> ~ enumerable p.
Proof.
  intros [f Hf] [c Hc] % W_spec.
  destruct (Hf c) as [H1 % Hc H2].
  eapply Hc. tauto.
Qed.

Lemma K0_productive :
  productive (compl K0).
Proof.
  exists (fun n => n). intros c H.
  specialize (H c). unfold K0, compl in *. tauto.
Qed.

Lemma productive_dedekind_infinite p :
  productive p -> dedekind_infinite p.
Proof.
  specialize List_id as [c_l c_spec]. intros [f Hf].
  eapply (weakly_generative_dedekind_infinite). econstructor.
  intros l.
  exists (f (c_l l)). intros Hl. split.
  - specialize (Hf (c_l l)).
    rewrite <- c_spec. eapply Hf.
    intros x. rewrite c_spec. eapply Hl.
  - eapply Hf. intros x. rewrite c_spec. eapply Hl.
Qed.

Lemma productive_subpredicate p :
  productive p ->
  exists q : nat -> Prop, enumerable q /\ dedekind_infinite q /\ (forall x, q x -> p x).
Proof.
  intros H.
  eapply dedekind_infinite_problem.
  eapply productive_dedekind_infinite. eauto.
Qed.

Lemma productive_red p q :
  p ⪯ₘ q -> productive p -> productive q.
Proof. 
  intros [f Hf] [g Hg].
  specialize (SMN' f) as [k Hk].
  exists (fun c => f (g (k c))). intros c Hs.
  assert (Hkc : forall x, W (k c) x -> p x) by  (intros; now eapply Hf, Hs, Hk).
  split.
  - now eapply Hf, Hg. 
  - intros ?. eapply Hg, Hk; eauto.
Qed.

Lemma many_one_complete_subpredicate p :
  m-complete p ->
  exists q : nat -> Prop, enumerable q /\ dedekind_infinite q /\ (forall x, q x -> compl p x).
Proof.
  intros Hcomp. eapply productive_subpredicate.
  eapply productive_red.
  - eapply red_m_complement. eapply Hcomp. eapply K0_enum.
  - eapply K0_productive. 
Qed.

Definition simple (p : nat -> Prop) :=
  enumerable p /\ ~ exhaustible (compl p) /\ ~ exists q, enumerable q /\ ~ exhaustible q /\ (forall x, q x -> compl p x).

Lemma simple_non_enumerable p : 
  simple p -> ~ enumerable (compl p).
Proof.
  intros (H1 & H2 & H3) H4.
  apply H3. eauto.
Qed.

Lemma simple_undecidable p :
  simple p -> ~ decidable p.
Proof.
  intros Hs Hd % decidable_complement % decidable_enumerable; eauto.
  now eapply simple_non_enumerable in Hs.
Qed.

Lemma simple_m_incomplete p :
  simple p -> ~ m-complete p.
Proof.
  intros (H1 & H2 & H3) (q & Hq1 & Hq2 & Hq3) % many_one_complete_subpredicate.
  eapply H3. exists q; repeat split; eauto.
  now eapply unbounded_non_finite, dedekind_infinite_unbounded.
Qed.

Lemma non_finite_non_empty {X} (p : X -> Prop) :
  ~ exhaustible p -> ~~ exists x, p x.
Proof.
  intros H1 H2. apply H1. exists []. firstorder.
Qed.

Lemma simple_no_cylinder p :
  (fun '((x, n) : nat * nat) => p x) ⪯₁ p -> ~ simple p.
Proof.
  intros [f [inj_f Hf]] (H1 & H2 & H3). red in Hf.
  apply (non_finite_non_empty _ H2). intros [x0 Hx0].
  apply H3.
  exists (fun x => exists n, x = f (x0, n)). split. 2:split.
  - eapply semi_decidable_enumerable; eauto.
    exists (fun x n => Nat.eqb x (f (x0, n))).
    intros x. split; intros [n H]; exists n; destruct (Nat.eqb_spec x (f (x0, n))); firstorder congruence.
  - eapply unbounded_non_finite, dedekind_infinite_unbounded.
    exists (fun n => f (x0, n)). intros. split. eauto.
    now intros ? [=] % inj_f.
  - intros ? [n ->]. red. now rewrite <- (Hf (x0, n)).
Qed.
