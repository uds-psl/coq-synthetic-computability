From SyntheticComputability Require Import Equivalence EA equiv_on DecidabilityFacts SemiDecidabilityFacts Definitions reductions EnumerabilityFacts ReducibilityTransport Dec.

Import EmbedNatNotations.

Section Assume_EA.

Context {EA : EA}.

Notation φ := (proj1_sig EA).
Notation EAP := (proj2_sig EA).

Set Default Goal Selector "!".

Lemma Rice {p : nat -> Prop} c_bot c :
  (forall x, ~ W c_bot x) ->
  (forall c1 c2, W c1 ≡{_} W c2 -> p c1 -> p c2) ->
  ~ p c ->
  p c_bot -> compl K0 ⪯ₘ p.
Proof.
  intros Hbot Hequiv Hc Hpbot.
  edestruct EAP with (p := fun x y => K0 x /\ W c y) as [f Hf]. {
    exists (fun x => fun! ⟨n,m⟩ => if φ x n is Some x' then if Nat.eqb x x' then φ c m else None else None).
    intros x y. split.
    + intros [[n H1] [m H2]]. exists ⟨n,m⟩. now rewrite embedP, H1, PeanoNat.Nat.eqb_refl, H2.
    + intros [nm H]. destruct (unembed nm) as [n m].
      destruct φ as [x' | ] eqn:E; try congruence.
      destruct (PeanoNat.Nat.eqb_spec x x') as [-> | ]; try congruence.
      firstorder.
  } 
  exists f. intros x. unfold K0, compl.
  split.
  - intros H. eapply Hequiv. 2:exact Hpbot.
    cbn. intros. rewrite <- (Hf x x0). firstorder.
  - intros H. intros Hx.
    apply Hc. eapply Hequiv. 2: exact H.
    intros y. rewrite <- (Hf x y). firstorder.
Qed.

Lemma Rice_Theorem {p : nat -> Prop} :
  (forall c1 c2, W c1 ≡{_} W c2 -> p c1 -> p c2) ->
  (exists c1, p c1) ->
  (exists c2, ~ p c2) -> ~ (enumerable p /\ enumerable (compl p)).
Proof.
  intros Hequiv [c1 Hc1] [c2 Hc2] [Hp1 Hp2].
  destruct (do_EA (fun _ => False)) as [c_bot Hbot].
  - exists (fun _ => None). firstorder congruence.
  - assert (~~ (p c_bot \/ ~ p c_bot)) as Hc by tauto.
    apply Hc; clear Hc. intros [? | ?].
    + clear Hp2. eapply K0_not_enumerable; eauto.
      eapply enumerable_red; eauto.
      1: eapply Rice with (c_bot := c_bot); eauto.
      firstorder.
    + clear Hp1. eapply K0_not_enumerable; eauto.
      eapply enumerable_red; eauto.
      1: eapply Rice with (c_bot := c_bot) (c := c1); eauto.
      1: firstorder.
      intros ? ? ? H1 ?. eapply H1, Hequiv; eauto; firstorder.
Qed.

Lemma Rice_TheoremCorr {p : nat -> Prop} :
  (forall c1 c2, W c1 ≡{_} W c2 -> p c1 -> p c2) ->
  (exists c1, p c1) ->
  (exists c2, ~ p c2) -> ~ decidable p.
Proof.
  intros Hequiv Hc1 Hc2 Hp.
  eapply Rice_Theorem; eauto.
  split.
  - eapply decidable_enumerable; eauto.
  - eapply decidable_enumerable; eauto.
    now eapply decidable_complement.
Qed.

Lemma Rice_HO {p : (nat -> Prop) -> Prop} :
  (forall (q q' : nat -> Prop), (forall x, q x <-> q' x) -> p q <-> p q') ->
  forall q1 q2, 
    enumerable q1 -> enumerable q2 ->
    p q1 -> ~ p q2 -> ~ decidable p.
Proof.
  intros Hequiv q1 q2 H1 H2 Hq1 Hq2 H.
  eapply (@Rice_TheoremCorr (fun c => p (W c))).
  - firstorder.
  - eapply do_EA in H1 as [c Hc]. exists c. firstorder. 
  - eapply do_EA in H2 as [c Hc]. exists c. firstorder. 
  - destruct H as [f Hf]. exists (fun c => f (W c)). firstorder.
Qed.

Section EPF.

Variable Part : partiality.

Variable Θ : nat -> (nat ↛ nat).

Instance equiv_part `{partiality} {A} : equiv_on (part A) := {| equiv_rel := @partial.equiv _ A |}.

Variable EPF : forall f : nat -> nat ↛ nat, exists γ, forall x, Θ (γ x) ≡{nat ↛ nat} f x.

Lemma FP : forall f, exists e, Θ e ≡{_} Θ (f e).
Proof.
  intros f.
  pose (h := fun x y => bind (Θ x x) (fun e => Θ e y)).
  destruct (EPF h)  as [γ Hγ].
  destruct (EPF (fun _ x => ret (f (γ x))))  as [γ' Hc].
  pose (c := γ' 0).
  exists (γ c).
  rewrite Hγ. unfold h.
  intros x v. rewrite bind_hasvalue. split.
  - now intros (y & <- % Hc % ret_hasvalue_inv & H2).
  - intros Hv. eexists. split; eauto.
    eapply Hc. now eapply ret_hasvalue.
Qed.

Lemma Rice_Theorem' {p : nat -> Prop} :
  (forall c1 c2, Θ c1 ≡{_} Θ c2 -> p c1 -> p c2) ->
  (exists c1, p c1) ->
  (exists c2, ~ p c2) -> ~ decidable p.
Proof.
  intros Hequiv [c1 Hc1] [c2 Hc2] [f Hf].
  pose (h x := if f x then Θ c2 else Θ c1).
  destruct (EPF h) as [γ H].
  destruct (FP γ) as [c Hc].
  rewrite H in Hc. unfold h in Hc.
  destruct (f c) eqn:E.
  - assert (Hx : p c) by firstorder.
    eapply Hc2. eapply Hequiv. 2: eapply Hx. eapply Hc.
  - assert (Hx : ~ p c) by firstorder congruence.
    eapply Hx. eapply Hequiv. 1:symmetry; eapply Hc. exact Hc1.
Qed.

End EPF.

Corollary Rice_HO' {Part : partiality} {p : (nat ↛ nat) -> Prop} :
  EPF -> (forall f f', f ≡{_} f' -> p f <-> p f') ->
  forall f1 f2, p f1 -> ~ p f2 -> ~ decidable p.
Proof.
  intros [θ EPF] Hequiv f1 f2 H1 H2 H.
  eapply (@Rice_Theorem' Part θ EPF (fun c => p (θ c))).
  - firstorder.
  - destruct (EPF (fun _ => f1)) as [c Hc]. exists (c 0).
    firstorder.
  - destruct (EPF (fun _ => f2)) as [c Hc]. exists (c 0).
    firstorder.
  - destruct H as [f Hf]. exists (fun c => f (θ c)). firstorder.
Qed.

End Assume_EA.
