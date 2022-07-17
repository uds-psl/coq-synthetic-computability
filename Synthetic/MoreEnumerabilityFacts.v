(* 
  Autor(s):
    Yannick Forster (1)
    Dominik Kirst (1), contributed the code in section Inf
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From SyntheticComputability.Shared Require Import ListAutomation Dec.
Require Import List Lia.
Import ListNotations ListAutomationNotations.

Lemma enumerable_enum {X} {p : X -> Prop} :
  enumerable p <-> list_enumerable p.
Proof.
  split. eapply enumerable_list_enumerable. eapply list_enumerable_enumerable.
Qed.

#[export] Hint Extern 4 => match goal with [H : list_enumerator _ ?p |- ?p _ ] => eapply H end : core.

Lemma decider_eq_dec {X} {d} :
  decider d (eq_on X) -> eq_dec X.
Proof.
  intros Hd x y. eapply (decider_dec _ _ _ Hd (x,y)).
Qed.
Local Hint Extern 0 => match goal with [H : decider ?d (eq_on ?X) |- eq_dec ?X ] => exact (decider_eq_dec H) end : typeclass_instances.

Lemma list_enumerator_conj X (p q : X -> Prop) d f g (Hd : decider d (eq_on X)) :
  list_enumerator f p -> list_enumerator g q -> list_enumerator (fun n => [ x | x ∈ cumul f n, x el cumul g n]) (fun x => p x /\ q x).
Proof.
  intros Hf Hg x. split.
  + intros [Hp Hq]. eapply (cumul_spec Hf) in Hp as [m1]. eapply (cumul_spec Hg) in Hq as [m2].
    exists (m1 + m2). in_collect x.
    eapply cum_ge'; eauto. lia.
    eapply cum_ge'; eauto. lia.
  + intros [m].
    inv_collect; eauto.
Qed.

Lemma list_enumerable_conj X (p q : X -> Prop) :
  discrete X -> list_enumerable p -> list_enumerable q -> list_enumerable (fun x => p x /\ q x).
Proof.
  intros [] [] []. eapply ex_intro, @list_enumerator_conj; eauto. Unshelve. 2: eauto.
Qed.

Lemma enumerator_conj X (p q : X -> Prop) d f g :
  decider d (eq_on X) -> enumerator f p -> enumerator g q -> ∑ h, enumerator h (fun x => p x /\ q x).
Proof.
  intros Hd Hf % enumerator_list_enumerator Hg % enumerator_list_enumerator.
  unshelve eapply exist, list_enumerator_enumerator, list_enumerator_conj; eauto.
Qed.

Lemma list_enumerator_disj X (p q : X -> Prop) f g :
  list_enumerator f p -> list_enumerator g q -> list_enumerator (fun n => [ x | x ∈ f n] ++ [ y | y ∈ g n]) (fun x => p x \/ q x).
Proof.
  intros Hf Hg x. split.
  - intros [H1 | H1].
    + eapply Hf in H1 as [m]. exists m. in_app 1. in_collect x. eauto.
    + eapply Hg in H1 as [m]. exists m. in_app 2. in_collect x. eauto.
  - intros [m]. 
    inv_collect; eauto.
Qed.

Lemma list_enumerable_disj X (p q : X -> Prop) :
  list_enumerable p -> list_enumerable q -> list_enumerable (fun x => p x \/ q x).
Proof.
  intros [] []. eapply ex_intro, @list_enumerator_disj; eauto.
Qed.

Lemma enumerator_disj X (p q : X -> Prop) f g :
  enumerator f p -> enumerator g q -> ∑ h, enumerator h (fun x => p x \/ q x).
Proof.
  intros Hf % enumerator_list_enumerator Hg % enumerator_list_enumerator.
  unshelve eapply exist, list_enumerator_enumerator, list_enumerator_disj; eauto.
Qed.



Lemma enumerable_conj X (p q : X -> Prop) :
  discrete X -> enumerable p -> enumerable q -> enumerable (fun x => p x /\ q x).
Proof.
  intros [] [] []. edestruct enumerator_conj as [h Hh]. 4:eapply ex_intro, Hh. 
  all: eauto.
Qed.

Lemma enumerable_disj X (p q : X -> Prop) :
  enumerable p -> enumerable q -> enumerable (fun x => p x \/ q x).
Proof.
  intros [] []. edestruct enumerator_disj as [h Hh]. 3:eapply ex_intro, Hh.
  all: eauto.
Qed.



Require Import ConstructiveEpsilon.
From SyntheticComputability Require Import Shared.ListAutomation Shared.mu_nat.


Import ListAutomationNotations.

Definition mu_nat_p := constructive_indefinite_ground_description_nat.

Lemma mu_nat_p_least (P : nat -> Prop) d H : forall m, P m -> m >= proj1_sig (@mu_nat_p P d H).
Proof.
  intros m Hm. unfold mu_nat_p, constructive_indefinite_ground_description_nat in *.
  destruct (Compare_dec.le_lt_dec (proj1_sig (linear_search P d 0 (let (n, p) := H in O_witness P n (stop P n p)))) m) as [Hl|Hl].
  eassumption. exfalso.
  unfold linear_search in Hl.
  destruct (linear_search_conform P d 0) as [r Hr].
  eapply (rel_ls_lower_bound _ Hr) in Hm. cbn in Hl. all:lia.
Qed.

Opaque mu_nat.

Set Implicit Arguments.
Unset Strict Implicit.
(* ** Definition of infinite and generating types *)

Definition injective X Y (f : X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Definition infinite {X} (p : X -> Prop) :=
  exists (f : nat -> X), injective f /\ forall n, p (f n).

Section Inf.
  
  Variables (X : Type) (f : nat -> option X).
  Variable p : X -> Prop.
  Hypothesis Hf : forall x, p x <-> exists n, f n = Some x.
  Hypothesis HX : eq_dec X.

  Hypothesis Hg : generative p.

  Instance el_dec :
    forall (A : list X) x, dec (x el A).
  Proof.
    intros A x. induction A; cbn; auto.
  Qed.

  From Coq.Logic Require Import ConstructiveEpsilon.

  Definition le_f x y :=
    exists n, f n = Some x /\ forall n', f n' = Some y -> n <= n'.

  Lemma nxt' (l : list X) :
    { x | ~ x el l /\ (forall y, ~ y el l -> le_f x y) /\ p x}.
  Proof.
    pose (q := fun n => exists x, f n = Some x /\ ~ x el l).
    assert (H1 : forall x, dec (q x)).
    { intros n. unfold q. destruct (f n). 2:firstorder congruence.
      decide (x el l); firstorder congruence. }
    assert (H2 : exists x, q x).
    { destruct (Hg l) as (x & [n Hx1] % Hf & Hx2). exists n. red. eauto. }
    eapply mu_nat_dep_least in H2 as [n Hn].
    destruct (f n) as [x | ] eqn:E.
    - exists x. destruct Hn as (H2 & (x' & H3 & H4) & H5). rewrite E in H3. specialize H3 as [= <-]. split. 2:split.
      + eauto.
      + intros y Hy. exists n. split. eauto. intros. eapply H5. lia. firstorder.
      + eapply Hf. eauto.
    - exfalso. firstorder congruence.
    - eapply H1.
  Qed.

  Definition nxt l :=
    proj1_sig (nxt' l).

  Lemma nxt_spec l :
    ~ nxt l el l.
  Proof.
    unfold nxt. destruct (nxt' l); cbn. apply a.
  Qed.

  Lemma nxt_le_f l :
    forall x, ~ x el l -> le_f (nxt l) x.
  Proof.
    unfold nxt. destruct (nxt' l); cbn. apply a.
  Qed.
  
  Definition LL := generate nxt.

  Definition F n :=
    nxt (LL n).

  Lemma LL_cum :
    cumulative LL.
  Proof.
    intros n. now exists [(F n)].
  Qed.

  Lemma F_nel n :
    ~ F n el LL n.
  Proof.
    apply nxt_spec.
  Qed.

  Lemma F_el n :
    F n el LL (S n).
  Proof.
    cbn. apply in_app_iff. right. left. reflexivity.
  Qed.

  Lemma F_lt n m :
    n < m -> F n el LL m.
  Proof.
    intros H. apply (cum_ge' (n:=S n)).
    - apply LL_cum.
    - apply F_el.
    - lia.
  Qed.

  Lemma F_inj' n m :
    F n = F m -> ~ n < m.
  Proof.
    intros H1 H2 % F_lt. rewrite H1 in H2. apply (F_nel H2).
  Qed.

  Lemma F_inj :
    injective F.
  Proof.
    intros n m Hnm. destruct (PeanoNat.Nat.lt_total n m) as [H|[H|H] ]; trivial.
    - contradiction (F_inj' Hnm H).
    - symmetry in Hnm. contradiction (F_inj' Hnm H).
  Qed.

  Lemma F_p :
    forall n, p (F n).
  Proof.
    unfold F. unfold nxt. intros.
    destruct nxt' as (? & ? & ? & ?); eassumption.
  Qed.

  (* ** Generating data types are in bijection to nat *)

  Lemma LL_f n x :
    f n = Some x -> x el LL (S n).
  Proof.
    revert x.
    induction n as [n IH] using Wf_nat.lt_wf_ind. intros x He.
    decide _; try eassumption. exfalso.
    assert (H : ~ x el LL n).
    { intros H. apply n0. apply (cum_ge' LL_cum H). auto. }
    apply nxt_le_f in H as [n'[H1 H2] ].
    specialize (H2 n He).
    destruct (PeanoNat.Nat.lt_total n' n) as [H3|[->|H3] ].
    - apply (nxt_spec (l:=LL n)).
      eapply cum_ge'; eauto.
    - apply n0. cbn. apply in_app_iff.
      right. left. congruence.
    - lia.
  Qed.

  Lemma LL_F x n :
    x el LL n -> exists m, F m = x.
  Proof.
    induction n; cbn; auto.
    - intros [H|[H|H]] % in_app_iff; auto.
      now exists n.
  Qed.

  Lemma F_sur :
    forall x, p x -> exists n, F n = x.
  Proof.
    intros x [n H] % Hf.
    destruct (LL_F (LL_f H)) as [m H'].
    exists m. congruence.
  Qed.

  Definition G x (H : p x) : nat := (proj1_sig (mu_nat_p _ (fun n => HX (F n) x) (F_sur H))).

  Lemma FG x (H : p x) :
    F (@G x H) = x.
  Proof.
    unfold G. apply @proj2_sig.
  Qed.
  
  Lemma GF n H :
    @G (F n) H = n.
  Proof.
    apply F_inj. now rewrite FG.
  Qed.

End Inf.

Lemma generative_enumerable_strong {X} (p : X -> Prop) :
  discrete X -> enumerable p -> generative p -> exists f : nat -> X, (forall n1 n2, f n1 = f n2 -> n1 = n2) /\ forall x, p x <-> exists n, f n = x.
Proof.
  intros [D] % discrete_iff [e He] G.
  unshelve eexists (F He _ _). abstract firstorder.
  split.
  - intros. eapply F_inj; eauto.
  - intros x. split.
    + eapply F_sur.
    + intros [n <-]. eapply F_p.
Qed.

Lemma generative_cantor_infinite {X} (p : X -> Prop) : 
  discrete X -> enumerable p -> generative p -> cantor_infinite p.
Proof.
  intros H1 H2 H3.
  destruct (generative_enumerable_strong H1 H2 H3) as [f [Hf1 Hf2]].
  exists f. split.
  - eapply Hf2. eauto.
  - eauto.
Qed.