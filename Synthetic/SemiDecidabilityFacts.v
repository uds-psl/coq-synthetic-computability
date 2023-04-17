Require Import List Morphisms Lia.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts SyntheticComputability.Synthetic.EnumerabilityFacts SyntheticComputability.Shared.partial SyntheticComputability.Shared.embed_nat SyntheticComputability.Shared.FinitenessFacts.
Export EmbedNatNotations.

(** ** Semi-decidability  *)

Definition equiv_sdec {X} := fun (f g : X -> nat -> bool) => forall x, (exists n, f x n = true) <-> exists n, g x n = true.

Instance Proper_semi_decider {X} :
  Proper (@equiv_sdec X ==> pointwise_relation X iff ==> iff ) (@semi_decider X).
Proof.
  intros f g H1 p q H2. red in H1, H2.
  unfold semi_decider. 
  split; intros H x; cbn in H1.
  - now rewrite <- H2, H, H1.
  - now rewrite H2, H, H1.
Qed.

Instance Proper_semi_decidable {X} :
  Proper (pointwise_relation X iff ==> iff) (@semi_decidable X).
Proof.
  intros p q H2.
  split; intros [f H]; exists f; red.
  - intros x. now rewrite <- (H2 x).
  - intros x. now rewrite H2.
Qed.

Lemma semi_decider_ext {X} {p q : X -> Prop} {f g} :
  semi_decider f p -> semi_decider g q -> equiv_sdec f g -> p ≡{_} q.
Proof.
  unfold semi_decider. cbn.
  intros Hp Hq E x. red in E.
  now rewrite Hp, E, Hq.
Qed. 

Lemma semi_decidable_part_iff {X} {p : X -> Prop} {Part : partiality}:
  semi_decidable p <-> exists Y (f : X -> part Y), forall x, p x <-> exists y, f x =! y.
Proof.
  split.
  - intros [f Hf].
    exists nat, (fun x => mu_tot (f x)). intros x.
    rewrite (Hf x). split; intros [n H].
    + eapply mu_tot_ter in H as [y H]. eauto.
    + eapply mu_tot_hasvalue in H as [H _]. eauto.
  - intros (Y & f & Hf). exists (fun x n => if seval (f x) n is Some _ then true else false).
    intros x. rewrite Hf. split.
    + intros [y H]. eapply seval_hasvalue in H as [n H].
      exists n. now rewrite H.
    + intros [n H]. destruct seval eqn:E; inversion H.
      eexists. eapply seval_hasvalue. eauto.
Qed.

Lemma forall_neg_exists_iff (f : nat -> bool) :
  (forall n, f n = false) <-> ~ exists n, f n = true.
Proof.
  split.
  - intros H [n Hn]. rewrite H in Hn. congruence.
  - intros H n. destruct (f n) eqn:E; try reflexivity.
    destruct H. eauto.
Qed.

Lemma semi_decider_co_semi_decider {X} (p : X -> Prop) f :
  semi_decider f p -> co_semi_decider f (complement p).
Proof.
  intros Hf.
  red in Hf. unfold complement. intros x. rewrite Hf.
  now rewrite forall_neg_exists_iff.
Qed.

Lemma semi_decidable_co_semi_decidable {X} (p : X -> Prop) :
  semi_decidable p -> co_semi_decidable (complement p).
Proof.
  intros [f Hf]. eapply ex_intro, semi_decider_co_semi_decider, Hf.
Qed.

Lemma co_semi_decidable_stable :
  forall X (p : X -> Prop), co_semi_decidable p -> stable p.
Proof.
  intros X p [f Hf] x Hx.
  eapply Hf. eapply forall_neg_exists_iff. red in Hf. rewrite Hf, forall_neg_exists_iff in Hx. 
  tauto.
Qed.

Lemma decider_semi_decider  {X} {p : X -> Prop} f :
  decider f p -> semi_decider (fun x n => f x) p.
Proof.
  intros H x.
  unfold decider, reflects in H.
  rewrite H. now firstorder; econstructor.
Qed.

Lemma decider_co_semi_decider {X} {p : X -> Prop} f :
  decider f p -> co_semi_decider (fun x n => negb (f x)) p.
Proof. 
  intros H x.
  unfold decider, reflects in H.
  rewrite H. split.
  - now intros -> _.
  - intros H0. destruct (f x); cbn in *; now try rewrite (H0 0).
Qed.

Lemma decidable_semi_decidable {X} {p : X -> Prop} :
  decidable p -> semi_decidable p.
Proof.
  intros [f H]. eapply ex_intro, decider_semi_decider, H.
Qed.

Lemma decidable_compl_semi_decidable {X} {p : X -> Prop} :
  decidable p -> semi_decidable (complement p).
Proof.
  intros H.
  now eapply decidable_semi_decidable, decidable_complement.
Qed.

Lemma decidable_co_semi_decidable {X} {p : X -> Prop} :
  decidable p -> co_semi_decidable p.
Proof.
  intros [f H]. eapply ex_intro, decider_co_semi_decider, H.
Qed.

Lemma semi_decidable_projection_iff X (p : X -> Prop) :
  semi_decidable p <-> exists (q : nat * X -> Prop), decidable q /\ forall x, p x <-> exists n, q (n, x).
Proof.
  split.
  - intros [d Hd].
    exists (fun '(n, x) => d x n = true). split. 
    + exists (fun '(n,x) => d x n). intros [n x]. firstorder congruence.
    + intros x. eapply Hd.
  - intros (q & [f Hf] & Hq).
    exists (fun x n => f (n, x)). unfold semi_decider, decider, reflects in *.
    intros x. rewrite Hq. now setoid_rewrite Hf.
Qed.

Lemma semi_decider_and {X} {p q : X -> Prop} f g :
  semi_decider f p -> semi_decider g q -> semi_decider (fun x n => andb (existsb (f x) (seq 0 n)) (existsb (g x) (seq 0 n))) (fun x => p x /\ q x).
Proof.
  intros Hf Hg x.
  red in Hf, Hg |- *. rewrite Hf, Hg.
  setoid_rewrite Bool.andb_true_iff.
  setoid_rewrite existsb_exists.
  repeat setoid_rewrite in_seq. cbn.
  clear.
  split.
  - intros [[n1 Hn1] [n2 Hn2]]. 
    exists (1 + n1 + n2). firstorder lia. 
  - firstorder.
Qed.

Lemma semi_decidable_and {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> semi_decidable (fun x => p x /\ q x).
Proof.
  intros [f Hf] [g Hg]. eapply ex_intro, semi_decider_and; eauto.
Qed.

Lemma reflects_cases {P} {b} :
  reflects b P -> b = true /\ P \/ b = false /\ ~ P.
Proof.
  destruct b; firstorder congruence.
Qed.

Lemma semi_decider_or {X} {p q : X -> Prop} f g :
  semi_decider f p -> semi_decider g q -> semi_decider (fun x n => orb (f x n) (g x n)) (fun x => p x \/ q x).
Proof.
  intros Hf Hg.
  red in Hf, Hg |- *. intros x.
  rewrite Hf, Hg.
  setoid_rewrite Bool.orb_true_iff.
  clear. firstorder.
Qed.

Lemma semi_decidable_or {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> semi_decidable (fun x => p x \/ q x).
Proof.
  intros [f Hf] [g Hg]. eapply ex_intro, semi_decider_or; eauto.
Qed.

Lemma semi_decidable_ex {X} {p : nat -> X -> Prop} :
  semi_decidable (fun pa => p (fst pa) (snd pa)) -> semi_decidable (fun x => exists n, p n x).
Proof.
  intros [f Hf].
  eapply semi_decidable_projection_iff.
  exists (fun '(n,x) => (fun! ⟨n1,n2⟩ => f (n1, x) n2 = true) n).
  split.
  - eapply dec_decidable. intros (n, x).
    destruct unembed. exact _.
  - intros x. setoid_rewrite (Hf (_, x)).
    split.
    + intros (n1 & n2 & H). exists ⟨n1, n2⟩. now rewrite embedP.
    + intros (n & H). destruct unembed as [n1 n2].
      exists n1, n2. eauto.
Qed.

Lemma co_semi_decider_and {X} {p q : X -> Prop} f g :
  co_semi_decider f p -> co_semi_decider g q -> co_semi_decider (fun x n => orb (f x n) (g x n)) (fun x => p x /\ q x).
Proof.
  intros Hf Hg x. red in Hf, Hg. rewrite Hf, Hg.
  setoid_rewrite Bool.orb_false_iff.
  clear. firstorder.
Qed.

Lemma co_semi_decidable_and {X} {p q : X -> Prop} :
  co_semi_decidable p -> co_semi_decidable q -> co_semi_decidable (fun x => p x /\ q x).
Proof.
  intros [f Hf] [g Hg]. eapply ex_intro, co_semi_decider_and; eauto.
Qed.

Lemma semi_decider_AC X g (R : X -> nat -> Prop) :
  semi_decider g (uncurry R) ->
  (forall x, exists y, R x y) ->
  ∑ f : X -> nat, forall x, R x (f x).
Proof.
  intros Hg Htot'. red in Hg. unfold uncurry in *.
  pose (R' x := fun! ⟨n,m⟩ => g (x,n) m = true).
  assert (Htot : forall x, exists n, R' x n). {
    subst R'. intros x. destruct (Htot' x) as (n & [m H] % (Hg (_, _))).
    exists ⟨n,m⟩. now rewrite embedP.
  }
  assert (Hdec : decider (fun '(x, nm) => let (n, m) := unembed nm in g (x, n) m) (uncurry R')). {
    unfold R'. unfold uncurry. intros (x, nm). destruct (unembed nm) as (n, m).
    destruct g; firstorder congruence.
  }
  eapply (decider_AC _ _ _ Hdec) in Htot as [f' Hf'].
  exists (fun x => (fun! ⟨n, m⟩ => n) (f' x)).
  intros x. subst R'. specialize (Hf' x). cbn in Hf'.
  destruct (unembed (f' x)). eapply (Hg (_, _)). eauto.
Qed.

(* Lemma sdec_commpute_lor {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> (forall x, p x \/ q x) -> exists f : X -> bool, forall x, if f x then p x else q x.
Proof.
  intros [f_p Hp] [f_q Hq] Ho.
  unshelve eexists.
  - refine (fun x => let (n, H) := mu_nat (P := fun n => orb (f_p x n) (f_q x n) = true) (ltac:(cbn; decide equality)) _ in f_p x n).
    destruct (Ho x) as [[n H] % Hp | [n H] % Hq].
    + exists n. now rewrite H.
    + exists n. rewrite H. now destruct f_p.
  - intros x. cbn -[mu_nat]. destruct mu_nat.
    specialize (Hp x). specialize (Hq x).
    destruct (f_p) eqn:E1. eapply Hp. eauto.
    destruct (f_q) eqn:E2. eapply Hq. eauto.
    inversion e.
Qed.

 *)

(* ** Other  *)

Lemma d_semi_decidable_impl {X} {p q : X -> Prop} :
  decidable p -> semi_decidable q -> semi_decidable (fun x => p x -> q x).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => if f x then g x n else true).
  intros x. split.
  - intros H. destruct (reflects_cases (Hf x)) as [ [-> H2] | [-> H2] ].
    + firstorder.
    + now exists 0.
  - intros [n H]. revert H.
    destruct (reflects_cases (Hf x)) as [ [-> H2] | [-> H2]]; intros H.
    + firstorder.
    + firstorder.
Qed.

Lemma d_co_semi_decidable_impl {X} {p q : X -> Prop} :
  decidable p -> semi_decidable (complement q) -> semi_decidable (complement (fun x => p x -> q x)).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => if f x then g x n else false).
  intros x. split.
  - intros H. destruct (reflects_cases (Hf x)) as [ [-> H2] | [-> H2] ].
    + red in H. firstorder.
    + firstorder.
  - intros [n H]. revert H.
    destruct (reflects_cases (Hf x)) as [ [-> H2] | [-> H2]]; intros H.
    + firstorder.
    + firstorder congruence.
Qed.

Lemma co_semi_decidable_impl {X} {p q : X -> Prop} :
  (* (forall x, ~~ p x -> p x) -> *)
  semi_decidable (complement (complement p)) -> decidable q -> semi_decidable (complement (fun x => p x -> q x)).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => if g x then false else f x n).
  intros x. split.
  - intros H. destruct (reflects_cases (Hg x)) as [ [-> H2] | [-> H2] ].
    + firstorder.
    + eapply Hf. firstorder.
  - intros [n H]. revert H.
    destruct (reflects_cases (Hg x)) as [ [-> H2] | [-> H2]]; intros H.
    + congruence.
    + intros ?. firstorder.
Qed.

Lemma semi_decidable_impl {X} {p q : X -> Prop} :
  semi_decidable (complement p) -> decidable q -> semi_decidable (fun x => p x -> q x).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => if g x then true else f x n).
  intros x. split.
  - intros H. destruct (reflects_cases (Hg x)) as [ [-> H2] | [-> H2] ].
    + now exists 0.
    + eapply Hf. firstorder.
  - intros [n H]. revert H.
    destruct (reflects_cases (Hg x)) as [ [-> H2] | [-> H2]]; intros H.
    + eauto.
    + intros. firstorder.
Qed.

Lemma enumerator_semi_decider {X} {p : X -> Prop} d f :
  decider d (eq_on X) -> enumerator f p -> semi_decider (fun x n => if f n is Some y then d (x,y) else false) p.
Proof.
  intros Hd Hf x. red in Hf. rewrite Hf. split.
  - intros [n Hn]. exists n.
    rewrite Hn. now eapply Hd.
  - intros [n Hn]. exists n.
    destruct (f n); inversion Hn.
    eapply Hd in Hn. now subst.
Qed.

Lemma enumerable_semi_decidable {X} {p : X -> Prop} :
  discrete X -> enumerable p -> semi_decidable p.
Proof.
  unfold enumerable, enumerator.
  intros [d Hd] [f Hf].
  eexists. eapply enumerator_semi_decider; eauto.
Qed.

Lemma semi_decider_enumerator {X} {p : X -> Prop} e f : 
  enumeratorᵗ e X -> semi_decider f p -> 
  enumerator (fun! ⟨n,m⟩ => if e n is Some x then if f x m then Some x else None else None) p.
Proof.
  intros He Hf x. rewrite (Hf x). split.
  - intros [n Hn]. destruct (He x) as [m Hm].
    exists (embed (m,n)). now rewrite embedP, Hm, Hn.
  - intros [mn Hmn]. destruct (unembed mn) as (m, n).
    destruct (e m) as [x'|]; try congruence.
    destruct (f x' n) eqn:E; inversion Hmn. subst.
    exists n. exact E.
Qed.

Lemma semi_decidable_enumerable {X} {p : X -> Prop} :
  enumerableᵗ X -> semi_decidable p -> enumerable p.
Proof.
  unfold semi_decidable, semi_decider.
  intros [e He] [f Hf].
  now eapply ex_intro, semi_decider_enumerator.
Qed.
