From Undecidability.Synthetic Require Import DecidabilityFacts.
From Undecidability.Shared Require Export embed_nat equiv_on partial mu_nat.
Require Import List Morphisms Lia.
Export EmbedNatNotations.

(** ** Enumerability  *)

Instance Proper_enumerator {X} :
  Proper (@equiv_rel _ (equiv_ran) ==> pointwise_relation X iff ==> iff ) (@enumerator X).
Proof.
  intros f g H1 p q H2. red in H1, H2.
  unfold enumerator, reflects. 
  split; intros H x; cbn in H1.
  - now rewrite <- H2, H, H1.
  - now rewrite H2, H, H1.
Qed.

Instance Proper_enumerable {X} :
  Proper (pointwise_relation X iff ==> iff) (@enumerable X).
Proof.
  intros p q H2.
  split; intros [f H]; exists f.
  - now rewrite <- H2.
  - now rewrite H2.
Qed.

Lemma enumerator_ext {X} {p q : X -> Prop} {f g} :
  enumerator f p -> enumerator g q -> f ≡{ran} g -> p ≡{_} q.
Proof.
  unfold enumerator. cbn.
  intros Hp Hq E x.
  now rewrite Hp, E, Hq.
Qed. 

Definition enumeratorᵗ' X f := forall x : X, exists n : nat, f n = Some x.
Notation enumeratorᵗ f X := (enumeratorᵗ' X f).
Definition enumerableᵗ X := exists f : nat -> option X, enumeratorᵗ f X.

Lemma decider_enumerator {X} {p : X -> Prop} f e :
  decider f p -> enumeratorᵗ e X -> enumerator (fun n => if e n is Some x then if f x then Some x else None else None) p.
Proof.
  intros Hf He x. specialize (Hf x).
  red in Hf. rewrite Hf.
  split.
  - destruct (He x) as [n Hn].
    intros H. exists n. now rewrite Hn, H.
  - intros [n H]. destruct (e n) as [x' | ] eqn:E; [ | now inversion H].
    now destruct (f x') eqn:E2; inversion H; subst; clear H.
Qed.

Theorem decidable_enumerable {X} {p : X -> Prop} :
  decidable p -> enumerableᵗ X -> enumerable p.
Proof.
  intros [f Hf] [e He]. eapply ex_intro, decider_enumerator; eauto.
Qed.

Theorem decidable_enumerable_complement X (p : X -> Prop) :
  decidable p -> enumerableᵗ X -> enumerable (fun x => ~ p x).
Proof.
  intros ? % decidable_complement ?. eapply decidable_enumerable; eauto.
Qed.

Lemma enumerator_conj X (p q : X -> Prop) d f g :
  decider d (eq_on X) -> enumerator f p -> enumerator g q -> enumerator (fun! ⟨n,m⟩ => if (f n, g m) is (Some x, Some y) then if d (x,y) then Some x else None else None) (fun x => p x /\ q x).
Proof.
  intros Hd Hf Hg x.
  rewrite (Hf x), (Hg x). split.
  - intros [[n H1] [m H2]]. exists ⟨n,m⟩. rewrite embedP, H1, H2.
    specialize (Hd (x,x)). red in Hd. destruct (d (x,x)); firstorder congruence.
  - intros [nm H]. destruct (unembed nm) as [n m], (f n) as [x' | ] eqn:Ef, (g m) as [y | ] eqn:Eg; [ | congruence.. ].
    specialize (Hd (x', y)). destruct (d (x', y)); inversion H; subst.
    assert (x = y) as -> by now eapply Hd. eauto.
Qed.

Lemma enumerator_disj X (p q : X -> Prop) f g :
  enumerator f p -> enumerator g q -> enumerator (fun! ⟨n,m⟩ => if n then f m else g m) (fun x => p x \/ q x).
Proof.
  intros Hf Hg x.
  rewrite (Hf x), (Hg x). split.
  - intros [[n H1] | [n H1]].
    + exists ⟨0,n⟩. now rewrite embedP, H1. 
    + exists ⟨1,n⟩. now rewrite embedP, H1.
  - intros [nm H]. destruct (unembed nm) as [[ | _] m]; eauto.
Qed.

Lemma enumerable_conj X (p q : X -> Prop) :
  discrete X -> enumerable p -> enumerable q -> enumerable (fun x => p x /\ q x).
Proof.
  intros [] [] []. eapply ex_intro, enumerator_conj; eauto.
Qed.

Lemma enumerable_disj X (p q : X -> Prop) :
  enumerable p -> enumerable q -> enumerable (fun x => p x \/ q x).
Proof.
  intros [] []. eapply ex_intro, enumerator_disj; eauto.
Qed.

Lemma enumerator_projection1 X Y (p : X * Y -> Prop) f :
  enumerator f p -> enumerator (fun n => match f n with Some (x, y) => Some x | None => None end) (fun x => exists y, p (x,y)).
Proof.
  intros; split.
  - intros [y ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
  - intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inversion H0; subst.
    exists y. eapply H. eauto.
Qed.

Lemma enumerable_projection1 X Y (p : X * Y -> Prop) :
  enumerable p -> enumerable (fun x => exists y, p (x,y)).
Proof.
  intros [f H]. eapply ex_intro, enumerator_projection1, H.
Qed.

Lemma enumerator_projection2 X Y (p : X * Y -> Prop) f :
  enumerator f p -> enumerator (fun n => match f n with Some (x, y) => Some y | None => None end) (fun y => exists x, p (x,y)).
Proof.
  intros; split.
  - intros [y ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
  - intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inversion H0; subst.
    eexists. eapply H. eauto.
Qed.

Lemma enumerable_projection2 X Y (p : X * Y -> Prop) :
  enumerable p -> enumerable (fun y => exists x, p (x,y)).
Proof.
  intros [f H]. eapply ex_intro, enumerator_projection2, H.
Qed.

Definition strong_enumerator {X} (f : nat -> X) (P : X -> Prop) : Prop :=
  forall x, P x <-> exists n, f n = x.

Definition strongly_enumerable {X} (P : X -> Prop) : Prop :=
  exists f : nat -> X, strong_enumerator f P.

Lemma enumerator_strong_enumerator {X} (p : X -> Prop) f x0 :
  p x0 -> enumerator f p -> strong_enumerator (fun n => if f n is Some x then x else x0) p.
Proof.
  intros H0 Hf x. eapply Hf in H0 as [n0 H0]. specialize (Hf x) as ->.
  split; intros [n Hn].
  - exists n. now rewrite Hn.
  - destruct (f n) eqn:E; subst; eauto.
Qed.

Lemma strong_enumerator_enumerator {X} (p : X -> Prop) f :
  strong_enumerator f p -> enumerator (fun n => Some (f n)) p.
Proof.
  intros Hf x. specialize (Hf x) as ->.
  split; intros [n Hn]; exists n; congruence.
Qed.

Lemma enumerable_strongly_enumerable_iff {X} p:
  (enumerable p /\ exists x : X, p x) <-> strongly_enumerable p.
Proof.
  split.
  - intros [[f Hf] [x0 H0]]. eapply ex_intro, enumerator_strong_enumerator; eauto.
  - intros [f Hf]. split.
    + eapply ex_intro, strong_enumerator_enumerator, Hf.
    + exists (f 0). eapply Hf. eauto.
Qed.

Definition parametric_enumerator {X Y} (f : X -> nat -> option Y) (p : X -> Y -> Prop) :=
  forall x y, p x y <-> exists n, f x n = Some y.

Definition penumerable {X Y} (p : X -> Y -> Prop) :=
  exists f, parametric_enumerator f p.

Lemma penumerator_enumerator {X Y} f g (p : X -> Y -> Prop) :
  parametric_enumerator f p -> enumeratorᵗ g X ->
  enumerator (fun! ⟨n,m⟩ => if g n is Some x then if f x m is Some y then Some (x,y) else None else None) (uncurry p).
Proof.
  intros Hf Hg. intros (x,y). cbn.
  rewrite (Hf x y). split.
  - intros [m Hm]. destruct (Hg x) as [n Hn].
    exists ⟨n,m⟩. now rewrite embedP, Hn, Hm.
  - intros [nm H]. destruct (unembed nm) as [n m].
    destruct (g n) as [x' | ]; try congruence.
    destruct f as [y' | ] eqn:E; inversion H; subst.
    eauto.
Qed.

Lemma enumerator_penumerator {X Y} f g (p : X -> Y -> Prop) :
  enumerator f (uncurry p) -> decider g (eq_on X) ->
  parametric_enumerator (fun x n => if f n is Some (x', y) then if g (x, x') then Some y else None else None) p.
Proof.
  intros Hf Hg. intros x y.
  rewrite (Hf (x,y)). split.
  - intros [n Hn]. exists n. rewrite Hn.
    now specialize (Hg (x,x)) as [-> _].
  - intros [n H]. destruct (f n) as [(x',y') | ] eqn:E; try congruence.
    specialize (Hg (x,x')). destruct g; inversion H; subst.
    destruct Hg. rewrite H1 in *; eauto.
Qed.

Lemma penumerable_iff {X Y} (p : X -> Y -> Prop) :
  enumerableᵗ X -> discrete X ->
  penumerable p <-> enumerable (uncurry p).
Proof.
  intros [g1 Hg1] [g2 Hg2]. split.
  - intros [f Hf]. eexists. eapply penumerator_enumerator; eauto.
  - intros [f Hf]. eexists. eapply enumerator_penumerator; eauto.
Qed.

Lemma inspect_opt {X} (o : option X) :
  {x | o = Some x} + {o = None}.
Proof.
  destruct o; eauto.
Qed.

Lemma enumerable_part_iff {X} (p : X -> Prop) {Part : partiality}:
  enumerable p <-> exists f : nat -> part X, forall x, p x <-> exists n, f n =! x.
Proof.
  split.
  - intros [f Hf]. exists (fun n => if f n is Some x then ret x else undef).
    intros x. specialize (Hf x) as ->.
    split; intros [n H]; exists n; destruct (f n).
    + eapply ret_hasvalue'. congruence.
    + congruence.
    + eapply ret_hasvalue_inv in H; try congruence.
    + now eapply undef_hasvalue in H.
  - intros [f Hf]. exists (fun! ⟨n,m⟩ => seval (f n) m). 
    intros x. specialize (Hf x) as ->. split.
    + intros [n H]. eapply seval_hasvalue in H as [m H].
      exists ⟨n, m⟩. now rewrite embedP.
    + intros [nm H]. destruct (unembed nm) as [n m].
      eexists. eapply seval_hasvalue. eauto.
Qed.

Lemma enumerator_graph {X} {Y} e :
  enumeratorᵗ e X ->
  forall f : X -> Y, enumerator (fun n => if e n is Some x then Some (x, f x) else None) (fun p => exists x, p = ( x, f x )).
Proof.
  intros He f y. split.
  - intros [x ->]. specialize (He x) as [n Hn]. exists n.
    now rewrite Hn.
  - intros [n Hn].
    destruct (e n); inversion Hn. eauto.
Qed.

Lemma enumerable_graph {X} {Y} (f : X -> Y) :
  enumerableᵗ X ->
  enumerable (fun p => exists x, p = ( x, f x )).
Proof.
  intros [e He]. eexists. eapply enumerator_graph; eauto.
Qed.

Lemma enumerable_graph_part {Part : partiality} {X} {Y} (f : X -> part Y) :
  enumerableᵗ X ->
  enumerable (fun (x : X * Y) => hasvalue (f (fst x)) (snd x)).
Proof.
  intros [e He].
  exists (fun! ⟨n, m⟩ => if e n is Some x then if seval (f x) m is Some y then Some (x, y) else None else None).
  intros (x,y). split; cbn.
  - intros [n Hn] % seval_hasvalue.
    destruct (He x) as [m Hm].
    exists ⟨m, n⟩. now rewrite embedP, Hm, Hn.
  - intros [mn H]. destruct (unembed mn) as [m n].
    destruct (e m) as [x' | ] eqn:E; try congruence.
    destruct seval eqn:E'; inversion H; subst.
    eapply seval_hasvalue. 
    eauto.
Qed.

Lemma enumerator_AC X Y e d (R : X -> Y -> Prop) :
  decider d (eq_on X) ->
  enumerator e (uncurry R) ->
  (forall x, exists y, R x y) ->
  ∑ f : X -> Y, forall x, R x (f x).
Proof.
  intros Hd He Htot'. red in He. unfold uncurry in *.
  pose (R' x n := exists y, e n = Some (x, y)).
  assert (Htot : forall x, exists m, R' x m). {
    unfold R'. intros x. destruct (Htot' x) as (y & [n H] % (He (_, _))). eauto.
  } clear Htot'.
  assert (Hdec : decider (fun '(x,m) => if e m is Some (x',_) then d (x',x) else false) (uncurry R')). {
    unfold R'. intros (x, m). unfold uncurry, reflects. destruct (e m) as [(x', y) | ].
    - specialize (Hd (x', x)). red in Hd. rewrite <- Hd. clear. firstorder (subst; eauto; congruence).
    - clear. now firstorder; congruence. 
  }
  eapply (decider_AC _ _ _ Hdec) in Htot as [g Hg].
  subst R'. unshelve eexists (fun x => match inspect_opt (e (g x)) with
                      | inleft (exist _ (x', y) _) => y
                      | inright E => _
                      end).
  - exfalso. destruct (Hg x) as [y H]. congruence.
  - cbn. intros x. pose proof (Hg x) as H. cbn in H. eapply (He (_, _)). exists (g x).
    destruct (inspect_opt (e (g x))) as [[(x',y) E']| E'];
    rewrite? E' in *. destruct H as [? [= <- <-]]. congruence. destruct H as [? [=]].
Qed.

Lemma mu_enumerable {X} {p : nat -> X -> Prop} :
  discrete X ->
  enumerable (uncurry p) ->
  inhabited (forall n, (exists x, p n x) -> ∑ x, p n x).
Proof.
  intros [D] % discrete_iff [e He].
  econstructor.
  intros n Hn.
  enough (∑ m, exists x, e m = Some (n,x)) as (m & Hx). {
    destruct (e m) as [(n', x) | ] eqn:E.
    * exists x. eapply (He (_, _)). destruct Hx as (? & [= -> ->]). eauto.
    * exfalso. destruct Hx. congruence.
  }
  eapply mu_nat_dep.
  - intros m. destruct (e m) as [[] | ].
    + destruct (PeanoNat.Nat.eq_dec n n0). subst. eauto.
      right. intros (? & [= -> ->]). congruence.
    + right. clear. firstorder congruence.
  - destruct Hn as (x & [m H] % (He (_ , _ ))). eauto.
Qed.

(** *** Enumerable types  *)

(** # <a id="enumerator_enumerator__T" /> #*)
Lemma enumerator_enumeratorᵗ X f :
  enumerator f (fun _ : X => True) <-> enumeratorᵗ f X.
Proof.
  split; intros Hf x.
  - destruct (Hf x) as [[n H] _]; eauto.
  - destruct (Hf x) as [n H]; firstorder.
Qed.

(** # <a id="enumerable_enumerable__T" /> #*)
Lemma enumerable_enumerableᵗ X :
  enumerable (fun _ : X => True) <-> enumerableᵗ X.
Proof.
  split; intros [f Hf]; eapply ex_intro, enumerator_enumeratorᵗ, Hf.
Qed.

Definition nat_enum (n : nat) := Some n.
(** # <a id="enumerator__T_nat" /> #*)
Lemma enumeratorᵗ_nat :
  enumeratorᵗ nat_enum nat.
Proof.
  intros n. cbv. eauto.
Qed.

Definition unit_enum (n : nat) := Some tt.
(** # <a id="enumerator__T_unit" /> #*)
Lemma enumeratorᵗ_unit :
  enumeratorᵗ unit_enum unit.
Proof.
  intros []. cbv. now exists 0.
Qed. 

Definition bool_enum (n : nat) := Some (if n is 0 then true else false).
(** # <a id="enumerator__T_bool" /> #*)
Lemma enumeratorᵗ_bool :
  enumeratorᵗ bool_enum bool.
Proof.
  intros []. cbv.
  - now exists 0.
  - now exists 1.
Qed.

(** # <a id="enumerable__T_nat" /> #*)
Lemma enumerableᵗ_nat : enumerableᵗ nat.
Proof.
  eexists. eapply enumeratorᵗ_nat.
Qed.

(** # <a id="enumerable__T_bool" /> #*)
Lemma enumerableᵗ_bool : enumerableᵗ bool.
Proof.
  eexists. eapply enumeratorᵗ_bool.
Qed.

(** # <a id="enumerable__T_unit" /> #*)
Lemma enumerableᵗ_unit : enumerableᵗ unit.
Proof.
  eexists. eapply enumeratorᵗ_unit.
Qed.

Definition prod_enum {X Y} (f1 : nat -> option X) (f2 : nat -> option Y) : nat -> option (X * Y) :=
  fun! ⟨n, m⟩ => if (f1 n, f2 m) is (Some x, Some y) then Some (x, y) else None.
(** # <a id="enumerator__T_prod" /> #*)
Lemma enumeratorᵗ_prod {X Y} f1 f2 :
  enumeratorᵗ f1 X -> enumeratorᵗ f2 Y ->
  enumeratorᵗ (prod_enum f1 f2) (X * Y).
Proof.
  intros H1 H2 (x, y).
  destruct (H1 x) as [n1 Hn1], (H2 y) as [n2 Hn2].
  exists (embed (n1, n2)). unfold prod_enum.
  now rewrite embedP, Hn1, Hn2.
Qed.

(** # <a id="enumerable__T_prod" /> #*)
Lemma enumerableᵗ_prod {X Y} :
  enumerableᵗ X -> enumerableᵗ Y -> enumerableᵗ (X * Y).
Proof.
  intros [] []. eexists. now eapply enumeratorᵗ_prod.
Qed.

Definition dep_prod_enum {X} {Y : X -> Type} (f1 : nat -> option X) (f2 : forall x, nat -> option (Y x)) : nat -> option ({x : X & Y x}) :=
  fun! ⟨n, m⟩ => if f1 n is Some x then if f2 x m is Some y then Some (existT x y) else None else None.
Lemma enumeratorᵗ_dep_prod {X Y} f1 f2 :
  enumeratorᵗ f1 X -> (forall x, enumeratorᵗ (f2 x) (Y x)) ->
  enumeratorᵗ (dep_prod_enum f1 f2) {x : X & Y x}.
Proof.
  intros H1 H2 (x, y).
  destruct (H1 x) as [n1 Hn1], (H2 x y) as [n2 Hn2].
  exists (embed (n1, n2)). unfold dep_prod_enum.
  now rewrite embedP, Hn1, Hn2.
Qed.

Definition Sigma_enum {X} {Y : X -> Prop} (f1 : nat -> option X) (f2 : forall x, nat -> option (Y x)) : nat -> option ({x : X | Y x}) :=
  fun! ⟨n, m⟩ => if f1 n is Some x then if f2 x m is Some y then Some (exist _ x y) else None else None.
(** # <a id="enumerator__T_Sigma" /> #*)
Lemma enumeratorᵗ_Sigma {X} (Y : X -> Prop) f1 f2 :
  enumeratorᵗ f1 X -> (forall x, enumeratorᵗ (f2 x) (Y x)) ->
  enumeratorᵗ (Sigma_enum f1 f2) {x : X | Y x}.
Proof.
  intros H1 H2 (x, y).
  destruct (H1 x) as [n1 Hn1], (H2 x y) as [n2 Hn2].
  exists (embed (n1, n2)). unfold Sigma_enum.
  now rewrite embedP, Hn1, Hn2.
Qed.

Definition option_enum {X} (f : nat -> option X) n :=
  match n with 0 => Some None | S n => Some (f n) end.
(** # <a id="enumerator__T_option" /> #*)
Lemma enumeratorᵗ_option {X} f :
  enumeratorᵗ f X -> enumeratorᵗ (option_enum f) (option X).
Proof.
  intros H [x | ].
  - destruct (H x) as [n Hn]. exists (S n). cbn. now rewrite Hn.
  - exists 0. reflexivity.
Qed.

(** # <a id="enumerable__T_option" /> #*)
Lemma enumerableᵗ_option {X} :
  enumerableᵗ X -> enumerableᵗ (option X).
Proof.
  intros []. eexists. now eapply enumeratorᵗ_option.
Qed.

Definition sum_enum {X Y} (f1 : nat -> option X) (f2 : nat -> option Y) : nat -> option (X + Y) :=
  fun! ⟨n, m⟩ => if n is 0 then if f1 m is Some x then Some (inl x) else None else if f2 m is Some y then Some (inr y) else None.
(** # <a id="enumerator__T_sum" /> #*)
Lemma enumeratorᵗ_sum {X Y} f1 f2 :
  enumeratorᵗ f1 X -> enumeratorᵗ f2 Y ->
  enumeratorᵗ (sum_enum f1 f2) (X + Y).
Proof.
  intros H1 H2.
  intros [x | y].
  - destruct (H1 x) as [n Hn].
    exists ⟨0, n⟩. unfold sum_enum. now rewrite embedP, Hn.
  - destruct (H2 y) as [n Hn].
    exists ⟨1, n⟩. unfold sum_enum. now rewrite embedP, Hn.
Qed.

(** # <a id="enumerable__T_sum" /> #*)
Lemma enumerableᵗ_sum {X Y} :
  enumerableᵗ X -> enumerableᵗ Y -> enumerableᵗ (X + Y).
Proof.
  intros [] []. eexists. now eapply enumeratorᵗ_sum.
Qed.

Definition retraction' {X} {Y} (I : X -> Y) R := forall x : X, R (I x) = Some x.
Notation retraction I R X Y := (@retraction' X Y I R).

Definition retract X Y := exists I R, retraction I R X Y.
Definition datatype X := retract X nat.

Lemma enumerator_retraction X d e :
  decider d (eq_on X) -> enumeratorᵗ e X -> {I | retraction I e X nat}.
Proof.
  intros Hd He. unshelve eexists (fun x => proj1_sig (mu_nat (fun n => if e n is Some y then d (x, y) else false) _)).
  - abstract (destruct (He x) as [n Hn]; exists n; rewrite Hn; now eapply Hd).
  - intros x.
    destruct mu_nat as [n (H1 & Hn & H2)]; cbn.
    destruct (e n); inversion Hn.
    now eapply Hd in Hn; subst.
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

Definition retraction_tight {X} {Y} (I : X -> Y) R := forall x : X, R (I x) = Some x /\ forall y, R y = Some x -> I x = y.

From Undecidability Require Import Dec.

Lemma retraction_to_tight {X} {Y} (I : X -> Y) R (HY : eq_dec Y) :
  retraction' I R ->
  exists R',
  retraction_tight I R'.
Proof.
  exists (fun y => if R y is Some x then if Dec (y = I x) then Some x else None else None).
  intros x. rewrite H.  destruct Dec; try congruence. split.
  - reflexivity.
  - intros y. destruct (R y). destruct Dec.
    all: now intros [= ->].
Qed.

Lemma datatype_retract X :
  discrete X /\ enumerableᵗ X <-> exists I R, @retraction_tight X nat I R.
Proof.
  split.
  intros [Hd He].
  - edestruct enumerable_discrete_datatype as (I & R & H); eauto.
    exists I. eapply retraction_to_tight in H as [R' H]; eauto.
  - intros (I & R & H).
    split.
    + eapply datatype_discrete; firstorder.
    + eapply datatype_enumerable; firstorder.
Qed.

(** Type classes *)

Existing Class enumeratorᵗ'.
(* Existing Class enumerableᵗ. *)

Lemma enumerator_enumerable {X} {f} :
  enumeratorᵗ f X -> enumerableᵗ X.
Proof.
  intros H. exists f. eapply H.
Qed.
Hint Resolve enumerator_enumerable : core.

Existing Instance enumeratorᵗ_prod.
Existing Instance enumeratorᵗ_option.
Existing Instance enumeratorᵗ_bool.
Existing Instance enumeratorᵗ_nat.

Lemma enumerable_graph' (f : nat -> nat) :
  enumerable (fun p => exists x, p = ⟨ x, f x ⟩).
Proof.
  destruct (enumerable_graph f) as [e He].
  - eauto.
  - exists (fun n => if e n is Some (x, y) then Some ⟨ x, y ⟩ else None).
    intros xy.
    split.
    + intros [x ->].
      destruct (He (x, f x)) as [[n] _]; eauto.
      exists n. rewrite H. eauto.
    + intros [n H].
      destruct (e n) as [ [x fx] | ] eqn:E; inversion H; subst.
      destruct (He (x, fx)) as [_ []].
      * eauto.
      * exists x. inversion H0. subst. eauto.
Qed.
(* 
Require Import Undecidability.Shared.Dec Undecidability.Shared.Pigeonhole.

Section dedekind_infinite.

  Variable X : Type.
  Variable E : eq_dec X.
  Variable p : X -> Prop.

  Variables (e : _ ) (He : enumerator e p).

  Variable G : generative p.

  Definition nxt' l : {n | least (fun n => exists x, e n = Some x /\ ~ In x l) 0 n}.
  Proof.
    eapply mu_nat_dep_least.
    - intros n. destruct (e n) as [x | ]. 
      + decide (In x l); firstorder congruence.
      + firstorder congruence.
    - destruct (G l) as (x & [n H1] % He & H2). eauto.
  Qed.

  Definition nxt (l : list X) : X.
  Proof.
    destruct (nxt' l) as (n & H1 & H2 & H3).
    destruct (e n) as [x | ].
    + exact x.
    + abstract (exfalso; firstorder congruence).
  Defined.

  Definition F : nat -> X := fun n => nxt (generate nxt n).

  Lemma F_in x  n : In x (generate nxt n) -> exists n, F n = x.
  Proof.
    induction n.
    - inversion 1.
    - cbn. intros [ | [<- | ]] % in_app_iff; eauto.
  Qed.

  Lemma F_inn n x  : e n = Some x -> In x (generate nxt (S n)).
  Proof.
    revert x. induction n as [n IH] using Wf_nat.lt_wf_ind.
    intros x H. cbn. eapply in_app_iff.
    decide (In x (generate nxt n)); eauto. 
    right. left. unfold nxt at 1.
    destruct nxt' as (n' & H1 & H2 & H3). cbn -[generate] in *.
    destruct (e n') as [x' | ] eqn:Eq.
    2: exfalso; firstorder congruence.
    destruct H2 as (? & [= <-] & H2).
    assert (n' <= n). { eapply H3; try split; eauto. lia. }
    assert (n' = n \/ n' < n) as [-> | ] by lia; try congruence.
    exfalso. eapply H2.
    eapply generative_is_prefix; eauto.
  Qed.

  Lemma F_spec x : p x <-> exists n, F n = x.
  Proof.
    split.
    - intros [n H] % He. eapply F_in, F_inn, H.
    - intros [n <-]. unfold F, nxt. destruct nxt' as (n' & H1 & H2 & H3). cbn in *.
      destruct (e n') as [x' | ] eqn:Eq. 2:exfalso; firstorder congruence.
      eapply He. eauto.      
  Qed.

  Lemma F_nel n :
    ~ In (F n) (generate nxt n).
  Proof.

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

  Lemma injective_F n1 n2 : F n1 = F n2 -> n1 = n2.
  Proof.
    unfold F. unfold nxt at 1 3.
    destruct nxt' as (n & H1 & H2 & H3) eqn:E1. cbn in *.
    destruct (nxt' (generate nxt n2)) as (n' & H1' & H2' & H3') eqn:E2. cbn in *.
    eapply (f_equal proj1_sig) in E1. eapply (f_equal proj1_sig) in E2. cbn in *. 
    destruct (e n) as [x | ]. 2: exfalso; firstorder congruence.
    destruct (e n') as [x' | ]. 2: exfalso; firstorder congruence.
    destruct H2 as (? & [= <-] & H2). destruct H2' as (? & [= <-] & H2').
    intros <-.
    assert (n1 < n2 \/ n1 = n2 \/ n2 < n1) as [Hl | [Hl | Hl]] by lia; eauto; exfalso.
    -


  



End dedekind_infinite.
 *)
