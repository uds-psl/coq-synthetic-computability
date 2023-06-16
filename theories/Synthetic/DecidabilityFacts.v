Require SyntheticComputability.Shared.Dec.
Require Import Setoid Morphisms.
Require Export SyntheticComputability.Synthetic.Definitions SyntheticComputability.Shared.FinitenessFacts.
From SyntheticComputability.Shared Require Import mu_nat equiv_on.

(** Facts on reflects *)

Lemma reflects_iff (b : bool) P :
  (if b then P else ~ P) <-> reflects b P.
Proof.
  destruct b; firstorder congruence.
Qed.

Lemma reflects_true P :
  reflects true P <-> P.
Proof.
  clear.
  firstorder congruence.
Qed.


Lemma reflects_false P :
  reflects false P <-> ~ P.
Proof. clear.
       firstorder congruence.
Qed.

Lemma reflects_not b P :
  reflects b P -> reflects (negb b) (~P).
Proof.
  unfold reflects.
  destruct b; cbn; intuition congruence.
Qed.

Lemma reflects_conj {b1 b2 P1 P2} :
  reflects b1 P1  -> reflects b2 P2 -> reflects (b1 && b2) (P1 /\ P2).
Proof.
  unfold reflects.
  destruct b1, b2; cbn; firstorder congruence.
Qed.

Lemma reflects_disj {b1 b2 P1 P2} :
  reflects b1 P1  -> reflects b2 P2 -> reflects (b1 || b2) (P1 \/ P2).
Proof.
  unfold reflects.
  destruct b1, b2; cbn; firstorder congruence.
Qed.

Lemma reflects_prv b (P : Prop) : (b = true -> P) -> (b = false -> ~ P) -> reflects b P.
Proof.
  intros H1 H2.
  destruct b; cbn; firstorder.
Qed.

Lemma reflects_prv_iff b (P : Prop) : ((b = true -> P) /\ (b = false -> ~ P)) <-> reflects b P.
Proof.
  split.
  - intros []; now eapply reflects_prv.
  - intros H. split; intros ->.
    + now eapply H.
    + intros H1 % H. congruence.
Qed.

(** * Decidability and Enumerability  *)

(** ** Decidability  *)

(** Proper lemmas *)

#[export] Instance Proper_decider {X} :
  Proper (pointwise_relation X (@eq bool) ==> pointwise_relation X iff ==> iff ) (@decider X).
Proof.
  intros f g H1 p q H2. red in H1, H2.
  unfold decider, reflects. 
  split; intros H x.
  - now rewrite <- H2, H, H1.
  - now rewrite H2, H, H1.
Qed.

#[export] Instance Proper_decidable {X} :
  Proper (pointwise_relation X iff ==> iff) (@decidable X).
Proof.
  intros p q H2.
  split; intros [f H]; exists f.
  - now rewrite <- H2.
  - now rewrite H2.
Qed.

Lemma decider_ext {X} {p q : X -> Prop} {f g} :
  decider f p -> decider g q -> f ≡{X -> bool} g -> p ≡{_} q.
Proof.
  unfold enumerator. cbn.
  intros Hp Hq E x.
  etransitivity. eapply (Hp x). rewrite E. symmetry. eapply Hq.
Qed.

(** Decidable predicates are logically decidable and stable  *)

Lemma decider_decide {X} {f} {p} :
  decider f p -> forall x : X, p x \/ ~ p x.
Proof.
  intros H x. specialize (H x). destruct (f x); firstorder congruence.
Qed.

Lemma decidable_decide {X} {p} :
  decidable p -> forall x : X, p x \/ ~ p x.
Proof.
  intros [f H]. now eapply decider_decide.
Qed.

Lemma decidable_stable {X} (p : X -> Prop) :
  decidable p -> stable p.
Proof.
  intros H x. destruct (decidable_decide H x); tauto.
Qed.

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

(** Closure properties of decidability *)

Lemma decider_complement X {p : X -> Prop} f :
  decider f p -> decider (fun x => negb (f x)) (complement p).
Proof.
  intros H x. eapply reflects_not, H.
Qed.

Lemma decider_conj X p q f g:
  decider f p -> decider g q -> decider (fun x => andb (f x) (g x)) (fun x : X => p x /\ q x).
Proof.
  intros Hf Hg x. eapply reflects_conj; eauto.
Qed.

Lemma decider_disj X p q f g:
  decider f p -> decider g q -> decider (fun x => orb (f x) (g x)) (fun x : X => p x \/ q x).
Proof.
  intros Hf Hg x. eapply reflects_disj; eauto.
Qed.

Lemma decidable_complement X {p : X -> Prop} :
  decidable p -> decidable (complement p).
Proof.
  intros [f H]. eapply ex_intro, decider_complement, H.
Qed.

Lemma decidable_conj X p q :
  decidable p -> decidable q -> decidable (fun x : X => p x /\ q x).
Proof.
  intros [f Hf] [g Hg]. eapply ex_intro, decider_conj; eauto.
Qed.

Lemma decidable_disj X p q :
  decidable p -> decidable q -> decidable (fun x : X => p x \/ q x).
Proof.
  intros [f Hf] [g Hg]. eapply ex_intro, decider_disj; eauto.
Qed.

Lemma decider_AC X f (R : X -> nat -> Prop) :
  decider f (uncurry R) ->
  (forall x, exists y, R x y) ->
  ∑ f : X -> nat, forall x, R x (f x).
Proof.
  intros Hf Htot.
  assert (H : forall x, exists n, f (x, n) = true).  { intros x. destruct (Htot x) as [y]. exists y. now eapply Hf. }
  eexists (fun x => proj1_sig (mu_nat _ (H x))).
  intros x. destruct mu_nat as [n Hn]; cbn.
  eapply (Hf (x, n)), Hn.
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

Lemma decider_eq_bool : decider (fun '(x,y) => Bool.eqb x y) (eq_on bool).
Proof.
  intros (x,y). red. now rewrite Bool.eqb_true_iff.
Qed.

Lemma decider_eq_nat : decider (fun '(x,y) => Nat.eqb x y) (eq_on nat).
Proof.
  intros (x,y). red. now rewrite PeanoNat.Nat.eqb_eq.
Qed.

Lemma decider_eq_prod X Y f g : decider f (eq_on X) -> decider g (eq_on Y) -> decider (fun '((x1,y1),(x2,y2)) => andb (f (x1, x2)) (g (y1,y2))) (eq_on (X * Y)).
Proof.
  intros Hf Hg. intros ((x1,y1),(x2,y2)). red.
  rewrite Bool.andb_true_iff.
  specialize (Hf (x1, x2)). specialize (Hg (y1, y2)).
  red in Hf, Hg. rewrite <- Hf, <- Hg.
  firstorder congruence.
Qed.

Lemma decider_eq_sum X Y f g : decider f (eq_on X) -> decider g (eq_on Y) -> decider (fun i => match i with (inl x1, inl x2) => f (x1, x2) 
                                                                                                  | (inr y1, inr y2) => g (y1, y2)
                                                                                                  | _ => false
                                                                                          end) (eq_on (X + Y)).
Proof.
  intros Hf Hg ([x1 | y1], [x2 | y2]); red. 2, 3: now firstorder congruence.
  - specialize (Hf (x1, x2)). red in Hf. rewrite <- Hf. clear. firstorder congruence.
  - specialize (Hg (y1, y2)). red in Hg. rewrite <- Hg. clear. firstorder congruence.
Qed.

Lemma decider_eq_option X f : decider f (eq_on X) -> decider (fun i => match i with (Some x1, Some x2) => f (x1, x2) | (None, None) => true | _ => false end) (eq_on (option X)).
Proof.
  intros Hf ([x1 | ], [x2 | ]); red. 2,3,4: now firstorder congruence.
  specialize (Hf (x1, x2)). red in Hf. rewrite <- Hf. clear. firstorder congruence.
Qed.

Fixpoint eqb_list {X} (f : X * X -> bool) (l1 : list X) (l2 : list X) :=
  match l1, l2 with
  | nil, nil => true
  | List.cons x1 l1, List.cons x2 l2 => andb (f (x1,x2)) (eqb_list f l1 l2)
  | _, _ => false
  end.

Lemma decider_eq_list X f : decider f (eq_on X) -> decider (fun '(l1,l2) => eqb_list f l1 l2) (eq_on (list X)).
Proof.
  intros Hf (l1, l2). induction l1 as [ | x1 l1 IH] in l2 |- *; cbn; red.
  - clear. destruct l2; firstorder congruence.
  - destruct l2 as [ | x2 l2]. 1: now firstorder congruence.
    specialize (Hf (x1, x2)). red in Hf. specialize (IH l2). red in IH.
    rewrite Bool.andb_true_iff, <- Hf, <- IH. firstorder congruence.
Qed.


Lemma discrete_bool : discrete bool.
Proof.
  eapply ex_intro, decider_eq_bool.
Qed.

Lemma discrete_nat : discrete nat.
Proof.
  eapply ex_intro, decider_eq_nat.
Qed.

Lemma discrete_prod X Y : discrete X -> discrete Y -> discrete (X * Y).
Proof.
  intros [f Hf] [g Hg]. eapply ex_intro, decider_eq_prod; eauto.
Qed.

Lemma discrete_sum X Y : discrete X -> discrete Y -> discrete (X + Y).
Proof.
  intros [f Hf] [g Hg]. eapply ex_intro, decider_eq_sum; eauto.
Qed.

Lemma discrete_option X : discrete X -> discrete (option X).
Proof.
   intros [f Hf]. eapply ex_intro, decider_eq_option, Hf.
Qed.

Lemma discrete_list X : discrete X -> discrete (list X).
Proof.
  intros [f Hf]. eapply ex_intro, decider_eq_list, Hf.
Qed.

Section fix_X.
Context {X : Type}.
Variable f : X * X -> bool.

Fixpoint inb x l :=
  match l with
  | nil => false
  | cons x' l => orb (f (x, x')) (inb x l)
  end.
End fix_X.

Theorem inb_spec X f : decider f (eq_on X) -> decider (uncurry (inb f)) (uncurry (@List.In X)).
Proof.
  intros Hf. unfold uncurry. intros (x, l). red.
  induction l as [ | x' l IH]; cbn.
  - clear. firstorder congruence.
  - rewrite IH. specialize (Hf (x, x')). red in Hf.
    rewrite Bool.orb_true_iff, <- Hf.
    clear. destruct inb; firstorder congruence.
Qed.

Lemma lists_decider {X} d l p : 
  decider d (eq_on X) ->
  lists l p -> decider (fun x => inb d x l) p.
Proof.
  intros Hd Hl x. red. 
  rewrite (Hl _). eapply (inb_spec _ _ Hd (_, _)).
Qed.

Lemma listable_decidable {X} (p : X -> Prop) :
  discrete X ->
  listable p -> decidable p.
Proof.
  intros [d Hd] [l H]. eapply ex_intro, lists_decider; eauto.
Qed.
