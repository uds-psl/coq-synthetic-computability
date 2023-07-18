From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts MoreEnumerabilityFacts reductions.
From SyntheticComputability.Shared Require Import ListAutomation.
Require Import List Lia.
Import ListNotations ListAutomationNotations.

Set Implicit Arguments.

(** ** Definitions *)

(** ** Pre-order properties *)

(** BEGIN LEGACY CODE FOR LIBRARY  *)

Section Properties.

  Variables (X : Type) (P : X -> Prop)
            (Y : Type) (Q : Y -> Prop)
            (Z : Type) (R : Z -> Prop).

  Fact reduces_reflexive : P ⪯ P.
  Proof. exists (fun x => x); red; tauto. Qed.

  Fact reduces_transitive : P ⪯ Q -> Q ⪯ R -> P ⪯ R.
  Proof.
    unfold reduces, reduction.
    intros (f & Hf) (g & Hg).
    exists (fun x => g (f x)).
    intro; rewrite Hf, Hg; tauto.
  Qed.

  (* ** An equivalent dependent definition *)

  Fact reduces_dependent :
    P ⪯ Q <-> inhabited (forall x, { y | P x <-> Q y }).
  Proof.
    constructor.
    - intros [f Hf]. constructor. intros x. now exists (f x).
    - intros [f]. exists (fun x => proj1_sig (f x)).
      intros x. exact (proj2_sig (f x)).
  Qed.

End Properties.

(*Module ReductionChainNotations.

 (* DLW: Thx to M. Wuttke for the tip, see coq-club ML *)

Ltac redchain2Prop_rec xs :=
  lazymatch xs with
  | pair ?x (pair ?y ?xs) =>
    let z := redchain2Prop_rec (pair y xs) in
    constr:(x ⪯ y /\ z)
  | pair ?x ?y => constr:(x ⪯ y)
  end.

Ltac redchain2Prop xs :=
  let z := redchain2Prop_rec xs 
  in  exact z.

Declare Scope reduction_chain.
Delimit Scope reduction_chain with redchain_scope.
Notation "x '⪯ₘ' y" := (pair x y) (at level 80, right associativity, only parsing) : reduction_chain.
Notation "'⎩' xs '⎭'" := (ltac:(redchain2Prop (xs % redchain_scope))) (only parsing).
 *)
(** END LEGACY  *)

Lemma red_comp X (p : X -> Prop) Y (q : Y -> Prop) :
  p ⪯ q -> (fun x => ~ p x) ⪯ (fun y => ~ q y).
Proof.
  intros [f]. exists f. intros x. red in H. now rewrite H.
Qed.

Section enum_red.

  Variables (X Y : Type) (p : X -> Prop) (q : Y -> Prop).
  Variables (f : X -> Y) (Hf : forall x, p x <-> q (f x)).

  Variables (Lq : _) (qe : list_enumerator Lq q).

  Variables (x0 : X).
  
  Variables (d : eq_dec Y).
  
  Local Fixpoint L L' n :=
    match n with
    | 0 => []
    | S n => L L' n ++ [ x | x ∈ cumul L' n , In (f x) (cumul Lq n) ]
    end.

  Lemma enum_red L' :
    list_enumeratorᵗ L' X ->
    list_enumerator (L L') p.
  Proof.
    intros HL'.
    split.
    + intros H.
      eapply Hf in H. eapply (cumul_spec qe) in H as [m1]. destruct (cumul_specᵗ HL' x) as [m2 ?]. 
      exists (1 + m1 + m2). cbn. in_app 2.
      in_collect x.
      eapply cum_ge'; eauto; try lia.
      eapply cum_ge'; eauto; try lia.
    + intros [m H]. induction m.
      * inversion H.
      * cbn in H. inv_collect. 
        eapply Hf. eauto.
  Qed.

End enum_red.

Lemma enumerator_red X Y (p : X -> Prop) (q : Y -> Prop) f d g r:
  forall H1 : decider d (eq_on Y),
  reduces_m r p q -> enumeratorᵗ f X -> enumerator g q -> enumerator (fun! ⟨ n, m ⟩ =>
   nth_error
     (L r (fun n0 : nat => if g n0 is (Some x) then [x] else [])
        (decider_eq_dec (fun H3 : Y * Y => H1 H3))
        (fun n0 : nat => if f n0 is (Some x) then [x] else []) n) m)  p.
Proof.
  intros.
  eapply list_enumerator_enumerator.
  eapply enum_red with (p := p) (q := q); eauto.
  eapply enumerator_list_enumerator.
  eauto.
Qed.

Lemma enumerable_red X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerableᵗ X -> discrete Y -> enumerable q -> enumerable p.
Proof.
  intros [f] [] % enum_enumT [] % discrete_iff [L] % enumerable_enum.
  eapply list_enumerable_enumerable.
  eexists. eapply enum_red; eauto.
Qed.

Theorem not_decidable X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerableᵗ X -> ~ enumerable (compl p) ->
  ~ decidable q /\ ~ decidable (compl q).
Proof.
  intros. split; intros ?.
  - eapply H1. eapply red_m_transports in H2; eauto.
    eapply decidable_complement in H2. eapply decidable_enumerable; eauto.
  - eapply H1. eapply red_m_transports in H2. 2: eapply red_m_complement; eauto.
    eapply decidable_enumerable; eauto.
Qed.

Theorem not_coenumerable X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerableᵗ X -> ~ enumerable (compl p) -> discrete Y ->
  ~ enumerable (compl q).
Proof.
  intros. intros ?. eapply H1. eapply enumerable_red in H3; eauto.
  now eapply red_comp.
Qed.
