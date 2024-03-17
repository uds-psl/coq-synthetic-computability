From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions Limit simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith Arith.Compare_dec Lia Coq.Program.Equality List.
Import ListNotations.

Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Definition disj {X} (A: list X) (B: X -> Prop) := forall x, In x A -> B x -> False.
Definition intersect {X} (A B: X -> Prop) := forall x, A x -> B x -> False.
Notation "A # B" := (disj A B) (at level 30).

Section Construction.
  Record Extension :=
  {
      extendP: list nat -> nat -> nat -> Prop;
      extend_dec: forall l x, (Σ y, extendP l x y) + (forall y, ~ extendP l x y);
      extend_uni: forall l x y1 y2, extendP l x y1 -> extendP l x y2 -> y1 = y2
  }.

  Inductive F_ (E: Extension) : nat -> list nat -> Prop :=
    | Base : F_ E O []
    | ExtendS n l a : F_ E n l -> extendP E l n a -> F_ E (S n) (a::l)
    | ExtendN n l   : F_ E n l -> (forall a, ~ extendP E l n a) -> F_ E (S n) l.

  Lemma F_uni E : forall n l1 l2, F_ E n l1 -> F_ E n l2 -> l1 = l2 .
  Proof.
    intros n l1 l2.
    dependent induction n.
    - intros H1 H2. inv H1. now inv H2.
    - intros H1 H2. inv H1; inv H2.
      assert(l = l0) as -> by now apply IHn.
      f_equal. apply (extend_uni H3 H4).
      assert (l = l2) as -> by now apply IHn.
      exfalso. apply (H4 a H3).
      assert (l = l1) as -> by now apply IHn.
      exfalso. apply (H3 a H4).
      now apply IHn.
  Qed.

  Lemma F_mono E n m l1 l2: F_ E n l1 -> F_ E m l2 -> n <= m -> incl l1 l2.
  Proof.
      intros H1 H2 HE.
      revert H1 H2; induction HE in l2 |-*; intros H1 H2.
      - now assert (l1 = l2) as -> by (eapply F_uni; eauto).
      - inv H2; last now apply IHHE.
        specialize (IHHE l H1 H0). eauto.
  Qed.

  Lemma F_pop E n x l: F_ E n (x::l) -> exists m, F_ E m l.
  Proof.
    intros H. dependent induction H. 
    - now exists n.
    - eapply IHF_. eauto.
  Qed.
  
  Lemma F_pick E n x l: F_ E n (x::l) -> exists m, F_ E m l /\ extendP E l m x.
  Proof.
    intros H. dependent induction H.
    - exists n; eauto.
    - eapply IHF_; eauto.
  Qed.

  Lemma F_computable E : Σ f: nat -> list nat, 
    forall n, F_ E n (f n) /\ length (f n) <= n.
  Proof.
    set (F := fix f x :=
           match x with
           | O => []
           | S x => match (extend_dec E) (f x) x with
                   | inr _ => f x
                   | inl aH => (projT1 aH) :: (f x)
                   end
           end).
    exists F. induction n; simpl.
    - split. constructor. easy.
    - destruct (extend_dec E (F n) n); split.
      + eapply ExtendS; first apply IHn. now destruct s.
      + cbn. destruct IHn. lia.
      + now eapply ExtendN.
      + destruct IHn. lia.
  Qed.

  Definition F_func E := projT1 (F_computable E).
  Lemma F_func_correctness {E}: forall n, F_ E n (F_func E n).
  Proof.
    intros n; unfold F_func. 
    destruct (F_computable E) as [f H].
    now destruct (H n).
  Qed.

  Lemma F_func_correctness' {E}: forall n, length (F_func E n) <= n.
  Proof.
    intros n; unfold F_func. 
    destruct (F_computable E) as [f H].
    now destruct (H n).
  Qed.

  Definition F_with E x := exists l n, In x l /\ (F_ E n l).

  Lemma F_with_semi_decidable E: semi_decidable (F_with E).
  Proof.
    unfold semi_decidable, semi_decider.
    destruct (F_computable E) as [f Hf ].
    exists (fun x n => (Dec (In x (f n)))).
    intros x. split.
    - intros (l & n & Hxl & Hl).
      exists n. rewrite Dec_auto; first easy.
      destruct (Hf n) as [Hf' _].
      now rewrite (F_uni Hf' Hl).
    - intros (n & Hn%Dec_true).
      exists (f n), n; split; eauto.
      apply Hf.
  Qed.

End Construction.

Section StrongInduction.

  Definition strong_induction (p: nat -> Type) :
    (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
  Proof.
      intros H x; apply H.
      induction x; [intros; lia| ].
      intros; apply H; intros; apply IHx; lia.
  Defined.

End StrongInduction.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.