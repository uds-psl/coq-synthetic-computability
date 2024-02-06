From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions Limit simple.

Require Import Vectors.VectorDef Arith.Compare_dec Lia.
Import Vector.VectorNotations.

Local Notation vec := Vector.t.


(* ########################################################################## *)
(** * Low Simple Set *)
(* ########################################################################## *)

(** This file contains the definition of low simple set and proves the
essential property of low simple, i.e. Low simple as a solution to
Post's Problem in Turing degree. **)

  (* Definition of low *)
  Definition low (P: nat -> Prop) := P´ ⪯ᴛ K.


Section LowFacts.
  (* If the turing jump of A is low, then A is not reduciable to K *)

  Lemma lowness (P: nat -> Prop) :
    low P -> ~ K ⪯ᴛ P.
  Proof.
    intros H IH.
    eapply not_turing_red_J with (Q := P).
    eapply Turing_transitive; [apply H| easy].
  Qed.

  Lemma limit_jump_lowness (A: nat -> Prop) :
    LEM_Σ 1 ->
    definite K ->
    limit_computable (A´) -> ~ K ⪯ᴛ A.
  Proof.
    intros LEM defK H IH.
    apply lowness with (P := A); [|apply IH].
  Admitted.

End LowFacts.


Section LowSimplePredicate.

Definition low_simple P := low P /\ simple P.

Definition sol_Post's_problem (P: nat -> Prop) :=
  (~ decidable P) /\ (enumerable P) /\ ~ (K ⪯ᴛ P).

Fact low_simple_correct:
  forall P, low_simple P -> sol_Post's_problem P.
Proof.
  intros P [H1 H2]; split; [now apply simple_undecidable|].
  split; [destruct H2 as [H2 _]; eauto| now apply lowness].
Qed.

End LowSimplePredicate.


Require Import List.
Import ListNotations.
Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Require Import SyntheticComputability.Shared.FinitenessFacts.

Section Construction.

  Definition mu n (P: nat -> Prop) := P n /\ forall m, P m -> n <= m.

  Variable W_: nat -> nat -> nat -> Prop.
  Hypothesis W_spec: forall P, semi_decidable P -> exists c, forall x, P x <-> exists n, W_ c n x.

  Definition disj (A B: nat -> Prop) := forall x, A x -> B x -> False.
  Definition disj__l (A: list nat) (B: nat -> Prop) := forall x, In x A -> B x -> False.

  Notation "A # B" := (disj A B) (at level 30).
  Notation "A l# B" := (disj__l A B) (at level 30).

  Record Extendsion :=
  {
      extendP: list nat -> nat -> option nat -> Prop;
      extend_dec: forall l x, Σ y, extendP l x y;
      extend_uni: forall l x y1 y2, extendP l x y1 -> extendP l x y2 -> y1 = y2
  }.

  Fixpoint P_templete (E: (nat -> Prop) -> nat -> nat -> Prop) n x: Prop :=
    match n with
    | O => False
    | S n => P_templete E n x \/ E (P_templete E n) n x
    end.

  Fixpoint F_ (E: Extendsion) n l: Prop :=
    match n with
    | O => l = []
    | S n => exists ls a, F_ E n ls /\ (extendP E ls n a) /\ l = if a is Some a then a :: ls else ls
    end.

  Definition F_with E x := exists l n, In x l /\ (F_ E n l).

  Lemma F_uni E : forall n l1 l2, F_ E n l1 -> F_ E n l2 -> l1 = l2 .
  Proof.
    induction n; simpl; [intros ?? -> ->; easy |].
    intros l1 l2 (ls & a & H1 & H2 & ->) (ls' & a' & H1' & H2' & ->).
    rewrite !(IHn _ _ H1 H1') in *.
    rewrite !(extend_uni H2 H2') in *.
    easy.
  Qed.

  Lemma F_computable E : exists f: nat -> list nat, forall n, F_ E n (f n).
  Proof.
    set (F := fix f x :=
           match x with
           | O => []
           | S x => match projT1 ((extend_dec E) (f x) x) with
                   | None => f x
                   | Some a => a :: (f x)
                   end
           end).
    exists F. induction n; simpl.
    - easy.
    - exists (F n). destruct (extend_dec E (F n) n).
      exists x. cbn. split; [eauto|]. split; [eauto|].
      easy.
  Qed.

  Definition decider: nat -> list nat -> bool.
  Proof.
    intros x l.
    destruct (ListDec.In_dec EqDec.nat_eq_dec x l).
    - exact true. - exact false.
  Defined.

  Fact decider_spec: forall x l, (decider x l) = true <-> In x l.
  Proof.
    intros x l. unfold decider.
    destruct (ListDec.In_dec EqDec.nat_eq_dec x l); firstorder.
  Qed.

  Lemma F_with_semi_decidable E: semi_decidable (F_with E).
  Proof.
    unfold semi_decidable, semi_decider.
    destruct (F_computable E) as [f Hf].
    exists (fun x n => decider x (f n)).
    intros x. split.
    - intros (l & n & Hxl & Hl).
      exists n. rewrite decider_spec.
      now rewrite (F_uni (Hf n) Hl).
    - intros (n & Hn%decider_spec).
      exists (f n), n; split; eauto.
  Qed.

  Section SimpleSet.

  Definition extend_simple l__n n x :=
    exists e, mu e (fun alpha => e < n /\ (l__n l# W_ alpha n) /\ mu x (fun beta => W_ alpha n beta /\ 2 * alpha < beta)).

  Definition simple_extendsion: Extendsion.
  Proof.
    exists (fun l n a => forall x, a = Some x <-> extend_simple l n x).
    - intros l x. admit.
    - intros l x y1 y2 Hy1 Hy2.
      admit.
  Admitted.

  Definition E_simple P__n n x :=
    exists e, mu e (fun alpha => e < n /\ (W_ alpha n # P__n) /\ mu x (fun beta => W_ alpha n beta /\ 2 * alpha < beta)).


(*  Definition P_ := P_templete E_simple. *)
  Definition P_ := F_ simple_extendsion.
  Definition W e x := exists n, W_ e n x.
  Definition P := F_with simple_extendsion.

  Definition R_simple P e := (~ exhaustible (W e)) -> ~ (W e) # P.

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

  Lemma P_meet_R_simple : forall e, R_simple P e.
  Proof.
    strong induction e.
    intros Hex Hdisj.
    unfold disj in Hdisj.
  Admitted.

  Lemma P_semi_decidable : semi_decidable P.
  Proof.
    apply F_with_semi_decidable.
  Qed.

  Lemma P_coinfinite : ~ exhaustible (compl P).
  Proof.
  Admitted.

  Lemma P_simple : simple P.
  Proof.
    unfold simple; repeat split.
    - rewrite EA.enum_iff. now apply P_semi_decidable.
    - apply P_coinfinite.
    - intros [q (Hqenum & Hqinf & Hq)].
      rewrite EA.enum_iff in Hqenum.
      destruct (W_spec Hqenum) as [c HWq].
      apply (@P_meet_R_simple c).
      intros [l Hqe]; apply Hqinf.
      exists l. intros x Hqx. apply (Hqe x).
      now rewrite HWq in Hqx.
      intros x HWcx HPx. unfold W in HWcx.
      rewrite <- HWq in HWcx. apply (Hq x HWcx HPx).
  Qed.

  End SimpleSet.

End Construction.
