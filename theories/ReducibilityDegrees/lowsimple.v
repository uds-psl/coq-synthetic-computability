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


Section Construction.

  Definition mu (P: nat -> Prop) n := P n /\ forall m, P m -> n <= m.

  Variable W: nat -> nat -> nat -> Prop.

  Definition W_spec (c n x: nat) : Prop := forall P, semi_decidable P -> exists c, forall x, P x <-> exists n, W c n x.

  Definition disj (A B: nat -> Prop) := forall x, A x <-> ~ B x.
  Notation "A ⊎ B" := (disj A B) (at level 30).

  (** ** Is this a correct definition for inifity ? **)

  Definition infity (P: nat -> Prop) := forall x, exists y, y > x -> P y.

  Fixpoint P n : nat -> Prop :=
    match n with
    | O => fun _ => False
    | S n => fun x =>
              P n x \/ exists e, mu (fun e => e < n /\ ((W e n) ⊎ (P n)) /\ mu (fun x => W e n x /\ 2 * e < x) x) e
    end.

  Definition W' e x := exists n, W e n x.
  Definition P' x := exists n, P n x.

  Definition R P e := infity (W' e) -> exists w, (W' e w) /\ P w.

  Lemma P_meet_R : forall n, R P' n.
  Proof.
  Admitted.

  Lemma P_semi_decidable : semi_decidable P'.
  Proof.
  Admitted.


End Construction.
