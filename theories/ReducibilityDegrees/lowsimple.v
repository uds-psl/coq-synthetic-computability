From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions Limit simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith.
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
    (* specialize (limit_turing_red_K _ _ _ _ defK H). *)
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