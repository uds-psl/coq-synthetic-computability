From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions limit_computability simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
From SyntheticComputability Require Export lowness.
From SyntheticComputability Require Export simpleness.
Require Import Arith.
Require Import SyntheticComputability.PostsTheorem.PostsTheorem.
Require Import Vectors.VectorDef Arith.Compare_dec Lia.
Import Vector.VectorNotations.
Require Import stdpp.list.

Local Notation vec := Vector.t.



(* ########################################################################## *)
(** * Low Simple Set *)
(* ########################################################################## *)

(** This file contains the definition of low simple set and proves the
essential property of low simple, i.e. Low simple as a solution to
Post's Problem in Turing degree. **)

Section Facts.
  Lemma m_red_complete {X Y} (P: X → Prop) (Q: Y → Prop):
    semi_decidable P → Q ⪯ₘ P → semi_decidable Q.
  Proof. intros [g H1] [f H2]; exists (fun x => g (f x)); firstorder. Qed.

  Lemma m_red_complete_definite {X Y} (P: X → Prop) (Q: Y → Prop):
    definite P → Q ⪯ₘ P → definite Q.
  Proof. intros H [f H2]; firstorder. Qed.
End Facts.



  (* Definition of low *)
  Definition low (P: nat -> Prop) := P´ ⪯ᴛ K.

Section LowFacts.

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat (nat_to_vec k n) = n.

  Variable list_vec_to_nat : forall k, list (vec nat k) -> nat.
  Variable nat_to_list_vec : forall k, nat -> list (vec nat k).
  Variable list_vec_nat_inv : forall k v, nat_to_list_vec k (list_vec_to_nat v) = v.
  Variable nat_list_vec_inv : forall k n, list_vec_to_nat (nat_to_list_vec k n) = n.

  Variable nat_to_list_bool : nat -> list bool.
  Variable list_bool_to_nat : list bool -> nat.
  Variable list_bool_nat_inv : forall l, nat_to_list_bool (list_bool_to_nat l) = l.
  Variable nat_list_bool_inv : forall n, list_bool_to_nat (nat_to_list_bool n) = n.

  Lemma lowness (P: nat -> Prop) :
    low P -> ~ K ⪯ᴛ P.
  Proof.
    intros H IH.
    eapply not_turing_red_J with (Q := P).
    eapply Turing_transitive; [apply H| easy].
  Qed.

  Lemma DN_lowness (P: nat -> Prop) :
    ~ ~ low P -> ~ K ⪯ᴛ P.
  Proof.
    intros H_ IH.
    apply H_. intros H.
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
    eapply limit_turing_red_K; eauto. exact 42. 
  Qed.

  Definition low_simple P := low P /\ simple P.

  Definition sol_Post's_problem (P: nat -> Prop) :=
    (~ decidable P) /\ (enumerable P) /\ ~ (K ⪯ᴛ P).

  Fact low_simple_correct:
    forall P, low_simple P -> sol_Post's_problem P.
  Proof.
    intros P [H1 H2]; split; [now apply simple_undecidable|].
    split; [destruct H2 as [H2 _]; eauto| now apply lowness].
  Qed.



    (*** Instance of low simple predicate ***)

  Section LowSimplePredicate.

  Variable η: nat -> nat -> option nat.
  Hypothesis EA: 
    forall P, semi_decidable P -> exists e, forall x, P x <-> exists n, η e n = Some x.

  (* Used to eliminate ~~Φ *)
  (* should be able to weaker to DNE_Σ_2 *)
  Hypothesis DN: forall P, ~ ~ P -> P.

  (* Used to prove limit computable from N requirements *)
  Hypothesis LEM_Σ_2: 
  forall (P: nat -> nat -> Prop), 
    (forall n m, dec (P n m)) -> 
      (exists n, forall m, P n m) \/ ~ (exists n, forall m, P n m).

  (* Used to prove Limit Lemma *)
  Hypothesis LEM_Σ_1: LEM_Σ 1.
  Hypothesis def_K: definite K.

  Theorem a_sol_Post's_problem: exists P, sol_Post's_problem P.
  Proof.
    eexists. eapply low_simple_correct; split.
    - eapply limit_turing_red_K; eauto. exact 42.
      apply jump_P_limit; eauto.  
    - eapply P_simple.
      intros. intros d. apply d.
      apply wall_convergence_test. assumption.
  Qed.

  End LowSimplePredicate.

  Notation "(¬¬Σ⁰₁)-LEM" := ((∀ (k : nat) (p : vec nat k → Prop), isΣsem 1 p → ~~ definite p)) (at level 0).

  Lemma m_red_K_semi_decidable {n} (P: vec nat n → Prop):
    semi_decidable P -> P ⪯ₘ K.
  Proof.
    intros H. unfold K. rewrite <- red_m_iff_semidec_jump_vec.
    by apply semi_decidable_OracleSemiDecidable. eauto.
  Qed.

  Theorem PostProblem_from_neg_negLPO :
    ∃ p: nat → Prop, ¬ decidable p ∧ semi_decidable p ∧ (¬¬ (¬¬Σ⁰₁)-LEM -> ¬ K ⪯ᴛ p).
  Proof.
    eexists.
    repeat split.
    - apply simple_undecidable. 
      eapply P_simple. apply wall_convergence.
    - apply P_semi_decidable.
    - intros L. intros G. apply L. clear L. intros L.
      assert (~~ definite K) as hK.
      {
        specialize (L 1 (fun v => K (Vector.hd v))).
        intros h. apply L. 
        rewrite <- semi_dec_iff_Σ1.
        eapply m_red_complete; first apply semi_dec_halting.
        exists (fun v => Vector.hd v); done.
        intros h1. apply h.
        intros x. specialize (h1 (Vector.cons x Vector.nil)). exact h1.
      }
      apply hK. clear hK. intros hK.
      assert (LEM_Σ 1).
      {
        intros n p Hs.
        eapply m_red_complete_definite; first apply hK.
        rewrite <- semi_dec_iff_Σ1 in Hs.
        by eapply m_red_K_semi_decidable.
      }
      revert G. apply lowness. red.
      eapply limit_turing_red_K; eauto. exact 42.
      apply jump_P_limit_2; eauto.
  Qed.

End LowFacts.

Check PostProblem_from_neg_negLPO.
Print Assumptions PostProblem_from_neg_negLPO.

(* general proof that (¬¬Σ⁰₁)-LEM <-> ¬¬(Σ⁰₁)-LEM under many-one complete Σ⁰₁ predicate  *)
Section assume.

  Variable enumerable : (nat -> Prop) -> Prop.

  Variable K : nat -> Prop.
  Variable eK : enumerable K.
  Variable cK : forall p : nat -> Prop, enumerable p -> red_m p K.

  Goal ~~ (forall p : nat -> Prop, enumerable p -> forall x, p x \/ ~ p x)
         <->
      (forall p : nat -> Prop, enumerable p -> ~~ forall x, p x \/ ~ p x).
  Proof.
    split.
    - firstorder.
    - intros nnLPO H.
      apply (nnLPO K eK). intros dK.
      apply H.
      intros p [f Hf] % cK x.
      specialize (dK (f x)).
      red in Hf. rewrite <- Hf in dK.
      assumption.
  Qed.

End assume.
