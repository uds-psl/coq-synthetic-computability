From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions Limit simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith Arith.Compare_dec Lia Coq.Program.Equality List.
Require Import SyntheticComputability.ReducibilityDegrees.priority_method.
Require Import SyntheticComputability.ReducibilityDegrees.simple_extension.

Section Requirements_Lowness_Correctness.

  Variable P: nat -> Prop.

  Notation "f ↓" := (f = Some tt) (at level 30).

  Variable Φ_: (nat -> bool -> Prop) -> nat -> nat -> nat -> option unit.

  Hypothesis Φ_spec:
    forall e x, Ξ e (char_rel P) x -> (∞∀ n, Φ_ (char_rel P) e x n ↓).

  Definition Ω e n := Φ_ (char_rel P) e e n.

  Hypothesis N_requirements:
    forall e, (∞∃ n, Ω e n ↓) -> Ξ e (char_rel P) e.

  Hypothesis LEM_Σ_2: forall (P: nat -> nat -> Prop), 
    (forall n m, dec (P n m)) -> dec (exists n, forall m, P n m).

  Lemma limit_case e: (∞∀ n, Ω e n ↓) \/ (∞∀ n, ~ Ω e n ↓).
  Proof.
    assert (forall m n, dec (m < n -> ~ Ω e n ↓)) as H' by eauto.
    destruct (LEM_Σ_2 H'); first now right.
    assert (forall m n, dec (m < n -> Ω e n ↓)) as H by eauto.
    destruct (LEM_Σ_2 H); first now left.
    left. apply Φ_spec. eapply N_requirements.
    intros i. 
    assert (forall n, dec (n > i /\ Ω e n ↓)) as H'' by eauto.
    destruct (@LEM_Σ_2 (fun n _ => (n > i /\ Ω e n ↓)) ); first eauto.
    destruct e0 as [w Hw]. exists w. apply Hw. exact 42.
    exfalso. firstorder.
  Qed.

  Definition limit_decider e n: bool := Dec (Ω e n ↓).

  Lemma Jump_limit :limit_computable (P´).
  Proof.
    exists limit_decider; split; intros.
    - unfold J. split. 
      intros [w Hw]%Φ_spec; exists (S w); intros??.
      apply Dec_auto. now eapply Hw.
      intros [N HN]. eapply N_requirements. 
      intros m. exists (S N + m); split; first lia.
      eapply Dec_true. eapply HN. lia.
    - unfold J. split; intros H. 
      destruct (limit_case x) as [[k Hk]|h2].
      enough (Ξ x (char_rel P) x) by easy.
      eapply N_requirements. intros m. exists (S k + m).
      split; first lia. eapply Hk. lia.
      destruct h2 as [w Hw]. exists (S w).
      intros. specialize (Hw n H0). unfold limit_decider.
      destruct (Dec _); eauto.
      destruct H as [w Hw].
      intros [k Hneg]%Φ_spec.
      set (N := S (max w k)).
      assert (Φ_ (char_rel P) x x N ↓).
      { eapply Hneg. lia. }
      enough (~ Φ_ (char_rel P) x x N ↓) by eauto.
      eapply Dec_false. eapply Hw. lia.  
  Qed.

End Requirements_Lowness_Correctness.


