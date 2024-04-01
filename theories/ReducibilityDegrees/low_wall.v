From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions StepIndex Limit simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith Arith.Compare_dec Lia Coq.Program.Equality List.
Require Import SyntheticComputability.ReducibilityDegrees.priority_method.
Require Import SyntheticComputability.ReducibilityDegrees.simple_extension.

Definition inf_exists (P: nat → Prop) := ∀ n, ∃ m, n ≤ m ∧ P m.
  Notation "'∞∃' x .. y , p" :=
    (inf_exists (λ x, .. (inf_exists (λ y, p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' '∞∃'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Section Requirements_Lowness_Correctness.

  Variable P: nat → Prop.
  Hypothesis S_P: Σ f, semi_decider f P.

  Notation "f ↓" := (f = Some ()) (at level 30).

  Definition Φ_ := projT1 (Φ_spec S_P).

  Fact Φ_spec e x: Ξ e (char_rel P) x → ∞∀ n, Φ_ (StepIndex.f S_P) e x n ↓.
  Proof.
    intro H. unfold Φ_. destruct (Φ_spec S_P) as [Φ Φ_spec].
    cbn. destruct (Φ_spec e x H) as [w Hw].
    exists w. intros. eapply Hw. easy.
  Qed.

  Definition Ω e n := Φ_ (StepIndex.f S_P) e e n.

  Hypothesis N_requirements: ∀ e, (∞∃ n, Ω e n ↓) → Ξ e (char_rel P) e.

  Hypothesis LEM_Σ_2: 
      ∀ (P: nat → nat → Prop), (∀ n m, dec (P n m)) → dec (∃ n, ∀ m, P n m).

  #[export]Instance dec_le: ∀ m n, dec (m ≤ n).
  Proof. intros n m; destruct (le_gt_dec n m); [by left|right; lia]. Qed.

  Lemma limit_case e: (∞∀ n, Ω e n ↓) ∨ (∞∀ n, ¬ Ω e n ↓).
  Proof.
    assert (∀ m n, dec (m ≤ n → ¬ Ω e n ↓)) as H by eauto.
    destruct (LEM_Σ_2 H); first by right.
    left. apply Φ_spec, N_requirements. intros i. 
    assert (∀ n, dec (n ≤ i ∧ Ω e n ↓)) as H'' by eauto.
    destruct (@LEM_Σ_2 (λ n _, i ≤ n ∧ Ω e n ↓) ) as [[w Hw]|h1]; first eauto.
    exists w; apply Hw; exact 42.
    assert (∀ n, i ≤ n → ~ Ω e n ↓).
    { intros m Hm HM. eapply h1. exists m; eauto. }
    exfalso. by eapply n; exists i.
  Qed.

  Definition limit_decider e n: bool := Dec (Ω e n ↓).

  Lemma Jump_limit :limit_computable (P´).
  Proof.
    exists limit_decider; split; intros.
    - unfold J. split. 
      intros [w Hw]%Φ_spec; exists w; intros??.
      apply Dec_auto. by eapply Hw.
      intros [N HN]. eapply N_requirements. 
      intros m. exists (S N + m); split; first lia.
      eapply Dec_true. eapply HN. lia.
    - unfold J. split; intros H. 
      destruct (limit_case x) as [[k Hk]|h2].
      enough (Ξ x (char_rel P) x) by easy.
      eapply N_requirements. intros m. exists (S k + m).
      split; first lia. eapply Hk. lia.
      destruct h2 as [w Hw]. exists w.
      intros. specialize (Hw n H0). unfold limit_decider.
      destruct (Dec _); eauto.
      destruct H as [w Hw].
      intros [k Hneg]%Φ_spec.
      set (N := S (max w k)).
      assert (Ω x N ↓). { eapply Hneg. lia. }
      enough (¬ Ω x N ↓) by eauto.
      eapply Dec_false. eapply Hw. lia.  
  Qed.

End Requirements_Lowness_Correctness.


