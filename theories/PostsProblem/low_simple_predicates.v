From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions limit_computability simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
From SyntheticComputability Require Export lowness.
From SyntheticComputability Require Export simpleness.
From Stdlib Require Import Arith.
Require Import stdpp.list.

From SyntheticComputability.Shared.Libs.PSL Require Power EqDec.

(* ########################################################################## *)
(** * Low Simple Predicates *)
(* ########################################################################## *)

(** This file contains the definition of low simple set and proves the
essential property of low simple, i.e. Low simple as a solution to
Post's Problem in Turing degree. **)

Section AssumePartiality.

Context {Part : partial.partiality}.

Context {enc : encoding ()}.

Context {EPF_assm : EPF.EPF}.

(* Definition of low *)
Definition low (P: nat → Prop) := red_Turing_classical (P´) K.

Section LowFacts.

  Lemma lowness (P: nat → Prop) :
    low P → ¬ red_Turing K P.
  Proof.
    intros H IH.
    eapply not_turing_red_classical_J with (Q := P).
    eapply Turing_classical_transitive; [apply H| ].
    destruct IH as (F & HF & HH).
    exists F. split. eassumption. firstorder.
  Qed.

  Definition low_simple P := low P ∧ simple P.

  Definition sol_Post's_problem (P: nat → Prop) :=
    (¬ decidable P) ∧ (enumerable P) ∧ ¬ (K ⪯ᴛ P).

  Fact low_simple_correct:
    ∀ P, low_simple P → sol_Post's_problem P.
  Proof.
    intros P [H1 H2]; split; [now apply simple_undecidable|].
    split; [destruct H2 as [H2 _]; eauto| now apply lowness ].
  Qed.

  Lemma PostProblem_aux :
    ∃ p: nat → Prop, ¬ decidable p ∧ semi_decidable p ∧ ¬ K ⪯ᴛ p.
  Proof.
    exists (P wall).
    repeat split.
    - apply simple_undecidable. 
      eapply P_simple. intro e.
      unfold lim_to. cbn.
      apply wall_convergence_classically.
      by unfold wall.
    - apply P_semi_decidable.
    - apply lowness.
      eapply limit_turing_red_K_classical; eauto. 
      apply jump_P_limit; eauto.
  Qed.

End LowFacts.

End AssumePartiality.

From SyntheticComputability Require Import EnumerabilityFacts ListEnumerabilityFacts.

Theorem PostProblem {Part : partial.partiality} {epf : EPF.EPF} {enc : encoding unit} :
  ∃ p: nat → Prop, ¬ decidable p ∧ semi_decidable p ∧ ¬ K ⪯ᴛ p.
Proof.
  unshelve edestruct @PostProblem_aux as (p & undec & semidec & H).
  - assumption.
  - assumption. 
  - assumption.
  - exists p. auto.
Qed.

Theorem PostProblem_noK {Part : partial.partiality} :
(exists θ, EPF.EPF_for θ) ->
  ∃ p: nat → Prop, ¬ decidable p ∧ semi_decidable p ∧ (forall K : nat -> Prop, (forall q : nat -> Prop, semi_decidable q -> q ⪯ₘ K) -> ~ K ⪯ᴛ p).
Proof.
  destruct (EnumerabilityFacts.datatype_retract (nat * list bool)) as [(I & R & HIR) _].
  {
    split. eapply discrete_iff. econstructor. exact _.
    apply enumerableᵗ_prod. 
    eapply enumerableᵗ_nat.
    apply enum_enumT.
    apply enumerable_list. apply enum_enumT.  eapply enumerableᵗ_bool.
  }
  intros [θ EPF].
  unshelve edestruct @PostProblem as (p & undec & semidec & H).
  - assumption.
  - exists θ. assumption.
  - unshelve econstructor.
    exact I. exact (fun x => match x with inl n => S n | inr _ => 0 end).
    exact (fun n => match R n with None => (0, []) | Some x => x end).
    exact (fun v => match v with 0 => inr tt | S n => inl n end).
    cbn. intros n.
    now destruct (HIR n) as [-> _]. 
    intros []. reflexivity. now destruct u.
  - exists p. repeat split. assumption. assumption.
    intros K HK Hp.
    apply H. 
    eapply Turing_transitive.
    eapply red_m_impl_red_T.
    eapply HK. eapply semi_dec_halting.
    assumption.
Qed.

Check @PostProblem.
Print Assumptions PostProblem.

Check @PostProblem_noK.
Print Assumptions PostProblem_noK.
