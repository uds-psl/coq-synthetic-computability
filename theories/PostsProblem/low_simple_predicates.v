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
(** * Low Simple Predicates *)
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


Notation "(¬¬Σ⁰₁)-LEM" := 
  ((∀ (k : nat) (p : vec nat k → Prop), isΣsem 1 p → ¬¬ definite p)) (at level 0).

Section AssumePartiality.

Context {Part : partial.partiality}.

Context {enc : encoding ()}.

Context {EPF_assm : EPF.EPF}.

(* Definition of low *)
Definition low (P: nat → Prop) := P´ ⪯ᴛ K.

Section LowFacts.

  Context {vec_datatype : datatype (vec nat)}.

  Notation vec_to_nat := (@X_to_nat (vec nat) _ _).
  Notation nat_to_vec := (@nat_to_X (vec nat) _ _).
  Notation vec_nat_inv := (@X_nat_inv (vec nat) _ _).

  Context {list_vec_datatype : datatype (fun k => list (vec nat k))}.

  Notation list_vec_to_nat := (@X_to_nat  (fun k => list (vec nat k)) _ _).
  Notation nat_to_list_vec := (@nat_to_X  (fun k => list (vec nat k)) _).
  Notation list_vec_nat_inv := (@X_nat_inv  (fun k => list (vec nat k)) _ _).

  Context {list_bool_datatype : datatype (fun _ => list bool)}.

  Notation list_bool_to_nat := (@X_to_nat (fun _ => list bool) _ 0).
  Notation nat_to_list_bool := (@nat_to_X (fun _ => list bool) _ 0).
  Notation list_bool_nat_inv := (@X_nat_inv (fun _ => list bool) _ 0).

  Lemma lowness (P: nat → Prop) :
    low P → ¬ K ⪯ᴛ P.
  Proof.
    intros H IH.
    eapply not_turing_red_J with (Q := P).
    eapply Turing_transitive; [apply H| easy].
  Qed.

  Lemma DN_lowness (P: nat → Prop) :
    ¬¬ low P → ¬ K ⪯ᴛ P.
  Proof.
    intros H_ IH.
    apply H_. intros H.
    eapply not_turing_red_J with (Q := P).
    eapply Turing_transitive; [apply H| easy].
  Qed.

  Lemma limit_jump_lowness (A: nat → Prop) :
    LEM_Σ 1 →
    definite K →
    limit_computable (A´) → ¬ K ⪯ᴛ A.
  Proof.
    intros LEM defK H IH.
    apply lowness with (P := A); [|apply IH].
    eapply limit_turing_red_K; eauto. Unshelve. exact 42.
  Qed.

  Definition low_simple P := low P ∧ simple P.

  Definition sol_Post's_problem (P: nat → Prop) :=
    (¬ decidable P) ∧ (enumerable P) ∧ ¬ (K ⪯ᴛ P).

  Fact low_simple_correct:
    ∀ P, low_simple P → sol_Post's_problem P.
  Proof.
    intros P [H1 H2]; split; [now apply simple_undecidable|].
    split; [destruct H2 as [H2 _]; eauto| now apply lowness].
  Qed.

  (*** Instance of low simple predicate ***)

  Section LowSimplePredicate.

  Hypothesis LEM_Σ_1: LEM_Σ 1.
  Hypothesis def_K: definite K.

  Theorem a_sol_Post's_problem: ∃ P, sol_Post's_problem P.
  Proof.
    eexists. eapply low_simple_correct; split.
    - eapply limit_turing_red_K; eauto. 
      apply jump_P_limit; eauto.  
    - eapply P_simple.
      intros. intros d. apply d.
      apply wall_convergence. by unfold wall. 
      assumption. Unshelve. exact 42.
  Qed.

  End LowSimplePredicate.

  Lemma m_red_K_semi_decidable {n} (P: vec nat n → Prop):
    semi_decidable P → P ⪯ₘ K.
  Proof.
    intros H. unfold K. rewrite <- red_m_iff_semidec_jump_vec.
    by apply semi_decidable_OracleSemiDecidable. 
  Qed.

  Lemma PostProblem_from_neg_negLPO_aux :
    ∃ p: nat → Prop, ¬ decidable p ∧ semi_decidable p ∧ (¬¬ (¬¬Σ⁰₁)-LEM → ¬ K ⪯ᴛ p).
  Proof.
    exists (P wall).
    repeat split.
    - apply simple_undecidable. 
      eapply P_simple. intro e.
      unfold lim_to. cbn.
      apply wall_convergence_classically.
      by unfold wall.
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
      eapply limit_turing_red_K; eauto. Unshelve. 2: exact 42.
      apply jump_P_limit; eauto.
  Qed.

End LowFacts.

End AssumePartiality.

From SyntheticComputability Require Import EnumerabilityFacts ListEnumerabilityFacts.

Theorem PostProblem_from_neg_negLPO {Part : partial.partiality} :
(exists θ, EPF.EPF_for θ) ->
  ∃ p: nat → Prop, ¬ decidable p ∧ semi_decidable p ∧ (¬¬ (¬¬Σ⁰₁)-LEM → forall K : nat -> Prop, (forall q : nat -> Prop, semi_decidable q -> q ⪯ₘ K) -> ~ K ⪯ᴛ p).
Proof.
  intros [θ EPF].
  destruct (EnumerabilityFacts.datatype_retract (nat * list bool)) as [(I & R & HIR) _].
  {
    split. eapply discrete_iff. econstructor. exact _.
    apply enumerableᵗ_prod. 
    eapply enumerableᵗ_nat.
    apply enum_enumT.
    apply enumerable_list. apply enum_enumT.  eapply enumerableᵗ_bool.
  }
  destruct (EnumerabilityFacts.datatype_retract (list bool)) as [(I2 & R2 & HIR2) _].
  {
    split. eapply discrete_iff. econstructor. exact _.
    apply enum_enumT.
    apply enumerable_list. apply enum_enumT.  eapply enumerableᵗ_bool.
  }
  unshelve edestruct @PostProblem_from_neg_negLPO_aux as (p & undec & semidec & H).
  - assumption.
  - unshelve econstructor.
    exact I. exact (fun x => match x with inl n => S n | inr _ => 0 end).
    exact (fun n => match R n with None => (0, []) | Some x => x end).
    exact (fun v => match v with 0 => inr tt | S n => inl n end).
    cbn. intros n.
    now destruct (HIR n) as [-> _]. 
    intros []. reflexivity. now destruct u.
  - exists θ. assumption.
  - unshelve econstructor.
    3: eapply VectorEmbedding.vec_nat_inv.
  - eassert (forall k, enumeratorᵗ _ (list (vec nat k))).
    {
      intros k. eapply list_enumeratorᵗ_enumeratorᵗ.
      eapply enumeratorᵗ_list.
      eapply enumeratorᵗ_of_list.
      Unshelve.
      2:{ intros n. apply Some. apply (VectorEmbedding.nat_to_vec k n). }
      red. intros. exists (VectorEmbedding.vec_to_nat x).
      now rewrite VectorEmbedding.vec_nat_inv.
    }
    eassert (forall k, decider _ (eq_on (list (vec nat k)))).
    {
      intros k. apply decider_eq_list.
      Unshelve.
      2:{ intros [l1 l2].
          exact (VectorEmbedding.vec_to_nat l1 =? VectorEmbedding.vec_to_nat l2). }
      cbn.
      red. intros [l1 l2].
      red.
      split. intros ->.
      eapply Nat.eqb_refl.
      intros Heq.
      destruct (Nat.eqb_spec  (VectorEmbedding.vec_to_nat l1) (VectorEmbedding.vec_to_nat l2)).
      eapply (f_equal (VectorEmbedding.nat_to_vec k)) in e.
      now rewrite !VectorEmbedding.vec_nat_inv in e.
      congruence.
    }
    unshelve econstructor.
    + intros k.
      specialize (H k). eapply enumerator_retraction in H as [I3 HI].
      exact I3. eapply (H0 k). 
    + intros k. specialize (H k). eapply enumerator_retraction in H as [I3 HI].
      set (fun! ⟨ n, m ⟩ => nth_error (L_list (λ n0 : nat, [VectorEmbedding.nat_to_vec k n0]) n) m) as R3.
      refine (fun n => match R3 n with None => [] | Some x => x end). eapply (H0 k). 
    + cbn. intros. destruct enumerator_retraction.
      red in r. now rewrite r.
  - unshelve econstructor. exact (fun _ => I2).
    exact (fun _ n => match R2 n with None => [] | Some x => x end).
    cbn. intros _ n.
    now destruct (HIR2 n) as [-> _]. 
  - exists p. repeat split. assumption. assumption.
    intros lpo K HK Hp.
    apply H. assumption.
    eapply Turing_transitive.
    eapply red_m_impl_red_T.
    eapply HK. eapply semi_dec_halting.
    assumption.
Qed.

Check @PostProblem_from_neg_negLPO.
Print Assumptions PostProblem_from_neg_negLPO.

(* general proof that (¬¬Σ⁰₁)-LEM <-> ¬¬(Σ⁰₁)-LEM under many-one complete Σ⁰₁ predicate  *)
Section assume.

  Variable enumerable : (nat → Prop) → Prop.

  Variable K : nat → Prop.
  Variable eK : enumerable K.
  Variable cK : ∀ p : nat → Prop, enumerable p → red_m p K.

  Goal
      ¬¬ (∀ p : nat → Prop, enumerable p → ∀ x, p x ∨ ¬ p x)
      ↔
      (∀ p : nat → Prop, enumerable p → ¬¬ ∀ x, p x ∨ ¬ p x).
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

