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

  Lemma Jump_limit :limit_computable (P´).
  Proof.
    unfold J. 
    unfold limit_computable.
    admit.
  Admitted.
End Requirements_Lowness_Correctness.
