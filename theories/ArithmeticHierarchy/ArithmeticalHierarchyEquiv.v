(** ** Equivalence of Both Definitions *)

From Undecidability.FOL Require Import Facts FullFacts.
Require Import Lia Vector Fin List.
Import Vector.VectorNotations.
From SyntheticComputability Require Import PrenexNormalForm.
From SyntheticComputability Require Import ArithmeticalHierarchySyntactic ArithmeticalHierarchySemantic.

Require Import PeanoNat (* Nat.eqb *) Bool.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.
Derive Signature for vec.

Section ArithmeticalHierarchyEquiv.

  Existing Instance interp_nat.

  Lemma noQuant_dec {ff:falsity_flag} {ϕ}:
    noQuant_ind ϕ -> forall ρ, {(ρ ⊨ ϕ)} + {~(ρ ⊨ ϕ)}.
  Proof.
    intros nQ ρ. induction ϕ  as [| ff P v | ff op φ1 IH1 φ2 IH2|].
    - cbn. now right.
    - destruct P. cbn in *.
      repeat dependent destruction v.
      apply Nat.eq_dec.
    - specialize (IH1 ltac:(now destruct (noQuand_ind_inv nQ))) as [IH1 | IH1];
      specialize (IH2 ltac:(now destruct (noQuand_ind_inv nQ))) as [IH2 | IH2];
      destruct op; cbn.
      all: firstorder.
    - exfalso. inversion nQ.
  Qed.

  (** # <a id="isSigmasyn_in_isSigmasem" /> #*)
  Lemma isΣnsyn_in_isΣsem:
    (forall n k (p: vec nat k -> Prop), isΣsyn n p -> isΣsem n p)
 /\ (forall n k (p: vec nat k -> Prop), isΠsyn n p -> isΠsem n p).
  Proof.
    enough (
         (forall (b : falsity_flag) (n : nat) (ϕ : form) (i : isΣf_ind n ϕ) k, isΣsem n ((fun v : vec nat k => vec_to_env v ⊨ ϕ)))
      /\ (forall (b : falsity_flag) (n : nat) (ϕ : form) (i : isΠf_ind n ϕ) k, isΠsem n ((fun v : vec nat k => vec_to_env v ⊨ ϕ)))
     ) as H. {
        split.
        all: intros n k p [ff [ϕ [Σi r]]].
        all: eapply PredExt. 2,4: eapply r.
        all: eapply H; eauto.
      }
    apply isΣ_syn_isΠ_syn_mutind.
    - intros ff n ϕ nQ k.
      unshelve eapply PredExt. exact (fun v => (fun v => if (noQuant_dec nQ (vec_to_env v)) then true else false) v = true).
      + apply isΣΠsem0.
      + intros v. cbn. now destruct noQuant_dec.
    - intros ff n ϕ iΣ IH k.
      specialize (IH (S k)).
      dependent destruction IH.
      change (isΣsem (S n) (fun v : vec nat k => exists d, (fun v => (vec_to_env v) ⊨ ϕ)(d::v))).
      cbn in H0.
      eapply PredExt. 2:{ intros. etransitivity. setoid_rewrite H0. reflexivity. instantiate (1 := fun v => (exists d x : nat, p (x :: d :: v))). reflexivity. }
      now eapply isΣsemTwoEx.
    - intros ff n ϕ iΠ IH k.
      change (isΣsem (S n) (fun v : vec nat k => exists d, (fun v => (vec_to_env v) ⊨ ϕ)(d::v))).
      eapply isΣsemS. now apply IH.
    - intros ff n ϕ nQ k.
      unshelve eapply PredExt. exact (fun v => (fun v => if (noQuant_dec nQ (vec_to_env v)) then true else false) v = true).
      + apply isΣΠsem0.
      + intros v. cbn. now destruct noQuant_dec.
    - intros ff n ϕ iΠ IH k.
      specialize (IH (S k)).
      dependent destruction IH.
      change (isΠsem (S n) (fun v : vec nat k => forall d, (fun v => (vec_to_env v) ⊨ ϕ)(d::v))).
      cbn in H0.
      eapply PredExt. 2:{ intros. etransitivity. setoid_rewrite H0. reflexivity. refine (iff_refl _). }
      now apply isΠsemTwoAll.
    - intros ff n ϕ iΣ IH k.
      change (isΠsem (S n) (fun v : vec nat k => forall d, (fun v => (vec_to_env v) ⊨ ϕ)(d::v))).
      eapply isΠsemS. now apply IH.
  Qed.

  (* Rückrichtung annehmen entscheidbar -> Δ1 *)

  Definition decΔ1syn := forall k (f: vec nat k -> bool), isΔsyn 1 (fun v => f v = true).
  (** # <a id="decSigma1syn" /> #*)
  Definition decΣ1syn := forall k (f: vec nat k -> bool), isΣsyn 1 (fun v => f v = true).

  (** # <a id="decSigma1syn_decDelta1syn" /> #*)
  Lemma decΣ1syn_decΔ1syn : decΣ1syn <-> decΔ1syn.
  Proof.
    unfold decΣ1syn, decΔ1syn.
    split.
    - intros decΣ1syn k f. split; [apply decΣ1syn|].
      unshelve eapply extensional_Πsyn. exact (fun v => (fun v => if f v then false else true) v <> true). now intros; cbn; destruct f; firstorder.
      apply Σ1syn_notΠ1_int, decΣ1syn.
    - intros H k f. apply H. 
  Qed.

  (** # <a id="decSigma1syn_incl_1" /> #*)
  Lemma decΣ1syn_incl_1 :
    decΣ1syn <->
      (forall k (p : vec nat k -> Prop), isΣsem 1 p -> isΣsyn 1 p)
  /\  (forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΠsyn 1 p).
  Proof.
    split. {
      intros decΔ1syn%decΣ1syn_decΔ1syn.
      split.
      all: intros k p H.
      all: do 2 dependent destruction H.
      all: specialize (decΔ1syn _ f) as [HΣ HΠ].
      - destruct HΣ as [ff [φ [Hφ Hr]]].
        exists ff, (∃φ). split.
        + now constructor 2.
        + intros v. unfold reflecting in Hr. cbn in *. rewrite H0. setoid_rewrite H. now setoid_rewrite Hr. 
      - destruct HΠ as [ff [φ [Hφ Hr]]].
        exists ff, (∀φ). split.
        + now constructor 2.
        + intros v. unfold reflecting in Hr. cbn in *. rewrite H0. setoid_rewrite H. now setoid_rewrite Hr. 
    } {
      intros H k f. apply H. apply isΣΠsem0.
    }
  Qed.

  (** # <a id="isSigmasem_in_isSigmasyn" /> #*)
  Lemma isΣsem_in_isΣsyn :
  decΣ1syn ->
    (forall n k (p: vec nat k -> Prop), isΣsem n p -> n <> 0 -> isΣsyn n p)
  /\ (forall n k (p: vec nat k -> Prop), isΠsem n p -> n <> 0 -> isΠsyn n p).
  Proof.
    intros HdecΔ1%decΣ1syn_incl_1.
    apply isΣsem_isΠsem_mutind; try lia.
    - intros [] k p' p H IH Heq eq. { intros. apply HdecΔ1. econstructor. 2: eassumption. eauto. }
      destruct (IH ltac:(lia)) as [ff [ϕ [IH1 IH2]]].
      exists ff, (∃ ϕ). split.
      + now apply isΠex.
      + revert IH2. unfold reflecting. setoid_rewrite Heq. clear. firstorder.
    - intros [] k p' p H IH Heq eq. { intros. apply HdecΔ1. econstructor. 2: eassumption. eauto. }
      destruct (IH ltac:(lia)) as [ff [ϕ [IH1 IH2]]].
      exists ff, (∀ ϕ). split.
      + now apply isΣall.
      + revert IH2. unfold reflecting. setoid_rewrite Heq. clear. firstorder.
  Qed.

  End ArithmeticalHierarchyEquiv.
