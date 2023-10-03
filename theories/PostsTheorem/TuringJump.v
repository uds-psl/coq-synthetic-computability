(** * Turing Jump *)

From SyntheticComputability.Shared Require Import embed_nat.
From SyntheticComputability Require Import Definitions EPF SemiDec reductions.
Import EmbedNatNotations.

From SyntheticComputability Require Import partial.
Require Import ssreflect Setoid.

Require Import Lia Vector List PeanoNat.
Import ListNotations.
Local Notation vec := Vector.t.

Require Import SyntheticComputability.TuringReducibility.OracleComputability.

Notation compl p := (fun x => ~ p x).

Local Tactic Notation "intros" "⟨" ident(n) "," ident(m) "⟩" :=
  let nm := fresh "nm" in
  let E := fresh "E" in
  intros nm; destruct (unembed nm) as [n m] eqn:E.

Section halting.

  Variable Part : partiality.

  Lemma semi_decidable_part_iff_unit {X} {p : X -> Prop} :
    semi_decidable p <-> exists (f : X -> part unit), forall x, p x <-> f x =! tt.
  Proof.
    split.
    - intros [f Hf].
      exists (fun x : X => mkpart (fun n : nat => if f x n then Some tt else None)).
      intros x.
      rewrite (Hf x). split.
      + intros [n H].
        apply mkpart_hasvalue. {
          intros n1 n2 [] []. destruct (f x n1), (f x n2). all: congruence.
        }
        exists n. now rewrite H.
      + intros [n H]%mkpart_hasvalue1. exists n.
        destruct f; congruence.
    - intros [f Hf]. exists (fun x n => if seval (f x) n is Some _ then true else false).
      intros x. rewrite Hf. split.
      + intros H. eapply seval_hasvalue in H as [n H].
        exists n. now rewrite H.
      + intros [n H]. eapply seval_hasvalue. exists n.
        destruct seval as [[]|]; congruence.
  Qed.

  Variable θ : nat -> nat ↛ nat.

  Variable EPF :
      forall f, exists i, forall x n, f x =! n <-> θ i x =! n.

  Definition K c := exists n, θ c c =! n.

  Lemma semidecidable_K : semi_decidable K.
  Proof.
    apply semi_decidable_part_iff_unit.
    exists (fun i => bind (θ i i) (fun _ => ret tt)).
    intros n. rewrite bind_hasvalue. setoid_rewrite <- ret_hasvalue_iff.
    firstorder.
  Qed.

  Lemma not_semidecidable_compl_K : ~ semi_decidable (compl K).
  Proof.
    intros (f & Hf) % semi_decidable_part_iff_unit.
    unfold K in Hf.
    specialize (EPF (fun i => bind (f i) (fun _ => ret 42))) as [i Hi].
    specialize (Hf i). specialize (Hi i).
    setoid_rewrite bind_hasvalue in Hi.
    enough (compl K i <-> K i) by firstorder.
    unfold K. rewrite Hf.
    split.
    - intros. exists 42. apply Hi. exists tt. now rewrite <- ret_hasvalue_iff.
    - now intros [n [[] H]%Hi].
  Qed.

  Definition θ' := (fun ic x => let (i, c) := unembed ic in θ c (embed (i, x))).

  Theorem EPFP' :
    forall f : nat -> nat ↛ nat, exists γ, forall i x y, θ' (γ i) x =! y <-> f i x =! y.
  Proof.
    intros f. unfold θ'.
    destruct (EPF (fun x => let (k, l) := unembed x in f k l)) as [c Hc].
    exists (fun i => embed(i, c)). intros i x y. rewrite embedP.
    rewrite <- (Hc ⟨i, x⟩). rewrite embedP. reflexivity.
  Qed.

  Definition W' := fun! ⟨c, x⟩ => exists v, θ' c x =! v.
  Definition K' c := exists v, θ' c c =! v.

  Lemma red_W'_K' : 
    exists f, forall x, W' x <-> K' (f x).
  Proof.
    destruct (EPFP' (fun! ⟨c, x⟩ => fun _ => θ' c x)) as [γ Hγ].
    exists γ. unfold W', K'. intros ⟨c, x⟩.
    setoid_rewrite Hγ. rewrite E.
    reflexivity.
  Qed.

End halting.

Section Enumerator.
  (** ** Enumerating Oracle Machines *)

  Context {Part : partiality}.

  Axiom EPF_assm : EPF.
  Definition θ := proj1_sig EPF_assm.
  Definition EPF := proj2_sig EPF_assm.

  Variable O : Type.

  Parameter iota1 : (nat * list bool) -> nat.
  Parameter iota2 : (nat + O) -> nat.
  Parameter rho1 : nat -> nat * list bool.
  Parameter rho2 : nat -> nat + O.

  Parameter bij1 : forall y, (rho1 (iota1 y) = y).
  Parameter bij2 : forall y, (rho2 (iota2 y) = y).

  Definition ξ : nat -> nat -> tree nat bool O :=
    fun c x l => bind (θ c (iota1 (x, l))) (fun v => ret (rho2 v)).

  Lemma ξ_parametric :
    forall τ : nat -> nat -> tree nat bool O, exists γ, forall n l i o, ξ (γ n) i l =! o <-> τ n i l =! o.
  Proof.
    intros τ.
    destruct (EPF (fun n x => let (i,l) := rho1 x in bind (τ n i l) (fun v => ret (iota2 v)))) as [γ H].
    cbn in *. exists γ. intros. cbn in *. unfold partial.equiv in *.
    unfold ξ. rewrite bind_hasvalue.
    setoid_rewrite H.
    setoid_rewrite bij1.
    setoid_rewrite bind_hasvalue.
    setoid_rewrite <- ret_hasvalue_iff.
    firstorder subst.
    now rewrite bij2.
    repeat eexists. eauto. eapply bij2.
  Qed.

  Fact ξ_surjective (τ : nat -> tree nat bool O) :
    exists j, forall l i o, ξ j i l =! o <-> τ i l =! o.
  Proof.
    destruct (ξ_parametric (fun _ => τ)) as [γ Hγ].
    now exists (γ 42).
  Qed.

End Enumerator.

Section SemiDecEnumerator.

  Context {Part : partiality}.

  Definition rel {I A Q} (τ : I -> list A ↛ (Q + unit)) R x :=
    exists qs ans, interrogation (τ x) R qs ans /\ (τ x) ans =! inr tt.

  Definition Ξ c R x := rel (ξ unit c) R x.

  Fact computable :
    OracleComputable (fun R '(c,x) (o : unit) => Ξ c R x).
  Proof.
    exists (fun '(c,x) => ξ unit c x). intros R [c x] [].
    reflexivity.
  Qed.

  Fact parametric (τ : nat -> nat -> list bool ↛ (nat + unit)) :
    exists γ, forall j R x, Ξ (γ j) R x <-> rel (τ j) R x.
  Proof.
    destruct (ξ_parametric τ) as [γ Hγ].
    exists γ. intros j.
    intros. unfold Ξ, rel.
    specialize (Hγ j).
    cbn.
    setoid_rewrite Hγ. firstorder.
    exists x0, x1. split; eauto. eapply interrogation_ext. 2: reflexivity. 2: eassumption.
    firstorder.
    exists x0, x1. split; eauto. eapply interrogation_ext. 2: reflexivity. 2: eauto.
    firstorder.
  Qed.

  Fact surjective (F : (nat -> bool -> Prop) -> nat -> unit -> Prop) (H : OracleComputable F) :
    exists c, forall R x, Ξ c R x <-> F R x tt.
  Proof.
    destruct H as [τ Hτ].
    unshelve edestruct (@parametric) as [γ Hγ].
    - intros _. exact τ. 
    - exists (γ 27). intros. rewrite Hτ Hγ. reflexivity.
  Qed.

End SemiDecEnumerator.

Section TuringRedEnumerator.

  Context {Part : partiality}.

  Definition rel_b {I A Q} (τ : I -> list A ↛ (Q + bool)) R x o :=
    exists qs ans, interrogation (τ x) R qs ans /\ (τ x) ans =! inr o.

  Definition χ c R x := rel_b (ξ bool c) R x.

  Fact computable_b :
    OracleComputable (fun R '(c,x) (o : bool) => χ c R x o).
  Proof.
    exists (fun '(c,x) => ξ bool c x). intros R [c x].
    reflexivity.
  Qed.

  Fact surjective_b (F : (nat -> bool -> Prop) -> nat -> bool -> Prop) (H : OracleComputable F) :
    exists c, forall R x b, χ c R x b <-> F R x b.
  Proof.
    destruct H as [τ Hτ].
    destruct (ξ_surjective τ) as [c Hc].
    exists c. intros. unfold χ, rel_b.
    setoid_rewrite Hτ. setoid_rewrite Hc.
    firstorder.
    exists x0, x1. split; eauto. eapply interrogation_ext. 2: reflexivity. 2: eassumption.
    firstorder.
    exists x0, x1. split; eauto. eapply interrogation_ext. 2: reflexivity. 2: eauto.
    firstorder.
  Qed.

End TuringRedEnumerator.

Module Reverse.

  Context {Part : partiality}.

  Variable χ : nat -> (nat -> bool -> Prop) -> nat -> bool -> Prop.
  Variable computable_b : OracleComputable (fun R '(c,x) (o : bool) => χ c R x o).
  Variable surjective_b : forall (F : (nat -> bool -> Prop) -> nat -> bool -> Prop) (H : OracleComputable F),
    exists c, forall R x b, χ c R x b <-> F R x b.

  Lemma EPF_bool : exists θ : nat -> (nat ↛ bool), forall f : nat ↛ bool,
    exists c, forall x v, θ c x =! v <-> f x =! v.
  Proof.
    destruct computable_b as [τ Hτ].
    unshelve eexists.
    - intros c.
      edestruct @Turing_transports_computable_strong with (F := χ c) as [f Hf].
      intros. rewrite (Hτ R (c,x) o). eapply iff_refl.
      exact (f (fun _ => ret false)).
    - cbn. intros f.
      destruct surjective_b with (F := fun (R : nat -> bool -> Prop) x b => f x =! b) as [c Hc].
      + eapply computable_partial_function. 
      + exists c. intros x v. destruct Turing_transports_computable_strong as [F Hf].
        unfold pcomputes in Hf.
        specialize Hf with (R := fun _ o => o = false).
        rewrite Hf. intros. rewrite <- ret_hasvalue_iff. firstorder congruence.
        eapply Hc.
  Qed.

End Reverse.

(* Opaque Ξ.Ξ. *)

Notation oracle_semi_decidable := OracleSemiDecidable.

Section jump.
  (** ** Synthetic Turing Jump *)

  Context {Part : partiality}.

  Definition J Q c := Ξ c (char_rel Q) c.

  Lemma semidecidable_J Q : oracle_semi_decidable Q (J Q).
  Proof.
    exists (fun O c o => Ξ c O c). split.
    - eapply OracleComputable_ext.
      eapply computable_bind.
      2: eapply computable. 2: cbn.
      eapply computable_ident. cbn.
      intros ? ? []; firstorder subst.
      firstorder.
    - unfold J. reflexivity.
  Qed.

  (** Complement not semi-decidable ***)

  Lemma not_semidecidable_compl_J Q : ~ oracle_semi_decidable Q (compl (J Q)).
  Proof.
    intros (F & Hcomp & H).
    specialize (surjective Hcomp) as [c Hc].
    unfold J in H. specialize (H c).
    rewrite <- Hc in H. tauto.
  Qed.

  Definition 𝒥 Q := fun! ⟨c, x⟩ =>  Ξ c (char_rel Q) x.

  Lemma jump_gt Q :
    Q ⪯ₘ 𝒥 Q /\ (~ compl (J Q) ⪯ᴛ Q).
  Proof.
    split.
    - assert (OracleComputable (fun R (x : nat) (o : unit) => R x true))
               as [c Hc] % surjective.
      { eapply OracleComputable_ext.
        eapply computable_bind. eapply computable_id.
        eapply computable_if with (test := snd).
        eapply computable_ret with (v := tt).
        eapply computable_nothing.
        cbn; split.
        - intros [[]]; firstorder.
        - destruct o. exists true; firstorder.
      }
      exists (fun x => ⟨c,x⟩). intros x. unfold 𝒥. rewrite embedP.
      specialize (Hc (char_rel Q)). cbn in Hc. firstorder.
    - intros H % Turing_to_sdec.
      eapply not_semidecidable_compl_J; eassumption.
  Qed.

  Lemma not_turing_red_J Q: ~ (J Q ⪯ᴛ Q).
  Proof.
    intros H % Turing_to_sdec_compl.
    eapply not_semidecidable_compl_J; eassumption.
  Qed.

  (** # <a id="J_self_J_m_red" /> #*)
  Lemma J_self_𝒥_m_red:
    forall Q, (J Q) ⪯ₘ (𝒥 Q).
  Proof.
    intros Q. exists (fun c => embed(c,c)).
    intros c. unfold J, 𝒥. now rewrite embedP.
  Qed.

  Lemma red_𝒥_J_self Q : 
    𝒥 Q ⪯ₘ J Q.
  Proof.
    destruct (parametric (fun! ⟨c,x⟩ => fun _ => ξ unit c x)) as [γ Hγ].
    exists γ. unfold J, 𝒥. red. setoid_rewrite Hγ. intros ⟨c, x⟩.
    reflexivity. 
  Qed.

  Lemma red_m_iff_semidec_jump (P : nat -> Prop) (Q : nat -> Prop):
    oracle_semi_decidable Q P <-> P ⪯ₘ (J Q).
  Proof.
    split.
    - intros [F [Hom H]]. apply red_m_transitive with (𝒥 Q). 2: apply red_𝒥_J_self.
      specialize (surjective Hom) as [c Hc].
      unfold 𝒥.
      exists (fun x => embed (c, x)).
      intros x. rewrite H. rewrite embedP. now rewrite Hc.
    - intros [f Hf]. unfold reduction in Hf.
      unfold oracle_semi_decidable.
      red in Hf.
      setoid_rewrite Hf.
      exists (fun O c o => Ξ (f c) O (f c)). split.
      + eapply OracleComputable_ext.
        eapply computable_bind.
        2: eapply computable_precompose with (g := fun '(c, i) => (f c, f i)).
        2: eapply computable.
        2: cbn.
        eapply computable_ident.
        intros ? ? []. firstorder subst. firstorder.
      + reflexivity.
  Qed.

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat (nat_to_vec k n) = n.

  Lemma red_m_iff_semidec_jump_vec {k} (P : vec nat k -> Prop) (Q : nat -> Prop): 
    oracle_semi_decidable Q P <-> P ⪯ₘ (J Q).
  Proof.
    specialize (red_m_iff_semidec_jump (fun n => P (nat_to_vec k n)) Q) as [H1 H2].
    split.
    - intros [F [Hcom Hom]]. cbn in *.
      eapply red_m_transitive with (fun n : nat => P (nat_to_vec k n)). {
        exists (@vec_to_nat k). intros v. now rewrite vec_nat_inv.
      }
      apply H1.
      exists (fun R n o => F R (nat_to_vec k n ) tt). split.
      + eapply OracleComputable_ext.
        eapply computable_precompose.
        eapply Hcom. cbn.
        intros ? ? []. reflexivity.
      + now setoid_rewrite <- Hom.
    - intros H. specialize (H2 ltac:(eapply red_m_transitive with P, H; now exists (nat_to_vec k))).
      destruct H2 as [F [Hcom Hom]]. cbn in *.
      exists (fun R v o => F R (vec_to_nat v) tt). split.
      + eapply OracleComputable_ext.
        eapply computable_precompose.
        eapply Hcom. cbn.
        intros ? ? []. reflexivity.
      + intros v. rewrite <- Hom. now rewrite vec_nat_inv.
  Qed.

  Notation "P ⪯ᴛ Q" := (red_Turing P Q) (at level 50).

  Lemma red_T_imp_red_m_jumps  (P : nat -> Prop) (Q : nat -> Prop): 
    P ⪯ᴛ Q -> (J P) ⪯ₘ (J Q).
  Proof.
    intros rT. apply red_m_iff_semidec_jump.
    eapply Turing_transports_sdec; [apply semidecidable_J|apply rT].
  Qed.

End jump.

Notation "A '´'" := (J A) (at level 20, format "A ´").
Notation "­{0}" := (fun x:nat => x=0).

Fixpoint jump_n {Part : partiality} Q n :=
  match n with
  | 0 => Q
  | S n => J (jump_n Q n)
  end.
Notation "A '^(' n ')'" := (jump_n A n) (at level 25, format "A ^( n )").