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

Module Ξ.
  (** ** Enumerating Oracle Machines *)

  Context {Part : partiality}.

  Variable EPF_assm : EPF.
  Definition θ := proj1_sig EPF_assm.
  Definition EPF := proj2_sig EPF_assm.

  Variable ξ : nat -> nat -> tree nat bool unit.

  Axiom ξ_surjective :
    forall τ : nat -> tree nat bool unit, exists c, forall l i o, ξ c i l =! o <-> τ i l =! o.

  Definition ξ' : nat -> nat -> tree nat bool unit :=
      (fun ic x l => let (i, c) := unembed ic in ξ c (embed (i, x)) l).


  Fact ξ'_parametric :
    forall f : nat -> nat -> tree nat bool unit, exists γ, forall j l i o, ξ' (γ j) i l =! o <-> f j i l =! o.
  Proof.
    intros f. unfold ξ'.
    destruct (ξ_surjective (fun ji l => let (j, i) := unembed ji in f j i l)) as [c Hc].
    exists (fun i => embed(i, c)). intros i. rewrite embedP.
    intros r n ?. rewrite Hc. now rewrite embedP.
  Qed.

  Fact ξ'_surjective (τ : nat -> tree nat bool unit) :
    exists j, forall l i o, ξ' j i l =! o <-> τ i l =! o.
  Proof.
    destruct (ξ'_parametric (fun _ => τ)) as [γ Hγ].
    now exists (γ 27).
  Qed.

  Lemma Ξ_spec (c : nat) :
    { F : (nat -> bool -> Prop) -> nat -> unit -> Prop | forall R x o, F R x o <-> (exists (qs : list _) (ans : list _), interrogation (ξ' c x) R qs ans /\ ξ' c x ans =! inr o)}.
  Proof.
    pose (τ := ξ' c).
    exists (fun R i o => (exists (qs : list _) (ans : list _), interrogation (τ i) R qs ans /\ τ i ans =! inr o)).
    reflexivity.
  Qed.

  Definition Ξ c := proj1_sig (Ξ_spec c).

  Fact computable :
    OracleComputable (fun R '(c,i) o => Ξ c R i o).
  Proof.
    exists (fun '(c,i) => ξ' c i). intros R [c i] [].
    unfold Ξ. destruct Ξ_spec as [F H]; cbn in *.
    eapply H.
  Qed.

  Notation oracle_machine Q A I O := {F : (Q -> A -> Prop) -> I -> O -> Prop & {τ | forall R i o, F R i o <-> (exists (qs : list _) (ans : list _), interrogation (τ i) R qs ans /\ τ i ans =! inr o)}}.

  Fact parametric (f : nat -> oracle_machine nat bool nat unit) :
    exists γ, forall j R x i, Ξ (γ j) R x i <-> projT1 (f j) R x i.
  Proof.
    destruct (ξ'_parametric (fun c => proj1_sig (projT2 (f c)))) as [γ Hγ].
    exists γ. intros j. 
    unfold Ξ. destruct (Ξ_spec (γ j)) as [om' eq].
    intros f' x z. specialize (Hγ j).
    cbn.
    rewrite eq. symmetry.
    rewrite (proj2_sig (projT2 (f j))).
    setoid_rewrite Hγ.
    destruct (f j) as [? []]; cbn in *.
    firstorder.
    exists x2, x3. split; eauto. eapply interrogation_ext; eauto.
    exists x2, x3. split; eauto. eapply interrogation_ext. 3: eauto. 2: eauto.
    firstorder.
  Qed.

  Fact surjective (F : (nat -> bool -> Prop) -> nat -> unit -> Prop) (H : OracleComputable F) :
    exists c, forall R x i, Ξ c R x i <-> F R x i.
  Proof.
    destruct H as [τ Hτ].
    unshelve edestruct (@parametric) as [γ Hγ].
    - intros _. exists F. exists τ. eauto.
    - now exists (γ 27).
  Qed.

  Lemma parametric_jump' c x :
    ∑ τ : nat -> (list bool) ↛ (nat + unit),
        forall (R : nat -> bool -> Prop) (i : nat) (o : unit), Ξ c R x tt <-> (exists (qs : list nat) (ans : list bool), interrogation (τ i) R qs ans /\ τ i ans =! inr o).
  Proof.
    unfold Ξ. destruct (Ξ_spec c) as [F HF]. cbn.
    exists (fun _ => ξ' c x). intros ? ? []. eapply HF.
  Qed.

End Ξ.

Opaque Ξ.Ξ.
Notation Ξ := Ξ.Ξ.

Notation oracle_semi_decidable := OracleSemiDecidable.

Section jump.
  (** ** Synthetic Turing Jump *)

  Definition J Q c := Ξ c (char_rel Q) c tt.

  Lemma semidecidable_J Q : oracle_semi_decidable Q (J Q).
  Proof.
    exists (fun O c o => Ξ c O c tt). split.
    - eapply OracleComputable_ext.
      eapply computable_bind.
      2: eapply Ξ.computable. 2: cbn.
      eapply computable_ident. cbn.
      intros ? ? []; firstorder subst.
      assumption.
    - unfold J. reflexivity.
  Qed.

  Lemma not_semidecidable_compl_J Q : ~ oracle_semi_decidable Q (compl (J Q)).
  Proof.
    intros (F & Hcomp & H). 
    specialize (Ξ.surjective Hcomp) as [c Hc].
    unfold J in H. specialize (H c).
    rewrite <- Hc in H. tauto.
  Qed.

  (** Complement not semi-decidable ***)

  Definition 𝒥 Q := fun! ⟨c, x⟩ =>  Ξ c (char_rel Q) x tt.

  Lemma J_self_𝒥_m_red:
    forall Q, (J Q) ⪯ₘ (𝒥 Q).
  Proof.
    intros Q. exists (fun c => embed(c,c)).
    intros c. unfold J, 𝒥. now rewrite embedP.
  Qed.

  Notation oracle_machine Q A I O := {F : (Q -> A -> Prop) -> I -> O -> Prop & {τ | forall R i o, F R i o <-> (exists (qs : list _) (ans : list _), interrogation (τ i) R qs ans /\ τ i ans =! inr o)}}.

  Definition parametric_jump : nat -> oracle_machine nat bool nat unit.
  Proof.
    intros ⟨c, x⟩.
    exists (fun R _ o => Ξ c R x tt).
    eapply Ξ.parametric_jump'.
  Defined.

  Lemma red_𝒥_J_self Q : 
    𝒥 Q ⪯ₘ J Q.
  Proof.
    destruct (Ξ.parametric parametric_jump) as [γ Hγ].
    exists γ. unfold J, 𝒥. intros ⟨c, x⟩.
    setoid_rewrite Hγ. unfold parametric_jump. rewrite E. cbn.
    reflexivity.
  Qed.

  Lemma red_m_iff_semidec_jump (P : nat -> Prop) (Q : nat -> Prop): 
    oracle_semi_decidable Q P <-> P ⪯ₘ (J Q).
  Proof.
    split.
    - intros [om [Hom H]]. apply red_m_transitive with (𝒥 Q). 2: apply red_𝒥_J_self.
      specialize (Ξ.surjective Hom) as [c Hc].
      unfold 𝒥.
      exists (fun x => embed (c, x)).
      intros x. rewrite H. rewrite embedP. now rewrite Hc.
    - intros [f Hf]. unfold reduction in Hf.
      unfold oracle_semi_decidable.
      red in Hf.
      setoid_rewrite Hf.
      exists (fun O c o => Ξ (f c) O (f c) tt). split.
      + eapply OracleComputable_ext.
        eapply computable_bind.
        2: eapply computable_precompose with (g := fun '(c, i) => (f c, f i)).
        2: eapply Ξ.computable.
        2: cbn.
        eapply computable_ident.
        intros ? ? []. firstorder subst. auto.
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

  Lemma red_m_impl_red_T {X Y} (p : X -> Prop) (q : Y -> Prop) :
    p ⪯ₘ q -> p ⪯ᴛ q.
  Proof.
    intros [f Hf].
    eexists. split.
    eapply computable_precompose with (g := f).
    eapply computable_id. cbn.
    intros ? []; firstorder.
  Qed.

  Lemma red_T_imp_red_T_jumps  (P : nat -> Prop) (Q : nat -> Prop): 
    P ⪯ᴛ Q -> (J P) ⪯ᴛ (J Q).
  Proof.
    intros rT. apply red_m_impl_red_T, red_m_iff_semidec_jump.
    eapply Turing_transports_sdec; [apply semidecidable_J|apply rT].
  Qed.

End jump.

Notation "A '´'" := (J A) (at level 20, format "A ´").
Notation "­∅" := (fun _:nat => False).

Fixpoint jump_n Q n :=
  match n with
  | 0 => Q
  | S n => J (jump_n Q n)
  end.
Notation "A '^(' n ')'" := (jump_n A n) (at level 25, format "A ^( n )").
