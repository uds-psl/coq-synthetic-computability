(** * Turing Jump *)

From SyntheticComputability.Shared Require Import embed_nat.
From SyntheticComputability.Synthetic Require Import Definitions.

From SyntheticComputability Require Import partial.
Require Import ssreflect Setoid.

Require Import Lia Vector List PeanoNat.
Import ListNotations.
Local Notation vec := Vector.t.

Require Import SyntheticComputability.PostsTheorem.OracleComputability.

Section halting.

  Variable Part : partiality.
  Variable θ : nat -> nat ↛ nat.

  Variable EPF :
      forall f, exists i, forall x n, f x =! n <-> θ i x =! n.

  Definition K c := exists n, θ c c =! n.

  Lemma semidecidable_K : semi_decidable K.
  Proof.
    apply semi_decidable_part_iff_True.
    exists (fun i => bind (θ i i) (fun _ => ret I)).
    intros n. rewrite bind_hasvalue. setoid_rewrite <- ret_hasvalue_iff.
    firstorder.
  Qed.

  Lemma not_semidecidable_compl_K : ~ semi_decidable (compl K).
  Proof.
    intros (f & Hf) % semi_decidable_part_iff_True.
    unfold compl, K in Hf.
    specialize (EPF (fun i => bind (f i) (fun _ => ret 42))) as [i Hi].
    specialize (Hf i). specialize (Hi i).
    setoid_rewrite bind_hasvalue in Hi.
    enough (compl K i <-> K i) by firstorder.
    unfold compl, K. rewrite Hf.
    split.
    - intros. exists 42. apply Hi. exists I. now rewrite <- ret_hasvalue_iff.
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

  Axiom ξ : nat -> (nat ↛ bool) -> (nat ↛ True).

  Axiom ξ_surjective :
    forall f : (nat ↛ bool) -> (nat ↛ True), (continuous_f f) -> exists c, forall r n i, ξ c r n =! i <-> f r n =! i.

  Axiom ξ_cont :
    forall c, continuous_f (ξ c).

  Definition ξ' : nat -> (nat ↛ bool) -> (nat ↛ True) := 
      (fun ic f x => let (i, c) := unembed ic in ξ c f (embed (i, x))).

  Fact ξ'_parametric :
    forall f : nat -> (nat ↛ bool) -> (nat ↛ True), (forall i, continuous_f (f i)) -> exists γ, forall j r n i, ξ' (γ j) r n =! i <-> f j r n =! i.
  Proof.
    intros f cont. unfold ξ'.
    assert (continuous_f (fun f' x => let (k, l) := unembed x in f k f' l)) as contF. {
      intros f' x []. destruct unembed. apply cont.
    }
    destruct (ξ_surjective _ contF) as [c Hc].
    exists (fun i => embed(i, c)). intros i. rewrite embedP.
    intros r n []. rewrite Hc. now rewrite embedP.
  Qed.

  Fact ξ'_surjective (f : (nat ↛ bool) -> (nat ↛ True)) (contF : continuous_f f):
    exists c, forall r n i, ξ' c r n =! i <-> f r n =! i.
  Proof.
    destruct (ξ'_parametric _ (fun _ => contF)) as [γ Hγ].
    now exists (γ 27).
  Qed.

  Fact ξ'_cont :
    forall c, continuous_f (ξ' c).
  Proof.
    intros ⟨i, c⟩. intros f x. unfold ξ'. rewrite E. apply ξ_cont.
  Qed.
  
  Lemma Ξ_spec (c : nat) :
    { om : @oracle_machine Part nat bool nat True | om.(oracle_fun_part) = ξ' c }.
  Proof.
    unshelve eexists. {
      destruct (@core_to_om Part nat nat True Nat.eq_dec) with (C := ξ' c) as [om Hom].
      - intros f x []. apply ξ'_cont.
      - exact om.
    } cbn. now destruct core_to_om.
  Qed.

  Definition Ξ c := proj1_sig (Ξ_spec c).

  Fact parametric (f : nat -> @oracle_machine Part nat bool nat True) : 
    exists γ, forall j R x i, Ξ (γ j) R x i <-> f j R x i.
  Proof.
    destruct (ξ'_parametric _ (fun j => (@oracle_machine_core_coninous _ _ _ _ _ (f j)))) as [γ Hγ].
    exists γ. intros j. apply (eq_core Nat.eq_dec).
    unfold Ξ. destruct (Ξ_spec (γ j)) as [om' eq].
    intros f' x z. specialize (Hγ j).
    rewrite <- eq in Hγ. apply Hγ.
  Qed.

  Fact surjective (om : oracle_machine nat bool nat True) : 
    exists c, forall R x i, Ξ c R x i <-> om R x i.
  Proof.
    destruct (parametric (fun _ => om)) as [γ Hγ].
    now exists (γ 27).
  Qed.
End Ξ.

Opaque Ξ.Ξ.
Notation Ξ := Ξ.Ξ.

Section jump.
  (** ** Synthetic Turing Jump *)

  Definition J Q c := Ξ c (char_rel Q) c I.

  Lemma semidecidable_J Q : oracle_semi_decidable Q (J Q).
  Proof.
    eapply mk_semi_dec with
      (r := fun O c => Ξ c O c I)
      (r' := fun f c => (Ξ c).(oracle_fun_part) f c).
    - intros f R Hf c. now apply Ξ.
    - intros R c. apply Ξ.
    - unfold J. reflexivity.
  Qed.

  Lemma not_semidecidable_compl_J Q : ~ oracle_semi_decidable Q (compl (J Q)).
  Proof.
    intros (om & H). cbn in *.
    specialize (Ξ.surjective om) as [c Hc].
    unfold compl, J in H. specialize (H c).
    rewrite <- Hc in H. tauto.
  Qed.

  (** Complement not semi-decidable ***)

  Definition 𝒥 Q := fun! ⟨c, x⟩ =>  Ξ c (char_rel Q) x I.

  Lemma J_self_𝒥_m_red:
    forall Q, (J Q) ⪯ₘ (𝒥 Q).
  Proof.
    intros Q. exists (fun c => embed(c,c)).
    intros c. unfold J, 𝒥. now rewrite embedP.
  Qed.

  Definition parametric_jump : nat -> oracle_machine nat bool nat True.
  Proof.
    intros ⟨c, x⟩.
    eapply mk𝕄True with (r := fun R _ => Ξ c R x I) (r' := fun f _ => (Ξ c).(oracle_fun_part) f x).
    - intros f R H cx. now apply Ξ.
    - intros R _. apply Ξ.
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
    - intros [om H]. apply red_m_transitive with (𝒥 Q). 2: apply red_𝒥_J_self.
      specialize (Ξ.surjective om) as [c Hc].
      unfold 𝒥.
      exists (fun x => embed (c, x)).
      intros x. rewrite H. rewrite embedP. now rewrite Hc.
    - intros [f Hf]. unfold reduction in Hf.
      unfold oracle_semi_decidable.
      setoid_rewrite Hf.
      eapply mk_semi_dec with 
        (r := fun O c => Ξ (f c) O (f c) I)
        (r' := fun o c => (Ξ (f c)).(oracle_fun_part) o (f c)).
      + intros. now apply Ξ.
      + intros R c. apply Ξ.
      + reflexivity.
  Qed.

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat _ v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat _ (nat_to_vec k n) = n.

  Lemma red_m_iff_semidec_jump_vec {k} (P : vec nat k -> Prop) (Q : nat -> Prop): 
    oracle_semi_decidable Q P <-> P ⪯ₘ (J Q).
  Proof.
    specialize (red_m_iff_semidec_jump (fun n => P (nat_to_vec k n)) Q) as [H1 H2].
    split.
    - intros [[r r' Hr cont] Hom]. cbn in *.
      eapply red_m_transitive with (fun n : nat => P (nat_to_vec k n)). {
        exists (@vec_to_nat k). intros v. now rewrite vec_nat_inv.
      }
      apply H1.
      eapply mk_semi_dec with
        (r := fun R n => r R (nat_to_vec k n ) I)
        (r' := fun f n => r' f (nat_to_vec k n)).
      + intros f R Hf x. now apply Hr.
      + intros R x. apply cont.
      + now setoid_rewrite <- Hom.
    - intros H. specialize (H2 ltac:(eapply red_m_transitive with P, H; now exists (nat_to_vec k))).
      destruct H2 as [[r r' Hr cont] Hom]. cbn in *.
      eapply mk_semi_dec with
        (r := fun R v => r R (vec_to_nat _ v) I)
        (r' := fun f v => r' f (vec_to_nat _ v)).
      + cbn. unfold pcomputes. intros f R Hf x. now apply Hr.
      + intros R x. apply cont.
      + intros v. rewrite <- Hom. now rewrite vec_nat_inv.
  Qed.

  Lemma red_T_imp_red_T_jumps  (P : nat -> Prop) (Q : nat -> Prop): 
    P ⪯ᴛ Q -> (J P) ⪯ᴛ (J Q).
  Proof.
    intros rT. apply red_m_impl_red_T, red_m_iff_semidec_jump.
    eapply semi_dec_turing_red_trans; [apply semidecidable_J|apply rT].
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
