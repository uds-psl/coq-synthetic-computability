(** * Post's Theorem *)

From SyntheticComputability.Shared Require Import embed_nat.
From SyntheticComputability.PostsTheorem Require Import OracleComputability TuringJump ArithmeticalHierarchySemantic.
Require Import Lia List Vector PeanoNat.
Import Vector.VectorNotations.
Local Notation vec := Vector.t.
From SyntheticComputability Require Import partial.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Section PostsTheorem.

  (* Axiom LEM : forall p, p \/ ~p. *)

  (* Lemma DN p : ~~p -> p. Proof. now destruct (LEM p). Qed. *)

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat k v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat k (nat_to_vec k n) = n.

  Variable list_vec_to_nat : forall k, list (vec nat k) -> nat.
  Variable nat_to_list_vec : forall k, nat -> list (vec nat k).
  Variable list_vec_nat_inv : forall k v, nat_to_list_vec k (list_vec_to_nat k v) = v.
  Variable nat_list_vec_inv : forall k n, list_vec_to_nat k (nat_to_list_vec k n) = n.

  Lemma dec_vec {k} (v v' : vec nat k) :
    {v = v'} + {v <> v'}.
  Proof.
    specialize (Nat.eq_dec (vec_to_nat k v) (vec_to_nat k v')) as [eq | neq].
    - left. rewrite <- (vec_nat_inv k v). rewrite <- (vec_nat_inv k v'). now f_equal.
    - right. now intros ->.
  Qed.

  Definition jumpNK (n : nat) {k : nat} (v : vec nat (S k)) :=
    (fix jumpNK {k} (v : vec nat k) :=
    match v with
    | [] => False
    | x::[] => ­∅^(n) x
    | x::v' => jumpNK v'
    end) (S k) v.

  Notation "'∅^[' n ',' k ']'" := (@jumpNK n k) (at level 25, format "∅^[ n , k ]").
  Notation "'∅^[' n ']'" := (jumpNK n) (at level 25, format "∅^[ n ]").

  Lemma jumpNKspec n {k} :
    ∅^[n,k] ⪯ₘ ­∅^(n) /\ ­∅^(n) ⪯ₘ ∅^[n,k].
  Proof.
    induction k as [|k IH].
    - split.
      + exists (fun v => hd v). intros v. now repeat dependent destruction v.
      + now exists (fun x => x::[]).
    - split.
      + eapply red_m_transitive. 2: apply IH.
        exists tl. intros v. now do 2 dependent destruction v.
      + eapply red_m_transitive. 1: apply IH.
        exists (fun v => 27::v). intros v. now do 2 dependent destruction v.
  Qed.

  Lemma jumpNK0 {k} (v : vec nat (S k)):
    ∅^[0] v <-> False.
  Proof.
    induction k.
    - now repeat dependent destruction v.
    - do 2 dependent destruction v.
      now rewrite <- (IHk (h0::v)).
  Qed.

  Lemma jumpNKSemiDec n {k1 k2}:
    oracle_semi_decidable (∅^[n,k1]) (∅^[S n,k2]).
  Proof.
    eapply semi_decidable_m_red. 1: apply jumpNKspec.
    eapply semi_dec_turing_red_trans.
    - apply semidecidable_J.
    - apply red_m_impl_red_T, jumpNKspec.
  Qed.

  Lemma Σ_semi_decidable_in_Π1 {k} (p: (vec nat k) -> Prop) n:
      isΣsem (S n) p -> exists (p': vec nat (S k) -> Prop), isΠsem n p' /\ oracle_semi_decidable p' p.
  Proof.
    intros H. inversion H as [| n' k' p' Hp' eqN eqk eqp]; subst.
    exists p'. split;[easy|].
    unshelve eapply mk_semi_dec with
    (r := fun R v => exists n, R (n::v) true)
    (r' := fun f v => mkpart (fun! ⟨x,m⟩ => match seval (f (x::v)) m with
      | Some true => Some I 
      | _ => None
    end)).
    + intros f R Hf v. rewrite mkpart_hasvalue;[|intros ? ? [] []; reflexivity].
      split.
      * intros [em H']. destruct unembed as [x m]. exists x.
        destruct seval as [[]|] eqn:eq; try congruence.
        apply Hf. apply seval_hasvalue. eauto.
      * intros [x H'%Hf].
        apply seval_hasvalue in H' as [m Hf'].
        exists (embed (x, m)).
        rewrite embedP.
        destruct seval as [[]|] eqn:eq; congruence.
    + intros R v [x Hx]. exists (List.cons (x::v) List.nil).
      split; [exists true|]; firstorder congruence.
    + now apply Eqdep.EqdepTheory.inj_pair2 in eqp as <-.
  Qed.

  Lemma Σ_semi_decidable_in_Π2 {k} (p: (vec nat k) -> Prop) n (DN : DNE_Σ n):
    (exists (p': vec nat (S k) -> Prop), isΠsem n p' /\ oracle_semi_decidable p' p) -> isΣsem (S n) p.
  Proof.
    intros [p' [Πp' [om Hom]]].
    erewrite PredExt. 2: apply Hom.

    erewrite PredExt. 2: intros v; apply (oracle_iff_exists_LT_LF dec_vec). destruct om as [r r' Hr cont]. cbn in *.
    unshelve erewrite PredExt. { intros v. apply (exists LTLFx : nat, 
      (fun v =>
      ((fun v => let (LT, LFx) := unembed (hd v) in let (LF, x) := unembed LFx in let v := (tl v) in 
        List.Forall p' (nat_to_list_vec (S k) LT)) v) /\
      ((fun v => let (LT, LFx) := unembed (hd v) in let (LF, x) := unembed LFx in let v := (tl v) in
        List.Forall (fun y => ~p' y) (nat_to_list_vec (S k) LF)) v) /\
      (fun v => let (LT, LFx) := unembed (hd v) in let (LF, x) := unembed LFx in let v := (tl v) in
        seval (r' (oracle_from_lists dec_vec (nat_to_list_vec (S k) LT) (nat_to_list_vec (S k) LF)) v) x = Some I) v) (LTLFx::v)). }
      2: {
        setoid_rewrite seval_hasvalue.
        intros v. split.
        - intros [LT [LF [H1 [H2 [x H3]]]]].
          exists (embed ((list_vec_to_nat _ LT), embed((list_vec_to_nat _ LF), x))).
          rewrite eqhd. repeat rewrite embedP. rewrite eqtl. cbn.
          repeat rewrite List.Forall_forall.
          now repeat rewrite (list_vec_nat_inv).
        - intros [LTLFx H]. rewrite eqhd in H. rewrite eqtl in H.
          destruct (unembed LTLFx) as [LT LFx].
          destruct (unembed LFx) as [LF x].
          exists (nat_to_list_vec _ LT), (nat_to_list_vec _ LF).
          repeat rewrite <- List.Forall_forall.
          repeat split. 3: eexists. all: apply H.
      } apply isΣsemE.
      repeat apply isΣsem_and_closed.
      - clear DN.
        eapply isΣsem_m_red_closed. { apply isΣΠn_In_ΠΣSn in Πp'. eapply (isΣsemListΣ vec_nat_inv), Πp'. }
        exists (fun v => let (LT, LFx) := unembed (hd v) in LT::(tl v)).
        intros v. dependent destruction v. rewrite eqhd. now destruct unembed; destruct unembed.
      - eapply isΣsem_m_red_closed. { eapply negΣinΠsem, (isΣΠn_In_ΣΠSn 1) in Πp'. apply (isΣsemListΣ vec_nat_inv), Πp'. exact DN. }
        exists (fun v => let (_, LFx) := unembed (hd v) in let (LF, _) := unembed LFx in LF::(tl v)).
        intros v. dependent destruction v. rewrite eqhd. now destruct unembed; destruct unembed.
      - clear DN. erewrite PredExt with (g := fun v => (fun v => let (LT, LFx) := unembed (hd v) in
        let (LF, x) := unembed LFx in
        let v0 := tl v in
        match seval (A:=True)
        (r' (oracle_from_lists dec_vec (nat_to_list_vec (S k) LT)
                (nat_to_list_vec (S k) LF)) v0) x
        with Some _ => true | None => false end) v = true).
        + apply isΣΠsem0.
        + intros v. dependent destruction v. rewrite eqhd. rewrite eqtl.
          destruct unembed. destruct unembed. destruct seval; split; now destruct t + intros [=].
  Qed.

  Lemma Σ_semi_decidable_in_Π {k} (p: (vec nat k) -> Prop) n (DN : DNE_Σ n) :
    isΣsem (S n) p <-> exists (p': vec nat (S k) -> Prop), isΠsem n p' /\ oracle_semi_decidable p' p.
  Proof.
    split; apply Σ_semi_decidable_in_Π1 + apply Σ_semi_decidable_in_Π2. eauto.
  Qed.

  Hint Resolve DNEimpl.

  Lemma Σ_semi_decidable_in_Σ {k} (p: (vec nat k) -> Prop) n (DN : DNE_Σ n) :
      isΣsem (S n) p <-> exists (p': vec nat (S k) -> Prop), isΣsem n p' /\ oracle_semi_decidable p' p.
  Proof.
    rewrite Σ_semi_decidable_in_Π; eauto.
    split.
    - intros [p' [H S]]. eapply negΣinΠsem in H as H'.
      2:assumption.
      eexists. split;[apply H'|].
      rewrite <- oracle_semi_decidable_complement_iff. eauto.
      eapply DNEimpl; eauto.
    - intros [p' [H S]]. eapply negΣinΠsem in H as H'; eauto.
      eexists. split;[apply H'|].
      rewrite <- oracle_semi_decidable_complement_iff; eauto.
      eapply DN; eauto.
  Qed.

  Lemma jump_in_Σn n {k} (DN : DNE_Σ n) :
    @isΣsem n (S k) (∅^[n]).
  Proof.
    induction n as [|n IH] in k, DN |-*.
    - rewrite PredExt with (g := fun _ => false=true). { apply isΣsem0. } setoid_rewrite jumpNK0. clear. firstorder congruence.
    - apply Σ_semi_decidable_in_Σ; eauto.
      { intros n' p Hp. eapply DN. now eapply isΣΠn_In_ΣΠSn with (l := 1). }
      exists (jumpNK n). split; [apply IH|].
      { intros n' p Hp. eapply DN. now eapply isΣΠn_In_ΣΠSn with (l := 1). }
      apply jumpNKSemiDec.
  Qed.

  Lemma jump_Σn_complete n (DN : DNE_Σ n) :
    forall k (p : vec nat k -> Prop), isΣsem (S n) p -> p ⪯ₘ (­∅^(S n)).
  Proof.
    induction n as [|n IH].
    - intros k p H.
      apply (red_m_iff_semidec_jump_vec vec_to_nat nat_to_vec vec_nat_inv).
      apply no_oracle_semi_decidable. { exists (fun _ => false). split; [intros [] |intros [=]]. }
      now apply semi_dec_iff_Σ1.
    - intros k p [p' [Σp' Sp']]%Σ_semi_decidable_in_Σ.
      apply (red_m_iff_semidec_jump_vec vec_to_nat nat_to_vec vec_nat_inv).
      eapply (semi_dec_turing_red_trans Sp').
      apply red_m_impl_red_T. eapply IH; eauto.
      all: eauto.
      { intros n' q Hq. eapply DN. now eapply isΣΠn_In_ΣΠSn with (l := 1). }
  Qed.

  Lemma jump_Σn_complete_redT n (DN : DNE_Σ n) :
    forall k (p : vec nat k -> Prop), isΣsem n p -> p ⪯ᴛ (­∅^(n)).
  Proof.
    intros k p H. destruct n.
    - dependent destruction H.
      unshelve eexists. {
        unshelve econstructor.
        - intros _. apply (@Build_FunRel _ _ (fun v b => f v = b)). { now intros ? ? ? -> ->. }
        - intros _ v. apply ret, f, v.
        - intros f' ? _ x b. cbn. now rewrite ret_hasvalue_iff.
        - intros ? ? ?. now exists List.nil.
      } cbn. intros x []. reflexivity. now destruct f.
    - apply red_m_impl_red_T. eapply jump_Σn_complete; eauto.
      { intros n' q Hq. eapply DN. now eapply isΣΠn_In_ΣΠSn with (l := 1). }
  Qed.

  Lemma Σ_semi_decidable_jump {k} (p: (vec nat k) -> Prop) n (DN : DNE_Σ n) :
      isΣsem (S n) p <-> oracle_semi_decidable (­∅^(n)) p.
  Proof.
    split.
    - intros [p' [Σp' Sp']]%Σ_semi_decidable_in_Σ.
      eapply (semi_dec_turing_red_trans Sp').
      eapply jump_Σn_complete_redT.
      all: eauto.
    - intros H. apply Σ_semi_decidable_in_Σ; eauto.
      exists (∅^[n]). split.
      + apply jump_in_Σn; eauto.
      + apply (semi_dec_turing_red_trans H), red_m_impl_red_T, jumpNKspec.
  Qed.

  Theorem PostsTheorem {k} (p: (vec nat k) -> Prop) n (DN : DNE_Σ n) :
    (isΣsem (S n) p <-> exists (p': vec nat (S k) -> Prop), isΠsem n p' /\ oracle_semi_decidable p' p)
 /\ (isΣsem (S n) p <-> exists (p': vec nat (S k) -> Prop), isΣsem n p' /\ oracle_semi_decidable p' p)
 /\ (@isΣsem n (S k) (∅^[n]))
 /\ (isΣsem (S n) p -> p ⪯ₘ (­∅^(S n)))
 /\ (isΣsem n p -> p ⪯ᴛ (­∅^(n)))
 /\ (isΣsem (S n) p <-> oracle_semi_decidable (­∅^(n)) p).
  Proof with eauto.
    split; [|split]; [| |split]; [| | |split]; [| | | |split].
    - apply Σ_semi_decidable_in_Π...
    - apply Σ_semi_decidable_in_Σ...
    - apply jump_in_Σn...
    - apply jump_Σn_complete...
    - apply jump_Σn_complete_redT...
    - apply Σ_semi_decidable_jump...
  Qed.
  Print Assumptions PostsTheorem.


End PostsTheorem.
