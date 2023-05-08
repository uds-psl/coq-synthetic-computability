(** * Post's Theorem *)

From SyntheticComputability.Shared Require Import embed_nat.
From SyntheticComputability Require Import TuringReducibility.OracleComputability TuringJump ArithmeticalHierarchySemantic SemiDec reductions.
Require Import Lia List Vector PeanoNat.
Import Vector.VectorNotations.
Local Notation vec := Vector.t.
From SyntheticComputability Require Import partial.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Section PostsTheorem.

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat (nat_to_vec k n) = n.

  Variable list_vec_to_nat : forall k, list (vec nat k) -> nat.
  Variable nat_to_list_vec : forall k, nat -> list (vec nat k).
  Variable list_vec_nat_inv : forall k v, nat_to_list_vec k (list_vec_to_nat v) = v.
  Variable nat_list_vec_inv : forall k n, list_vec_to_nat (nat_to_list_vec k n) = n.

  Variable nat_to_list_bool : nat -> list bool.
  Variable list_bool_to_nat : list bool -> nat.
  Variable list_bool_nat_inv : forall l, nat_to_list_bool (list_bool_to_nat l) = l.
  Variable nat_list_bool_inv : forall n, list_bool_to_nat (nat_to_list_bool n) = n.

  Lemma dec_vec {k} (v v' : vec nat k) :
    {v = v'} + {v <> v'}.
  Proof.
    specialize (Nat.eq_dec (vec_to_nat v) (vec_to_nat v')) as [eq | neq].
    - left. rewrite <- (vec_nat_inv v). rewrite <- (vec_nat_inv v'). now f_equal.
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
    eapply red_m_transports_sdec. 2: apply jumpNKspec.
    eapply Turing_transports_sdec.
    - apply semidecidable_J.
    - apply red_m_impl_red_T, jumpNKspec.
  Qed.

  Lemma Σ_semi_decidable_in_Π1 {k} (p: (vec nat k) -> Prop) n : LEM_Π n ->
      isΣsem (S n) p -> exists (p': vec nat (S k) -> Prop), isΠsem n p' /\ oracle_semi_decidable p' p.
  Proof.
    intros lem H. depelim H.  rename p0 into p'. rename H into Hp'.
    exists p'. split;[easy|].
    exists (fun R v o => exists n, R (n::v) true /\ forall n', n' < n -> R (n' :: v) false). split.
    2:{ cbn. intros. split.
        2: firstorder.
        intros H.
        eapply Wf_nat.dec_inh_nat_subset_has_unique_least_element in H as [m [[H1 H2] H3]].
        2:{ intros n0. eapply (lem _ _ Hp' (n0 :: x)). }
        firstorder lia.
    }
    eapply OracleComputable_ext.
    eapply computable_bind.
    eapply computable_comp.
    2: eapply computable_search. all: cbn.
    2: eapply computable_ret with (v := tt).
    eapply computable_precompose with (g := fun '(v,x) => x :: v).
    eapply computable_id.
    intros ? ? []; cbn; firstorder.
  Qed.

  Lemma interrogation_is_Π (k n : nat) (p' : vec nat (S k) -> Prop) (τ : vec nat k -> tree (vec nat (S k)) bool unit) :
      isΠsem n p' ->
        isΠsem n
          (fun v : vec nat (S k) => let (qs, ans) := unembed (hd v) in let v0 := tl v in interrogation (τ v0) (char_rel p') (nat_to_list_vec (S k) qs) (nat_to_list_bool ans)).
  Proof.
  Admitted.

  Lemma Σ_semi_decidable_in_Π2 {k} (p: (vec nat k) -> Prop) n (DN : DNE_Σ n):
    (exists (p': vec nat (S k) -> Prop), isΠsem n p' /\ oracle_semi_decidable p' p) -> isΣsem (S n) p.
  Proof.
    intros [p' [Πp' [om [[τ Hom] H]]]].
    erewrite PredExt. 2: apply H.
    erewrite PredExt. 2: intros v; apply Hom.
    unshelve erewrite PredExt. { intros v. apply (exists num : nat,
      (fun v => (fun v => let (qs, ans) := unembed (hd v) in let v := (tl v) in
         interrogation (τ v) (char_rel p') (nat_to_list_vec (S k) qs) (nat_to_list_bool ans)) v
             /\ (fun v => let (qs, ans) := unembed (hd v) in let v := (tl v) in τ v (nat_to_list_bool ans) =! inr tt) v)
       (num :: v)). }
    2: { intros v. split.
         - intros (qs & ans & H1 & H2).
           exists (embed (list_vec_to_nat qs, (list_bool_to_nat ans))).
           rewrite eqhd. repeat rewrite embedP. rewrite eqtl. cbn.
           rewrite !list_vec_nat_inv, !list_bool_nat_inv. eauto.
         - intros [num Hn]. rewrite eqhd in Hn.
           destruct (unembed num) as [qs ans].
           rewrite eqtl in Hn. cbn in Hn.
           eauto.
      } apply isΣsemE.
      repeat apply isΣsem_and_closed.
      - eapply isΣΠn_In_ΠΣSn. now eapply interrogation_is_Π.
      - replace (S n) with (n + 1) by lia. eapply isΣΠn_In_ΣΠSn.
        eapply semi_dec_iff_Σ1.
        exists (fun v i => let (_, ans) := unembed (hd v) in let v0 := tl v in
                                                     match seval (τ v0 (nat_to_list_bool ans)) i with
                                                     | Some (inr _) => true
                                                     | _ => false
                                                     end).
        red. intros x. destruct unembed. rewrite seval_hasvalue.
        firstorder. eexists. rewrite H0. reflexivity.
        destruct seval as [ [ | [] ] | ]eqn:E; eauto.
  Qed.

  Lemma Σ_semi_decidable_in_Π {k} (p: (vec nat k) -> Prop) n (DN : LEM_Σ n) :
    isΣsem (S n) p <-> exists (p': vec nat (S k) -> Prop), isΠsem n p' /\ oracle_semi_decidable p' p.
  Proof.
    split; apply Σ_semi_decidable_in_Π1 + apply Σ_semi_decidable_in_Π2.
    now eapply LEM_Σ_to_LEM_Π.
    now eapply LEM_Σ_to_DNE_Σ.
  Qed.

  Hint Resolve DNEimpl.

  Lemma Σ_semi_decidable_in_Σ {k} (p: (vec nat k) -> Prop) n (DN : LEM_Σ n) :
      isΣsem (S n) p <-> exists (p': vec nat (S k) -> Prop), isΣsem n p' /\ oracle_semi_decidable p' p.
  Proof.
    rewrite Σ_semi_decidable_in_Π; eauto.
    split.
    - intros [p' [H S]]. eapply negΣinΠsem in H as H'.
      2: now eapply LEM_Σ_to_DNE_Σ.
      eexists. split;[apply H'|].
      rewrite <- oracle_semi_decidable_complement_iff. eauto.
      eapply DNEimpl; eauto.
      now eapply LEM_Σ_to_DNE_Σ.
    - intros [p' [H S]]. eapply negΣinΠsem in H as H'; eauto.
      eexists. split;[apply H'|].
      rewrite <- oracle_semi_decidable_complement_iff; eauto.
      eapply LEM_Σ_to_DNE_Σ in DN.
      eapply DN; eauto.
      now eapply DNEimpl, LEM_Σ_to_DNE_Σ.
  Qed.

  Lemma jump_in_Σn n {k} (DN : LEM_Σ n) :
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

  Lemma jump_Σn_complete n (DN : LEM_Σ n) :
    forall k (p : vec nat k -> Prop), isΣsem (S n) p -> p ⪯ₘ (­∅^(S n)).
  Proof.
    induction n as [|n IH].
    - intros k p H.
      apply (@red_m_iff_semidec_jump_vec vec_to_nat nat_to_vec vec_nat_inv).
      eapply semi_decidable_OracleSemiDecidable. 
      now apply semi_dec_iff_Σ1.
    - intros k p [p' [Σp' Sp']]%Σ_semi_decidable_in_Σ.
      apply (@red_m_iff_semidec_jump_vec vec_to_nat nat_to_vec vec_nat_inv).
      eapply (Turing_transports_sdec Sp').
      apply red_m_impl_red_T. eapply IH; eauto.
      all: eauto.
      { intros n' q Hq. eapply DN. now eapply isΣΠn_In_ΣΠSn with (l := 1). }
  Qed.

  Lemma jump_Σn_complete_redT n (DN : LEM_Σ n) :
    forall k (p : vec nat k -> Prop), isΣsem n p -> p ⪯ᴛ (­∅^(n)).
  Proof.
    intros k p H. destruct n.
    - dependent destruction H.
      eexists. split.
      eapply computable_function with (f := f).
      cbn. intros x []. reflexivity. cbn. destruct (f x); firstorder congruence.
    - apply red_m_impl_red_T. eapply jump_Σn_complete; eauto.
      { intros n' q Hq. eapply DN. now eapply isΣΠn_In_ΣΠSn with (l := 1). }
  Qed.

  Lemma Σ_semi_decidable_jump {k} (p: (vec nat k) -> Prop) n (DN : LEM_Σ n) :
      isΣsem (S n) p <-> oracle_semi_decidable (­∅^(n)) p.
  Proof.
    split.
    - intros [p' [Σp' Sp']]%Σ_semi_decidable_in_Σ.
      eapply (Turing_transports_sdec Sp').
      eapply jump_Σn_complete_redT.
      all: eauto.
    - intros H. apply Σ_semi_decidable_in_Σ; eauto.
      exists (∅^[n]). split.
      + apply jump_in_Σn; eauto.
      + apply (Turing_transports_sdec H), red_m_impl_red_T, jumpNKspec.
  Qed.

  Theorem PostsTheorem {k} (p: (vec nat k) -> Prop) n (DN : LEM_Σ n) :
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
