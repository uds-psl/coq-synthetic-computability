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


  Notation "f ↓" := (f = Some ()) (at level 30).

  Global Instance dec_le: ∀ m n, dec (m ≤ n).
  Proof. intros n m; destruct (le_gt_dec n m); [by left|right; lia]. Qed.

Section Requirements_Lowness_Correctness.

  Variable P: nat → Prop.
  Variable f: nat → nat → bool.
  Hypothesis S_P: stable_semi_decider P f.

  Definition Φ_ := (Φ_ f).

  Fact Φ_spec e x: Ξ e (char_rel P) x → ∞∀ n, Φ_ e x n ↓.
  Proof. intro H. unfold Φ_. apply (Φ_spec S_P H). Qed.

  Definition Ω e n := Φ_ e e n.

  Section classic_logic.

  Hypothesis N_requirements: ∀ e, (∞∃ n, Ω e n ↓) → Ξ e (char_rel P) e.
  Definition limit_decider e n: bool := Dec (Ω e n ↓).

  Section with_LEM_2.

  Hypothesis LEM_Σ_2: 
  ∀ (P: nat → nat → Prop), (∀ n m, dec (P n m)) → (∃ n, ∀ m, P n m) ∨ ¬ (∃ n, ∀ m, P n m).

  Hypothesis LEM_Π_2: 
  ∀ (P: nat → nat → Prop), (∀ n m, dec (P n m)) → (∀ n, ∃ m, P n m) ∨ ¬ (∀ n, ∃ m, P n m).

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
    exfalso. eapply H0. by exists i.
  Qed.

  Lemma Jump_limit : limit_computable (P´).
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
  End with_LEM_2.

  Section with_LEM_1.
  
  Hypothesis convergent: ∀ e, (∞∀ n, Ω e n ↓) ∨ (∞∀ n, ¬ Ω e n ↓).

  Lemma Jump_limit_1 : limit_computable (P´).
  Proof.
    exists limit_decider; split; intros.
    - unfold J. split. 
      intros [w Hw]%Φ_spec; exists w; intros??.
      apply Dec_auto. by eapply Hw.
      intros [N HN]. eapply N_requirements. 
      intros m. exists (S N + m); split; first lia.
      eapply Dec_true. eapply HN. lia.
    - unfold J. split; intros H. 
      destruct (convergent x) as [[k Hk]|h2].
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
  End with_LEM_1.
    
  End classic_logic.
(* 
  Section intuitionistic_logic.
  Hypothesis N_requirements: ∀ e, (∞∃ n, Ω e n ↓) → ¬¬ Ξ e (char_rel P) e.

  Lemma N_requirements': ∀ e, ¬¬ ((∞∃ n, Ω e n ↓) → Ξ e (char_rel P) e).
  Proof. firstorder. Qed.

  Fact dn_or (R Q: Prop): (¬¬ R ∨ ¬¬ Q) → ¬¬ (R ∨ Q).
  Proof. firstorder. Qed.
  Lemma not_not_limit_case e: ~ ~ ((∞∀ n, Ω e n ↓) ∨ (∞∀ n, ¬ Ω e n ↓)).
  Proof.
    ccase (∃ n, ∀ m, n ≤ m → ¬ Ω e m ↓) as [H1|H1].
    apply dn_or. { right. eauto. }
    ccase (∀ i, ∃ n, i ≤ n ∧ Ω e n ↓) as [H2|H2].
    intros H_. apply (@N_requirements' e).
    intros N_requirements'.
    apply H_. left. apply Φ_spec, N_requirements'. intros i.
    { destruct (H2 i) as [w Hw]. exists w. apply Hw.  }
    exfalso. clear P S_P N_requirements.
    apply H2. intros i.
  Admitted.
  
    Definition not_not_limit_computable {X} (P: X -> Prop) :=
      exists f: X -> nat -> bool, 
        forall x, ~~
        ((P x <-> exists N, forall n, n >= N -> f x n = true) /\
          (~ P x <-> exists N, forall n, n >= N -> f x n = false)).

    Fact dn_and (R Q: Prop): (¬¬ R ∧ ¬¬ Q) → ¬¬ (R ∧ Q).
    Proof. firstorder. Qed.

    Lemma not_not_Jump_limit : not_not_limit_computable (P´).
    Proof.
      exists limit_decider; intro x.
      apply dn_and.   
      split; intros.
      - unfold J. intros H_.
        eapply (@N_requirements' x). intros N_requirements'.
        apply H_. split.
        intros [w Hw]%Φ_spec; exists w; intros??.
        apply Dec_auto. by eapply Hw.
        intros [N HN].
        eapply N_requirements'. 
        intros m. exists (S N + m); split; first lia.
        eapply Dec_true. eapply HN. lia.
      - unfold J. intros H_.
        eapply (@N_requirements' x). intros N_requirements'.
        eapply (@not_not_limit_case x).
        intros [[k Hk]|h2].
        apply H_. split.
        enough (Ξ x (char_rel P) x) by easy.
        eapply N_requirements'. intros m. exists (S k + m).
        split; first lia. eapply Hk. lia.
        intro H. destruct H as [w Hw].
        intros [k' Hneg]%Φ_spec.
        set (N := S (max w k')).
        assert (Ω x N ↓). { eapply Hneg. lia. }
        enough (¬ Ω x N ↓) by eauto.
        eapply Dec_false. eapply Hw. lia.  
        apply H_. split. 
        destruct h2 as [w Hw]. exists w.
        intros. specialize (Hw n H0). unfold limit_decider.
        destruct (Dec _); eauto.
        intro H. destruct H as [w Hw].
        intros [k Hneg]%Φ_spec.
        set (N := S (max w k)).
        assert (Ω x N ↓). { eapply Hneg. lia. }
        enough (¬ Ω x N ↓) by eauto.
        eapply Dec_false. eapply Hw. lia.  
    Qed.
    
End intuitionistic_logic. *)

End Requirements_Lowness_Correctness.


Section Wall.

    Variable η: nat → nat → option nat.
    Hypothesis EA: EA η.

    Instance wall_instance: Wall := λ e L n, φ (λ x, Dec (In x L)) e e n.
    Definition P := P η wall.
    Definition P_func := P_func η wall.
    Instance E: Extension := simple_extension η wall.

    Fact P_semi_decidable: semi_decidable P.
    Proof. eapply P_semi_decidable. Qed.

    Definition χ := χ (simple_extension η wall).
    Definition P_Φ := (Φ_ χ).
    Definition P_Ω := (Ω χ).

    Section TEST.

    Hypothesis Σ_1_lem: LEM_Σ 1.

    Lemma attend_at_most_once_bound_constructive:  
      ∀ k, ∃ s, ∀ e, e < k -> ∀ s', s < s' -> ~ attend η wall e s'.
    Proof. by apply attend_at_most_once_bound_test. Qed.

    Lemma eventally_wall_test: 
      ∀ e, (∞∀ s, ∀ x, extendP (P_func s) s x → wall e (P_func s) s < x).
    Proof.
      intros e.
      destruct (@attend_at_most_once_bound_constructive (S e)) as [s Hs].
      exists (S s). intros m Hm x [e_ [He_ He_']].
      destruct (Dec (e_ < e)) as [E|E].
      { exfalso. enough (attend η wall e_ m).
        unshelve eapply (Hs e_ _ m); eauto; lia.
        split; first lia. destruct He_' as [H _].
        apply H. }
      assert (e ≤ e_) by lia; clear E.
      destruct He_', H1, H1, H1, H1, H3.
      by eapply H5.
    Qed. 

    Fact wall_convergence_test e : ∃ b : nat, lim_to η wall (wall e) b.
    Proof.
      destruct (@eventally_wall_test e) as [N HN].
      assert (∀ m, dec (wall e (P_func m) m = 0)) as HD by eauto.
      assert (pdec (∀ x, N ≤ x → wall e (P_func x) x = 0)) as [H'|H'].
      { apply assume_Π_1_lem. apply Σ_1_lem. intros x. eauto. }

      (* ccase (∀ x, N ≤ x → wall e (P_func x) x = 0) as [H'|H']. *)
      - exists 0. exists N. intros. by apply H'.
      - enough (∃ x, N ≤ x ∧ wall e (P_func x) x ≠ 0) as H''.
        clear H'. destruct H'' as [x [H1 H2]].
        destruct (wall e (P_func x) x) as [|k] eqn: H; first done; clear H2.
        exists (S k), x. intros t Ht. induction Ht; first done.
        rewrite <- (@φ_spec1 χ _ _ _ _ IHHt).
        reflexivity.
        intros; split.
        + intros K%Dec_true. apply Dec_auto.
          enough (incl (F_func (simple_extension η wall) m) (F_func (simple_extension η wall) (S m))).
          eauto. eapply F_mono; [apply F_func_correctness|apply F_func_correctness|lia].
        + intros K%Dec_true. specialize (F_func_correctness (simple_extension η wall) (S m)) as HE.
          inv HE. 
          * assert (wall e (P_func m) m < a).
            { eapply HN. lia. enough (P_func m = l) as ->. apply H5.
              eapply F_uni; [apply F_func_correctness|apply H4]. }
            assert (wall e (P_func m) m = S k). { rewrite <-IHHt. reflexivity. }
            rewrite H6 in H2. destruct (Dec (a = x0)).
            lia. apply Dec_auto. rewrite <- H3 in K.
            destruct K; first done.
            enough ((F_func (simple_extension η wall) m) = l) as -> by done.
            eapply F_uni; last apply H4; apply F_func_correctness.
          * apply Dec_auto.
            enough (F_func (simple_extension η wall) m = F_func (simple_extension η wall) (S m)) as -> by eauto. 
            eapply F_uni; first apply F_func_correctness.
            assumption.
        + eapply assume_Σ_1_dne. apply Σ_1_lem.
          { intro x. eauto.   }
          intro H. apply H'. intros x Hx.
          assert (∀ n m: nat, ~~n=m → n=m).
           { intros n m Hnm. destruct (Dec (n=m)); eauto.
              exfalso. by apply Hnm. }
          apply H0. intros Hmn.
          apply H. now exists x; split.
    Qed.

    Lemma N_requirements_test: ∀ e, (∞∃ n, P_Ω e n ↓) → Ξ e (char_rel P) e.
    Proof.
      intros e He.
      destruct (@eventally_wall_test e) as [N HN].
      destruct (@wall_convergence_test e) as [B [b Hb]].
      set (M := max N b). destruct (He M) as [k [Hk Hk']].
      eapply (@φ_spec χ e e k); first apply Hk'. 
      intros x Hx. unfold P, simple_extension.P.
      rewrite F_with_top. split.
      - intros (L & m & HL & HLs &HP).
        assert (L = P_func m) as E. { eapply F_uni. apply HL. apply F_func_correctness. }
        assert (x::L = P_func (S m)) as E'. { eapply F_uni. apply HLs. apply F_func_correctness. }
        apply Dec_auto. destruct (Dec (S m ≤ k)) as [E_|E_].
        enough (incl (P_func (S m)) (P_func k)). rewrite <-E' in H.
        eauto. eapply F_mono; last apply E_; apply F_func_correctness.
        assert (N ≤ m) as Em by lia. rewrite E in HP. specialize (HN m Em x HP).
        assert (k ≤ m) as Ek by lia. enough (x ≤ φ (χ m) e e m).
        exfalso. assert (φ (χ m) e e m < x).
        apply HN. lia. enough (φ (χ m) e e m = φ (χ k) e e k) by congruence.
        assert (φ (χ m) e e m = B).  
        { rewrite <- (Hb m). reflexivity. lia. }
        assert (φ (χ k) e e k = B).  
        { rewrite <- (Hb k). reflexivity. lia. }
        congruence.
      - intros H%Dec_true.
        eapply F_with_top. exists (F_func _ k), k; split; eauto.
        eapply F_func_correctness.
    Qed.

    Lemma convergent e : (∞∀ n, P_Ω e n ↓) ∨ (∞∀ n, ¬ P_Ω e n ↓).
    Proof.
      destruct (@eventally_wall_test e) as [N HN].
      assert (pdec (∃ k, N ≤ k ∧ P_Ω e k ↓)) as [[k [Hk HNk]]|H'] by (apply assume_Σ_1_lem; eauto).
      - left. exists k. intros n Hm.
        induction Hm; first done.
        unfold P_Ω, Ω, Φ_ in *.
        destruct (φ (χ m) e e m) eqn: E.
        { eapply φ_spec0' in E. congruence. }
        (* Check φ_spec2. *)
        eapply (@φ_spec2 χ _ ); eauto.
        intros x Hx; split.
        + intros K%Dec_true. apply Dec_auto.
          enough (incl (F_func (simple_extension η wall) m) (F_func (simple_extension η wall) (S m))).
          eauto. eapply F_mono; [apply F_func_correctness|apply F_func_correctness|lia].
        + intros K%Dec_true. specialize (F_func_correctness (simple_extension η wall) (S m)) as HE.
          inv HE. 
          * assert (wall e (P_func m) m < a).
            { eapply HN. lia. enough (P_func m = l) as ->. apply H2.
              eapply F_uni; [apply F_func_correctness|apply H1]. }
              assert (wall e (P_func m) m = S n). { unfold wall, wall_instance.
               rewrite <-E. reflexivity. }
            rewrite H3 in H. destruct (Dec (a = x)).
            lia. apply Dec_auto. rewrite <- H0 in K.
            destruct K; first done.
            enough ((F_func (simple_extension η wall) m) = l) as -> by done.
            eapply F_uni; last apply H1; apply F_func_correctness.
          * apply Dec_auto.
            enough (F_func (simple_extension η wall) m = F_func (simple_extension η wall) (S m)) as -> by eauto. 
            eapply F_uni; first apply F_func_correctness.
            assumption. 
      - right. exists N. intros m Hm.
        destruct (Dec (P_Ω e m ↓)); eauto.
    Qed.

    (* Should be enough if we use DNE_Σ_2 to drop out ¬¬ for both
        eventally_wall and wall_convergence *)
    Fact P_simple_test: simple P.
    Proof. eapply P_simple; first apply EA. intro e.
      intros H. apply H. apply wall_convergence_test. Qed.

    Hypothesis Σ_2_LEM: 
      ∀ (P: nat → nat → Prop), 
        (∀ n m, dec (P n m)) → (∃ n, ∀ m, P n m) ∨ ¬ (∃ n, ∀ m, P n m).  

    Fact jump_P_limit_test: limit_computable (P´).
    Proof.
      eapply Jump_limit; last done. apply F_with_χ.
      intros e He. eapply N_requirements_test; eauto.
    Qed.
    End TEST.
    

    Lemma eventally_wall e:
      ¬¬ (∞∀ s, ∀ x, extendP (P_func s) s x → wall e (P_func s) s < x).
    Proof.
      intros H_. eapply (@attend_at_most_once_bound η wall (S e)).
      intros [s Hs]. eapply H_; clear H_.
      exists (S s). intros m Hm x [e_ [He_ He_']].
      destruct (Dec (e_ < e)) as [E|E].
      { exfalso. enough (attend η wall e_ m).
        unshelve eapply (Hs e_ _ m); eauto; lia.
        split; first lia. destruct He_' as [H _].
        apply H. }
      assert (e ≤ e_) by lia; clear E.
      destruct He_', H1, H1, H1, H1, H3.
      by eapply H5.
    Qed. 

    Fact wall_convergence e : ¬¬ ∃ b : nat, lim_to η wall (wall e) b.
    Proof.
      intros H_.
      destruct (@eventally_wall e). intros [N HN].
      assert (∀ m, dec (wall e (P_func m) m = 0)) as HD by eauto.
      ccase (∀ x, N ≤ x → wall e (P_func x) x = 0) as [H'|H'].
      - apply H_; clear H_. exists 0. exists N. intros. by apply H'.
      - enough (~~∃ x, N ≤ x ∧ wall e (P_func x) x ≠ 0) as H__.
        apply H__. intros H''.
        clear H'. destruct H'' as [x [H1 H2]].
        apply H_; clear H_.
        destruct (wall e (P_func x) x) as [|k] eqn: H; first done; clear H2.
        exists (S k), x. intros t Ht. induction Ht; first done.
        rewrite <- (@φ_spec1 χ _ _ _ _ IHHt).
        reflexivity.
        intros; split.
        + intros K%Dec_true. apply Dec_auto.
          enough (incl (F_func (simple_extension η wall) m) (F_func (simple_extension η wall) (S m))).
          eauto. eapply F_mono; [apply F_func_correctness|apply F_func_correctness|lia].
        + intros K%Dec_true. specialize (F_func_correctness (simple_extension η wall) (S m)) as HE.
          inv HE. 
          * assert (wall e (P_func m) m < a).
            { eapply HN. lia. enough (P_func m = l) as ->. apply H5.
              eapply F_uni; [apply F_func_correctness|apply H4]. }
            assert (wall e (P_func m) m = S k). { rewrite <-IHHt. reflexivity. }
            rewrite H6 in H2. destruct (Dec (a = x0)).
            lia. apply Dec_auto. rewrite <- H3 in K.
            destruct K; first done.
            enough ((F_func (simple_extension η wall) m) = l) as -> by done.
            eapply F_uni; last apply H4; apply F_func_correctness.
          * apply Dec_auto.
            enough (F_func (simple_extension η wall) m = F_func (simple_extension η wall) (S m)) as -> by eauto. 
            eapply F_uni; first apply F_func_correctness.
            assumption.
        + intro H.
          apply H'. intros x Hx.
          assert (∀ n m: nat, ~~n=m → n=m).
           { intros n m Hnm. destruct (Dec (n=m)); eauto.
              exfalso. by apply Hnm. }
          apply H0. intros Hmn.
          apply H. now exists x; split.
    Qed.

    Lemma N_requirements: ∀ e, (∞∃ n, P_Ω e n ↓) → ¬ ¬ Ξ e (char_rel P) e.
    Proof.
      intros e He H_.
      apply (@eventally_wall e). intros [N HN].
      apply (@wall_convergence e). intros [B [b Hb]].
      apply H_; clear H_.
      set (M := max N b). destruct (He M) as [k [Hk Hk']].
      eapply (@φ_spec  χ e e k); first apply Hk'. 
      intros x Hx. unfold P, simple_extension.P.
      rewrite F_with_top. split.
      - intros (L & m & HL & HLs &HP).
        assert (L = P_func m) as E. { eapply F_uni. apply HL. apply F_func_correctness. }
        assert (x::L = P_func (S m)) as E'. { eapply F_uni. apply HLs. apply F_func_correctness. }
        apply Dec_auto. destruct (Dec (S m ≤ k)) as [E_|E_].
        enough (incl (P_func (S m)) (P_func k)). rewrite <-E' in H.
        eauto. eapply F_mono; last apply E_; apply F_func_correctness.
        assert (N ≤ m) as Em by lia. rewrite E in HP. specialize (HN m Em x HP).
        assert (k ≤ m) as Ek by lia. enough (x ≤ φ (χ m) e e m).
        exfalso. assert (φ (χ m) e e m < x).
        apply HN. lia. enough (φ (χ m) e e m = φ (χ k) e e k) by congruence.
        assert (φ (χ m) e e m = B).  
        { rewrite <- (Hb m). reflexivity. lia. }
        assert (φ (χ k) e e k = B).  
        { rewrite <- (Hb k). reflexivity. lia. }
        congruence.
      - intros H%Dec_true.
        eapply F_with_top. exists (F_func _ k), k; split; eauto.
        eapply F_func_correctness.
    Qed.
  
    (* Should be enough if we use DNE_Σ_2 to drop out ¬¬ for both
        eventally_wall and wall_convergence *)
    Fact P_simple: simple P.
    Proof. eapply P_simple; first apply EA. intro e. apply wall_convergence. Qed.

    Section with_LEM_2.

    Hypothesis LEM_Σ_2: 
    ∀ (P: nat → nat → Prop), (∀ n m, dec (P n m)) → (∃ n, ∀ m, P n m) ∨ ¬ (∃ n, ∀ m, P n m).  

    Hypothesis DN: ∀ P, ¬ ¬ P → P.
    Fact jump_P_limit: limit_computable (P´).
    Proof.
      eapply Jump_limit; last done. apply F_with_χ.
      intros e He. eapply DN, N_requirements; eauto.
    Qed.

    End with_LEM_2.

    Section with_LEM_1.

    Hypothesis LEM_Σ_1: LEM_Σ 1.

    Fact jump_P_limit_2: limit_computable (P´).
    Proof.
      eapply Jump_limit_1; first apply F_with_χ.
      - intros e He. eapply N_requirements_test; eauto.
      - eapply convergent; eauto.
    Qed.

    End with_LEM_1.

End Wall.

(* Check jump_P_limit_2. *)




