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

Section Requirements_Lowness_Correctness.

  Variable P: nat → Prop.
  Variable f: nat → nat → bool.
  Hypothesis S_P: stable_semi_decider P f.

  Definition Φ_ := (Φ_ f).

  Fact Φ_spec e x: Ξ e (char_rel P) x → ∞∀ n, Φ_ e x n ↓.
  Proof. intro H. unfold Φ_. apply (Φ_spec S_P H). Qed.

  Definition Ω e n := Φ_ e e n.

  Hypothesis N_requirements: ∀ e, (∞∃ n, Ω e n ↓) → Ξ e (char_rel P) e.

  Hypothesis LEM_Σ_2: 
      ∀ (P: nat → nat → Prop), (∀ n m, dec (P n m)) → dec (∃ n, ∀ m, P n m).

  #[export]Instance dec_le: ∀ m n, dec (m ≤ n).
  Proof. intros n m; destruct (le_gt_dec n m); [by left|right; lia]. Qed.

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
    exfalso. by eapply n; exists i.
  Qed.

  Definition limit_decider e n: bool := Dec (Ω e n ↓).

  Lemma Jump_limit :limit_computable (P´).
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

    Hypothesis NoIdea: ∀ (P: nat → Prop) (k: nat), 
        (∀ x, k ≤ x → P x) ∨ (∃ x, k ≤ x ∧ ¬ P x).

    Definition χ := χ (simple_extension η wall).
    Definition P_Φ := (Φ_ χ).
    Definition P_Ω := (Ω χ).

    Fact wall_convergence e : ¬¬ ∃ b : nat, lim_to η wall (wall e) b.
    Proof.
      intros H_.
      destruct (@eventally_wall e). intros [N HN]. apply H_; clear H_.
      destruct (NoIdea (λ m, wall e (P_func m) m = 0) N).
      - exists 0. exists N. intros. by apply H.
      - destruct H as [x [H1 H2]].
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
    Qed.

    Hypothesis DN: ∀ P, ¬ ¬ P → P.
    Fact P_simple: simple P.
    Proof. eapply P_simple; first apply EA. intro e. apply DN, wall_convergence. Qed.

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
        apply Dec_auto.  destruct (Dec (S m ≤ k)) as [E_|E_].
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

    Hypothesis LEM_Σ_2: 
      ∀ (P: nat → nat → Prop), (∀ n m, dec (P n m)) → dec (∃ n, ∀ m, P n m).

    Fact jump_P_limit: limit_computable (P´).
    Proof.
      eapply Jump_limit; last done. apply F_with_χ.
      intros e He. eapply DN, N_requirements; eauto.
    Qed.

End Wall.



