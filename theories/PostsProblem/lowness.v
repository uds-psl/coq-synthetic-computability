From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions step_indexing limit_computability simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith Arith.Compare_dec Lia Coq.Program.Equality List.
From SyntheticComputability Require Import the_priority_method.
From SyntheticComputability Require Import simpleness.

Definition inf_exists (P: nat → Prop) := ∀ n, ∃ m, n ≤ m ∧ P m.

Global Instance dec_le: ∀ m n, dec (m ≤ n).
  Proof. intros n m; destruct (le_gt_dec n m); [by left|right; lia]. Qed.

Notation "'∞∃' x .. y , p" :=
  (inf_exists (λ x, .. (inf_exists (λ y, p)) ..))
      (at level 200, x binder, right associativity,
      format "'[' '∞∃'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "f ↓" := (f = Some ()) (at level 30).

Section Requirements_Verification.

  Variable P: nat → Prop.
  Variable f: nat → nat → bool.
  Hypothesis S_P: stable_semi_decider P f.

  Definition Φ_ := (Φ_ f).

  Fact Φ_spec e x: Ξ e (char_rel P) x → ∞∀ n, Φ_ e x n ↓.
  Proof. intro H. unfold Φ_. apply (Φ_spec S_P H). Qed.
  Definition Ω e n := Φ_ e e n.
  Definition limit_decider e n: bool := Dec (Ω e n ↓).

    (** ** Requirements *)

  Hypothesis step_ex_spec: ∀ e, (∞∃ n, Ω e n ↓) → Ξ e (char_rel P) e.
  Hypothesis N_requirements: ∀ e, (∞∀ n, Ω e n ↓) ∨ (∞∀ n, ¬ Ω e n ↓).
  
  Lemma Jump_limit_1 : limit_computable (P´).
  Proof.
    exists limit_decider; split; intros.
    - unfold J. split. 
      intros [w Hw]%Φ_spec; exists w; intros??.
      apply Dec_auto. by eapply Hw.
      intros [N HN]. eapply step_ex_spec. 
      intros m. exists (Datatypes.S N + m); split; first lia.
      eapply Dec_true. eapply HN. lia.
    - unfold J. split; intros H. 
      destruct (N_requirements x) as [[k Hk]|h2].
      enough (Ξ x (char_rel P) x) by easy.
      eapply step_ex_spec. intros m. exists (Datatypes.S k + m).
      split; first lia. eapply Hk. lia.
      destruct h2 as [w Hw]. exists w.
      intros. specialize (Hw n H0). unfold limit_decider.
      destruct (Dec _); eauto.
      destruct H as [w Hw].
      intros [k Hneg]%Φ_spec.
      set (N := Datatypes.S (max w k)).
      assert (Ω x N ↓). { eapply Hneg. lia. }
      enough (¬ Ω x N ↓) by eauto.
      eapply Dec_false. eapply Hw. lia.  
  Qed.

End Requirements_Verification.

Section Requirements_Meet.

  Variables wall: Wall.

  Definition P := P wall.
  Definition P_func := P_func wall.
  Instance E: Extension := simple_extension wall.

  Fact P_semi_decidable: semi_decidable P.
  Proof. eapply P_semi_decidable. Qed.

  Definition χ := χ (simple_extension wall).
  Definition P_Φ := (Φ_ χ).
  Definition P_Ω := (Ω χ).

  Section wall_greater_than_use.

    Hypothesis wall_spec: forall e L n, φ (λ x, Dec (In x L)) e e n ≤ wall e L n.
    Hypothesis Σ_1_lem: LEM_Σ 1.

    Lemma attention_bound:  
      ∀ k, ∃ s, ∀ e, e < k -> ∀ s', s < s' -> ~ recv_att wall e s'.
    Proof. by apply recv_at_most_once_bound. Qed.

    Lemma eventally_greater_than_wall: 
      ∀ e, (∞∀ s, ∀ x, extendP (P_func s) s x → wall e (P_func s) s < x).
    Proof.
      intros e.
      destruct (@attention_bound (S e)) as [s Hs].
      exists (S s). intros m Hm x [e_ [He_ He_']].
      destruct (Dec (e_ < e)) as [E|E].
      { exfalso. enough (recv_att wall e_ m).
        unshelve eapply (Hs e_ _ m); eauto; lia.
        split; first lia. destruct He_' as [H _].
        apply H. }
      assert (e ≤ e_) by lia; clear E.
      destruct He_', H1, H1, H1, H1, H3.
      by eapply H5.
    Qed.

    Lemma N_requirements e : (∞∀ n, P_Ω e n ↓) ∨ (∞∀ n, ¬ P_Ω e n ↓).
    Proof.
      destruct (@eventally_greater_than_wall e) as [N HN].
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
          enough (incl (F_func (simple_extension wall) m) (F_func (simple_extension wall) (S m))).
          eauto. eapply F_mono; [apply F_func_correctness|apply F_func_correctness|lia].
        + intros K%Dec_true. specialize (F_func_correctness (simple_extension wall) (S m)) as HE.
          inv HE. 
          * assert (wall e (P_func m) m < a).
            { eapply HN. lia. enough (P_func m = l) as ->. apply H2.
              eapply F_uni; [apply F_func_correctness|apply H1]. }
              assert (wall e (P_func m) m ≥ S n). {
              rewrite <-E. apply wall_spec. }
            destruct (Dec (a = x)).
            lia. apply Dec_auto. rewrite <- H0 in K.
            destruct K; first done.
            enough ((F_func (simple_extension wall) m) = l) as -> by done.
            eapply F_uni; last apply H1; apply F_func_correctness.
          * apply Dec_auto.
            enough (F_func (simple_extension wall) m = F_func (simple_extension wall) (S m)) as -> by eauto. 
            eapply F_uni; first apply F_func_correctness.
            assumption. 
      - right. exists N. intros m Hm.
        destruct (Dec (P_Ω e m ↓)); eauto. 
    Qed.

  End wall_greater_than_use.

End Requirements_Meet.

Section Concret_Wall.

  (** ** Construction *)

    Definition wall: Wall := λ e L n, φ (λ x, Dec (In x L)) e e n.
    Instance E_low: Extension := simple_extension wall.
    Hypothesis Σ_1_lem: LEM_Σ 1.

    Fact wall_convergence e : ∃ b : nat, lim_to wall (wall e) b.
    Proof.
      destruct (eventally_greater_than_wall wall Σ_1_lem e) as [N HN].
      assert (∀ m, dec (wall e (P_func wall m) m = 0)) as HD by eauto.
      assert (pdec (∀ x, N ≤ x → wall e (P_func wall x) x = 0)) as [H'|H'].
      { apply assume_Π_1_lem. apply Σ_1_lem. intros x. eauto. }

      (* ccase (∀ x, N ≤ x → wall e (P_func x) x = 0) as [H'|H']. *)
      - exists 0. exists N. intros. by apply H'.
      - enough (∃ x, N ≤ x ∧ wall e (P_func wall x) x ≠ 0) as H''.
        clear H'. destruct H'' as [x [H1 H2]].
        destruct (wall e (P_func wall x) x) as [|k] eqn: H; first done; clear H2.
        exists (S k), x. intros t Ht. induction Ht; first done.
        rewrite <- (@φ_spec1 (χ wall) _ _ _ _ IHHt).
        reflexivity.
        intros; split.
        + intros K%Dec_true. apply Dec_auto.
          enough (incl (F_func (simple_extension wall) m) (F_func (simple_extension wall) (S m))).
          eauto. eapply F_mono; [apply F_func_correctness|apply F_func_correctness|lia].
        + intros K%Dec_true. specialize (F_func_correctness (simple_extension wall) (S m)) as HE.
          inv HE. 
          * assert (wall e (P_func wall m) m < a).
            { eapply HN. lia. enough (P_func wall m = l) as ->. apply H5.
              eapply F_uni; [apply F_func_correctness|apply H4]. }
            assert (wall e (P_func wall m) m = S k). { rewrite <-IHHt. reflexivity. }
            rewrite H6 in H2. destruct (Dec (a = x0)).
            lia. apply Dec_auto. rewrite <- H3 in K.
            destruct K; first done.
            enough ((F_func (simple_extension wall) m) = l) as -> by done.
            eapply F_uni; last apply H4; apply F_func_correctness.
          * apply Dec_auto.
            enough (F_func (simple_extension wall) m = F_func (simple_extension wall) (S m)) as -> by eauto. 
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

    Lemma step_ex_spec: ∀ e, (∞∃ n, P_Ω wall e n ↓) → Ξ e (char_rel (P wall)) e.
    Proof.
      intros e He.
      destruct (@eventally_greater_than_wall wall Σ_1_lem e) as [N HN].
      destruct (@wall_convergence e) as [B [b Hb]].
      set (M := max N b). destruct (He M) as [k [Hk Hk']].
      eapply (@φ_spec (χ wall) e e k); first apply Hk'. 
      intros x Hx. unfold P, simpleness.P.
      rewrite F_with_top. split.
      - intros (L & m & HL & HLs &HP).
        assert (L = (P_func wall) m) as E. { eapply F_uni. apply HL. apply F_func_correctness. }
        assert (x::L = (P_func wall) (S m)) as E'. { eapply F_uni. apply HLs. apply F_func_correctness. }
        apply Dec_auto. destruct (Dec (S m ≤ k)) as [E_|E_].
        enough (incl ((P_func wall) (S m)) ((P_func wall) k)). rewrite <-E' in H.
        eauto. eapply F_mono; last apply E_; apply F_func_correctness.
        assert (N ≤ m) as Em by lia. rewrite E in HP. specialize (HN m Em x HP).
        assert (k ≤ m) as Ek by lia. enough (x ≤ φ (χ wall m) e e m).
        exfalso. assert (φ (χ wall m) e e m < x).
        apply HN. lia. enough (φ (χ wall m) e e m = φ (χ wall k) e e k) by congruence.
        assert (φ (χ wall m) e e m = B).  
        { rewrite <- (Hb m). reflexivity. lia. }
        assert (φ (χ wall k) e e k = B).  
        { rewrite <- (Hb k). reflexivity. lia. }
        congruence.
      - intros H%Dec_true.
        eapply F_with_top. 
        exists (F_func _ k), k; split; eauto.
        eapply F_func_correctness.
    Qed.

    Lemma eventally_greater_than_wall_classically e:
      ¬¬ (∞∀ s, ∀ x, extendP (P_func wall s) s x → wall e (P_func wall s) s < x).
    Proof.
      intros H_. eapply (@recv_at_most_once_bound_classically wall (S e)).
      intros [s Hs]. eapply H_; clear H_.
      exists (S s). intros m Hm x [e_ [He_ He_']].
      destruct (Dec (e_ < e)) as [E|E].
      { exfalso. enough (recv_att wall e_ m).
        unshelve eapply (Hs e_ _ m); eauto; lia.
        split; first lia. destruct He_' as [H _].
        apply H. }
      assert (e ≤ e_) by lia; clear E.
      destruct He_', H1, H1, H1, H1, H3.
      by eapply H5.
    Qed.

    Fact wall_convergence_classically e : ¬¬ ∃ b : nat, lim_to wall (wall e) b.
    Proof.
      intros H_.
      destruct (@eventally_greater_than_wall_classically e). intros [N HN].
      assert (∀ m, dec (wall e (P_func wall m) m = 0)) as HD by eauto.
      ccase (∀ x, N ≤ x → wall e (P_func wall x) x = 0) as [H'|H'].
      - apply H_; clear H_. exists 0. exists N. intros. by apply H'.
      - enough (~~∃ x, N ≤ x ∧ wall e (P_func wall x) x ≠ 0) as H__.
        apply H__. intros H''.
        clear H'. destruct H'' as [x [H1 H2]].
        apply H_; clear H_.
        destruct (wall e (P_func wall x) x) as [|k] eqn: H; first done; clear H2.
        exists (S k), x. intros t Ht. induction Ht; first done.
        rewrite <- (@φ_spec1 (χ wall) _ _ _ _ IHHt).
        reflexivity.
        intros; split.
        + intros K%Dec_true. apply Dec_auto.
          enough (incl (F_func (simple_extension wall) m) (F_func (simple_extension wall) (S m))).
          eauto. eapply F_mono; [apply F_func_correctness|apply F_func_correctness|lia].
        + intros K%Dec_true. specialize (F_func_correctness (simple_extension wall) (S m)) as HE.
          inv HE. 
          * assert (wall e (P_func wall m) m < a).
            { eapply HN. lia. enough (P_func wall m = l) as ->. apply H5.
              eapply F_uni; [apply F_func_correctness|apply H4]. }
            assert (wall e (P_func wall m) m = S k). { rewrite <-IHHt. reflexivity. }
            rewrite H6 in H2. destruct (Dec (a = x0)).
            lia. apply Dec_auto. rewrite <- H3 in K.
            destruct K; first done.
            enough ((F_func (simple_extension wall) m) = l) as -> by done.
            eapply F_uni; last apply H4; apply F_func_correctness.
          * apply Dec_auto.
            enough (F_func (simple_extension wall) m = F_func (simple_extension wall) (S m)) as -> by eauto. 
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

    Fact P_simple: simple (P wall).
    Proof. eapply P_simple, wall_convergence_classically. Qed.

End Concret_Wall.

Section Results.

  Hypothesis LEM_Σ_1: LEM_Σ 1.

  Fact jump_P_limit: limit_computable ((P wall)´).
  Proof.
    eapply Jump_limit_1; first apply F_with_χ.
    - intros e He. eapply step_ex_spec; eauto.
    - eapply N_requirements; eauto.
  Qed.

End Results.



