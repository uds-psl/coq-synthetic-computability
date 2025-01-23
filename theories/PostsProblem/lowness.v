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
  
  Lemma Jump_limit : limit_computable (P´).
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



(* 
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
    Qed. *)


  Definition use := λ e n, φ (χ n) e e n.

  Lemma eventally_greater_than_use_gen e:
    (∃ n, (∀ e', e' < e → ∀ n', n < n' → ¬ (recv_att wall) e' n')) →
    (∞∀ s, ∀ x, extendP (P_func s) s x → use e s < x).
  Proof.
    intros Hc. destruct Hc as [s Hs].
    exists (S s). intros m Hm x [e_ [He_ He_']].
    destruct (Dec (e_ < e)) as [E|E].
    { exfalso. enough (recv_att wall e_ m).
      unshelve eapply (Hs e_ _ m); eauto; lia.
      split; first lia. destruct He_' as [H _].
      apply H. }
    assert (e ≤ e_) by lia; clear E.
    destruct He_', H1, H1, H1, H1, H3.
    specialize(H5 e H).
    enough (use e m <= wall e (P_func m) m) by lia.
    apply wall_spec.
  Qed.

  Lemma eventally_greater_than_use_classically e:
    ¬¬ (∞∀ s, ∀ x, extendP (P_func s) s x → use e s < x).
  Proof.
    intros H_. eapply (@recv_at_most_once_bound_classically wall e).
    intros H'. apply H_. 
    by apply eventally_greater_than_use_gen.
  Qed.


  Fact wall_convergence_gen e : 
    (∃ N, (∀ s, N ≤ s → ∀ x, extendP (P_func s) s x → use e s < x)
      ∧ pdec (∃ x, N ≤ x ∧ use e x ≠ 0)) ->
    (∃ b n: nat, ∀ m : nat, n ≤ m → use e m = b).
  Proof.
    intros (N & HN & Hp).
    assert (∀ m, dec (use e m = 0)) as HD by eauto.
    destruct Hp as [H'|H'].
    - enough (∃ x, N ≤ x ∧ use e x ≠ 0) as H''.
      clear H'. destruct H'' as [x [H1 H2]].
      destruct (use e x) as [|k] eqn: H; first done; clear H2.
      exists (S k), x. intros t Ht. induction Ht; first done.
      rewrite <- (@φ_spec1 χ _ _ _ _ IHHt).
      reflexivity.
      intros; split.
      + intros K%Dec_true. apply Dec_auto.
        enough (incl (F_func (simple_extension wall) m) (F_func (simple_extension wall) (S m))).
        eauto. eapply F_mono; [apply F_func_correctness|apply F_func_correctness|lia].
      + intros K%Dec_true. specialize (F_func_correctness (simple_extension wall) (S m)) as HE.
        inv HE. 
        * assert (use e m < a).
          { eapply HN. lia. enough (P_func m = l) as ->. apply H5.
            eapply F_uni; [apply F_func_correctness|apply H4]. }
          assert (wall e (P_func m) m ≥ S k). { rewrite <-IHHt.
          unfold use. unfold χ, the_priority_method.χ.
          specialize (wall_spec e (F_func (simple_extension wall) m) m).  
          eapply wall_spec. }
          destruct (Dec (a = x0)).
          lia. apply Dec_auto. rewrite <- H3 in K.
          destruct K; first done.
          enough ((F_func (simple_extension wall) m) = l) as -> by done.
          eapply F_uni; last apply H4; apply F_func_correctness.
        * apply Dec_auto.
          enough (F_func (simple_extension wall) m = F_func (simple_extension wall) (S m)) as -> by eauto. 
          eapply F_uni; first apply F_func_correctness.
          assumption.
      + apply H'.
    - exists 0. exists N. intros.
      destruct (use e m) eqn: E; first done.
      exfalso. apply H'. exists m. split; first done.
      congruence.
  Qed.


  Fact wall_convergence_classically e : ¬¬ ∃ b n: nat, ∀ m : nat, n ≤ m → use e m = b.
  Proof.
    intros H. eapply (eventally_greater_than_use_classically). intros [N HN].
    assert (¬¬ pdec (∃ x, N ≤ x ∧ use e x ≠ 0)).
    { ccase (∃ x, N ≤ x ∧ use e x ≠ 0) as [H_|H'_]; eauto.
      - intros Hp. apply Hp. left. done.
      - intros Hp. apply Hp. right. done. }
    apply H0. intros H0'.
    apply H, wall_convergence_gen.
    exists N; eauto.
  Qed.

  Hypothesis Σ_1_lem: LEM_Σ 1.

  Lemma attention_bound:  
    ∀ k, ∃ s, ∀ e, e < k → ∀ s', s < s' → ~ recv_att wall e s'.
  Proof. by apply recv_at_most_once_bound. Qed.

  Lemma eventally_greater_than_use e: 
    (∞∀ s, ∀ x, extendP (P_func s) s x → use e s < x).
  Proof. apply eventally_greater_than_use_gen, attention_bound. Qed.

  Fact wall_convergence e : ∃ b n: nat, ∀ m : nat, n ≤ m → use e m = b.
  Proof.
    apply wall_convergence_gen.
    destruct (eventally_greater_than_use e) as [N HN].
    exists N. split; first done.
    destruct level1 as (_&h2&_).
    rewrite h2 in Σ_1_lem.
    unfold principles.LPO in *.
    destruct (@Σ_1_lem (λ x, Dec (N ≤ x ∧ use e x ≠ 0))) as [[N' HN']|].
    left. exists N'. eauto.
    right. intros [x Hx]. apply H. exists x. eauto.
  Qed.

  Corollary N_requirements e : ((∞∀ n, P_Ω e n ↓) ∨ (∞∀ n, ¬ P_Ω e n ↓)).
  Proof.
    destruct (wall_convergence e) as (b&n&Hn).
    destruct b. 
    - right. exists n. intros.
      enough(P_Ω e m = None) by congruence.
      unfold P_Ω, Ω.
      apply φ_spec0'.
      by apply Hn.
    - left. exists n. intros.
      unfold P_Ω, Ω.
      apply φ_spec0_1.
      unfold use in Hn.
      by rewrite (Hn m H).
  Qed.

  Lemma eventally_greater_than_wall e: 
    (∞∀ s, ∀ x, extendP (P_func s) s x → wall e (P_func s) s < x).
  Proof.
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

  Lemma step_ex_spec: ∀ e, (∞∃ n, P_Ω e n ↓) → Ξ e (char_rel P) e.
  Proof.
    intros e He.
    destruct (eventally_greater_than_wall e) as [N HN].
    destruct (wall_convergence e) as [B [b Hb]].
    set (M := max N b). destruct (He M) as [k [Hk Hk']].
    eapply (@φ_spec χ e e k); first apply Hk'. 
    intros x Hx. unfold P, simpleness.P.
    rewrite F_with_top. split.
    - intros (L & m & HL & HLs &HP).
      assert (L = P_func m) as E. { eapply F_uni. apply HL. apply F_func_correctness. }
      assert (x::L = P_func (S m)) as E'. { eapply F_uni. apply HLs. apply F_func_correctness. }
      apply Dec_auto. destruct (Dec (S m ≤ k)) as [E_|E_].
      enough (incl (P_func (S m)) (P_func k)). rewrite <-E' in H.
      eauto. eapply F_mono; last apply E_; apply F_func_correctness.
      assert (N ≤ m) as Em by lia. rewrite E in HP. specialize (HN m Em x HP).
      assert (k ≤ m) as Ek by lia.
      enough (x ≤ φ (χ m) e e m).
      exfalso. assert (φ (χ m) e e m < x).
      assert(φ (χ m) e e m  ≤ wall e (P_func m) m).
      { specialize (wall_spec e (F_func (simple_extension wall) m) m).
        unfold χ, the_priority_method.χ.
        by rewrite wall_spec. }
      lia.
      enough (φ (χ  m) e e m = φ (χ  k) e e k) by lia.
      assert (φ (χ m) e e m = B).  
      { rewrite <- (Hb m). reflexivity. lia. }
      assert (φ (χ k) e e k = B).  
      { rewrite <- (Hb k). reflexivity. lia. }
        lia. 
      enough (φ (χ  m) e e m = φ (χ  k) e e k) by lia.
      assert (φ (χ m) e e m = B).  
      { rewrite <- (Hb m). reflexivity. lia. }
      assert (φ (χ k) e e k = B).  
      { rewrite <- (Hb k). reflexivity. lia. }
      lia. 
    - intros H%Dec_true.
      eapply F_with_top. 
      exists (F_func _ k), k; split; eauto.
      eapply F_func_correctness.
  Qed.

  End wall_greater_than_use.

End Requirements_Meet.

Section Concret_Wall.

  (** ** Construction *)

    Definition wall: Wall := λ e L n, φ (λ x, Dec (In x L)) e e n.
    Instance E_low: Extension := simple_extension wall.
    Hypothesis Σ_1_lem: LEM_Σ 1.

    Fact P_simple: simple (P wall).
    Proof. eapply P_simple, wall_convergence_classically.
      unfold wall. done. Qed.

End Concret_Wall.

Section Results.

  Hypothesis LEM_Σ_1: LEM_Σ 1.

  Fact jump_P_limit: limit_computable ((P wall)´).
  Proof.
    eapply Jump_limit; first apply F_with_χ.
    - intros e He. 
      eapply step_ex_spec; eauto.
    - eapply N_requirements; eauto.
  Qed.

End Results.



