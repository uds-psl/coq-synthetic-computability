From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions limit_computability simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith Arith.Compare_dec Lia Coq.Program.Equality List.
From SyntheticComputability Require Import the_priority_method.
Import SyntheticComputability.Axioms.EA.Assume_EA.
Import ListNotations.

(* ########################################################################## *)
(** * The Simple Extension *)
(* ########################################################################## *)

Section ComplToBound.
    Definition complToBound L b : list nat 
        := filter (λ x, Dec (¬ In x L)) (seq 0 (S b)).

    Lemma complToBound_Bound L b :
        ∀ x, In x (complToBound L b) → x <= b.
    Proof.
        intros x [H % in_seq ?] % in_filter_iff. lia.
    Qed.
    Lemma filter_length {X} f (l : list X) :
        length l = length (filter f l) + length (filter (λ x, (negb (f x))) l).
    Proof.
        induction l; cbn.
        - reflexivity.
        - destruct f; cbn; lia.
    Qed.
    Lemma filter_NoDup {X} f (l : list X) :
        NoDup l → NoDup (filter f l).
    Proof.
        induction 1; cbn.
        - econstructor.
        - destruct f; eauto. econstructor; auto.
            intros ? % in_filter_iff. firstorder.
    Qed.
    Lemma complToBound_length L b:
        length (complToBound L b) + length L >= S b.
    Proof.
        rewrite <- (seq_length (S b) 0).
        erewrite filter_length with (l := seq 0 (S b)).
        unfold complToBound.
        eapply Plus.plus_le_compat_l_stt.
        generalize (seq_NoDup (S b) 0).
        generalize (seq 0 (S b)). clear.
        intros. erewrite filter_ext with (g := fun x => Dec (In x L)).
        2:{ intros a. destruct Dec; cbn; destruct Dec; firstorder congruence. }
        eapply NoDup_incl_length. now eapply filter_NoDup.
        clear. induction l; cbn.
        - firstorder.
        - destruct Dec; cbn. 2: eauto.
            intros ? [-> | ]; eauto.
    Qed.
    Lemma complToBound_NoDup L b:
        NoDup (complToBound L b).
    Proof.
        eapply filter_NoDup, seq_NoDup.
    Qed.
    Lemma firstn_In {X} (l : list X) n x : In x (firstn n l) → In x l.
    Proof.
        induction n in x, l |- *; destruct l; cbn; firstorder.
    Qed.

    Lemma firstn_NoDup {X} (l : list X) n : NoDup l → NoDup (firstn n l).
    Proof.
        induction 1 in n |- *; destruct n; cbn; try now econstructor.
        econstructor; eauto.
        now intros ? % firstn_In.
    Qed.
End ComplToBound.

Section Assume_EA.

  Definition θ := φ.
  Definition EA_spec := ∀ p, semi_decidable p → ∃ e, ∀ x, p x ↔ ∃ n, φ e n = Some x.

  Lemma EA: EA_spec.
  Proof.
    intros P HP%SyntheticComputability.Axioms.EA.enum_iff.
    rewrite W_spec in HP. destruct HP as [c Hc].
    exists c. intros x. unfold W in Hc.
    eapply Hc.
  Qed.

  Definition W_ n e x := φ n e = Some x.
  Definition W e x := ∃ n, W_ e n x.

  Lemma W_spec: ∀ P, semi_decidable P → ∃ e, ∀ x, P x ↔ W e x.
  Proof. intros P [e He]%EA. exists e; intros x; now rewrite He. Qed.

  Notation "'W[' s ']' e" := (λ x, ∃ n, n <= s ∧ W_ e n x) (at level 30).

  Section EA_dec.

    Lemma W_dec e: ∀ x n, dec (W_ e n x).
    Proof.
      intros x n.
      destruct (φ e n) eqn: E.
      - destruct (Dec (x = n0)) as [E'|E'].
        left. now subst. right. intros H. congruence.
      - right. intros H. congruence. 
    Qed.

    Lemma W_bounded_dec e : ∀ x s, dec ((W[s] e) x).
    Proof.
      intros x s. cbn. eapply exists_bounded_dec.
      intro; apply W_dec.
    Qed.

    Lemma W_bounded_bounded e s: bounded (W[s] e).
    Proof.
      unfold bounded.
      induction s.
      - destruct (φ e 0) as [w|] eqn: E.
        exists (S w). intros x [n [Hn1 Hn2]].
        inv Hn1. unfold W_ in Hn2.  rewrite E in Hn2.
        injection Hn2. lia.
        exists 42. intros x [n [Hn1 Hn2]].
        inv Hn1. unfold W_ in Hn2.
        rewrite E in Hn2. congruence.
      - destruct IHs as [N HN].
        destruct (φ e (S s)) as [w|] eqn: E.
        exists (max (S w) (S N)). intros x [n [Hn1 Hn2]].
        inv Hn1. unfold W_ in Hn2. 
        rewrite E in Hn2. injection Hn2. lia.
        eapply Nat.lt_trans. eapply HN. exists n; split; easy. lia.
        exists N. intros x [n [Hn1 Hn2]].
        inv Hn1. unfold W_ in Hn2.
        rewrite E in Hn2. congruence.
        eapply HN. exists n. split; eauto.
    Qed.

  End EA_dec.

  Definition disj_list_pred {X} (A: list X) (B: X → Prop) := ∀ x, In x A → B x → False.
  Definition disj_pred {X} (A B: X → Prop) := ∀ x, A x → B x → False.
  Notation "A # B" := (disj_list_pred A B) (at level 30).
  Notation "A #ₚ B" := (disj_pred A B) (at level 30).

  Lemma extra_bounded f m: Σ b, ∀ n, n < m → f n < b.
  Proof.
    induction m.
    - exists 42. intros. inv H. 
    - destruct IHm as [b' Hb'].
      exists (S (max b' (f m))).
      intros ? H. inv H. lia. specialize (Hb' n H1). lia.
  Qed.

  Section Assume_WALL.
    Definition Wall := nat → list nat → nat → nat.
    Variable wall: Wall.

    Section Extension. (** ** Construction *)

      Definition ext_intersect_W L n e := L # W[n] e.
      Definition ext_has_wit L n e x := (W[n] e) x ∧ 2 * e < x ∧ ∀ i, i <= e → wall i L n < x.
      Definition ext_pick L n e := ext_intersect_W L n e ∧ ∃ x, ext_has_wit L n e x.
      Definition ext_choice L n e x :=  e < n ∧ least (ext_pick L n) e ∧ least (ext_has_wit L n e) x.
      Definition ext_least_choice L n x := ∃ e, ext_choice L n e x.

    End Extension.

    Section Extension_Facts.

      #[export]Instance ext_intersect_W_dec L n e: dec (ext_intersect_W L n e).
      Proof.
        apply BaseLists.list_forall_dec.
        intro x. eapply dec_neg_dec, exists_bounded_dec; eauto.
      Qed. 

      #[export] Instance ext_wall L n e x: dec (∀ i, i <= e → wall i L n < x).
      Proof. eapply forall_bounded_dec; eauto. Qed.
      
      #[export]Instance ext_has_wit_dec L n e x : dec (ext_has_wit L n e x).
      Proof. apply and_dec; first apply exists_bounded_dec; eauto. Qed.

      #[export]Instance ext_has_wit_exists_dec L n e : dec (∃ x, ext_has_wit L n e x).
      Proof.
        unfold ext_has_wit. eapply bounded_dec; last eapply W_bounded_bounded.
        intro x; eapply W_bounded_dec; eauto. eauto.
      Qed.

      #[export]Instance ext_pick_dec L n e : dec (ext_pick L n e).
      Proof.
        eapply and_dec; first apply ext_intersect_W_dec.
        unfold ext_has_wit.
        eapply bounded_dec; last apply W_bounded_bounded.
        intros x. eapply exists_bounded_dec.
        intro; apply W_dec. eauto.
      Qed.

      #[export]Instance ext_pick_exists_dec L n: dec (∃ e, e < n ∧ least (ext_pick L n) e).
      Proof. 
        eapply exists_bounded_dec'. intro x.
        eapply least_dec. intros y.
        eapply ext_pick_dec.
      Qed.

      Fact ext_least_choice_dec L n:
        (Σ x : nat, ext_least_choice L n x) + (∀ x : nat, ¬ ext_least_choice L n x).
      Proof.
        unfold ext_least_choice.
        destruct (ext_pick_exists_dec L n) as [H|H].
        - left. apply ewo_nat; first last.
          destruct H as [e (h1 & [(h4 & h2) h3])].
          eapply least_ex in h2. destruct h2 as [k h6].
          exists k, e. split; first easy; split.
          2: { eapply h6. }
          split; last apply h3. split; first apply h4.
          destruct h6. now exists k.
          eapply ext_has_wit_dec.
          intro x. unfold ext_choice. eapply exists_bounded_dec'.
          intros x'. eapply and_dec.
          apply least_dec. eapply ext_pick_dec.
          apply least_dec. eapply ext_has_wit_dec.
        - right. intros x [e (h1 & h2 & _)]. apply H.
          exists e. split; eauto.
      Qed.

      Fact ext_least_choice_uni l x: unique (ext_least_choice l x).
      Proof.
        intros y1 y2 [? (h1 & h2 & h3)] [? (h1' & h2' & h3')].
        assert (x0 = x1) as ->. eapply least_unique; eauto.
        eapply least_unique; eauto.
      Qed.

      Instance simple_extension: Extension.
      Proof.
          unshelve econstructor.
          - exact ext_least_choice.
          - apply ext_least_choice_dec.
          - apply ext_least_choice_uni.
      Defined.

      Definition P_ := F_ simple_extension.
      Definition P_func := F_func simple_extension.
      Definition P := F_with simple_extension.

      Definition non_finite e := ¬ exhaustible (W e).

      Fact In_Pf k y: In y (P_func k) → P y.
      Proof.
        intros H. exists (P_func k), k.
        split; [easy| apply F_func_correctness].
      Qed.

      Definition lim_to (f: list nat → nat → nat) b := 
          (∃ n, ∀ m, n <= m → f (P_func m) m = b).

      Lemma finite_decs (P : nat → Prop) k Q :
        ((∀ k', k' < k → pdec (P k')) → ¬ Q) → ¬ Q.
      Proof.
        induction k.
        - firstorder lia.
        - intros H Hq.
          assert (¬¬ pdec (P k)) as Hk. { cbv. tauto. }
          apply Hk. clear Hk. intros Hk.
          apply IHk. 2: assumption.
          intros Ha. apply H. intros.
          assert (k' = k ∨ k' < k) as [-> | ] by lia.
          assumption.
          now apply Ha.
      Qed.

    End Extension_Facts.

    Hypothesis wall_spec: ∀ e, ¬¬ ∃ b, lim_to (wall e) b.

    Section Requirements.

      (** ** Requirements *)

      Definition P_requirements P e := non_finite e → ¬ (W e #ₚ P).
      Definition recv_att e n := e < n ∧ least (ext_pick (P_func n) n) e.
      Definition act e n := ¬ (P_func n) # W[n] e.
      Definition act_by e x := ∃ k, recv_att e k ∧ ext_least_choice (P_func k) k x.
      Definition done e n := ∀ s, n < s → ¬ recv_att e s.

      #[export]Instance attend_dec e n: dec (recv_att e n).
      Proof.
        unfold recv_att. apply and_dec; first eauto.
        eapply least_dec. intros y.
        eapply ext_pick_dec.
      Qed.

    End Requirements.

    Section Requirements_Facts.

      (** ** Verification *)

      Lemma ext_pick_witness L n e:
        ext_pick L n e → ∃ x, least (ext_has_wit L n e) x.
      Proof.
        intros [H1 H2].
        eapply least_ex. intro; eapply ext_has_wit_dec.
        trivial.
      Qed.
      
      Lemma W_incl e n m: 
        n <= m → ∀ x,  (W[n] e) x → (W[m] e) x.
      Proof.
        intros H x [y [H1 H2]].
        exists y. split; lia + easy.
      Qed.

      Lemma intersect_mono {X} (L L': list X) (P P': X → Prop) : 
        L' # P' → incl L L' → (∀ x, P x → P' x) → L # P.
      Proof.
        intros H h1 h2 x Hx1 Hx2.
        eapply (H x). now eapply h1. 
        now apply h2.
      Qed.

      Lemma act_impl_always_act e n: act e n → ∀ m, n <= m → act e m .
      Proof.
        intros H m Hm Hx. apply H. 
        eapply (intersect_mono Hx).
        eapply F_mono; try eapply F_func_correctness; easy.
        now eapply W_incl.
      Qed.

      Lemma recv_impl_next_act e k: recv_att e k → act e (S k).
      Proof.
        intros [He H] Hcontr.
        edestruct (ext_pick_witness) as [x Hx].
        { destruct H. eapply e0. }
        apply (Hcontr x).
        assert (P_ (S k) (P_func (S k))) by apply F_func_correctness.
        inv H0. cbn in H4. assert (ext_least_choice l k x) as Hwitness.
        exists e. assert (P_func k = l) as <-.
        eapply F_uni. apply F_func_correctness. apply H3.
        split; first easy. split; first easy. easy.
        assert (x = a) as ->. eapply (@extend_uni simple_extension); cbn; eauto.
        eauto. exfalso. eapply (H3 x). cbn.
        exists e. enough ((P_func k) = (P_func (S k))) as <-. 
        split; first easy. easy.
        assert (F_ simple_extension k (P_func k)) by apply F_func_correctness.
        eapply F_uni; eauto.
        firstorder.
      Qed.

      Lemma act_impl_not_recv e k: act e k → ¬ recv_att e k.
      Proof. now intros h2 [_ [[h _] _]]. Qed.

      Lemma recv_impl_next_always_act e k: recv_att e k → ∀ m, k < m → act e m.
      Proof.
        intros. eapply act_impl_always_act.
        apply recv_impl_next_act. apply H. lia.
      Qed.

      Lemma recv_impl_always_not_recv e k: 
        recv_att e k → ∀ m, k < m → ¬ recv_att e m.
      Proof.
        intros H1 m Hm. eapply act_impl_not_recv.
        apply (recv_impl_next_always_act H1 Hm).
      Qed.

      Lemma recv_at_most_once_gen e:
        (pdec (∃ k, recv_att e k)) ->
        (∃ s', ∀ s, s' < s → ¬ recv_att e s).
      Proof.
        intros [[w Hw]|H].
        - exists w.
          now eapply recv_impl_always_not_recv.
        - exists 0.
          intros k' Hk' Ha.
          apply H. now exists k'.
      Qed.

      Lemma recv_at_most_once e: ¬ ¬ (∃ s', ∀ s, s' < s → ¬ recv_att e s).
      Proof.
        intros H.
        assert (¬¬ (pdec (∃ k, recv_att e k))) as Hdec.
        { unfold pdec. tauto. }
        apply Hdec. clear Hdec. intros Hdec.
        apply H, recv_at_most_once_gen. assumption.
      Qed.

      Lemma recv_at_most_once_bound_gen k:
        (∀ k', k' < k → pdec (∃ k0 : nat, recv_att k' k0)) →
        ∃ s, (∀ e, e < k → ∀ s', s < s' → ¬ recv_att e s').
      Proof.
        intros Hle.
        induction k.
        - exists 42. intros ??. lia. 
        - destruct IHk as [s Hs].
          { intros. eapply Hle. lia. }
          destruct (@recv_at_most_once_gen k) as [sk Hsk].
          { apply Hle. lia. }
          set (max sk s) as N.
          exists N. intros e He.
          assert (e = k ∨ e < k) as [->|Hek] by lia.
          intros s' Hs'. eapply Hsk. lia.
          intros s' Hs'. eapply Hs; lia.
      Qed.

      Lemma recv_at_most_once_bound_classically k:
        ¬ ¬ ∃ s, (∀ e, e < k → ∀ s', s < s' → ¬ recv_att e s').
      Proof.
        eapply finite_decs.
        intros H % (recv_at_most_once_bound_gen (k := k)).
        tauto.
      Qed.
      Lemma recv_at_most_once_bound: 
        LEM_Σ 1 → ∀ k, ∃ s, (∀ e, e < k → ∀ s', s < s' → ¬ recv_att e s').
      Proof.
        intros Hlem k. apply recv_at_most_once_bound_gen.
        intros. eapply assume_Σ_1_lem. apply Hlem. eauto. 
      Qed.

      Lemma attend_uni e: unique (recv_att e).
      Proof.
        intros k1 k2 H1 H2.
        specialize (fun a b => @act_impl_not_recv _ _ (@recv_impl_next_always_act _ _ H1 a b)) as H1'.
        specialize (fun a b => @act_impl_not_recv _ _ (@recv_impl_next_always_act _ _ H2 a b)) as H2'.
        enough (¬ k1 < k2 ∧ ¬ k2 < k1) by lia; split.
        intro Hk. eapply H1'. apply Hk. easy. 
        intro Hk. eapply H2'. apply Hk. easy.
      Qed.

      Lemma pick_el_uni e: unique (act_by e).
      Proof.
        intros x1 x2 [k [Ht Hk]] [k' [Ht' Hk']].
        assert (k=k') as <-. eapply attend_uni; eauto.
        eapply (@extend_uni simple_extension); cbn; eauto.
      Qed.

    End Requirements_Facts.

    Section Complement_Inf.

      Lemma P_meet_spec x n : P x ∧ x <= 2*n → ∃ e, act_by e x ∧ e < n.
      Proof.
        intros [[L [k [Hin Hk]]] Hn].
        dependent induction L. inv Hin.
        destruct (Dec (a = x)) as [->|].
        - clear IHL Hin.
          destruct (F_pick Hk) as [k' [Hk' [e He]]].
          exists e. split. 
          exists k'. split; unfold recv_att.
          + destruct He; intuition eauto. enough (P_func k' = L) as -> by eauto.
            eapply F_uni. apply F_func_correctness. easy.
          + exists e. unfold ext_choice.
            enough (P_func k' = L) as -> by eauto.
            eapply F_uni. apply F_func_correctness.
            destruct He; intuition eauto. 
          + destruct He. destruct H0. destruct H1. destruct H1.
            lia.
        - destruct (F_pop Hk) as [m' Hm']. 
          eapply (IHL m'); eauto. firstorder. 
      Qed.

      Lemma P_extract_spec n L:
        (∀ x, In x L → P x ∧ x <= 2 * n) → 
        ∀ x, In x L → ∃ c, act_by c x ∧ c < n.
      Proof.
        intros. induction L. inv H0. 
        destruct H0 as [-> | Hln]; last apply IHL; eauto.
        apply P_meet_spec. now apply H.
      Qed.

      Lemma P_pullback_list n L:
        NoDup L → (∀ x, In x L → P x ∧ x <= 2 * n) → 
          ∃ (LC: list nat), NoDup LC ∧ length LC = length L ∧
            ∀ c, In c LC → ∃ x, act_by c x ∧ In x L ∧ c < n.
      Proof.
        intros HL H1.
        induction L.
        - exists []; intuition.
        - remember (@P_extract_spec n (a::L) H1 a).
          assert (In a (a::L)) as H0 by intuition.
          apply e in H0 as [c0 [H0 E1]].
          assert (NoDup L) by (inversion HL; intuition).
          apply IHL in H as [LC H].
          exists (c0::LC). intuition.
          + constructor; last now exact H2. 
            intros In. inv HL.
            apply H4 in In as [y (Hs & h2 & h3)].
            now rewrite (pick_el_uni H0 Hs) in H6.
          + cbn. rewrite H. trivial.
          + destruct H3 as [->|].
            * exists a; intuition.
            * destruct (H4 c H3) as [y Hy].
              exists y; intuition.
          + intros y In1. assert (In y (a::L)) by intuition.
            now apply H1 in H2.
      Qed.

      Definition PredListTo p : list nat → nat → Prop
        := λ L b, ∀ x, In x L ↔ p x ∧ x <= b.

      Lemma NoDupBoundH {L} b:
          NoDup L → (∀ x, In x L → x <= b) → ∀ x, x > b → NoDup (x::L).
      Proof.
          intros ND H x E.
          constructor.
          - intros H1 % H. lia.
          - exact ND.
      Qed.

      Lemma PredNoDupListTo_NNExist p:
        ∀ b, ¬¬ ∃ L, PredListTo p L b ∧ NoDup L.
      Proof.
        destruct (F_computable simple_extension) as [f Hf].
        induction b; intros H.
        - ccase (p 0) as [H0 | H0]; apply H.
          + exists [0]. split; try split.
            * intros [E | E]; (try contradiction E).
              rewrite <- E. intuition.
            * intros E. assert (x = 0) by lia.
              rewrite H1. intuition.
            * constructor; intuition; constructor.
          + exists nil. split; try split.
            * contradiction.
            * intros E. assert (x = 0) by lia.
              rewrite H1 in E. firstorder.
            * constructor.
        - apply IHb. intros [L H1].
          ccase (p (1 + b)) as [H0 | H0]; apply H.
          + exists ((1+ b) :: L). split; try split.
            * intros [E | E]; try (rewrite <- E; intuition).
              apply H1 in E. intuition.
            * intros [E1 E2]. assert (x <= b ∨ x = 1 + b) as [E | E] by lia.
              ** right. apply H1. intuition.
              ** left. lia.
            * apply (@NoDupBoundH _ b).
              ** apply H1.
              ** intros x H3 % H1. lia.
              ** lia.
          + exists L. split; try split.
            * intros E % H1. intuition.
            * intros [E1 E2]. assert (x <= b ∨ x = 1 + b) as [E | E] by lia.
              ** apply H1. intuition.
              ** rewrite E in E1. firstorder.
            * apply H1.
      Qed.

      Lemma P_bounded L n:
        NoDup L → (∀ x, In x L → P x ∧ x <= 2 * n) → length L <= n.
      Proof.
        intros ND [LC H] % P_pullback_list; intuition.
        rewrite <- H.
        assert (incl LC (seq 0 n)). unfold incl. 
        - intros c [e [x Hx]] % H2. apply in_seq. lia.
        - apply pigeonhole_length in H1.
          + now rewrite seq_length in H1.
          + intros. decide (x1 = x2); tauto.
          + exact H0.
      Qed.

      Lemma P_Listing:
        ∀ n, ¬¬ ∃ L, NoDup L ∧ length L <= n ∧ PredListTo P L (2*n).
      Proof.
        intros n H. apply (@PredNoDupListTo_NNExist P (2*n)).
        intros [L H1]. apply H. exists L; intuition.
        apply P_bounded.
        - exact H2.
        - apply H0.
      Qed.

      Lemma complToBound_compl p L b:
        PredListTo p L b → PredListTo (compl p) (complToBound L b) b.
      Proof.
      intros H x. split.
      - intros [H1 H1'] % in_filter_iff.
        destruct Dec; cbn in H1'; try congruence.
        enough (x <= b).
        + firstorder.
        + apply in_seq in H1. lia.
      - intros [H1 H2]. eapply in_filter_iff. split.
        + apply in_seq; lia.
        + destruct Dec; cbn; try tauto. exfalso. firstorder.
      Qed.

      Lemma compl_P_Listing:
      ∀ (n: nat) , ¬¬ ∃ L, length L >= n ∧ NoDup L 
                                    ∧ ∀ x, In x L → ¬ P x.
      Proof.
        intros n H.
        apply (@P_Listing n). intros [L H1].
        apply H. exists (complToBound L (2*n)). repeat split.
        - remember (complToBound_length L (2*n)). lia.
        - apply complToBound_NoDup.
        - intros x I % (@complToBound_compl P); intuition.
      Qed.

      Lemma P_coinfinite : ¬ exhaustible (compl P).
      Proof.
        eapply weakly_unbounded_non_finite.
        intros n H. eapply compl_P_Listing with (n := n).
        intros (l & ? & ? & H2).
        eapply H.
        exists (firstn n l).
        repeat split.
        - rewrite firstn_length. lia.
        - now eapply firstn_NoDup.
        - intros ? ? % firstn_In. now eapply H2.
      Qed.

    End Complement_Inf.

    Section Requirements_Meet.

      Lemma wall_bounded' e: ¬¬ ∃ w, ∀ x, wall e (P_func x) x < w.
      Proof.
        intro H_. apply (@wall_spec e). intros [v [k Hk]].
        apply H_.
        destruct (@extra_bounded (fun k => wall e (P_func k) k) k) as [w Hw].
        exists (S (max v w)). intros x.
        destruct (Dec (x < k)). apply Hw in l. lia.
        assert (wall e (P_func x) x = v). apply Hk. lia. lia.
      Qed.

      Lemma wall_bounded e: 
          ¬¬ ∃ w, ∀ i x, i <= e → wall i (P_func x) x < w.
      Proof.
        intro H_. induction e.
        - apply (@wall_bounded' 0). intros [w Hw]. apply H_. exists w.
          intros i x ?. inv H. trivial.
        - apply IHe. intros [w IHe_].
          apply (@wall_bounded' (S e)). intros [w' Hw'].
          apply H_. exists (S (max w w')). intros i x H.
          inv H. specialize (Hw' x). lia. 
          specialize (IHe_ i x H1). lia.
      Qed.

      Lemma non_finite_not_bounded e: 
        non_finite e → ¬¬ ∃ k, ∃ x, (W[k] e) x ∧ 2 * e < x ∧ 
                                      (∀ n, ∀ i, i <= e → wall i (P_func n) n < x).
      Proof.
        intro H. unfold non_finite in H.
        intros He.  rewrite non_finite_nat in H.
        apply (@wall_bounded e). intros [w Hw].
        pose (N := max (2*e + 1) w). specialize (H N).
        apply H. intros [m [Hm1 [k Hmk]]].
        apply He. exists k, m.
        repeat split. now exists k.
        lia. intros n i Hie. specialize (Hw i n Hie). lia.
      Qed.

      Lemma ext_pick_impl_recv N e: 
        e < N → ext_pick (P_func N) N e → 
        (∃ w, w ≤ e ∧ recv_att w N).
      Proof.
        intros HeN H1.
        assert (exists w, ext_pick (P_func N) N w) by now exists e.
        eapply least_ex in H; last eauto.
        destruct H as [k Hk]. assert (k <= e).
        { enough (¬ k > e) by lia. intro Hkw.
          destruct Hk. rewrite safe_char in H0.
          specialize (H0 e H1). lia. }
        exists k. do 2 (split; first lia). eapply Hk.
      Qed.

      Lemma non_finite_recv e:
        non_finite e → ¬ ¬ (∃ k, ¬ ext_intersect_W (P_func k) k e ∨ recv_att e k) .
      Proof.
        intros H He.
        eapply (non_finite_not_bounded H); intros (b & x & (Hx1 & Hx2 & Hx3)).
        eapply (@recv_at_most_once_bound_classically e); intros [s Hs].
        pose (N := S (max (max b s)  e)). apply He.
        destruct (Dec (ext_intersect_W (P_func N) N e)) as [He'|He'].
        - exists N. right.
          assert (ext_pick (P_func N) N e).
        { split; first easy. exists x. split.
          eapply W_incl; last apply Hx1. lia.
          split; first lia. eapply Hx3.
        }
          split. lia. split. easy.
          intros w HEw Hw.
          eapply ext_pick_impl_recv in Hw.
          destruct Hw as [g [HEg Hg]].
          eapply Hs; last apply Hg; lia. lia. 
        - exists N. now left.
      Qed.

      Lemma ext_intersect_W_intersect k e: 
        ¬ (P_func k # W[k] e) → W e #ₚ P → False.
      Proof.
        unfold ext_intersect_W.
        intros H1 H2. apply H1.
        intros y Hy1 [w Hy2].
        eapply (H2 y). now exists w.
        eapply (In_Pf Hy1).
      Qed.

      Lemma P_requirements_meet : ∀ e, P_requirements P e.
      Proof.
        intros e He He'.
        eapply (non_finite_recv He).
        intros [k [H|H]].
        - eapply ext_intersect_W_intersect; eauto.
        - eapply recv_impl_next_act in H.
          eapply ext_intersect_W_intersect; eauto.
      Qed.

    End Requirements_Meet.

    Section Results.

      Lemma P_semi_decidable : semi_decidable P.
      Proof. apply F_with_semi_decidable. Qed.

      Theorem P_simple : simple P.
      Proof.
        unfold simple; repeat split.
        - rewrite EA.enum_iff. now apply P_semi_decidable.
        - apply P_coinfinite.
        - intros [q (Hqenum & Hqinf & Hq)].
          rewrite EA.enum_iff in Hqenum.
          destruct (W_spec Hqenum) as [c HWq].
          apply (@P_requirements_meet c).
          intros [l Hqe]; apply Hqinf.
          exists l. intros x Hqx. apply (Hqe x).
          now rewrite HWq in Hqx.
          intros x HWcx HPx. unfold W in HWcx.
          rewrite <- (HWq x) in HWcx. apply (Hq x HWcx HPx).
      Qed.

    End Results.

  End Assume_WALL.

End Assume_EA.




