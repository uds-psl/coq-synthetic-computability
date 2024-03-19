From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions Limit simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith Arith.Compare_dec Lia Coq.Program.Equality List.
Require Import SyntheticComputability.ReducibilityDegrees.priority_method.
Import ListNotations.

Section ComplToBound.
    Definition complToBound L b : list nat 
        := filter (fun x => Dec (~ In x L)) (seq 0 (S b)).

    Lemma complToBound_Bound L b :
        forall x, In x (complToBound L b) -> x <= b.
    Proof.
        intros x [H % in_seq ?] % in_filter_iff. lia.
    Qed.
    Lemma filter_length {X} f (l : list X) :
        length l = length (filter f l) + length (filter (fun x => (negb (f x))) l).
    Proof.
        induction l; cbn.
        - reflexivity.
        - destruct f; cbn; lia.
    Qed.
    Lemma filter_NoDup {X} f (l : list X) :
        NoDup l -> NoDup (filter f l).
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
    Lemma firstn_In {X} (l : list X) n x : In x (firstn n l) -> In x l.
    Proof.
        induction n in x, l |- *; destruct l; cbn; firstorder.
    Qed.

    Lemma firstn_NoDup {X} (l : list X) n : NoDup l -> NoDup (firstn n l).
    Proof.
        induction 1 in n |- *; destruct n; cbn; try now econstructor.
        econstructor; eauto.
        now intros ? % firstn_In.
    Qed.
End ComplToBound.

Section Assume_EA.

  Variable φ: nat -> nat -> option nat.
  Definition EA := forall P, 
    semi_decidable P -> exists e, forall x, P x <-> exists n, φ e n = Some x.
  Hypothesis EA: EA.

  Definition W_ n e x := φ n e = Some x.
  Definition W e x := exists n, W_ e n x.

  Lemma W_spec: forall P, semi_decidable P -> exists e, forall x, P x <-> W e x.
  Proof. intros P [e He]%EA. exists e; intros x; now rewrite He. Qed.

  Notation "'W[' s ']' e" := (fun x => exists n, n <= s /\ W_ e n x) (at level 30).

  Section EA_dec.

    Lemma W_dec e: forall x n, dec (W_ e n x).
    Proof.
      intros x n.
      destruct (φ e n) eqn: E.
      - destruct (Dec (x = n0)) as [E'|E'].
        left. now subst. right. intros H. congruence.
      - right. intros H. congruence. 
    Qed.

    Lemma W_bounded_dec e : forall x s, dec ((W[s] e) x).
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

  Definition disj_list_pred {X} (A: list X) (B: X -> Prop) := forall x, In x A -> B x -> False.
  Definition disj_pred {X} (A B: X -> Prop) := forall x, A x -> B x -> False.
  Notation "A # B" := (disj_list_pred A B) (at level 30).
  Notation "A #ₚ B" := (disj_pred A B) (at level 30).


  Section Extension.

    Definition ext_intersect_W L n e := L # W[n] e.
    Definition ext_has_wit n e x := (W[n] e) x /\ 2 * e < x.
    Definition ext_pick L n e := ext_intersect_W L n e /\ exists x, ext_has_wit n e x.
    Definition ext_choice L n e x :=  e < n /\ least (ext_pick L n) e /\ least (ext_has_wit n e) x.
    Definition ext_least_choice L n x :=  exists e, ext_choice L n e x.

  End Extension.

  Section Extension_Facts.

    #[export]Instance ext_intersect_W_dec L n e: dec (ext_intersect_W L n e).
    Proof.
      apply BaseLists.list_forall_dec.
      intro x. eapply dec_neg_dec, exists_bounded_dec.
      intros y. apply W_dec.
    Qed.  

    #[export]Instance ext_has_wit_dec n e x : dec (ext_has_wit n e x).
    Proof.
      unfold ext_has_wit. apply and_dec.
      apply exists_bounded_dec. intro; apply W_dec.
      apply Pigeonhole.dec_lt.
    Qed.

    #[export]Instance ext_has_wit_exists_dec n e : dec (exists x, ext_has_wit n e x).
    Proof.
      unfold ext_has_wit. eapply bounded_dec; last eapply W_bounded_bounded.
      intro x; eapply W_bounded_dec.
      intro x; eapply lt_dec.
    Qed.

    #[export]Instance ext_pick_dec L n e : dec (ext_pick L n e).
    Proof.
      eapply and_dec; first apply ext_intersect_W_dec.
      unfold ext_has_wit.
      eapply bounded_dec; last apply W_bounded_bounded.
      intros x. eapply exists_bounded_dec.
      intro; apply W_dec.
      apply lt_dec.
    Qed.

    #[export]Instance ext_pick_exists_dec L n: dec (exists e, e < n /\ least (ext_pick L n) e).
    Proof.
      eapply exists_bounded_dec'. intro x.
      eapply least_dec. intros y.
      eapply ext_pick_dec.
    Qed.

    Fact ext_least_choice_dec L n:
      (Σ x : nat, ext_least_choice L n x) + (forall x : nat, ~ ext_least_choice L n x).
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

    Fact ext_least_choice_uni l x y1 y2:
      ext_least_choice l x y1 -> ext_least_choice l x y2 -> y1 = y2.
    Proof.
      intros [? (h1 & h2 & h3)] [? (h1' & h2' & h3')].
      assert (x0 = x1) as ->. eapply least_unique; eauto.
      eapply least_unique; eauto.
    Qed.

  End Extension_Facts.

  Section Simple_Extension.

    Definition simple_extendsion: Extension.
    Proof.
      unshelve econstructor.
      - exact ext_least_choice.
      - apply ext_least_choice_dec.
      - apply ext_least_choice_uni.
    Defined.

    Definition P_ := F_ simple_extendsion.
    Definition Pf_ := F_func simple_extendsion.
    Definition P := F_with simple_extendsion.

    Definition non_finite e := ~ exhaustible (W e).

    Fact In_Pf k y: In y (Pf_ k) -> P y .
    Proof.
      intros H. exists (Pf_ k), k.
      split; [easy| apply F_func_correctness].
    Qed.

  End Simple_Extension.

  Section Requirements.

    Definition R_simple P e := non_finite e -> ~ (W e #ₚ P).
    Definition attention e n := e < n /\ least (ext_pick (Pf_ n) n) e.
    Definition active e n := ~ (Pf_ n) # W[n] e.
    Definition pick_el e x := exists k, attention e k /\ ext_least_choice (Pf_ k) k x.

  End Requirements.

  Section Requirements_Facts.

    Lemma ext_pick_witness L n e:
      ext_pick L n e -> exists x, least (ext_has_wit n e) x.
    Proof.
      intros [H1 H2].
      eapply least_ex. intro; eapply ext_has_wit_dec.
      trivial.
    Qed.
    
    Lemma W_incl e n m: 
      n <= m -> forall x,  (W[n] e) x -> (W[m] e) x.
    Proof.
      intros H x [y [H1 H2]].
      exists y. split; lia + easy.
    Qed.

    Lemma intersect_mono {X} (L L': list X) (P P': X -> Prop) : 
      L' # P' -> incl L L' -> (forall x, P x -> P' x) -> L # P.
    Proof.
      intros H h1 h2 x Hx1 Hx2.
      eapply (H x). now eapply h1. 
      now apply h2.
    Qed.

    Lemma active_always_active e n: active e n -> forall m, n <= m -> active e m .
    Proof.
      intros H m Hm Hx. apply H. 
      eapply (intersect_mono Hx).
      eapply F_mono; try eapply F_func_correctness; easy.
      now eapply W_incl.
    Qed.

    Lemma attention_active e k: attention e k -> active e (S k).
    Proof.
      intros [He H] Hcontr.
      edestruct (ext_pick_witness) as [x Hx].
      { destruct H. eapply e0. }
      apply (Hcontr x).
      assert (P_ (S k) (Pf_ (S k))) by apply F_func_correctness.
      inv H0. cbn in H4. assert (ext_least_choice l k x) as Hwitness.
      exists e. assert (Pf_ k = l) as <-.
      eapply F_uni. apply F_func_correctness. apply H3.
      split; first easy. split; first easy. easy.
      assert (x = a) as ->. eapply (@extend_uni simple_extendsion); cbn; eauto.
      eauto. exfalso. eapply (H3 x). cbn.
      exists e. enough ((Pf_ k) = (Pf_ (S k))) as <-. 
      split; first easy. easy.
      assert (F_ simple_extendsion k (Pf_ k)) by apply F_func_correctness.
      eapply F_uni; eauto.
      firstorder.
    Qed.

    Lemma active_not_attention e k: active e k -> ~ attention e k.
    Proof. now intros h2 [_ [[h _] _]]. Qed.

    Lemma attention_always_active e k: attention e k -> forall m, k < m -> active e m.
    Proof.
      intros. eapply active_always_active.
      apply attention_active. apply H. lia.
    Qed.

    Lemma attention_always_not_attention e k: 
      attention e k -> forall m, k < m -> ~ attention e m.
    Proof.
      intros H1 m Hm. eapply active_not_attention.
      apply (attention_always_active H1 Hm).
    Qed.

    Lemma attention_at_most_once e: ~ ~ (exists s, forall s', s < s' -> ~ attention e s').
    Proof.
      ccase (exists k, attention e k) as [[w Hw]|H].
      - intros H. eapply H. exists w.
        now eapply attention_always_not_attention.
      - intros Hk. apply Hk. exists 0.
        intros k' Hk' Ha.
        apply H. now exists k'.
    Qed.

    Lemma attention_uni e k1 k2 : attention e k1 -> attention e k2 -> k1 = k2.
    Proof.
      intros H1 H2.
      specialize (fun a b => @active_not_attention _ _ (@attention_always_active _ _ H1 a b)) as H1'.
      specialize (fun a b => @active_not_attention _ _ (@attention_always_active _ _ H2 a b)) as H2'.
      enough (~ k1 < k2 /\ ~ k2 < k1) by lia; split.
      intro Hk. eapply H1'. apply Hk. easy. 
      intro Hk. eapply H2'. apply Hk. easy.
    Qed.

    Lemma pick_el_uni e x1 x2: pick_el e x1 -> pick_el e x2 -> x1 = x2 .
    Proof.
      intros [k [Ht Hk]] [k' [Ht' Hk']].
      assert (k=k') as <-. eapply attention_uni; eauto.
      eapply (@extend_uni simple_extendsion); cbn; eauto.
    Qed.

  End Requirements_Facts.

  Section Compl_P_non_finite.

    Lemma P_meet_spec x n : P x /\ x <= 2*n -> exists e, pick_el e x /\ e < n.
    Proof.
      intros [[L [k [Hin Hk]]] Hn].
      dependent induction L. inv Hin.
      destruct (Dec (a = x)) as [->|].
      - clear IHL Hin.
        destruct (F_pick Hk) as [k' [Hk' [e He]]].
        exists e. split. 
        exists k'. split; unfold attention.
        + destruct He; intuition eauto. enough (Pf_ k' = L) as -> by eauto.
          eapply F_uni. apply F_func_correctness. easy.
        + exists e. unfold ext_choice. destruct He; intuition eauto. 
          enough (Pf_ k' = L) as -> by eauto.
          eapply F_uni. apply F_func_correctness. easy.
        + destruct He. destruct H0. destruct H1. destruct H1.
          lia.
      - destruct (F_pop Hk) as [m' Hm']. 
        eapply (IHL m'); eauto. firstorder. 
    Qed.

    Lemma P_extract_spec n L:
      (forall x, In x L -> P x /\ x <= 2 * n) -> 
      forall x, In x L -> exists c, pick_el c x /\ c < n.
    Proof.
      intros. induction L. inv H0. 
      destruct H0 as [-> | Hln]; last apply IHL; eauto.
      apply P_meet_spec. now apply H.
    Qed.

    Lemma P_pullback_list n L:
      NoDup L -> (forall x, In x L -> P x /\ x <= 2 * n) -> 
        exists (LC: list nat), NoDup LC /\ length LC = length L /\
          forall c, In c LC -> exists x, pick_el c x /\ In x L /\ c < n.
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

    Definition PredListTo p : list nat -> nat -> Prop
      := fun L b => forall x, In x L <-> p x /\ x <= b.

    Lemma NoDupBoundH {L} b:
        NoDup L -> (forall x, In x L -> x <= b) -> forall x, x > b -> NoDup (x::L).
    Proof.
        intros ND H x E.
        constructor.
        - intros H1 % H. lia.
        - exact ND.
    Qed.

    Lemma PredNoDupListTo_NNExist p:
      forall b, ~~ exists L, PredListTo p L b /\ NoDup L.
    Proof.
      destruct (F_computable simple_extendsion) as [f Hf].
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
          * intros [E1 E2]. assert (x <= b \/ x = 1 + b) as [E | E] by lia.
            ** right. apply H1. intuition.
            ** left. lia.
          * apply (@NoDupBoundH _ b).
            ** apply H1.
            ** intros x H3 % H1. lia.
            ** lia.
        + exists L. split; try split.
          * intros E % H1. intuition.
          * intros [E1 E2]. assert (x <= b \/ x = 1 + b) as [E | E] by lia.
            ** apply H1. intuition.
            ** rewrite E in E1. firstorder.
          * apply H1.
    Qed.

    Lemma P_bounded L n:
      NoDup L -> (forall x, In x L -> P x /\ x <= 2 * n) -> length L <= n.
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
      forall n, ~~ exists L, NoDup L /\ length L <= n /\ PredListTo P L (2*n).
    Proof.
      intros n H. apply (@PredNoDupListTo_NNExist P (2*n)).
      intros [L H1]. apply H. exists L; intuition.
      apply P_bounded.
      - exact H2.
      - apply H0.
    Qed.

    Lemma complToBound_compl p L b:
      PredListTo p L b -> PredListTo (compl p) (complToBound L b) b.
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
    forall (n: nat) , ~~ exists L, length L >= n /\ NoDup L 
                                  /\ forall x, In x L -> ~ P x.
    Proof.
      intros n H.
      apply (@P_Listing n). intros [L H1].
      apply H. exists (complToBound L (2*n)). repeat split.
      - remember (complToBound_length L (2*n)). lia.
      - apply complToBound_NoDup.
      - intros x I % (@complToBound_compl P); intuition.
    Qed.

    Lemma P_coinfinite : ~ exhaustible (compl P).
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

  End Compl_P_non_finite.

  Section Meet_Requirement.

    Lemma attention_at_most_once_bound k: 
      ~ ~ exists s, (forall e, e < k -> forall s', s < s' -> ~ attention e s').
    Proof.
      induction k.
      - intros H. apply H. exists 42. intros ??. lia. 
      - intros H. apply IHk. intros [s Hs]; clear IHk.
        specialize (@attention_at_most_once k) as Hk.
        apply Hk. intros [sk Hsk]; clear Hk.
        set (max sk s) as N.
        eapply H. exists N. intros e He.
        assert (e = k \/ e < k) as [->|Hek] by lia.
        intros s' Hs'. eapply Hsk. lia.
        intros s' Hs'. eapply Hs; lia.
    Qed.

    Lemma non_finite_not_bounded e: 
      non_finite e -> ~~ exists k, exists x, (W[k] e) x /\ 2 * e < x.
    Proof.
      intro H. unfold non_finite in H.
      intros He.  rewrite non_finite_nat in H.
      specialize (H (2 * e + 1)).
      apply H. intros [m [Hm1 [k Hmk]]].
      apply He. exists k, m; split; last lia.
      now exists k.
    Qed.

    Lemma ext_pick_attention N e: 
      e < N -> (exists w, w < e /\ ext_pick (Pf_ N) N w) -> 
      (exists w, w < e /\ attention w N).
    Proof.
      intros HeN [w (Hw1 & Hw2)].
      assert (exists w, ext_pick (Pf_ N) N w) by now exists w.
      eapply least_ex in H; last eauto.
      destruct H as [k Hk]. assert (k <= w).
      { enough (~ k > w) by lia. intro Hkw.
        destruct Hk. rewrite safe_char in H0.
        specialize (H0 w Hw2). lia. }
      exists k. do 2 (split; first lia). eapply Hk.
    Qed.

    Lemma non_finite_attention e:
      non_finite e -> ~ ~ (exists k, ~ ext_intersect_W (Pf_ k) k e \/ attention e k) .
    Proof.
      intros H He.
      eapply (non_finite_not_bounded H); intros (b & x & Hxb1 & Hxb2).
      eapply (@attention_at_most_once_bound e); intros [s Hs].
      eapply He. 
      pose (N := S (max (max b s)  e)).
      destruct (Dec (ext_intersect_W (Pf_ N) N e)) as [He'|He'].
      - exists N. right.
        assert (ext_pick (Pf_ N) N e).
        { split; first easy. exists x. split; last easy.
          eapply W_incl; last apply Hxb1. lia. }
        split. lia. split. easy.
        intros w HEw Hw.
        assert (exists w, w < e /\ ext_pick (Pf_ N) N w).
        now exists w. eapply ext_pick_attention in H1.
        destruct H1 as [g [HEg Hg]].
        eapply (Hs g HEg); last apply Hg. lia. lia.
      - exists N. now left.
    Qed.

    Lemma ext_intersect_W_intersect k e: 
      ~ (Pf_ k # W[k] e) -> W e #ₚ P -> False.
    Proof.
      unfold ext_intersect_W.
      intros H1 H2. apply H1.
      intros y Hy1 [w Hy2].
      eapply (H2 y). now exists w.
      eapply (In_Pf Hy1).
    Qed.

    Lemma P_meet_R_simple : forall e, R_simple P e.
    Proof.
      intros e He. intros He'.
      eapply (non_finite_attention He).
      intros [k [H|H]].
      - eapply ext_intersect_W_intersect; eauto.
      - eapply attention_active in H.
        eapply ext_intersect_W_intersect; eauto.
    Qed.

  End Meet_Requirement.

  Section Result.

    Lemma P_semi_decidable : semi_decidable P.
    Proof.
      apply F_with_semi_decidable.
    Qed.

    Theorem P_simple : simple P.
    Proof.
      unfold simple; repeat split.
      - rewrite EA.enum_iff. now apply P_semi_decidable.
      - apply P_coinfinite.
      - intros [q (Hqenum & Hqinf & Hq)].
        rewrite EA.enum_iff in Hqenum.
        destruct (W_spec Hqenum) as [c HWq].
        apply (@P_meet_R_simple c).
        intros [l Hqe]; apply Hqinf.
        exists l. intros x Hqx. apply (Hqe x).
        now rewrite HWq in Hqx.
        intros x HWcx HPx. unfold W in HWcx.
        rewrite <- (HWq x) in HWcx. apply (Hq x HWcx HPx).
    Qed.

  End Result.

  Section Effectively_Simple.

    Definition effectively_simple P := 
      simple P /\  exists f, 
        forall e, (forall x, W e x -> (compl P) x) -> forall x, W e x -> x < (f e).

    Lemma attention_pick e k: attention e k -> exists x, x > 2*e /\ P x /\ W e x.
    Proof.
      intros [He H].
      edestruct (ext_pick_witness) as [x Hx].
      { destruct H. eapply e0. }
      assert (P_ (S k) (Pf_ (S k))) by apply F_func_correctness.
      inv H0. cbn in H4. assert (ext_least_choice l k x) as Hwitness.
      exists e. assert (Pf_ k = l) as <-.
      eapply F_uni. apply F_func_correctness. apply H3.
      split; first easy. split; first easy. easy.
      assert (x = a) as ->. eapply (@extend_uni simple_extendsion); cbn; eauto.
      exists a. split. destruct H4, H0, H1, H4, H4.
      assert (x=e) as HE.
      { eapply least_unique; last eapply H.
      enough (l=(Pf_ k)) as -> by easy. eapply F_uni; eauto. apply F_func_correctness. }
      lia. split. exists (Pf_ (S k)), (S k); split; eauto. now rewrite <- H2.
      apply F_func_correctness. destruct H4, H0, H1, H4, H4, H4, H4.
      assert (x=e) as HE.
      { eapply least_unique; last eapply H.
      enough (l=(Pf_ k)) as -> by easy. eapply F_uni; eauto. apply F_func_correctness. }
      exists x0; congruence.
      exfalso. eapply (H3 x); exists e; do 2 (split; eauto). 
      enough ((Pf_ k) = (Pf_ (S k))) as <- by easy. 
      assert (F_ simple_extendsion k (Pf_ k)) by apply F_func_correctness.
      eapply F_uni; eauto.
    Qed.
  
    Theorem P_effectively_simple: effectively_simple P.
    Proof.
      split; first apply P_simple.
      exists (fun e => 2 * e + 1).
      intros e He x Hex. enough (~ 2 * e < x) by lia.
      intros Hex'.
      assert (W e #ₚ P).
      { intros y Hy1 Hy2. now apply (He y). }
      assert (forall k, (Pf_ k) # W[k] e).
      { intros k y Hy1 [w [_ Hy2]]. eapply (H y). exists w; eauto.
        exists (Pf_ k), k; split; eauto. apply F_func_correctness. }
      enough (exists k, attention e k) as [k Hk].
      (* apply H1. intros [k Hk]. *)
      eapply attention_pick in Hk.
      destruct Hk as [y (Hx1&Hx2&Hx3)].
      eapply (He y); eauto.   
      { unfold attention.
        assert (exists k, least (ext_pick (Pf_ k) k) e /\ e < k).
        { destruct Hex as [k Hk].
          pose (S (max e k)) as N. 
          unfold ext_pick. exists N. split. split. split. admit.
          exists x. unfold ext_has_wit. split; last easy.
          exists k; split; eauto. lia. 2: {lia. } admit.
        }
      admit.
      }
    Admitted.

  End Effectively_Simple.

End Assume_EA.

Require SyntheticComputability.Axioms.EA.

Lemma EA_correctness: Σ φ, EA φ.
Proof.
    Import SyntheticComputability.Axioms.EA.Assume_EA.
    exists φ. intros P HP%SyntheticComputability.Axioms.EA.enum_iff.
    rewrite W_spec in HP. destruct HP as [c Hc].
    exists c. intros x. unfold W in Hc.
    apply Hc.
Qed.