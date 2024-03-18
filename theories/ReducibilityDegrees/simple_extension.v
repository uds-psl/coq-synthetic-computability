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

Section EWO.
  Variable p: nat -> Prop.
  Inductive T | (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Definition T_elim (q: nat -> Type)
    : (forall n, (~p n -> q (S n)) -> q n) ->
      forall n, T n -> q n
    := fun e => fix f n a :=
      let (phi) := a in
      e n (fun h => f (S n) (phi h)).

  (*** EWO for Numbers *)

  Lemma TI n :
    p n -> T n.
  Proof.
    intros H. constructor. intros H1. destruct (H1 H).
  Qed.

  Lemma TD n :
    T (S n) -> T n.
  Proof.
    intros H. constructor. intros _. exact H.
  Qed.

  Variable p_dec: forall n, dec (p n).

  Definition TE (q: nat -> Type)
    : (forall n, p n -> q n) ->
      (forall n, ~p n -> q (S n) -> q n) ->
      forall n, T n -> q n.
  Proof.
    intros e1 e2.
    apply T_elim. intros n IH.
    destruct (p_dec n); auto.
  Qed.

  (** From now on T will only be used through TI, TD, and TE *)

  
  Lemma T_zero n :
    T n -> T 0.
  Proof.
    induction n as [|n IH].
    - auto.
    - intros H. apply IH. apply TD, H.
  Qed.

  Definition ewo_nat :
    ex p -> Σ x, p x.
  Proof.
    intros H.
    refine (@TE (fun _ => Σ x, p x) _ _ 0 _).
    - eauto.
    - easy.
    - destruct H as [n H]. apply (@T_zero n), TI, H.
  Qed.
  
End EWO.

Notation unique p := (forall x x', p x -> p x' -> x = x').
Section LeastWitness.
    Definition safe p n := forall k, k < n -> ~ p k.
    Definition least p n := p n /\ safe p n.

    Fact least_unique p : unique (least p).
    Proof.
      intros n n' [H1 H2] [H1' H2'].
      enough (~(n < n') /\ ~(n' < n)) by lia.
      split; intros H.
      - eapply H2'; eassumption.
      - eapply H2; eassumption.
    Qed.

    Fact safe_O p :
      safe p 0.
    Proof.
      hnf. lia.
    Qed.

    Fact safe_S p n :
      safe p n -> ~p n -> safe p (S n).
    Proof.
      intros H1 H2 k H3. unfold safe in *.
      assert (k < n \/ k = n) as [H|H] by lia.
      - auto.
      - congruence.
    Qed.

    Fact safe_char p n :
      safe p n <-> forall k, p k -> k >= n.
    Proof.
      split.
      - intros H k H1.
        enough (k < n -> False) by lia.
        intros H2. apply H in H2. auto.
      - intros H k H1 H2. apply H in H2. lia.
    Qed.

    Fact safe_char_S p n :
      safe p (S n) <-> safe p n /\ ~p n.
    Proof.
      split.
      - intros H. split.
        + intros k H1. apply H. lia.
        + apply H. lia.
      - intros [H1 H2]. apply safe_S; assumption.
    Qed.

    Fact safe_eq p n k :
      safe p n -> k <= n -> p k -> k = n.
    Proof.
      intros H1 H2 H3. unfold safe in *.
      enough (~(k < n)) by lia.
      specialize (H1 k). tauto.
    Qed.

    Fact E14 x y z :
      x - y = z <-> least (fun k => x <= y + k) z.
    Proof.
      assert (H: least (fun k => x <= y + k) (x - y)).
      { split; unfold safe; lia. }
      split. congruence.
      eapply least_unique, H.
    Qed.  

    (*** Certifying LWOs *)

  Section LWO.
      Variable p : nat -> Prop.
      Variable p_dec : forall x, dec (p x).

    Definition lwo :
      forall n, (Σ k, k < n /\ least p k) + safe p n.
    Proof.
      induction n as [|n IH].
      - right. apply safe_O.
      - destruct IH as [[k H1]|H1].
        + left. exists k. destruct H1 as [H1 H2]. split. lia. exact H2.
        + destruct (p_dec n).
          * left. exists n. split. lia. easy.
          * right. apply safe_S; assumption.
    Defined.

    Definition lwo' :
      forall n, (Σ k, k <= n /\ least p k) + safe p (S n).
    Proof.
      intros n.
      destruct (lwo (S n)) as [(k&H1&H2)|H].
      - left. exists k. split. lia. exact H2.
      - right.  exact H.
    Qed.

    Definition least_sig :
      (Σ x, p x) -> Σ x, (least p) x.
    Proof.
      intros [n H].
      destruct (lwo (S n)) as [(k&H1&H2)|H1].
      - exists k. exact H2.
      - exfalso. apply (H1 n). lia. exact H.
    Qed.

    Definition least_ex :
      ex p -> ex (least p).
    Proof.
      intros [n H].
      destruct (lwo (S n)) as [(k&H1&H2)|H1].
      - exists k. exact H2.
      - exfalso. apply (H1 n). lia. exact H.
    Qed.

    Definition safe_dec n :
      dec (safe p n).
    Proof.
      destruct (lwo n) as [[k H1]|H1].
      - right. intros H. exfalso.
        destruct H1 as [H1 H2]. apply (H k). exact H1. apply H2.
      - left. exact H1.
    Defined.

    Definition least_dec n :
      dec (least p n).
    Proof.
      unfold least.
      destruct (p_dec n) as [H|H].
      2:{ right. tauto. }
      destruct (safe_dec n) as [H1|H1].
      - left. easy.
      - right. tauto.
    Qed.
  End LWO.

    Lemma exists_bounded_dec' P:
    (forall x, dec (P x)) -> forall k, dec (exists n, n < k /\ P n).
    Proof.
      intros Hp k.
      induction k. right; intros [? [? _]]; lia.
      destruct IHk as [Hw|Hw].
      - left. destruct Hw as [x [Hx1 Hx2]]. exists x; split; eauto; lia.
      - destruct (Hp k). left. exists k; split; eauto; lia.
        right. intros [x [Hx1 Hx2]].
        assert (x = k \/ x < k) as [->|Hk] by lia; firstorder.
    Qed.

    Lemma exists_bounded_dec P:
      (forall x, dec (P x)) -> forall k, dec (exists n, n <= k /\ P n).
    Proof.
      intros Hp k.
      induction k. destruct (Hp 0). left. exists 0. eauto.
      right. intros [x [Hx Hx']]. now assert (x=0) as -> by lia.
      destruct IHk as [Hw|Hw].
      - left. destruct Hw as [x [Hx1 Hx2]]. exists x; split; eauto; lia.
      - destruct (Hp (S k)). left. exists (S k); split; eauto; lia.
        right. intros [x [Hx1 Hx2]].
        assert (x = S k \/ x <= k) as [->|Hk] by lia; firstorder.
    Qed.

    Definition bounded (P: nat -> Prop) := Σ N, forall x, P x -> x < N.

    Fact bouned_le (P Q: nat -> Prop) N :
      (forall x, P x -> x < N) -> 
      (exists x, P x /\ Q x) <->  exists x, x < N /\ P x /\ Q x.
    Proof.
      intros Hn; split.
      - intros [x Hx]. exists x; intuition eauto.
      - intros (x&c&Hc). exists x; intuition eauto.
    Qed.

    Lemma bounded_dec (P Q: nat -> Prop):
      (forall x, dec (P x)) -> (forall x, dec (Q x)) -> 
      bounded P -> dec (exists n, P n /\ Q n).
    Proof.
      intros H1 H2 [N HN].
      assert (dec (exists n, n < N /\ P n /\ Q n)) as [H|H].
      - eapply exists_bounded_dec'. intro; eapply and_dec; eauto.
      - left. rewrite bouned_le; eauto.
      - right. intros H'%(@bouned_le _ _ N); easy.
    Qed.
    Lemma dec_neg_dec P: dec P -> dec (~ P).
    Proof. intros [H|H]. right; eauto. now left. Qed.

End LeastWitness.

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

  Definition disj {X} (A: list X) (B: X -> Prop) := forall x, In x A -> B x -> False.
  Definition intersect {X} (A B: X -> Prop) := forall x, A x -> B x -> False.
  Notation "A # B" := (disj A B) (at level 30).

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
    Definition incl_e L e := ~ (L # (W e)).

  End Simple_Extension.

  Section Requirements.
    Definition R_simple_list L e := non_finite e -> incl_e L e.

    Definition attention e n := e < n /\ least (ext_pick (Pf_ n) n) e.
    Definition active e n := ~ (Pf_ n) # W[n] e.
    Definition pick_el (e x: nat) := exists k, attention e k /\ ext_least_choice (Pf_ k) k x.

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

    Lemma active_incl e n: active e n -> forall m, n <= m -> active e m .
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

    Lemma active_hold e k: attention e k -> forall m, k < m -> active e m.
    Proof.
      intros. eapply active_incl.
      apply attention_active. apply H. lia.
    Qed.

    Lemma attention_uni e k1 k2 : attention e k1 -> attention e k2 -> k1 = k2.
    Proof.
      intros H1 H2.
      specialize (fun a b => @active_not_attention _ _ (@active_hold _ _ H1 a b)) as H1'.
      specialize (fun a b => @active_not_attention _ _ (@active_hold _ _ H2 a b)) as H2'.
      enough (~ k1 < k2 /\ ~ k2 < k1) by lia; split.
      intro Hk. eapply H1'. apply Hk. easy. 
      intro Hk. eapply H2'. apply Hk. easy.
    Qed.

    Lemma spec_uni e x1 x2: pick_el e x1 -> pick_el e x2 -> x1 = x2 .
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
          now rewrite (spec_uni H0 Hs) in H6.
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
      + intuition.
      + apply in_seq in H1. lia.
    - intros [H1 H2]. eapply in_filter_iff. split.
      + apply in_seq; lia.
      + destruct Dec; cbn; try tauto. exfalso. firstorder.
    Qed.

    Lemma Compl_P_Listing:
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
      intros n H. eapply Compl_P_Listing with (n := n).
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

    Definition R_simple P e := non_finite e -> ~ (intersect (W e) P).

    Lemma R_simple_acc e L:
      R_simple_list L e -> forall L', incl L L' -> R_simple_list L' e .
    Proof.
      intros H L' HL' h1 h2.
      apply H; first easy.
      firstorder.
    Qed.
(* 
    Lemma try1 e:
      non_finite e -> exists s, 
      ( ~~(Pf_ s) # (W[s] e)) \/ 
        (ext_intersect_W (Pf_ s) e s /\ exists x, 2 * e < x /\ (W[s] e) x).
    Proof.
      (* intros H HI. unfold inifite in H. *)
      (* rewrite non_finite_spec in H. *)
    Admitted.

    Lemma try3 e: 
      (forall n, n < e -> non_finite n -> exists k, incl_e (Pf_ k) n) -> 
      non_finite e ->
      exists w, attention e w \/ incl_e (Pf_ w) e.
    Proof.
      intros He Hinfe.
      destruct (try1 Hinfe) as [w [ Hx| Hw]].
      - exists w. right. unfold incl_e.
        intro H. apply Hx. intro Hx'.
        admit.
      - 
    Admitted. *)

    Lemma impl_dn (P Q: Prop):
      (~~ (P -> Q)) <-> (P -> ~~Q) .
    Proof. split; firstorder. Qed.
    
(* 
    Lemma try2:
      forall e, non_finite e -> ~~ exists m, incl_e (Pf_ m) e.
    Proof.
      (* strong induction e. intros He.
      destruct (@try3 e H He) as [w [Hw| Hw]].
      specialize (attention_active Hw) as Hw'.
      exists (S w).
      intro Hx. unfold active in Hw'.
      apply Hw'. intros y Hy1 [i [Hie Hi]].
      apply (Hx y Hy1). now exists i.
      now exists w. *)
    Admitted. *)

    (* Lemma P_meet_R_simple : forall e, R_simple P e.
    Proof.
      intros e H3. 
      destruct (try2 H3) as [m Hm].
      intros Hin. apply Hm.
      intros x Hx Hx'.
      apply (Hin x Hx').
      unfold P. unfold F_with.
      exists (Pf_ m), m. 
      split; last apply F_func_correctness.
      easy.
    Abort. *)

    Lemma which_one_is_the_best {X} (P Q: X -> Prop):
      (forall x, P x -> Q x -> False) <-> (~ exists x, P x /\ Q x) .
    Proof.
      split.
      - intros Hf [x [h1 h2]]. eapply Hf; eauto.
      - intros Hf x px qx. eapply Hf; eauto.
    Qed.

    Lemma quant_swap {X} (P: X -> Prop):
      (~ forall x, ~ P x) -> ~~ exists x, P x.
    Proof. eauto. Qed.


    Lemma non_finite_not_bounded e: 
      non_finite e -> 
        ~~ exists k, exists x, (W[k] e) x /\ 2 * e < x.
    Proof.
      intro H. unfold non_finite in H.
      intros He.  rewrite non_finite_nat in H.
      specialize (H (2 * e + 1)).
      apply H. intros [m [Hm1 [k Hmk]]].
      apply He. exists k, m; split; last lia.
      now exists k.
    Qed.
(* 
    Lemma : 
    forall y, y < e -> ~~ R_simple P y
      (exists k, exists x, W[k] e x /\ 2 * e < x).
    Proof.
      
    Qed.
     *)
    Lemma P_meet_R_simple' : forall e, ~ ~ R_simple P e.
    Proof.
      intro e. strong induction e.
      unfold R_simple. rewrite impl_dn.
      intros B%non_finite_not_bounded.
      intros Hi. eapply B. intros (k&x&Hk&Hx).
      eapply Hi. intros Hin.
      pose (N := S (max e k)).
      destruct (Dec (ext_intersect_W (Pf_ N) N e)) as [He|He].
      - assert (ext_pick (Pf_ N) N e).
      { unfold ext_pick. split. easy.
        exists x. split. destruct Hk as [w [Hw1 Hw2]].
        exists w. split; eauto. lia. eauto. }
        assert (attention e N).
        unfold attention. split. lia.
        split. easy. intros j Hj%H.
        intros Hj2. apply Hj.
        intros Hj3.
        unfold ext_pick in Hj2.
        admit.
        eapply attention_active in H1.
        apply H1. intros y Hy1 [w [_ Hw]].
        eapply Hin. exists w. eapply Hw.
        exists (Pf_ (S N)), (S N).
        split. easy. eapply F_func_correctness. 
      - eapply He. intros y Hy1 [w [_ Hw]].
        eapply Hin. exists w. eapply Hw.
        exists (Pf_ N), N; split.
        easy. eapply F_func_correctness.
    Admitted.
    
    (* Lemma Good_req Q e: ~~ R_simple Q e -> R_simple Q e.
    Proof.
      intros H. unfold R_simple, intersect.
      rewrite which_one_is_the_best.
      rewrite <- impl_dn. 
    Qed. *)
    


  End Meet_Requirement.

  (* Lemma list_accu e:
    (forall k, k < e -> inifite k -> exists L, incl_e L k /\ exists n, F_ simple_extendsion n L) ->
    exists m L, F_ simple_extendsion m L /\ forall n, n < e -> R_simple_list L n.
  Proof.
    intros. induction e.
    { exists 0, []; split; first econstructor. intros n Hn. lia. }
    destruct IHe as [m [HL' [Hm HL2']]].
    { intros n Hn He. apply H. lia. easy. }
    pose (H e).
    (* destruct (H e) as [L [HL1 HL2]]; first lia. *)
    (* destruct HL2 as [k Hk].  *)
    
    (* destruct (dec_le m k).
    + exists k, L; split; eauto.
      intros n Hn. assert (n = e \/ n < e) as [->|H'] by lia.
      apply HL1. eapply R_simple_acc. apply HL2'; first easy.
      eapply F_mono; eauto.
    + exists m, HL'; split; eauto.
      intros n Hn.  assert (n = e \/ n < e) as [->|H'] by lia.
      eapply R_simple_acc. apply HL1. eapply F_mono; eauto with lia.
      now eapply HL2'.
  Qed. *)
  Admitted. *)


  (* Lemma eventually_attention e m L: 
    inifite e -> 
    (forall n : nat, n < e -> inifite n -> incl_e L n -> F_ simple_extendsion m L) -> 
    exists k, attention e k.
  Proof.
    intros H1 H2.
    unfold attention. 
    
  Admitted. *)


  Section Result.

    Lemma P_semi_decidable : semi_decidable P.
    Proof.
      apply F_with_semi_decidable.
    Qed.


    Lemma P_simple : simple P.
    Proof.
      unfold simple; repeat split.
      - rewrite EA.enum_iff. now apply P_semi_decidable.
      - apply P_coinfinite.
      - intros [q (Hqenum & Hqinf & Hq)].
        rewrite EA.enum_iff in Hqenum.
        destruct (W_spec Hqenum) as [c HWq].
        apply (@P_meet_R_simple' c). intros H. apply H.
        intros [l Hqe]; apply Hqinf.
        exists l. intros x Hqx. apply (Hqe x).
        now rewrite HWq in Hqx.
        intros x HWcx HPx. unfold W in HWcx.
        rewrite <- (HWq x) in HWcx. apply (Hq x HWcx HPx).
    Qed.

  End Result.

End Assume_EA.


Require SyntheticComputability.Axioms.EA.

Lemma EA_correctness: Σ φ, EA φ.
Proof.
  Import SyntheticComputability.Axioms.EA.Assume_EA.
    exists φ.
    intros P HP%SyntheticComputability.Axioms.EA.enum_iff.
    rewrite W_spec in HP. destruct HP as [c Hc].
    exists c. intros x. unfold W in Hc.
    apply Hc.
Qed.