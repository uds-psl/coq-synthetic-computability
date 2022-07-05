Require Import stdpp.list stdpp.list_numbers.
From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts reductions partial Axioms.Equivalence principles kleenetree Synthetic.MoreEnumerabilityFacts mu_nat Shared.Dec.
Require Import ssreflect Nat.

(** ** Continuity  *)

Definition continuous {X Y} `{EqDecision X} `{EqDecision Y} (F : (nat -> X) -> (nat -> Y)) :=
  forall n f, exists L, forall g, map f L = map g L -> F f n = F g n.

Definition modulus {X Y} `{EqDecision X} `{EqDecision Y} (M : (nat -> X) -> nat -> list nat) (F : (nat -> X) -> (nat -> Y)) :=
  forall f n, forall g, map f (M f n) = map g (M f n) -> F f n = F g n.

Lemma equiv_on_eq A :
  equiv_on A.
Proof.
  exists eq. abstract exact _.
Defined.

Arguments ext_equiv {_ _ _}, {_ _} _.

Definition Homeo_M A B `{EqDecision A} `{EqDecision B} := exists (F : (nat -> A) -> (nat -> B)) M, Inj (@equiv_rel _ (ext_equiv (equiv_on_eq A)))
                                                                                           (@equiv_rel _ (ext_equiv (equiv_on_eq B))) F
                                                                                       /\ Surj (@equiv_rel _ (ext_equiv (equiv_on_eq B))) F
                                                                                       /\ modulus M F
                                                                                       /\ continuous M.

Definition extend (l : list bool) (n : nat) := nth n l false.

Lemma listable_list_length_lt : ∀ k : nat, listable (λ x : list bool, length x < k).
Proof.
  induction k as [ | k [L IH] ].
  - exists []. intros [] ; cbv ; firstorder auto with *.
  - destruct (listable_list_length k) as [Lk Hk].
    exists (L ++ Lk).
    intros l. cbn.
    rewrite in_app_iff - IH - Hk. lia.
Qed.

Lemma take_map {X} (l : list X) {Y} (f : X -> Y) n :
  take n (map f l) = map f (take n l).
Proof.
  induction n in l |- *.
  - reflexivity.
  - destruct l. reflexivity. cbn. congruence.
Qed.

Lemma take_seq n m s :
  n <= m -> take n (seq s m) = seq s n.
Proof.
  induction 1.
  - rewrite <- (seq_length n s) at 1.
    now rewrite firstn_all.
  - replace (S m) with (m + 1) by lia.
    rewrite seq_app firstn_app IHle seq_length.
    replace (n - m) with 0 by lia. cbn.
    now rewrite app_nil_r.
Qed.

Lemma max_list_incl A B :
  incl A B -> max_list A <= max_list B.
Proof.
  induction A.
  - cbn. lia.
  - cbn. intros H. eapply Max.max_lub.
    2: firstorder. eapply max_list_spec, H. firstorder.
Qed.

Lemma Homeo_M_Cantor_Baire_to_KT : Homeo_M bool nat -> inhabited Kleene_tree.
Proof.
  intros (F & M & Finj & Fsurj & Mmod & contM). econstructor.
  unshelve econstructor.
  exists (fun l => forall i, 0 < i <= length l -> Exists (le i) (M (extend (take i l)) 0)).
  econstructor; cbn.
  - exists []. cbn. intros [] H; try lia.
  - intros l1 l2 Hpref H i Hi.
    enough (take i l1 = take i l2) as ->.
    + eapply H. eapply prefix_length in Hpref. lia.
    + destruct Hpref as [l' ->]. rewrite firstn_app.
      replace (i - length l1) with 0 by lia. now rewrite firstn_O app_nil_r.
  - eapply decidable_iff. econstructor.
    intros. eapply listable_forall_dec.
    + exists (seq 1 (length x)). clear. intros. rewrite in_seq. lia.
    + intros. eapply Exists_dec. intros. eapply le_dec.
  - eapply not_bounded_infinite. cbn.
    intros [n H].
    destruct (listable_list_length_lt (S (S n))) as [L HL].
    pose (N := max_list (map (fun l => F (extend l) 0) L)).
    destruct (Fsurj (fun _ => S N)) as [f_N H_N].
    
    specialize (H (map f_N (seq 0 n))).
    rewrite map_length seq_length in H.
    specialize (H (le_refl _)).
    edestruct (listable_exists_dec (p := fun i => 0 < i <= n) ( q := fun i => ~ Exists (le i) (M (extend (take i (map f_N (seq 0 n)))) 0))).
    + exists (seq 1 n). clear. intros. rewrite in_seq. lia.
    + intros x. eapply not_dec. eapply Exists_dec. intros. eapply le_dec.
    + destruct e as (m & Hle & Hm).
      eapply Forall_Exists_neg in Hm.
      setoid_rewrite List.Forall_forall in Hm.
      setoid_rewrite take_map in Hm.
      setoid_rewrite take_seq in Hm. 2:lia.
      assert (Hm' :  ∀ x : nat, In x (M (extend (map f_N (seq 0 m))) 0) → x < m).
      { intros x H0. eapply not_le, Hm, H0. }
      clear Hm. rename Hm' into Hm.

      enough (F f_N 0 <= N) as H0.
      * rewrite H_N in H0. lia.
      * red in Mmod.
        erewrite <- Mmod with (f := extend (map f_N (seq 0 m))).
        -- eapply max_list_spec. eapply in_map_iff.
           eexists. split. reflexivity. eapply HL.
           rewrite map_length seq_length. lia.
        -- eapply map_ext_in.
           intros a Ha. unfold extend. eapply Hm in Ha.
           erewrite nth_indep.
           erewrite map_nth, seq_nth. reflexivity. lia.
           now rewrite map_length seq_length.
    + edestruct H. intros.
      edestruct @Exists_dec.
      2:{ exact e. }
      * intros. eapply le_dec.
      * edestruct n0. destruct H0. eauto. 
  - cbn. intros f.
    destruct (contM 0 f) as [L HL].
    pose (N := 1 + max_list (1 + length L :: L ++ M f 0)).
    exists N. intros H.
    enough (N < N) by lia.

    eapply lt_le_trans with (m := 1 + max_list (M (extend (map f (seq 0 N))) 0)).
    + specialize (H N). setoid_rewrite List.Exists_exists in H.
      destruct H as [i Hi].
      * split. unfold N. cbn. lia. now rewrite map_length seq_length.
      * eapply le_lt_trans. eapply Hi.
        enough (max_list [i] <=  max_list (M (extend (map f (seq 0 N))) 0)) as H0.
        unfold max_list in H0 at 1. rewrite Max.max_0_r in H0. unfold id in H0 at 1. lia.
        eapply max_list_incl. intros ? [-> | []].
        replace N with (length (map f (seq 0 N))) in Hi at 1.
        rewrite firstn_all in Hi. eapply Hi.
        now rewrite map_length seq_length.
    + unfold N. rewrite <- HL.
      eapply plus_le_compat_l.
      eapply max_list_incl, incl_tl, incl_appr, incl_refl.
      eapply map_ext_in.
      intros a Ha. unfold extend. 
      erewrite nth_indep.
      erewrite map_nth, seq_nth.
      * reflexivity.
      * enough (max_list [a] <=  max_list (1 + length L :: L ++ M f 0)) as H0.
        unfold max_list in H0 at 1. rewrite Max.max_0_r in H0. unfold id in H0 at 1. lia.
        eapply max_list_incl. intros ? [-> | []]. eapply in_cons, in_app_iff. eauto.
      * rewrite map_length seq_length.
        enough (max_list [a] <=  max_list (1 + length L :: L ++ M f 0)) as H0.
        unfold max_list in H0 at 1. rewrite Max.max_0_r in H0. unfold id in H0 at 1. lia.
        eapply max_list_incl. intros ? [-> | []]. eapply in_cons, in_app_iff. eauto.
        Unshelve. all:econstructor.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma nth_sig {X} i l : i < @length X l -> {x | l !! i = Some x}.
Proof.
  move => / lookup_lt_is_Some_2 H.
  destruct (l !! i).
  - eauto.
  - exfalso. firstorder congruence.
Qed.

Section fix_tree.

Variable T_K : Kleene_tree.

Definition leaf (l : list bool) : Prop := exists l' b, l = l' ++ [b] /\ T_K l' /\ ~ T_K l.

Variable ℓ : nat -> list bool.

Variable enumerable_leafs : forall l, leaf l <-> exists n, ℓ n = l.

Variable ℓ_injective : Inj (=) (=) ℓ.

Lemma ℓ_leaf n : leaf (ℓ n).
Proof.
  eapply enumerable_leafs. eauto.
Qed.
Hint Immediate ℓ_leaf : core.

Fact nil_no_leaf : ~ leaf [].
Proof.
  intros [[ | ?] [? [? ?]]]; cbn in *; congruence.
Qed.

Fact enum_length n : length (ℓ n) > 0.
Proof.
  specialize (ℓ_leaf n).
  destruct (ℓ n).
  - intros [] % nil_no_leaf.
  - cbn. lia.
Qed.

Notation nth H := (proj1_sig (nth_sig H)).

Lemma take_take {X} n m (l : list X) :
  n <= m -> take n (take m l) = take n l.
Proof.
  induction n in m, l |- *; move => H.
  - now rewrite !firstn_O.
  - destruct m. lia.
    destruct l; cbn. reflexivity.
    f_equal. eapply IHn. lia.
Qed.

Lemma take_prefix {X} n (l : list X) :
  prefix (take n l) l.
Proof.
  induction l in n |- *.
  - destruct n; cbn; eapply prefix_nil.
  - destruct n; cbn.
    + eapply prefix_nil.
    + now eapply prefix_cons.
Qed.

Lemma prefix_take_iff {X} (l1 l2 : list X) :
  prefix l1 l2 <-> l1 = take (length l1) l2.
Proof.
  induction l1 in l2 |- *; cbn.
  - destruct l2; cbn; intuition. eauto using prefix_nil.
  - destruct l2; cbn; split.
    + move => H. exfalso. eapply prefix_nil_not. eauto.
    + move => H1. congruence.
    + move => H. rewrite (prefix_cons_inv_1 _ _ _ _ H). 
      f_equal. eapply prefix_cons_inv_2 in H. now eapply IHl1.
    + move => [] -> ->. eapply prefix_cons, take_prefix.
Qed.

Lemma leaf_prefix l1 l2 :
  leaf l1 -> leaf l2 ->
  l1 `prefix_of` l2 -> l1 = l2.
Proof.
  move => [l1' [b1 [-> [H1 nH1]]]] [l2' [b2 [-> [H2 nH2]]]] [l3 Heq].
  rewrite <- app_assoc in Heq.
  destruct (lt_eq_lt_dec (length l2') (length l1')) as [[Hlt|e] | Hgt].
  - eapply (f_equal (take (length l1'))) in Heq.
    rewrite take_app take_ge in Heq.
    rewrite app_length. cbn. lia.
    subst. exfalso. eauto.
  - eapply app_inj_1 in Heq as [-> Heq]; eauto.
    destruct l3; cbn in *; congruence.
  - eapply (f_equal (take (length l2'))) in Heq.
    rewrite take_app in Heq.
    rewrite take_app_ge in Heq. lia.
    cbn in Heq.
    exfalso. destruct (length l2' - length l1') eqn:E. lia.
    cbn in *. subst. 
    eapply nH1, tree_p. eapply (Kleene_T T_K). 2:exact H2.
    eexists. now rewrite <- app_assoc.
Qed.

Fixpoint F' f offset n :=
  match n with
  | 0 => []
  | S n => F' f offset n ++ ℓ(f (offset + n))
  end.

Lemma F'_offset f o n1 n2 :
  F' f o (n1 + n2) = F' f o n2 ++ F' f (n2 + o) n1.
Proof.
  induction n1 in o, n2 |- *; cbn.
  - now rewrite app_nil_r.
  - rewrite IHn1. rewrite <- !app_assoc.
    do 4 f_equal. lia.
Qed.

Lemma F'_length f o n :
  n <= length (F' f o n).
Proof.
  induction n; cbn.
  - lia.
  - rewrite app_length.
    pose proof (enum_length (f (o + n))). lia.
Qed.

Definition F f n := nth (F'_length f 0 (S n)).

Lemma drop_lookup_iff {X} l i (x : X) :
  l !! i = Some x <-> exists l', drop i l = x :: l'.
Proof.
  induction l in i, x |- *.
  - cbn. split.
    + congruence.
    + move => [l' H].
      destruct i; inv H.
  - destruct i.
    + cbn. split.
      * move => [] ->. eauto. 
      * move => [l' []]. congruence.
    + cbn.
      eapply IHl.
Qed.

Lemma F_inj_help f g :
  F f ≡{nat -> bool} F g -> forall k, take k (F' f 0 k) = take k (F' g 0 k).
Proof.
  move => H k.
  induction k.
  - reflexivity.
  - assert (leaf (ℓ (f k))) by eauto.
    assert (leaf (ℓ (g k))) by eauto.
    cbn.
    replace (S k) with (k + 1) by lia.
    rewrite <- !take_take_drop.
    rewrite !take_app_le. 1-2:apply F'_length.
    rewrite IHk. f_equal.
    destruct (drop k (F' f 0 k ++ ℓ (f k))) eqn:E1.
    + eapply (f_equal length) in E1.
      rewrite drop_length in E1. cbn in E1.
      pose proof (F'_length f 0 (S k)). cbn in H2. rewrite app_length in H2, E1.
      lia.
    + destruct (drop k (F' g 0 k ++ ℓ (g k))) eqn:E2.
      * eapply (f_equal length) in E2.
        rewrite drop_length in E2. cbn in E2.
        pose proof (F'_length g 0 (S k)). cbn in H2. rewrite app_length in H2, E2.
        lia.
      * cbn. rewrite !firstn_O. f_equal.
        assert (F' f 0 (S k) !! k = Some b). eapply drop_lookup_iff. eauto.
        assert (F' g 0 (S k) !! k = Some b0). eapply drop_lookup_iff. eauto.
        specialize (H k). rewrite /F in H.
        unfold nth in H.
        destruct (nth_sig (i:=k) (l:=F' f 0 (S k))).
        destruct (nth_sig (i:=k) (l:=F' g 0 (S k))). cbn in *. subst. congruence.
Qed.

Lemma F'_prefix m n o f :
  m <= n -> F' f o m `prefix_of` F' f o n.
Proof.
  induction 1.
  - reflexivity.
  - etransitivity. eassumption.
    cbn. now eapply prefix_app_r.
Qed.

Lemma take_length_ℓ g o m n :
  m <= n ->
  take (length (F' g o m)) (F' g o n) = F' g o m.
Proof.
  induction 1.
  - now rewrite firstn_all.
  - cbn. rewrite take_app_le.
    apply prefix_length, F'_prefix, H. exact IHle.
Qed.

Lemma F'_eq_lt (f g : nat → nat) (n : nat) o : (∀ m : nat, m < o + n → f m ≡{ nat} g m) → F' f o n = F' g o n.
Proof.
  move => IH.
  induction n; cbn.
  - reflexivity.
  - rewrite IHn.
    + move => ? ?. eapply IH. lia.
    + f_equal. f_equal. eapply IH. lia.
Qed.

Lemma F_inj f g :
  F f ≡{nat -> bool} F g -> f ≡{nat -> nat} g.
Proof.
  move => H n. induction n using lt_wf_ind.
  rename H0 into IH.
  - destruct n.
    + clear IH.
      eapply ℓ_injective.
      destruct (le_ge_dec (length (ℓ (f 0))) (length (ℓ (g 0)))) as [Hle | Hge].
      * pose proof (F_inj_help H (length (ℓ (g 0)))) as Heq.
        rewrite (@take_length_ℓ g 0 1) in Heq. eapply (@F'_length g 0 1).
        eapply (f_equal (take (length (ℓ (f 0))))) in Heq.
        rewrite take_take in Heq. lia.
        rewrite (@take_length_ℓ f 0 1) in Heq. eapply enum_length. cbn in Heq.
        eapply prefix_take_iff in Heq.
        eapply leaf_prefix in Heq; eauto.
      * pose proof (F_inj_help H (length (ℓ (f 0)))) as Heq.
        rewrite (@take_length_ℓ f 0 1) in Heq. eapply (@F'_length f 0 1).
        eapply (f_equal (take (length (ℓ (g 0))))) in Heq.
        rewrite take_take in Heq. lia.
        rewrite (@take_length_ℓ g 0 1) in Heq. eapply enum_length. cbn in Heq.
        symmetry in Heq.
        eapply prefix_take_iff in Heq.
        eapply leaf_prefix in Heq; eauto.
    + eapply ℓ_injective.
      destruct (le_ge_dec (length (ℓ (f (S n)))) (length (ℓ (g (S n))))) as [Hle | Hge].
      * pose (k := (length (F' g 0 (S (S n))))).
        pose proof (F_inj_help H k) as Heq.
        pose proof (F'_eq_lt (o := 0) IH) as Hpref.
        assert (S n < k) as [k' Hsum] % nat_le_sum. {
          subst k.
          pose proof (F'_length g 0 ( S (S n))); lia.
        }
        replace (S (S n) + k') with (S k' + S n) in Hsum by lia.
        setoid_rewrite Hsum in Heq at 2 4.
        rewrite !F'_offset !Hpref in Heq.
        rewrite firstn_app in Heq.
        rewrite firstn_app in Heq.
        eapply app_inj_1 in Heq as [_ Heq]; try reflexivity.
        remember (k - length (F' g 0 (S n))) as k''.
        rewrite Nat.add_0_r in Heq.
        replace (S k') with (k' + 1) in Heq by lia.
        rewrite !F'_offset in Heq. cbn in Heq.
        pose (k''' := length (ℓ (g (S n)))).
        eapply (f_equal (take k''')) in Heq.
        assert (k''' <= k''). {
          subst k''' k'' k.
          cbn. rewrite app_length. lia.
        } 
        rewrite !take_take in Heq; eauto.
        rewrite firstn_app in Heq.
        rewrite !Nat.add_0_r in Heq.
        unfold k''' in Heq at 3.
        rewrite take_app in Heq.
        setoid_rewrite take_ge in Heq at 1. 2:eassumption.
        eapply leaf_prefix. eauto. eauto.
        eapply prefix_take_iff. rewrite <- Heq.
        now rewrite take_app.
      * pose (k := (length (F' f 0 (S (S n))))).
        pose proof (F_inj_help H k) as Heq.
        pose proof (F'_eq_lt (o := 0) IH) as Hpref.
        assert (S n < k) as [k' Hsum] % nat_le_sum. {
          subst k.
          pose proof (F'_length f 0 ( S (S n))); lia.
        }
        replace (S (S n) + k') with (S k' + S n) in Hsum by lia.
        setoid_rewrite Hsum in Heq at 2 4.
        rewrite !F'_offset in Heq. rewrite <- !Hpref in Heq.
        rewrite firstn_app in Heq.
        rewrite firstn_app in Heq.
        eapply app_inj_1 in Heq as [_ Heq]; try reflexivity.
        remember (k - length (F' f 0 (S n))) as k''.
        rewrite Nat.add_0_r in Heq.
        replace (S k') with (k' + 1) in Heq by lia.
        rewrite !F'_offset in Heq. cbn in Heq.
        pose (k''' := length (ℓ (f (S n)))).
        eapply (f_equal (take k''')) in Heq.
        assert (k''' <= k''). {
          subst k''' k'' k.
          cbn. rewrite app_length. lia.
        }
        rewrite !take_take in Heq; eauto.
        symmetry in Heq.
        rewrite firstn_app in Heq.
        rewrite !Nat.add_0_r in Heq.
        unfold k''' in Heq at 3.
        rewrite take_app in Heq.
        setoid_rewrite take_ge in Heq at 1. 2:eassumption.
        symmetry.
        eapply leaf_prefix. eauto. eauto.
        eapply prefix_take_iff. rewrite <- Heq.
        now rewrite take_app.
Qed.      

Lemma exists_leaf l2 :
  ~ T_K l2 -> exists l1, l1 `prefix_of` l2 /\ leaf l1.
Proof.
  induction l2 using rev_ind.
  - move => [].
    destruct (tree_inhab T_K).
    eapply tree_p. eapply Kleene_T. eapply prefix_nil. eassumption.
  - move => H.
    destruct (tree_dec T_K) as [f].
    specialize (H0 l2). destruct (f l2).
    + assert (T_K l2) by firstorder congruence.
      exists (l2 ++ [x]). split.
      * eauto.
      * exists l2, x. eauto.
    + assert (~ T_K l2) by firstorder congruence.
      eapply IHl2 in H1 as [l1 []].
      exists l1. split. now eapply prefix_app_r. eassumption.
Qed.

Lemma F_find_pref g :
  { l : list bool | leaf l /\ l = map g (seq 0 (length l)) }.
Proof.
  enough (exists n, ℓ n = map g (seq 0 (length (ℓ n)))).
  eapply mu_nat_p in H.
  - destruct H as [n H]. exists (ℓ n).
    eauto.
  - move => n. repeat decide equality.
  - pose proof (Kleene_inf_exit T_K g) as [k H].
    eapply exists_leaf in H as [l [H1 H2]].
    eapply enumerable_leafs in H2 as [n].
    exists n. rewrite H. clear - H1.
    destruct H1 as [l2 H].
    revert H. generalize 0 as n. move => n H.
    induction l in n, k, l2, H |- *.
    + cbn in *. eauto.
    + cbn in *. destruct k; inv H. f_equal.
      eapply IHl. eassumption.
Qed.

Lemma ℓ_sig l : leaf l -> {n | ℓ n = l}.
Proof.
  move => L.
  eapply mu_nat_dep.
  - move => n. repeat decide equality.
  - now eapply enumerable_leafs. 
Defined.

Lemma ℓ_sig_prf l H1 H2 : proj1_sig (@ℓ_sig l H1) = proj1_sig (@ℓ_sig l H2).
Proof.
  eapply mu_nat_dep_irrel.
Qed.

Definition nxt g := (fun n => g (n + length (proj1_sig (F_find_pref g)))).

Program Definition G g n := proj1_sig (@ℓ_sig (proj1_sig (F_find_pref (PeanoNat.Nat.iter n nxt g))) _). 
Next Obligation.
  intros. destruct F_find_pref. cbn. eapply a.
Qed.

Lemma G_inv g n :
  ℓ (G g n) = proj1_sig (F_find_pref (PeanoNat.Nat.iter n nxt g)).
Proof.
  unfold G. now destruct ℓ_sig.
Qed.

Lemma map_seq_eq {X} (f1 f2 : nat -> X) n1 n2 m :
  (forall x, f1 (x + n1) = f2 (x + n2)) ->
  map f1 (seq n1 m) = map f2 (seq n2 m).
Proof.
  move => H. induction m in n1, n2, H |- * ; cbn.
  - reflexivity.
  - f_equal.
    eapply (H 0). 
    eapply IHm. move => x.
    rewrite !Nat.add_succ_r.
    eapply (H (S x)). 
Qed.

Lemma F'_length_g o m g :
  length (F' (G g) (S o) m) = length (F' (G (nxt g)) o m).
Proof.
  induction m in o, g |- *; cbn.
  - reflexivity.
  - rewrite !app_length IHm.
    f_equal.
    now rewrite !G_inv Nat_iter_S_r.
Qed.

Lemma nxt_iter:
  ∀ (g : nat → bool) (m n : nat), Nat.iter m nxt g n = g (n + length (F' (G g) 0 m)).
Proof.
  move => g m n.
  induction m in g, n |- *.
  - cbn. now rewrite <- plus_n_O.
  - rewrite Nat_iter_S_r IHm. rewrite <- F'_length_g.
    replace (S m) with (m + 1) by lia.
    rewrite F'_offset /nxt app_length. cbn.
    f_equal. rewrite G_inv. cbn. lia.
Qed.

Lemma F_inv g m :
  F' (G g) 0 m = map g (seq 0 (length ((F' (G g) 0 m)))).
Proof.
  induction m in g |- *; cbn.
  - reflexivity.
  - rewrite IHm.
    rewrite app_length seq_app map_app map_length seq_length.
    f_equal.
    rewrite G_inv.
    destruct F_find_pref as [l [Hl e]].
    cbn. rewrite e.
    rewrite map_length seq_length.
    eapply map_seq_eq. clear.
    move => n. rewrite <- plus_n_O.
    eapply nxt_iter.
Qed.

Lemma F_surj g :
  F (G g) ≡{nat -> bool} g.
Proof.
  move => n. cbn.
  unfold F. destruct nth_sig as [b Hb].
  cbn.
  rewrite F_inv in Hb.
  eapply lookup_map in Hb as [? [H ->]].
  now eapply lookup_seq in H as [-> _].
Qed.

Theorem F_G_inv f g :
  G (F f) ≡{nat -> nat} f /\ F (G g)≡{nat -> bool} g.
Proof.
  split.
  - eapply F_inj.
    rewrite F_surj.
    reflexivity.
  - eapply F_surj.
Qed.
(* Print Assumptions F_G_inv. *)

Lemma continuous_F : modulus (fun f x => seq 0 (S x)) F.
Proof.
  move => f x g H.
  enough (F' f 0 (S x) = F' g 0 (S x)).
  - unfold F. destruct nth_sig, nth_sig. cbn. congruence.
  - revert H. generalize (S x). clear. move => x.
    generalize 0. 
    move => o H.
    induction x in o, H |- *.
    + reflexivity.
    + cbn.
      replace (S x) with (x + 1) in H by lia.
      rewrite !seq_app !map_app in H.
      unshelve epose proof (app_inj_1 _ _ _ _ _ H) as [E1 E2].
      now rewrite !map_length !seq_length.
      cbn in *. inv E2. now rewrite H1 IHx.
Qed.

Lemma to_Homeo_M_nat_bool :
  Homeo_M nat bool.
Proof.
  exists F. eexists.
  repeat split.
  - intros ? ? ?. eapply F_inj. eassumption.
  - intros ?. eexists. eapply F_surj.
  - eapply continuous_F.
  - intros x f. eexists []. reflexivity.
Qed.

Lemma F_find_pref_ext:
  ∀ g g2 : nat → bool, (∀ a : nat, a < length (proj1_sig (F_find_pref g)) → g a = g2 a) → proj1_sig (F_find_pref g) = proj1_sig (F_find_pref g2).
Proof.
  move => g g2 Hg.
  destruct F_find_pref as [l1 [H1 H2]], F_find_pref as [l2 [H3 H4]].
  cbn in *.
  destruct (lt_eq_lt_dec (length l1) (length l2)) as [[Hlt | Heq] | Hgt].
  + eapply leaf_prefix; eauto.
    rewrite H2 H4. eapply nat_le_sum in Hlt as [k Hk].
    rewrite Hk.
    replace (S (length l1) + k) with (length l1 + S k) by lia. rewrite seq_app.
    rewrite map_app. eapply prefix_app_r.
    enough (map g (seq 0 (length l1)) = map g2 (seq 0 (length l1))) as -> by reflexivity.
    eapply map_ext_in. move => a / in_seq [] ? ?. eapply Hg. lia.
  + rewrite H2 H4 Heq.
    eapply map_ext_in. move => a / in_seq [] ? ?. eapply Hg. lia.
  + symmetry. eapply leaf_prefix; eauto.
    rewrite H2 H4. eapply nat_le_sum in Hgt as [k Hk].
    rewrite Hk.
    replace (S (length l2) + k) with (length l2 + S k) by lia. rewrite seq_app.
    rewrite map_app. eapply prefix_app_r.
    enough (map g (seq 0 (length l2)) = map g2 (seq 0 (length l2))) as -> by reflexivity.
    eapply map_ext_in. move => a / in_seq [] ? ?. eapply Hg. lia.
Qed.

  Lemma help:
    ∀ (x : nat) (g g2 : nat → bool),
      (∀ a : nat,
          a <
          sum_list
            (map (λ n : nat, length (proj1_sig (F_find_pref (PeanoNat.Nat.iter n nxt g))))
                 (seq 0 (S x))) → g a = g2 a)
      → proj1_sig (F_find_pref (PeanoNat.Nat.iter x nxt g)) =
        proj1_sig (F_find_pref (PeanoNat.Nat.iter x nxt g2)).
  Proof.
    intros x.
    
  induction x using lt_wf_ind. move => g g2 Hg.
  rename H into IHx.
  destruct x.
  - cbn in *. clear IHx.
    rewrite <- plus_n_O in Hg. now eapply F_find_pref_ext.
  - rewrite !Nat_iter_S_r. eapply IHx. lia.
    move => a Ha.
    unfold nxt.
    pose proof (IHx 0) as E1. cbn in E1. erewrite E1. instantiate (1 := g2). 2:lia.
    2:{ move => a2 Ha2. eapply Hg. cbn. lia. }
    eapply Hg. erewrite <- E1. instantiate (1 := g). 2:lia.
    2:{move => a2 Ha2. eapply Hg. cbn. lia. }
    cbn in *. erewrite (map_seq_eq (f2 := (λ n : nat, length (proj1_sig (F_find_pref (PeanoNat.Nat.iter n nxt (nxt g)))))) (n2 := 1)).
    lia. clear. move => x.
    replace (x + 2) with (2 + x) by lia.
    replace (x + 1) with (1 + x) by lia.
    cbn [plus].
    now rewrite !Nat_iter_S_r.
  Qed.

Lemma continuous_G : modulus (fun g x => seq 0 (sum_list (map (fun n => length (proj1_sig (F_find_pref (PeanoNat.Nat.iter n nxt g)))) (seq 0 (S x))))) G.
Proof.
  move => g x g2 /map_ext_in_iff.
  setoid_rewrite in_seq.
  move => H.
  unfold G.
  destruct ℓ_sig, ℓ_sig.
  cbn. eapply ℓ_injective. rewrite e e0.
  clear - H.
  assert (Hg : ∀ a : nat, a < sum_list (map (λ n : nat, length (proj1_sig (F_find_pref (PeanoNat.Nat.iter n nxt g)))) (seq 0 (S x))) → g a = g2 a). {
    move => a Ha. eapply H. lia.
  } clear H.
  revert g g2 Hg.
  eapply help; eauto.
Qed.

Lemma app_sum_list_with {A} (f : A -> nat) l1 l2 :
  sum_list_with f (l1 ++ l2) = sum_list_with f l1 + sum_list_with f l2.
Proof.
  induction l1; cbn; lia.
Qed.

Lemma F_ext f1 f2 :
  f1 ≡{_} f2 -> F f1 ≡{_} F f2.
Proof.
  intros H n. unfold F.
  destruct nth_sig, nth_sig. cbn.
  erewrite F'_eq_lt in e.
  - erewrite e0 in e. now inv e.
  - intros. eapply H.
Qed.  

Lemma to_Homeo_M_bool_nat :
  Homeo_M bool nat.
Proof.
  exists G. eexists.
  repeat split.
  - intros ? ? ?.
    eapply F_ext in H.
    now setoid_rewrite F_surj in H.
  - intros f. eexists. eapply F_G_inv. econstructor.
  - eapply continuous_G.
  - intros x f.
    exists (seq 0 (sum_list (map (fun n => length (proj1_sig (F_find_pref (PeanoNat.Nat.iter n nxt f)))) (seq 0 (S x))))).
    intros g. move => /map_ext_in_iff.
    setoid_rewrite in_seq.
    move => H.
    f_equal. f_equal. eapply map_ext_in.
    intros ? ? % in_seq. f_equal.
    eapply help. intros.
    eapply H. split. lia.
    destruct H0 as [_ [? H0] % nat_le_sum].
    cbn in H0. inv H0.
    replace (S (a + x0)) with (S a + x0) by lia.
    rewrite seq_app map_app app_sum_list_with. lia.
Qed.

End fix_tree.

Lemma size_generating {X} (sz : X -> nat) (p : X -> Prop) :
  (forall n, exists x, sz x >= n /\ p x) ->
  generative p.
Proof.
  intros Hsz A.
  destruct (Hsz (1 + max_list_with sz A)) as (x & H1 & H2).
  exists x. split; eauto.
  intros H % (max_list_with_spec _ _ sz). lia.
Qed.

Lemma enumerable_leaf τ_K :
  enumerable (leaf τ_K).
Proof.
  pose proof (tree_dec τ_K) as [D] % decidable_iff.
  eapply decidable_enumerable; eauto.
  eapply decidable_iff. econstructor. intros u.
  destruct u as [ | b u _] using rev_rect.
  - right. intros (v & ? & H & ?). destruct v; inv H.
  - destruct (D u).
    + destruct (D (u ++ [b])).
      * right. intros (u' & b' & (H1 & H2) % app_inj_tail & H3 & H4); subst; eauto.
      * left. exists u, b; eauto.
    + right. intros (u' & b' & (H1 & H2) % app_inj_tail & H3 & H4); subst; eauto.
Qed.

Lemma map_nth_seq {X} (x0 : X) l :
  map (fun n => nth n l x0) (seq 0 (length l)) = l.
Proof.
  induction l using rev_ind.
  - reflexivity.
  - cbn. rewrite app_length seq_app map_app.
    cbn. rewrite app_nth2. lia.
    rewrite minus_diag. cbn. f_equal.
    rewrite <- IHl at 2.
    eapply map_ext_in.
    intros ? [_ ?] % in_seq. cbn in *.
    now rewrite app_nth1.
Qed.

Lemma KT_inj_enum_leafs (τ_K : Kleene_tree) :
  exists ℓ : nat -> list bool, (forall l, leaf τ_K l <-> exists n, ℓ n = l) /\ Inj (=) (=) ℓ.
Proof.
  destruct τ_K as [τ inf_τ wf_τ].
  pose proof (tree_dec τ) as [D] % decidable_iff.
  pose (τ_K := Build_Kleene_tree inf_τ wf_τ).
  destruct (enumerable_leaf τ_K) as [e He].
  unshelve eexists. 2:split.
  - eapply MoreEnumerabilityFacts.F.
    + eapply He.
    + exact _.
    + eapply size_generating with length.
      intros n.
      destruct (inf_τ n) as (u & Hu1 & Hu2).
      pose proof (wf_τ (extend u)).
      eapply mu_nat_dep_least in H as (k & H1 & H2 & H3). 
      -- exists (map (extend u) (seq 0 k)). split.
         ++ rewrite map_length seq_length.
            destruct (le_lt_dec n k); eauto.
            exfalso. eapply H2.
            eapply tree_p. eauto. 2:exact Hu1.
            exists (drop k u).
            rewrite <- (firstn_skipn k u) at 1.
            f_equal.
            rewrite <- (map_nth_seq false u) at 1.
            rewrite take_map take_seq. lia.
            reflexivity.
         ++ remember (map (extend u) (seq 0 k)) as l.
            destruct l as [ | b l _] using rev_ind.
            ** destruct H2. eauto.
            ** exists l, b. split. reflexivity. split; eauto.
               destruct (D l). eauto. exfalso.
               destruct k.
               --- inv Heql. destruct l; inv H0.
               --- replace (S k) with (k + 1) in Heql by lia.
                   rewrite seq_app map_app in Heql. 
                   cbn in Heql. eapply app_inj_tail in Heql as [-> ->].
                   eapply H3 in n0. lia. lia.
      -- intros. eapply not_dec. exact _.
  - intros l. split.
    * intros Hl. eapply F_sur. eassumption.
    * intros [n <-]. eapply F_p.
  - intros ? ? ?.
    now eapply MoreEnumerabilityFacts.F_inj in H.
Qed.

Lemma KT_iff_Homeo_N_nat_bool :
  KT <-> Homeo_M bool nat.
Proof.
  split.
  - intros (τ_K & inf_τ & wf_τ).
    pose proof (tree_dec τ_K) as [D] % decidable_iff.
    pose (T_K := Build_Kleene_tree inf_τ wf_τ).
    destruct (KT_inj_enum_leafs T_K) as (ℓ & Hℓ1 & Hℓ2).
    eapply to_Homeo_M_bool_nat; eauto.
  - intros H. eapply Homeo_M_Cantor_Baire_to_KT in H as [[T_K H1 H2]].
    eexists; eauto.
Qed.

Lemma KT_to_Homeo_N_nat_bool :
  KT -> Homeo_M nat bool.
Proof.
  intros (τ_K & inf_τ & wf_τ).
  pose proof (tree_dec τ_K) as [D] % decidable_iff.
  pose (T_K := Build_Kleene_tree inf_τ wf_τ).
  destruct (KT_inj_enum_leafs T_K) as (ℓ & Hℓ1 & Hℓ2).
  eapply to_Homeo_M_nat_bool; eauto.
Qed.
