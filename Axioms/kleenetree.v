Set Implicit Arguments.
Unset Strict Implicit.
Require Import stdpp.list stdpp.list_numbers.
From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.SemiDecidabilityFacts Synthetic.EnumerabilityFacts reductions partial Axioms.bestaxioms  principles Shared.Dec.
Require Import ssreflect Nat.
Require Import SyntheticComputability.Shared.FilterFacts.

Section Reverse_Induction.

  Lemma rev_list_rect {A} :
    forall P:list A -> Type,
	    P [] ->
	    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
	    forall l:list A, P (rev l).
  Proof.
    induction l; auto.
  Qed.

  Theorem rev_rect {A} :
    forall P:list A -> Type,
	    P [] ->
	    (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
  Proof.
    move => P H H0 l.
    generalize (rev_involutive l).
    move => E; rewrite <- E.
    apply (@rev_list_rect _ P).
    auto.

    simpl.
    move => a l0 H1.
    apply (H0 a (rev l0)).
    auto.
  Qed.

End Reverse_Induction.

Lemma lookup_map X Y {l : list X} n y (f : X -> Y) :
  map f l !! n = Some y <-> exists x, l !! n = Some x /\ y = f x.
Proof.
  induction l in n |- *; cbn in *.
  - split. congruence. move => [? []]. congruence.
  - destruct n.
    + cbn. split.
      * move => [] <-. eauto.
      * now move => [] x [] [] -> ->.
    + cbn. now rewrite IHl.
Qed.

Lemma length_inv {X} {n1 n2} {l : list X} :
  length l = n1 + n2 -> exists l1 l2 : list X, l = l1 ++ l2 /\ length l1 = n1 /\ length l2 = n2.
Proof.
  intros. induction l in n1, n2, H |- *.
  - exists [], []. destruct n1, n2; cbn in *; try lia. eauto.
  - cbn in H. destruct n1.
    + cbn in H. destruct n2. lia.
      inversion H.
      eapply (IHl 0 n2) in H1 as [l1 [l2 [-> [Hl1 Hl2]]]].
      destruct l1; cbn in *; try congruence.
      exists [], (a :: l2). cbn. eauto.
    + cbn in H. inversion H.
      eapply (IHl n1 n2) in H1 as [l1 [l2 [-> [Hl1 Hl2]]]].
      exists (a :: l1), l2. cbn. eauto.
Qed.

Lemma Is_true_iff b :
  Is_true b <-> b = true.
Proof.
  destruct b; cbv; firstorder congruence.
Qed.

Lemma Is_true_neg_iff b :
  ~ Is_true b <-> b = false.
Proof.
  destruct b; cbv; firstorder congruence.
Qed.

Definition listable {X} (p : X -> Prop) := ∑ L : list X, forall x, p x <-> In x L.

Lemma listable_forall_dec {X} (p q : X -> Prop) :
  listable p -> (forall x, dec (q x)) -> dec (forall x, p x -> q x).
Proof.
  intros [L HL] D.
  destruct (forallb (fun x => if D x is left _ then true else false) L) eqn:E.
  - left. setoid_rewrite forallb_forall in E.
    intros x H % HL % E. destruct (D x); firstorder congruence.
  - right. intros H.
    rewrite <- Is_true_neg_iff in E.
    setoid_rewrite forallb_True in E.
    rewrite <- Exists_Forall_neg in E. 2: intros x; destruct (D x); cbv; firstorder congruence.
    eapply List.Exists_exists in E as [x [H1 % HL H2]].
    destruct (D x); firstorder.
Qed.

Lemma listable_exists_dec {X} (p q : X -> Prop) :
  listable p -> (forall x, dec (q x)) -> dec (exists x, p x /\ q x).
Proof.
  intros [L HL] D.
  destruct (existsb (fun x => if D x is left _ then true else false) L) eqn:E.
  - left. setoid_rewrite existsb_exists in E.
    destruct E as [x [H1 % HL H2]].
    destruct (D x); try congruence. eauto.
  - right. intros [x [H1 % HL H2]].
    edestruct (existsb_exists (λ x : X, if D x is left _ then true else false) L) as [_ EE]. rewrite EE in E.
    + clear EE. exists x. split. eauto. destruct (D x); eauto.
    + inv E.
Qed.

Lemma listable_list_length:
  ∀ k : nat, listable (λ x : list bool, length x = k).
Proof.
  induction k as [ | k [L IH] ].
  - exists [ [] ]. intros [] ; cbv ; firstorder; try lia; congruence.
  - exists (map (cons true) L ++ map (cons false) L).
    intros l.
    rewrite in_app_iff !in_map_iff.
    repeat setoid_rewrite <- IH.
    destruct l as [ | [] ].
    + cbn. split. inversion 1. firstorder congruence.
    + cbn. split. 
      * inversion 1. eauto.
      * firstorder congruence.
    + cbn. split. 
      * inversion 1. eauto.
      * firstorder congruence.
Qed.

Lemma listable_list_length_lt : ∀ k : nat, listable (λ x : list bool, length x < k).
Proof.
  induction k as [ | k [L IH] ].
  - exists []. intros [] ; cbv ; firstorder auto with *.
  - destruct (listable_list_length k) as [Lk Hk].
    exists (L ++ Lk).
    intros l. cbn.
    rewrite in_app_iff - IH - Hk. lia.
Qed.

Record is_tree (tree_T : list bool -> Prop) :=
  {
    tree_inhab : exists l : list bool, tree_T l ;
    tree_p : forall l1 l2, prefix l1 l2 -> tree_T l2 -> tree_T l1 ;
    tree_dec :       decidable tree_T ;
  }.

Record tree :=
  {
  tree_T :> list bool -> Prop ;
  tree_is_tree :> is_tree tree_T
  }.

Definition bounded_tree (T : list bool -> Prop) := 
  exists k, forall a, length a >= k -> ~ T a.

Definition infinite_tree (T : list bool -> Prop) := 
  forall k, exists a, T a /\ (length a >= k ).

Definition infinite_path (T : list bool -> Prop) :=
  exists f : nat -> bool, forall n, T (map f (seq 0 n)).

Definition wellfounded_tree (T : list bool -> Prop) :=
  forall f : nat -> bool, exists n, ~ T (map f (seq 0 n)).

Lemma tree_nil T :
  is_tree T -> T nil.
Proof.
  intros [[inhab Hinhab] Hclos d]. 
  eapply Hclos. 2:eapply Hinhab. now econstructor.
Qed.

Hint Immediate tree_is_tree.
Hint Extern 2 => eapply tree_nil : core.

Record Kleene_tree :=
  {
  Kleene_T :> tree ;
  Kleene_infinite : infinite_tree Kleene_T ;
  Kleene_inf_exit :  wellfounded_tree Kleene_T ;
  }.

Lemma bounded_infinite_contra T :
  bounded_tree T -> infinite_tree T -> False.
Proof.
  firstorder.
Qed.

Definition bounded_tree' (T : list bool -> Prop) := 
  exists k, forall a, length a = k -> ~ T a.

Lemma not_bounded_infinite' :
  ∀ T, (∀ x : list bool, dec (T x)) → ¬ bounded_tree' T → infinite_tree T.
Proof.
  intros T D H k. cbn in *. enough (exists a, T a /\ length a = k) as [a [H1 H2]]. exists a. split. eassumption. lia.
  enough (∃ a : list bool, length a = k /\ T a) by firstorder.         
  edestruct (listable_exists_dec (X := list bool)).
  3:{ eapply e. }
  -- eapply listable_list_length.
  -- eauto.
  -- cbn in *. destruct H.
     exists k. intros ? ? ?. eapply n. eauto.
Qed.

Lemma bounded_iff (T : tree) k :
  (∀ a : list bool, length a ≥ k → ¬ T a) <-> forall l, length l = k -> ~ T l.
Proof.
  split.
  destruct T as [T [? ? ?]]; cbn. clear tree_inhab0.
  - intros H l ?. eapply H. lia.
  - intros H l [d [l1 [l2 [-> [Hl1 Hl2]]]] % length_inv] % nat_le_sum.
    intros Hl. eapply tree_p in Hl. 2:eapply T. 2:eexists; reflexivity.
    eapply H; eauto.
Qed.

Lemma bounded_tree_iff (T : tree) :
  bounded_tree T <-> bounded_tree' T.
Proof.
  split; intros [k]; exists k; now eapply bounded_iff.
Qed.

Lemma not_bounded_infinite:
  ∀ T : tree, ¬ bounded_tree T → infinite_tree T.
Proof.
  intros T H.
  pose proof (tree_dec T) as [D] % decidable_iff.
  setoid_rewrite bounded_tree_iff in H. now eapply not_bounded_infinite'.
Qed.

Lemma not_bounded_infinite_iff :
  ∀ T : tree, ¬ bounded_tree T <-> infinite_tree T.
Proof.
  intros T.
  split.
  - eapply not_bounded_infinite.
  - intros ? ?. eapply bounded_infinite_contra; eassumption.
Qed.

Lemma path_wellfounded_contra T :
  infinite_path T -> wellfounded_tree T -> False.
Proof.
  by move => [f] H / (_ f) [n].
Qed.

Lemma bounded_to_wellfounded T :
  bounded_tree T -> wellfounded_tree T.
Proof.
  intros [n H] f. exists n. eapply H.
  rewrite map_length seq_length. lia.
Qed.

Lemma infinite_path_to_infinite T :
  infinite_path T -> infinite_tree T.
Proof.
  intros [f Hf] n.
  exists (map f (seq 0 n)). split. eauto.
  rewrite map_length seq_length. lia.
Qed.

(** ** Constructions  *)
Section fix_enum.

Context {Part : partiality}.

Variable e : nat -> (nat ↛ bool).
Hypothesis e_enum : forall f : nat ↛ bool, ~~ exists n, e n ≡{nat ↛ bool} f.

Definition inconsistent {A B} (f : A ↛ B) (g : A -> B) := ~~ exists a b, f a =! b /\ g a <> b.

Definition d n := bind (e n n) (fun y => ret (negb y)).

Lemma diag f : inconsistent d f.
Proof.
  intros G.
  apply (@e_enum (fun x : nat => ret (f x))). intros [c Hc].
  apply G.
  exists c. exists (negb (f c)).
  rewrite bind_hasvalue.
  specialize (Hc c). hnf in Hc. setoid_rewrite Hc.
  split.
  - exists (f c). split; eapply ret_hasvalue. 
  - destruct (f c); cbn; congruence.  
Qed.

Definition D k n := seval (d n) k. 

(** * Kleene trees  *)

Definition MP_tree' := forall T : tree, ~ infinite_path T -> wellfounded_tree T.

Definition T_K : MP_tree' -> Kleene_tree.
Proof.
  intros mp.
  unshelve econstructor.
  exists (fun a : list bool => forall n, n < length a -> forall x, D (length a) n = Some x -> a !! n = Some x).
  econstructor.
  - exists []. cbn. move => n H. lia.
  - move => l1 l2 [l3 ->].
    rewrite !app_length.
    move => H n Hn x Hx.
    assert (Hg : D (length l1 + length l3) n = Some x). {
      eapply seval_mono. eassumption. lia. }
    specialize (H n (lt_plus_trans _ _ (length l3) Hn) x Hg).
    erewrite <- (lookup_app_l _ _ _ Hn). eassumption.
  - eapply decidable_iff. econstructor. move => a. generalize (length a) at 2 as k.
    induction a as [ | b a] using rev_rect; move => k; cbn.
    + left. move => n Hn. lia.
    + destruct (IHa k) as [L | R].
      * destruct (D k (length a)) as [ x | ] eqn:E.
        -- destruct (bool_eq_dec x b).
           ++ left. rewrite app_length. cbn. move => n Hn x' Hx'.
              destruct (nat_eq_dec n (length a)).
              ** subst. rewrite lookup_app_r. lia.
                 rewrite minus_diag. cbn. congruence.
              ** rewrite lookup_app_l. lia.
                 eapply L. lia. eassumption.
           ++ right. rewrite app_length. cbn. move => / (fun H => H (length a)) H.
              rewrite lookup_app_r ?minus_diag in H. lia. cbn in H.
              eapply n.
              eapply Some_inj. symmetry. eapply H. lia. eauto.
        -- left. rewrite app_length. cbn. move => n Hn x' Hx'.
           destruct (nat_eq_dec n (length a)).
           ** congruence.
           ** rewrite lookup_app_l. lia.
              eapply L. lia. eassumption.
      * right. move => H. contradiction R.
        move => n Hn x Hx.
        specialize (H n). rewrite app_length in H. cbn in H.
        rewrite lookup_app_l in H. lia.
        eapply H. lia. eassumption.
  - unfold infinite_tree, tree_T. move => k.
    pose (f k := (fix f n := match n with 0 => [] | S n => f n ++ [(if D k n is Some x then x else false)] end)).
    exists (f k k).
    assert (H_length : forall n, length (f k n) = n). {
      induction n; cbn; rewrite ?app_length; cbn.
      reflexivity.
      rewrite IHn. lia.
    }
    split.
    + rewrite H_length. generalize k at 1 4.
      move => m n Hn x Hx.
      induction m.
      * lia.
      * cbn. destruct (nat_eq_dec n m).
        -- subst. rewrite Hx. destruct m. cbn. reflexivity.
           rewrite lookup_app_r. rewrite H_length. lia.
           rewrite H_length minus_diag. reflexivity.
        -- rewrite lookup_app_l. rewrite H_length. lia.
           eapply IHm. lia.
    + rewrite H_length. lia.
  - eapply mp. move => [f H].
    pose proof (@diag f) as Df. red in Df.
    eapply Df. intros [n [b [H1 H2]]].
    eapply seval_hasvalue in H1 as [k H1].
    fold (D k n) in H1. cbn in *.
    specialize (H (1 + k + n) n). 
    rewrite map_length seq_length in H.
    assert (Hlt : n < 1 + k + n) by lia.
    setoid_rewrite lookup_map in H. setoid_rewrite (lookup_seq) in H.
    edestruct H as [x [[H3 H4] H5]].
    + lia.
    + eapply seval_mono. eassumption. lia.
    + subst. cbn in H2. congruence.
Qed.

End fix_enum.

(** ** Omniscience principles as axioms on trees  *)

Definition subtree_at b (T : list bool -> Prop) := fun l => T (b ++ l).

Lemma is_tree_subtree_at (T : tree) l :
  T l -> is_tree (subtree_at l T).
Proof.
  (* destruct T as [T]; cbn in *. *)
  split.
  - exists []. unfold subtree_at. rewrite app_nil_r. exact H.
  - intros l1 l2 Hp Hl1. red in Hl1. eapply tree_p in Hl1. eassumption. eapply T.
    now eapply prefix_app_alt.
  - pose proof (tree_dec T) as [D] % decidable_iff.
    eapply decidable_iff. econstructor. eauto.
Qed.

Definition LLPO_tree :=
  forall T : tree, infinite_tree T ->
              (is_tree (subtree_at [true] T) /\ infinite_tree ((subtree_at [true] T)))
              \/ (is_tree (subtree_at [false] T) /\ infinite_tree ((subtree_at [false] T))).

Definition LPO_tree :=
  forall T : tree, bounded_tree T \/ infinite_tree T.

Definition WLPO_tree :=
  forall T : tree, infinite_tree T \/ ~ infinite_tree T.

Definition T_inf_sdec (T : list bool -> Prop) (D : forall l, dec (T l)) : nat -> bool.
  intros k.
  destruct (@listable_forall_dec _ (fun x => length x = k) (fun x => ~ T x)).
  * eapply listable_list_length.
  * eauto.
  * exact true.
  * exact false.
Defined.

Lemma T_inf_sdec_iff' T (D : forall l, dec (T l)) :
  bounded_tree' T <-> (exists k, T_inf_sdec D k = true).
Proof.
  split.
  - intros [k]. exists k.
    unfold T_inf_sdec. destruct listable_forall_dec. reflexivity.
    destruct n. intros. eapply H. lia.
  - cbn in *. intros H.
    destruct H as [k H]. unfold T_inf_sdec in H. 
    edestruct (listable_forall_dec); try inv H. 
    now exists k.
Qed.

Lemma T_inf_sdec_iff (T : tree) (D : forall l, dec (T l)) :
  bounded_tree T <-> (exists k, T_inf_sdec D k = true).
Proof.
  rewrite <- T_inf_sdec_iff'.
  split; intros [k]; exists k; now eapply bounded_iff.
Qed.

Program Definition tree_from (f : nat -> bool) := (@Build_tree (fun l => forallb (fun n => negb (f n)) (seq 0 (length l)) = true) _).
Next Obligation.
  econstructor.
    + now exists [].
    + intros l1 l2 [k ->] % prefix_length % nat_le_sum.
      now rewrite seq_app forallb_app andb_true_iff.
    + eapply decidable_iff. econstructor. intros x. hnf. decide equality.
Qed.

Lemma tree_from_f_bounded_iff f :
  bounded_tree (tree_from f) <-> exists n, f n = true.
Proof.
  split.
  - intros [k Hb].
    specialize (Hb (map (fun _ => true) (seq 0 k))).
    rewrite map_length seq_length in Hb.
    specialize (Hb (le_refl _)).
    unfold tree_from in Hb. cbn in Hb.
    rewrite <- Is_true_iff in Hb.
    setoid_rewrite forallb_True in Hb.
    eapply Exists_Forall_neg in Hb.
    * eapply List.Exists_exists in Hb as [n [_ H2]].
      exists n. destruct (f n); cbv in *; tauto.
    * intros x; destruct (f x); cbn; eauto.
  - intros [n Hn].
    exists (S n). intros l Hll Hl.
    unfold tree_from in Hl.
    eapply forallb_forall in Hl.
    setoid_rewrite Hn in Hl. inv Hl.
    eapply in_seq. lia.
Qed.

Lemma tree_from_f_bounded_iff_wf f :
  wellfounded_tree (tree_from f) <-> exists n, f n = true.
Proof.
  split.
  - intros H. specialize (H f) as [n Hn].
    cbn in Hn.
    eapply not_true_is_false in Hn.
    eapply Is_true_neg_iff in Hn.
    setoid_rewrite forallb_True in Hn.
    eapply Exists_Forall_neg in Hn.
    * eapply List.Exists_exists in Hn as [m [_ H2]].
      exists m. destruct (f m); cbv in *; tauto.
    * intros x; destruct (f x); cbn; eauto.
  - intros [n Hn]. intros g.
    exists (S n). 
    eapply not_true_iff_false, Is_true_neg_iff.
    intros Hl % Is_true_iff.
    eapply forallb_forall in Hl.
    setoid_rewrite Hn in Hl. inv Hl.
    eapply in_seq. rewrite map_length seq_length. lia.
Qed.

Lemma LPO_tree_iff :
  LPO <-> LPO_tree.
Proof.
  split.
  - intros LPO T. pose proof (tree_dec T) as [D] % decidable_iff.
    destruct (LPO (T_inf_sdec D)).
    + left. eapply T_inf_sdec_iff. eapply H.
    + right. rewrite <- T_inf_sdec_iff in H.
      now eapply not_bounded_infinite.
  - intros H f.
    destruct (H (tree_from f)).
    + left. now eapply tree_from_f_bounded_iff.
    + right. intros ? % tree_from_f_bounded_iff.
      eapply bounded_infinite_contra; eauto.
Qed.

Lemma WLPO_tree_iff :
  WLPO <-> WLPO_tree.
Proof.
  split.
  - intros WLPO T. unfold bounded_tree.
    pose proof (tree_dec T) as [D] % decidable_iff.
    destruct (WLPO (T_inf_sdec D)).
    + left.
      eapply not_bounded_infinite. eauto.
      rewrite T_inf_sdec_iff.
      now eapply forall_neg_exists_iff.
    + cbn in *.
      right. intros Hi.
      eapply H. intros. destruct T_inf_sdec eqn:E; eauto.
      exfalso.
      eapply bounded_infinite_contra; eauto.
      eapply T_inf_sdec_iff. eauto.
  - intros H f.
    destruct (H (tree_from f)).
    + left. eapply forall_neg_exists_iff.
      intros ? % tree_from_f_bounded_iff.
      eapply bounded_infinite_contra; eauto.
    + right. intros ? % forall_neg_exists_iff.
      rewrite <- tree_from_f_bounded_iff in H1.
      eapply H0. eapply not_bounded_infinite; eauto.
Qed.

Lemma is_tree_subtree_at_from_inf (T : tree) l :
  infinite_tree (subtree_at l T) -> is_tree (subtree_at l T).
Proof.
  intros H. destruct (H 0) as [l' [H1 H2]].
  split.
  - eauto.
  - intros l1 l2 Hp Hl1. red in Hl1. eapply tree_p in Hl1. eassumption. eapply T.
    now eapply prefix_app_alt.
  - pose proof (tree_dec T) as [D] % decidable_iff.
    eapply decidable_iff. econstructor. eauto.
Qed.


Definition is_infinite_tree τ := is_tree τ /\ infinite_tree τ.

Lemma LLPO_LLPO_tree_iff :
  LLPO <-> LLPO_tree.
Proof.
  split.
  - intros LLPO % LLPO_to_DM_Sigma_0_1 T infT.
    pose proof (tree_dec T) as [D] % decidable_iff.
    assert (D1 : forall l, dec (subtree_at [true] T l)) by intuition.
    assert (D2 : forall l, dec (subtree_at [false] T l)) by intuition.
    destruct (LLPO (T_inf_sdec D1) (T_inf_sdec D2)).
    + rewrite <- !T_inf_sdec_iff'. intros [[b1 Hb1] [b2 Hb2]].
      eapply bounded_infinite_contra; eauto.
      exists (1 + Nat.max b1 b2). intros l Hl.
      destruct l; cbn in *; try lia.
      eapply le_S_n in Hl.
      pose proof (Max.max_lub_l _ _ _ Hl).
      pose proof (Max.max_lub_r _ _ _ Hl).
      destruct b; intros HT.
      * assert (T [true]). eapply tree_p. eapply T. 2:eauto. now eexists.
        eapply is_tree_subtree_at in H1.
        eapply (bounded_iff (Build_tree H1)) in Hb1. eapply Hb1. cbn. exact HT. lia.
      * assert (T [false]). eapply tree_p. eapply T. 2:eauto. now eexists.
        eapply is_tree_subtree_at in H1.
        eapply (bounded_iff (Build_tree H1)) in Hb2. eapply Hb2. cbn. exact HT. lia.
    + left. rewrite <- T_inf_sdec_iff' in H.
      eapply not_bounded_infinite' in H. 2:eauto.
      split. eapply is_tree_subtree_at_from_inf. eauto. eauto.
    + right. rewrite <- T_inf_sdec_iff' in H.
      eapply not_bounded_infinite' in H. 2:eauto.
      split. eapply is_tree_subtree_at_from_inf. eauto. eauto.
  - intros H. eapply LLPO_split_to_LLPO, DM_Sigma_0_1_to_LLPO_split. intros f g Hfg.
    unshelve epose proof (H (@Build_tree (fun l => match l with [] => True
                                                        | true :: l => forallb (fun n => negb (f n)) (seq 0 (length l)) = true
                                                        | false :: l => forallb (fun n => negb (g n)) (seq 0 (length l)) = true end) _)).
    econstructor.
    + now exists [].
    + intros [|[]] [|[]] pref; cbn; try tauto.
      all: try now (destruct pref as [ll Hll]; inv Hll).
      * eapply prefix_cons_inv_2 in pref.
        eapply prefix_length in pref.
        rewrite !forallb_forall.
        intros Hall x [_ Hl] % in_seq.
        eapply Hall, in_seq. lia.
      * eapply prefix_cons_inv_2 in pref.
        eapply prefix_length in pref.
        rewrite !forallb_forall.
        intros Hall x [_ Hl] % in_seq.
        eapply Hall, in_seq. lia.
    + eapply decidable_iff. econstructor. intros [ | []]; hnf; eauto; decide equality.
    + cbn in H0. destruct H0.
      * cbn. eapply not_bounded_infinite'.
        -- intros [ | []]; hnf; eauto; decide equality.
        -- intros [k Hk].
           destruct k. now eapply (Hk [] eq_refl).
           pose proof (Hk (true :: map (fun _ => true) (seq 0 k)) (ltac:(now cbn; rewrite map_length seq_length))) as Hf.
           cbn in Hf.
           destruct forallb eqn:E. congruence. clear Hf.
           eapply Is_true_neg_iff in E. setoid_rewrite forallb_True in E.
           eapply neg_Forall_Exists_neg in E.
           2: intros; destruct (f x); cbn; firstorder congruence.
           eapply List.Exists_exists in E as [n [Hn HHn]].

           pose proof (Hk (false :: map (fun _ => true) (seq 0 k)) (ltac:(now cbn; rewrite map_length seq_length))) as Hg.
           cbn in Hg.
           destruct forallb eqn:E. congruence. clear Hg.
           eapply Is_true_neg_iff in E. setoid_rewrite forallb_True in E.
           eapply neg_Forall_Exists_neg in E.
           2: intros; destruct (g x); cbn; firstorder congruence.
           eapply List.Exists_exists in E as [n2 [Hn2 HHn2]].
           eapply Hfg. split.
           ++ exists n. destruct (f n); cbv in *; firstorder.
           ++ exists n2. destruct (g n2); cbv in *; firstorder.
      * cbn in *. destruct H0 as [_ H0].
        left. intros [n Hn]. destruct (H0 (S n)) as [l [H1 H2]]. clear H0.
        cbn in *. setoid_rewrite forallb_forall in H1.
        specialize (H1 n).
        setoid_rewrite in_seq in H1.
        destruct (f n); try congruence. cbn in H1.
        enough (false = true) by congruence.
        eapply H1. split; lia.
      * cbn in *. destruct H0 as [_ H0].
        right. intros [n Hn]. destruct (H0 (S n)) as [l [H1 H2]]. clear H0.
        cbn in *. setoid_rewrite forallb_forall in H1.
        specialize (H1 n).
        setoid_rewrite in_seq in H1.
        destruct (g n); try congruence. cbn in H1.
        enough (false = true) by congruence.
        eapply H1. split; lia.
Qed.

Definition MP_tree := forall T : tree, ~ infinite_tree T -> bounded_tree T.

Lemma MP_tree_iff :
  MP <-> MP_tree.
Proof.
  split.
  - intros H T HT.
    pose proof (tree_dec T) as [D] % decidable_iff.
    eapply T_inf_sdec_iff.
    eapply H.
    rewrite <- T_inf_sdec_iff.
    intros not_bounded.
    eapply HT, not_bounded_infinite; eauto.
  - intros H f Hf.
    eapply (tree_from_f_bounded_iff).
    eapply H. intros Hinf.
    eapply Hf. rewrite <- tree_from_f_bounded_iff.
    intros Hb. eapply bounded_infinite_contra; eauto.
Qed.

(* Definition MP_tree' := forall T : tree, ~ infinite_path T -> wellfounded_tree T. *)

Lemma MP_tree_iff' :
  MP <-> MP_tree'.
Proof.
  split.
  - intros H T Hnp f.
    pose proof (tree_dec T) as [d Hd]. do 2 red in Hd. 
    setoid_rewrite Hd.
    setoid_rewrite not_true_iff_false.
    setoid_rewrite <- negb_true_iff.
    eapply H.
    rewrite <- forall_neg_exists_iff.
    setoid_rewrite negb_false_iff.
    setoid_rewrite <- Hd.
    intros n.
    eapply Hnp. now exists f.
  - intros H f Hf.
    eapply tree_from_f_bounded_iff_wf, H.
    intros p. eapply Hf. intros Hff.
    eapply tree_from_f_bounded_iff_wf in Hff.
    eapply path_wellfounded_contra; eauto.
Qed.

(** ** WKL *)

Definition WKL :=
  forall T : tree, infinite_tree T -> infinite_path T.

Definition FAN :=
  forall T : tree, wellfounded_tree T -> bounded_tree T.

Definition KT := exists T : tree, infinite_tree T /\ wellfounded_tree T.

Lemma KT_WKL_contra :
  KT -> WKL -> False.
Proof.
  by move => [T] [] Hinf Hwf / (_ T Hinf) / path_wellfounded_contra.
Qed.

Lemma KT_FAN_contra :
  KT -> FAN -> False.
Proof.
  by move => [T] [] Hinf Hwf / (_ T Hwf) / bounded_infinite_contra.
Qed.

Definition LPL :=
  forall T : tree, exists f : nat -> bool, forall a, T a -> T (map f (seq 0 (length a))).

Lemma decidable_stable {X} (p : X -> Prop) :
  decidable p -> stable p.
Proof.
  intros [d] % decidable_iff a.
  destruct (d a) as [H1 | H1]; tauto.
Qed.

Lemma prefix_length_eq {X} (u v : list X)  :
  length u = length v -> prefix u v -> u = v.
Proof.
  intros Hl [w ->].
  rewrite <- firstn_all.
  rewrite <- (firstn_all u) at 1.
  now rewrite Hl firstn_app Hl minus_diag firstn_O app_nil_r.
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

Lemma prefixes_inv {X} (l1 l2 l : list X) :
  l1 `prefix_of` l -> l2 `prefix_of` l -> l1 `prefix_of` l2 \/ l2 `prefix_of` l1.
Proof.
  intros [l' ->] [l'' [[l''' [-> ->]] | [l''' [-> ->]]] % app_eq_inv].
  - right. eexists; eauto.
  - left. eexists; eauto.
Qed.

Lemma listable_prefix {X} (l : list X) :
  listable (fun u => prefix u l).
Proof.
  induction l as [ | x l [L IH]].
  - exists [[]]. intros []. firstorder.
    split.
    + intros [] % prefix_nil_not.
    + cbn. firstorder congruence.
  - exists ([] :: map (cons x) L).
    intros u. cbn. rewrite in_map_iff. split.
    + destruct u.
      * eauto.
      * intros H.
        pose proof (prefix_cons_inv_1 _ _ _ _ H) as ->.
        pose proof (prefix_cons_inv_2 _ _ _ _ H) as H0 % IH.
        eauto.
    + intros [ <- | [l' [<- H]]].
      * eapply prefix_nil.
      * eapply prefix_cons. now eapply IH.
Qed.

Lemma decidable_length_T T :
  (∀ x : list bool, dec (T x)) → ∀ n : nat, dec (∃ v : list bool, length v = n ∧ T v).
Proof.
  intros d n.
  eapply listable_exists_dec. eapply listable_list_length.
  eauto.
Qed.

Lemma listable_has_max {X} (f : X -> nat) p x0 :
  @listable X p -> p x0 -> exists x, p x /\ forall y, p y -> f x >= f y.
Proof.
  intros [L HL]. setoid_rewrite HL. intros H.
  pose proof (max_list_with_spec' L f ) as (x & E & Hx) % in_map_iff.
  exists x. split. eauto.
  intros. rewrite E.
  now eapply max_list_with_spec.
  firstorder auto with *.
Qed.

Lemma bounded_longest_path (T : tree) :
  bounded_tree T -> exists u, T u /\ forall v, T v -> length v <= length u.
Proof.
  pose proof (tree_dec T) as [d] % decidable_iff.
  intros [n H].
  assert (listable T).
  - destruct (listable_list_length_lt n) as [L HL].
    exists (List.filter d L).
    intros l. rewrite in_filter_iff.
    split.
    + intros Hl. split.
      * eapply HL. destruct (lt_dec (length l) n). eauto. edestruct H.
        2:eauto. lia.
      * destruct (d l); firstorder.
    + intros [ ]. destruct (d l); firstorder auto with *.
  - eapply (@listable_has_max _ length T []); eauto. 
Qed.

Section WKL_to_LPL.

  Variable T : tree.

  Definition T' u := T u \/ exists v, prefix v u /\ T v /\ ~ exists w, length w = length v + 1 /\ T w.

  Lemma is_tree_T' : is_tree T'.
  Proof.
    pose proof (tree_dec T) as [d] % decidable_iff.
    econstructor.
    - exists []. left. eapply tree_nil, T.
    - intros l1 l2 Hpref [Hl2|[v [Hpref2 [Hv1 Hv2]]]].
      + left. eapply tree_p; eauto. 
      + destruct (d l1) as [Hl1 | Hl1]; clear d. left; eauto.
        assert (Hl2 : ~ T l2) by (intros ? % (tree_p T (l1 := l1)); eauto).
        right. exists v. split. 2: firstorder.
        destruct (prefixes_inv Hpref Hpref2) as [H1 | H1]; eauto.
        exfalso. eapply Hl1, tree_p; eauto.
    - eapply decidable_disj. eapply T.
      eapply decidable_iff. econstructor.
      intros l. eapply listable_exists_dec. eapply listable_prefix.
      clear - d. intros l. eapply and_dec. eauto.
      eapply not_dec. eapply decidable_length_T; eauto.
  Qed.

  Lemma inf_T' : infinite_tree T'.
  Proof.
    pose proof (tree_dec T) as [d] % decidable_iff.
    intros n.
    destruct (decidable_length_T d n) as [ [v [] ] | ].
    + exists v. split; try lia. now left.
    + assert (bounded_tree T) as [u [Hu1 Hu2]] % bounded_longest_path. {
        exists n. intros u Hu HuT. eapply n0.
        exists (take n u). split. rewrite firstn_length_le; lia.
        eapply tree_p. 3:eauto. eauto. eapply take_prefix.
      }
      exists (u ++ repeat false n).
      split. 2:{ rewrite app_length repeat_length. lia. }
      right. exists u. split. eexists; eauto.
      split. eauto.
      intros [v [Hv1 Hv2]]. eapply Hu2 in Hv2. lia.
  Qed.

  Lemma inf_to_longest f :
    (∀ n : nat, T' (map f (seq 0 n))) -> forall a, T a -> T (map f (seq 0 (length a))).
  Proof.
    intros Hf a Ha.
    pose proof (tree_dec T) as [d] % decidable_iff.
    eapply decidable_stable. eapply T.
    intros HT.
    destruct (Hf (length a)) as [HH | [v [Hpref Hv]]]; eauto.
    destruct (lt_eq_lt_dec (length v) (length a)) as [[H1 | H2] | H3].
    - eapply Hv. exists (take (1 + length v) a).
      split. rewrite firstn_length_le; lia. 
      eapply tree_p. eapply T. 2:exact Ha.
      eapply take_prefix.
    - eapply HT.
      eapply prefix_length_eq in Hpref.
      + subst. eapply Hv.
      + now rewrite map_length seq_length.
    - eapply prefix_length in Hpref.
      rewrite map_length seq_length in Hpref. lia.
  Qed.

End WKL_to_LPL.

Lemma WKL_to_FAN :
  WKL -> FAN.
Proof.
  intros wkl T wfT.
  specialize (wkl (Build_tree (is_tree_T' T)) (inf_T' T)) as [f Hf]. cbn in Hf.
  destruct (wfT f) as [n Hn].
  exists n. intros a Ha Hta.
  eapply inf_to_longest in Hta; eauto.
  eapply Hn, tree_p. eauto. 2:eassumption.
  eapply nat_le_sum in Ha as (k & ->).
  rewrite seq_app map_app. eexists; eauto.
Qed.

(** ** WKL equivalences  *)

Lemma WKL_to_LLPO :
  WKL -> LLPO.
Proof.
  intros H. eapply LLPO_LLPO_tree_iff.
  intros T infT.
  pose proof (tree_dec T) as [D] % decidable_iff.
  specialize (H T infT) as [f Hf].
  destruct (f 0) eqn:E.
  + left. split. 
    * eapply is_tree_subtree_at.
      rewrite <- E. eapply (Hf 1).
    * intros k. exists (map f (seq 1 k)).
      split. 2:rewrite map_length seq_length; lia.
      red. cbn. rewrite <- E.
      eapply (Hf (S k)).
  + right.
    split.
    * eapply is_tree_subtree_at.
      rewrite <- E. eapply (Hf 1).
    * intros k. exists (map f (seq 1 k)).
      split. 2:rewrite map_length seq_length; lia.
      red. cbn. rewrite <- E.
      eapply (Hf (S k)).
Qed.

Definition coS_AC_on X Y := forall R : X -> Y -> Prop,
    co_semi_decidable (fun '(x,y) => R x y) ->
    (∀ x : X, ∃ y : Y, R x y) → ∃ f : X → Y, ∀ x : X, R x (f x).

Lemma listable_lt n :
  listable (fun m => m < n).
Proof.
  exists (seq 0 n). intros. rewrite in_seq. lia.
Qed.

Lemma WKL_to_coS_AC_on_nat_bool :
  WKL -> coS_AC_on nat bool.
Proof.
  intros wkl R [f Hf'] Htot.
  assert (Hf : forall x b, R x b <-> forall n, f (x, b) n = false). {
    intros x b. eapply (Hf' (x, b)).
  } clear Hf'.
  pose (τ u := forall i, i < length u -> forall m, m < length u -> f (i,nth i u false) m = false).
  assert (tree_τ : is_tree τ). {
    split.
    - exists []. cbv. intros; lia.
    - intros l1 ? [l2 ->] H. intros i Hi. cbn in *. 
      specialize (H i (ltac:(rewrite app_length; lia))).
      rewrite (app_nth1 _ _ _ Hi) in H.
      intros. eapply H. rewrite app_length; lia.
    - eapply decidable_iff. econstructor. intros u. eapply listable_forall_dec.
      + eapply listable_lt.
      + intros i. eapply listable_forall_dec.
        * eapply listable_lt.
        * intros j. exact _.
  }
  assert (infinite_tree τ) as [g Hg] % (wkl (Build_tree tree_τ)). {
    intros n.
    enough (∃ u : list bool, (forall i, i < length u -> forall m, f (i,nth i u false) m = false) ∧ length u = n) as (? & ? & ?). {
      eexists. split. intros ? ? ? ?. eapply H. lia. lia.
    }
    induction n as [ | n (u & IH & Hu)].
    - exists []; cbn. split. intros; lia. eauto.
    - destruct (Htot n) as [b Hb].
      exists (u ++ [b]). split. 2:rewrite app_length; cbn; lia.
      intros i Hi'. rewrite app_length in Hi'; cbn in *.
      assert (i = length u \/ i < length u) as [-> | Hi] by lia.
      + subst. rewrite app_nth2. lia.
        intros. rewrite minus_diag. cbn. now eapply Hf.
      + intros. rewrite app_nth1. lia. now eapply IH.
  }
  exists g. intros n. cbn in *. eapply Hf. intros m.
  specialize (Hg (1 + n + m) n ltac:(rewrite map_length seq_length; cbn; lia) m ltac:(rewrite map_length seq_length; cbn; lia)).
  erewrite nth_indep in Hg. 2: rewrite map_length seq_length; cbn; lia.
  erewrite map_nth, seq_nth in Hg. eassumption. lia.
  Unshelve. exact 0.
Qed.

Definition coS_AC_on_weak X Y := forall R : X -> Y -> Prop,
    co_semi_decidable (fun '(x,y) => R x y) ->
    (∀ x : X, ~~ ∃ y : Y, R x y) → ∃ f : X → Y, ∀ x : X, R x (f x).

Definition coS_ADC_on_weak X := forall R : list X -> X -> Prop,
    co_semi_decidable (fun '(x,y) => R x y) ->
    (forall x, ~~ exists x', R x x') -> exists f : nat -> X, forall n, R (map f (seq 0 n)) (f n).

Lemma LLPO_coS_AC_on_to_coS_AC_on_weak :
  LLPO -> coS_AC_on nat bool -> coS_AC_on_weak nat bool.
Proof.
  intros llpo % LLPO_to_DM_Sigma_0_1 C R HR Htot.
  eapply C. eassumption.
  intros. eapply DM_Sigma_0_1_iff_totality; eauto.
Qed.

Lemma cos_AC_on_weak_to_coS_ADC_on_weak :
  coS_AC_on_weak nat bool -> coS_ADC_on_weak bool.
Proof.
  intros C R HR Htot.
  assert (datatype (list bool)) as (G & F & HFG). {
    eapply enumerable_discrete_datatype; eauto.
    eapply discrete_iff. econstructor. exact _.
  }
  pose (F' n := match F n with Some u => u | _ => [] end).
  destruct (C (fun n b => R (F' n) b)) as [f Hf].
  - destruct HR as [f Hf].
    exists (fun '(x,y) n => f (F' x,y) n). intros (n, b).
    now rewrite (Hf (_, _)).
  - eauto.
  - pose (g := fix g n := match n with 0 => []
                             | S n => g n ++ [f (G (g n))]
                     end).
    assert (Hg : forall n, length (g n) = n). { induction n; cbn; rewrite ?app_length; cbn; lia. }
    exists (fun n => f (G (g n))).
    induction n.
    + cbn. specialize (Hf (G [])). unfold F' in Hf.
      now rewrite HFG in Hf.
    + specialize (Hf (G (g (S n)))).
      rewrite /F' HFG in Hf.
      match goal with
      | [ H : R ?a _ |- R ?b _ ] => enough (a = b) as <- by eassumption
      end.
      generalize (S n) as m.
      clear - Hg. induction m.
      * reflexivity.
      * replace (S m) with (m + 1) at 2 by lia.
        rewrite seq_app map_app. cbn. congruence.
Qed.

Lemma inf_path_iff_inf (τ : tree) f :
  (forall n, infinite_tree (subtree_at (map f (seq 0 n)) τ)) -> (forall n, τ (map f (seq 0 n))).
Proof.
  intros H n.
  destruct (H n 0) as (v & Hv1 & Hv2).
  eapply tree_p. eapply τ. 2:eassumption.
  now exists v. 
Qed.

Lemma co_semi_decidable_iff {X} (p : nat -> X -> Prop) :
  (forall x y, dec (p x y)) -> co_semi_decidable (fun x => forall n : nat, p n x).
Proof.
  intros D.
  exists (fun n x => if D x n then false else true).
  intros x. split; intros; destruct (D n x); cbn; firstorder.
  specialize (H n); destruct (D n x); cbn in *; congruence.
Qed.

Lemma coS_ADC_on_weak_to_WKL :
  coS_ADC_on_weak bool -> WKL.
Proof.
  intros C τ inf_τ.
  pose proof (tree_dec τ) as [D] % decidable_iff.
  pose (d u m := exists v, length v = m /\ τ (u ++ v)).
  assert (Dd : forall u m, dec (d u m) ). {
    intros u m. eapply listable_exists_dec.
    eapply listable_list_length.
    eauto.
  }
  assert (Hd : forall u, infinite_tree (subtree_at u τ) <-> forall m, d u m). {
    split.
    - intros H m. specialize (H m) as (v & Hv1 & Hv2).
      exists (take m v). split.
      rewrite firstn_length_le. lia. reflexivity.
      eapply tree_p. eapply τ. 2:eauto.
      exists (drop m v).
      rewrite <- (firstn_skipn m v) at 1. now rewrite <- app_assoc.
    - intros H m. destruct (H m) as (v & Hv1 & Hv2).
      exists v. split; try lia. eassumption.
  } 
  destruct (C (fun u b => forall m, d (u ++ [b]) m \/ ~ d (u ++ [negb b]) m)) as [f Hf].
  - destruct (@co_semi_decidable_iff _ (fun m '(x,y) => d (x ++ [y]) m
                                                     ∨ ¬ d (x ++ [negb y]) m)) as [f Hf].
    + intros n (u, b). exact _.
    + exists f. intros (u, b).
      eapply (Hf (_, _)).
  - intros u H.
    assert (H1 : ~ forall m, d (u ++ [true]) m \/ ~ d (u ++ [false]) m).
    { intros ?. eapply H. exists true. cbn. eauto. }
    assert (H2 : ~ forall m, d (u ++ [false]) m \/ ~ d (u ++ [true]) m).
    { intros ?. eapply H. exists false. cbn. eauto. }
    eapply H1. intros m1.
    destruct (Dd (u ++ [true]) m1) as [H3 | H3]. eauto.
    right. intros H4.
    eapply H2. intros m2.
    destruct (Dd (u ++ [false]) m2) as [H5 | H5]. eauto.
    right. intros H6.
    destruct (le_ge_dec m1 m2).
    + eapply H3. destruct H6 as (v & Hv1 & Hv2).
      exists (take m1 v). split.
      rewrite firstn_length_le. lia. reflexivity.
      eapply tree_p. eapply τ.
      2:eauto.
      exists (drop m1 v).
      rewrite <- (firstn_skipn m1 v) at 1.
      now rewrite !app_assoc.
    + eapply H5. destruct H4 as (v & Hv1 & Hv2).
      exists (take m2 v). split.
      rewrite firstn_length_le. lia. reflexivity.
      eapply tree_p. eapply τ.
      2:eauto.
      exists (drop m2 v).
      rewrite <- (firstn_skipn m2 v) at 1.
      now rewrite !app_assoc.
   - exists f. eapply inf_path_iff_inf.
    induction n.
    + cbn. eapply inf_τ.
    + replace (S n) with (n + 1) by lia.
      rewrite seq_app map_app. cbn.
      rewrite !Hd in IHn |- *.
      intros m. destruct (IHn (S m)) as (v & Hv1 & Hv2).
      destruct v as [ | [] v]; inv Hv1.
      * destruct (f n) eqn:E.
        -- exists v. split; eauto.
           rewrite <- app_assoc. eassumption.
        -- edestruct Dd. eassumption.
           specialize (Hf n (length v)) as [].
           congruence. rewrite E in H.
           cbn in *. destruct H.
           exists v. split. eauto.
           now rewrite <- app_assoc.
      * destruct (f n) eqn:E.
        -- edestruct Dd. eassumption.
           specialize (Hf n (length v)) as [].
           congruence. rewrite E in H.
           cbn in *. destruct H.
           exists v. split. eauto.
           now rewrite <- app_assoc.
        -- exists v. split; eauto.
           rewrite <- app_assoc. eassumption.
Qed.

Lemma LEM_FAN_KT :
  LEM -> ~ FAN -> KT.
Proof.
  intros lem wkl.
  destruct (lem KT); eauto.
  exfalso. eapply wkl. intros T infT.
  destruct (lem (bounded_tree T)); eauto.
  exfalso. eapply H. exists T.
  split; eauto. now eapply not_bounded_infinite.
Qed.

Lemma LEM_WKL_KT :
  LEM -> ~ WKL -> KT.
Proof.
  intros lem wkl.
  destruct (lem KT); eauto.
  exfalso. eapply wkl. intros T infT.
  destruct (lem (infinite_path T)); eauto.
  exfalso. eapply H. exists T.
  split; eauto.
  assert (MP) as mp % MP_tree_iff'. { eapply LPO_MP_WLPO_iff. intros ?. eapply lem. }
  now eapply mp.
Qed.

(* Lemma is_tree_ext : *)
(*   Proper (pointwise_relation _ iff ==> iff) is_tree.  *)
(* Proof. *)
(*   intros T1 T2 H. split; intros []; repeat split. *)
(*   - firstorder. *)
(*   - intros. rewrite <- H in *. eauto. *)
(*   - rewrite <- H. eauto. *)
(*   - firstorder. *)
(*   - intros. rewrite H in H1 |- *. eauto. *)
(*   - rewrite H. eauto. *)
(* Qed. *)

(* Lemma infinite_tree_ext : *)
(*   Proper (pointwise_relation _ iff ==> iff) infinite_tree. *)
(* Proof. *)
(*   intros T1 T2 H. unfold infinite_tree. split; intros H1 k. *)
(*   - now setoid_rewrite <- H. *)
(*   - now setoid_rewrite H. *)
(* Qed. *)

(* Lemma subtree_at_app T l1 l2 : *)
(*   is_tree (subtree_at l2 (subtree_at l1 T)) <-> is_tree (subtree_at (l1 ++ l2) T). *)
(* Proof. *)
(*   rewrite is_tree_ext. reflexivity. *)
(*   red. unfold subtree_at. intros. now rewrite app_assoc. *)
(* Qed. *)

(* Lemma subtree_at_app_inf T l1 l2 : *)
(*   infinite_tree (subtree_at l2 (subtree_at l1 T)) <-> infinite_tree (subtree_at (l1 ++ l2) T). *)
(* Proof. *)
(*   rewrite infinite_tree_ext. reflexivity. *)
(*   red. unfold subtree_at. intros. now rewrite app_assoc. *)
(* Qed. *)

(* Lemma subtree_at_app' T l1 l2 : *)
(*   is_tree (subtree_at l2 (subtree_at l1 T)) -> is_tree (subtree_at (l1 ++ l2) T). *)
(* Proof. *)
(*   eapply subtree_at_app. *)
(* Qed. *)

(* Lemma subtree_at_app_inf' T l1 l2 : *)
(*   infinite_tree (subtree_at l2 (subtree_at l1 T)) -> infinite_tree (subtree_at (l1 ++ l2) T). *)
(* Proof. *)
(*   eapply subtree_at_app_inf. *)
(* Qed. *)

(* Hint Resolve subtree_at_app' subtree_at_app_inf' : core. *)

(* Lemma LLPO_ADCC_WKL : *)
(*   LLPO_tree -> (forall P, (ADC_on (sig (fun l : list bool => P l)))) -> WKL. *)
(* Proof. *)
(*   move => LLPO C T Hinf. *)
(*   unshelve edestruct (C (fun l => is_tree (subtree_at l T) /\ infinite_tree (subtree_at l T))  (fun l1 l2 => exists b, proj1_sig l2 = proj1_sig l1 ++ [b])) as [f [H0 Hf]]. *)
(*   - exists []. split. eapply T. eapply Hinf. *)
(*   - intros [l [l_tree l_inf]]. *)
(*     destruct (LLPO (Build_tree l_tree) l_inf) as [[Htree Hinft] | [Htree Hinft]]; cbn in *. *)
(*     + unshelve eexists. *)
(*       * exists (l ++ [true]). eauto. *)
(*       * exists true. reflexivity. *)
(*     + unshelve eexists. *)
(*       * exists (l ++ [false]). eauto. *)
(*       * exists false. reflexivity. *)
(*   - assert (Hl : forall n, length (proj1_sig (f n)) = n). { *)
(*       induction n. *)
(*       + rewrite H0. reflexivity. *)
(*       + destruct (Hf n) as [b ->].  rewrite app_length IHn //=. lia. *)
(*     } *)
(*     assert (Hmap : forall n, (map (λ n0 : nat, nth_default false (proj1_sig (f (S n0))) n0) (seq 0 n) = proj1_sig (f n))). { *)
(*       intros n. induction n. *)
(*       - cbn. rewrite H0. reflexivity. *)
(*       - replace (S n) with (n + 1) at 1 by lia. *)
(*         rewrite seq_app map_app IHn. cbn. *)
(*         specialize (Hf n) as [b ->]. *)
(*         rewrite nth_default_eq app_nth2. *)
(*         + rewrite Hl. lia. *)
(*         + rewrite Hl. cbn. now rewrite minus_diag. *)
(*     } *)
(*     exists (fun n => nth_default false (proj1_sig (f (S n))) n). *)
(*     intros n. rewrite Hmap. destruct (f n) as [l [Htree]]. *)
(*     cbn. eapply tree_nil in Htree. unfold subtree_at in Htree. *)
(*     revert Htree. now simpl_list. *)
(* Qed. *)

(* Definition DC_lor := forall p q, (forall u : list bool, p u \/ q u) -> exists f, forall n, if f n then p (map f (seq 0 n)) else q (map f (seq 0 n)). *)
(* Definition CC_lor := forall p q, (forall n : nat, p n \/ q n) ->      exists f, forall n, if f n then p n else q n. *)

(* Lemma Delta_DC_lor : forall p q, decidable p -> decidable q -> (forall u : list bool, p u \/ q u) -> exists f, forall n, if f n then p (map f (seq 0 n)) else q (map f (seq 0 n)). *)
(* Proof. *)
(*   intros p q [f Hf] [g Hg] H. *)
(*   pose (F := fix F n := match n with *)
(*                         | 0 => if f [] then [true] else [false] *)
(*                         | S n => if f (F n) then F n ++ [true] else F n ++ [false] *)
(*                         end). *)
(*   assert (HF : forall n, length (F n) = S n). { *)
(*     induction n; cbn. *)
(*     - destruct (f []); reflexivity. *)
(*     - destruct (f (F n)); rewrite app_length; cbn; lia. *)
(*   } *)
(*   exists (fun n => nth n (F n) false). *)
(*   induction n. *)
(*   - cbn. specialize (Hf []). *)
(*     destruct (f []); cbn. *)
(*     + now eapply Hf.  *)
(*     + edestruct (H []) as [H1 | H1]; eauto. eapply Hf in H1. congruence.  *)
(*   - specialize (Hf (F n)). *)
(*     cbn -[seq]. *)
(*     assert (E : map (λ n0 : nat, nth n0 (F n0) false) (seq 0 (length (F n))) = F n). *)
(*     + clear Hf. clear - HF. induction n. *)
(*       * cbn. destruct (f []); reflexivity. *)
(*       * cbn. destruct (f (F n)) eqn:E. *)
(*         -- rewrite app_length seq_app map_app. *)
(*            cbn. rewrite HF. cbn -[seq]. rewrite E. rewrite app_nth2. rewrite HF. lia. *)
(*            cbn -[seq]. rewrite HF minus_diag. *)
(*            rewrite <- IHn. now rewrite HF. *)
(*         -- rewrite app_length seq_app map_app. *)
(*            cbn. rewrite HF. cbn -[seq]. rewrite E. rewrite app_nth2. rewrite HF. lia. *)
(*            cbn -[seq]. rewrite HF minus_diag. *)
(*            rewrite <- IHn. now rewrite HF. *)
(*     + destruct (f (F n)). *)
(*       * rewrite app_nth2. rewrite HF. lia. *)
(*         rewrite HF minus_diag. cbn [nth]. *)
(*         rewrite <- HF, E. now eapply Hf. *)
(*       * rewrite app_nth2. rewrite HF. lia. *)
(*         rewrite HF minus_diag. cbn [nth]. *)
(*         rewrite <- HF, E. *)
(*         destruct (H (F n)); eauto. eapply Hf in H0. congruence. *)
(* Qed. *)

(* Lemma DC_CC_iff : *)
(*   DC_lor <-> CC_lor. *)
(* Proof. *)
(*   split. *)
(*   - intros dc p q H. *)
(*     destruct (dc (fun u => p (length u)) (fun u => q (length u))) as [f Hf]; eauto. *)
(*     exists f. intros n. specialize (Hf n). *)
(*     now rewrite map_length seq_length in Hf. *)
(*   - assert (countable (list bool)) as (G & F & HFG). { *)
(*       eapply enumerable_discrete_countable; eauto. *)
(*       eapply discrete_iff. econstructor. exact _. *)
(*     } *)
(*     intros cc p q H. *)
(*     pose (F' n := match F n with Some u => u | _ => [] end). *)
(*     destruct (cc (fun n => p (F' n)) (fun n => q (F' n))) as [f Hf]; eauto. *)
(*     assert (forall u, f (G u) = true \/ f (G u) = false) as [g Hg] % Delta_DC_lor. { *)
(*       intros u. destruct (f (G u)); eauto.  *)
(*     } *)
(*     + exists g. intros n. specialize (Hg n). *)
(*       specialize (Hf (G (map g (seq 0 n)))). *)
(*       destruct (g n); now rewrite Hg /F' HFG in Hf. *)
(*     + eapply decidable_iff. econstructor. *)
(*       intros. exact _. *)
(*     + eapply decidable_iff. econstructor. *)
(*       intros. exact _. *)
(* Qed. *)

(* (* Lemma LLPO_DC_WKL : *) *)
(* (*   LLPO_tree -> DC_lor -> WKL. *) *)
(* (* Proof. *) *)
(* (*   move => LLPO C T Hinf. *) *)
(* (*   specialize (C (fun u => is_tree (subtree_at (u) T) /\ infinite_tree (subtree_at (u) T) -> is_tree (subtree_at (u ++ [true]) T) /\ infinite_tree (subtree_at (u ++ [true]) T)) (fun u => is_tree (subtree_at (u) T) /\ infinite_tree (subtree_at (u) T) -> is_tree (subtree_at (u ++ [false]) T) /\ infinite_tree (subtree_at (u ++ [false]) T))) as [f Hf]. *) *)
(* (*   - induction u using rev_ind. *) *)
(* (*     + destruct (LLPO T); eauto. *) *)
(* (*     + destruct IHu as [(v & H1 & H2 & H3)|(v & H1 & H2 & H3)]. *) *)
(* (*       * eapply (LLPO (Build_tree H2)) in H3 as [[H3 H4] | [H3 H4]]; cbn in *. *) *)
(* (*         -- eapply subtree_at_app in H3. eapply subtree_at_app_inf in H4. *) *)
(* (*            left. exists (v ++ [true]). split. rewrite! app_length. cbn. lia. eauto. *) *)
(* (*         -- eapply subtree_at_app in H3. eapply subtree_at_app_inf in H4. *) *)
(* (*            right. exists (v ++ [true]). split. rewrite! app_length. cbn. lia. eauto. *) *)
(* (*       * eapply (LLPO (Build_tree H2)) in H3 as [[H3 H4] | [H3 H4]]; cbn in *. *) *)
(* (*         -- eapply subtree_at_app in H3. eapply subtree_at_app_inf in H4. *) *)
(* (*            left. exists (v ++ [false]). split. rewrite! app_length. cbn. lia. eauto. *) *)
(* (*         -- eapply subtree_at_app in H3. eapply subtree_at_app_inf in H4. *) *)
(* (*            right. exists (v ++ [false]). split. rewrite! app_length. cbn. lia. eauto. *) *)
(* (*   - exists f. induction n. *) *)
(* (*     + cbn. eauto. *) *)
(* (*     + replace (S n) with (n + 1) by lia. *) *)
(* (*       rewrite seq_app. cbn. *) *)

(* (* . *) *)
(* (*   destruct (C (fun u => T (u ++ [true])) (fun u => T (u ++ [false]))). *) *)
(* (*   unshelve edestruct (C (fun l => is_tree (subtree_at l T) /\ infinite_tree (subtree_at l T))  (fun l1 l2 => exists b, proj1_sig l2 = proj1_sig l1 ++ [b])) as [f [H0 Hf]]. *) *)
(* (*   - exists []. split. eapply T. eapply Hinf. *) *)
(* (*   - intros [l [l_tree l_inf]]. *) *)
(* (*     destruct (LLPO (Build_tree l_tree) l_inf) as [[Htree Hinft] | [Htree Hinft]]; cbn in *. *) *)
(* (*     + unshelve eexists. *) *)
(* (*       * exists (l ++ [true]). eauto. *) *)
(* (*       * exists true. reflexivity. *) *)
(* (*     + unshelve eexists. *) *)
(* (*       * exists (l ++ [false]). eauto. *) *)
(* (*       * exists false. reflexivity. *) *)
(* (*   - assert (Hl : forall n, length (proj1_sig (f n)) = n). { *) *)
(* (*       induction n. *) *)
(* (*       + rewrite H0. reflexivity. *) *)
(* (*       + destruct (Hf n) as [b ->].  rewrite app_length IHn //=. lia. *) *)
(* (*     } *) *)
(* (*     assert (Hmap : forall n, (map (λ n0 : nat, nth_default false (proj1_sig (f (S n0))) n0) (seq 0 n) = proj1_sig (f n))). { *) *)
(* (*       intros n. induction n. *) *)
(* (*       - cbn. rewrite H0. reflexivity. *) *)
(* (*       - replace (S n) with (n + 1) at 1 by lia. *) *)
(* (*         rewrite seq_app map_app IHn. cbn. *) *)
(* (*         specialize (Hf n) as [b ->]. *) *)
(* (*         rewrite nth_default_eq app_nth2. *) *)
(* (*         + rewrite Hl. lia. *) *)
(* (*         + rewrite Hl. cbn. now rewrite minus_diag. *) *)
(* (*     } *) *)
(* (*     exists (fun n => nth_default false (proj1_sig (f (S n))) n). *) *)
(* (*     intros n. rewrite Hmap. destruct (f n) as [l [Htree]]. *) *)
(* (*     cbn. eapply tree_nil in Htree. unfold subtree_at in Htree. *) *)
(* (*     revert Htree. now simpl_list. *) *)
(* (* Qed. *) *)


(* Lemma test : *)
(*   WKL <->   coS_ADC_on_weak bool. *)
(* Proof. *)
(*   split. *)
(*   - intros WKL. *)
(*     eapply maria, bla. *)
(*     eapply WKL_to_LPOO. eassumption. *)
(*     eapply WKL_to_coS_AC_on_nat_bool. eassumption. *)
(*   - eapply andback. *)
(* Qed. *)


