From Undecidability Require Import Definitions.
From Undecidability Require Import mu_nat partial equiv_on.

From Undecidability Require Import simple principles EnumerabilityFacts.

Require Import Nat Arith Lia.

From Undecidability Require Import FinitenessFacts.
From stdpp Require Import base.
Require Import List.

From Undecidability Require Import Pigeonhole.

From Undecidability Require Import Dec.

Set Default Goal Selector "!".

Lemma modality_return (P : Prop) : P -> ~~ P. Proof. tauto. Qed.
Lemma modality_bind (P Q : Prop) : P -> (P -> ~~ Q) -> ~~Q. Proof. tauto. Qed.
Lemma modality_case (P Q : Prop) : (P \/ ~ P -> ~~ Q) -> ~~Q. Proof. tauto. Qed.

Lemma modality_LEM {P : Prop} : LEM -> ~~ P -> P. Proof. intros lem H; destruct (lem P); tauto. Qed.

Theorem least_exists (p : nat -> Prop) :
  (exists n, p n) -> ~~ exists n, p n /\ forall i, p i -> n <= i.
Proof.
  intros H. destruct H as [n H].
  induction n using lt_wf_ind.
  ccase (exists m, m < n /\ p m) as [[m [Hm1 Hm2]] | Hm].
  - eauto.
  - cprove exists n; firstorder. 
    assert (i < n \/ n <= i) by lia; firstorder.
Qed.

Definition the_least_pred (P : nat -> Prop) : nat -> Prop :=
  fun y => P y /\ forall y', P y' -> y <= y'.

Lemma the_least_pred_unique {P : nat -> Prop} {x y} :
  the_least_pred P x -> the_least_pred P y -> x = y.
Proof.
  firstorder lia.
Qed.

Lemma the_least_pred_impl' {P Q : nat -> Prop} {x} :
  the_least_pred P x -> (forall x, P x <-> Q x) -> the_least_pred Q x.
Proof.
  intros [H2 H3] H1. eapply H1 in H2. split. 1:exact H2. intros y'. rewrite <- H1. apply H3.
Qed.

Lemma the_least_pred_equiv {P Q : nat -> Prop} {x} :
  (forall x, P x <-> Q x) -> the_least_pred P x <-> the_least_pred Q x.
Proof.
  intros. split; intros; eapply the_least_pred_impl'; eauto; firstorder.
Qed.

Lemma the_least_pred_impl {P Q : nat -> Prop} {x} :
  the_least_pred P x -> (forall x, P x -> exists y, Q y) -> ~~ exists x, the_least_pred Q x.
Proof.
  intros [H2 H3] H1. eapply H1 in H2.
  clear H1 H3 P.
  assert (exists x, Q x) as H by eauto. clear x H2. eapply least_exists in H.
  intros G. apply H. intros (x & H2 & H3).  apply G.
  exists x. split. 1:auto. intros. eapply H3. auto.
Qed.

Lemma the_least_ex (P : nat -> Prop) :
  (exists n, P n) -> ~~ exists n, the_least_pred P n.
Proof.
  intros H % least_exists.
  intros G. apply H. intros (n & H2 & H3).
  apply G. exists n. split; auto with arith.
Qed.

Record FunRel X Y := {
  the_rel :> X -> Y -> Prop ;
    is_fun : (forall x y1 y2, the_rel x y1 -> the_rel x y2 -> y1 = y2)
  }.

Definition total {X Y} (R : X -> Y -> Prop) :=
  forall x, exists y, R x y.

Definition weakly_total {X Y} (R : X -> Y -> Prop) :=
  forall x, ~~ exists y, R x y.

Axiom Part : partiality.
Existing Instance Part.

Notation "x ▷ y" := (@hasvalue Part nat x y) (at level 50).

Instance equiv_part {A} : equiv_on (part A) := {| equiv_rel := @partial.equiv _ A |}.

Lemma MP_total (R : nat -> nat -> Prop) :
  MP -> enumerable (curry R) -> weakly_total R -> total R.
Proof.
  intros H Henum x Hx. eapply MP_to_MP_semidecidable in H.
  red in H. eapply H with (p := fun x => exists n, R x n).
  - eapply SemiDecidabilityFacts.semi_decidable_ex.
    eapply SemiDecidabilityFacts.enumerable_semi_decidable; eauto.
    eapply ReducibilityFacts.enumerable_red.
    4: exact Henum. all:eauto.
    exists (fun '(x,y) => (y, x)). intros []. firstorder.
  - eauto.
Qed.

Lemma MP_choice (R : nat -> nat -> Prop) : MP -> enumerable (fun '(x,y) => R x y) ->
  (forall x, ~~ exists y, R x y) -> exists f, forall x, R x (f x).
Proof.
  intros.
  eapply enumerable_AC; eauto.
  eapply MP_total; eauto.
Qed.

Lemma get_partial_choice (R : nat -> nat -> Prop) :
  enumerable (fun '(x,y) => R x y) ->
  exists f : nat ↛ nat, forall x v_x,
    (f x ▷ v_x -> R x v_x) /\ (R x v_x -> exists v', f x ▷ v').
Proof.
  intros [f Hf].
  exists (fun x => bind (mu_tot (fun n => if f n is Some (x', y) then x =? x' else false))
                (fun n => if f n is Some (x', y) then ret y else undef)).
  intros x v_x. rewrite bind_hasvalue.
  split.
  - intros (n & (H1 & H3) % mu_tot_hasvalue & H2).
    destruct (f n) as [ [x' y] | ]eqn:E; try congruence.
    destruct (Nat.eqb_spec x x'); try congruence. subst.
    eapply ret_hasvalue_iff in H2. subst.
    eapply (Hf (x', v_x)). eauto.
  - intros [n Hn] % (Hf (x, v_x)).
    edestruct (mu_tot_ter) as [a Ha].
    2:{ destruct (f a) as [[x' y'] | ] eqn:E.
        - eexists. eapply bind_hasvalue. exists a. split. 1: eapply Ha.
          rewrite E. eapply ret_hasvalue.
        - eapply mu_tot_hasvalue in Ha as [Ha _].
          rewrite E in Ha. congruence.
    }
    cbn. rewrite Hn. eapply Nat.eqb_refl.
Qed.

Hint Rewrite List.app_nil_l @list.nil_length : length.

Program Definition the_least {X} (R : X -> nat -> Prop) : FunRel X nat :=
  {|
  the_rel x := the_least_pred (R x) ;
  is_fun := fun x y1 y2 H1 H2 => the_least_pred_unique H1 H2
  |}.

Axiom tonat : list bool -> nat.
Axiom ofnat : nat -> list bool.

Axiom ofnat_tonat : forall l, ofnat (tonat l) = l.
Axiom tonat_ofnat : forall n, tonat (ofnat n) = n.
Axiom length_log : forall n, length (ofnat n) <= Nat.log2 n + 1.

Module axioms_consistent.
  Require Import BinNums BinPos.

  Fixpoint pos_to_list (p : positive) :=
    match p with
    | xH => []
    | xI x => true :: pos_to_list x
    | xO x => false :: pos_to_list x
    end.

  Fixpoint list_to_pos (p : list bool) :=
    match p with
    | nil => xH
    | true  :: l => xI (list_to_pos l)
    | false :: l => xO (list_to_pos l)
    end.

  Lemma pos_to_list_iff p :
    pos_to_list (list_to_pos p) = p.
  Proof.
    induction p as [ | [] ? IH]; cbn in *; congruence.
  Qed.

  Lemma list_to_pos_iff p :
    list_to_pos (pos_to_list p) = p.
  Proof.
    induction p; cbn in *; congruence. 
  Qed.

  Definition tonat l :=
    Pos.to_nat (list_to_pos l) - 1.

  Definition ofnat n :=
    pos_to_list (Pos.of_nat (1 + n)).

  Lemma pos_size_nat_0 p :
    Pos.size_nat p > 0.
  Proof.
    induction p; cbn; lia.
  Qed.
  
  Lemma length_pos_to_list p :
    1 + length (pos_to_list p) = Pos.size_nat p.
  Proof.
    induction p; cbn; lia.
  Qed.

  Lemma size_eq n :
    BinNat.N.size_nat n = BinNat.N.to_nat (BinNat.N.size n).
  Proof.
    induction n; cbn; try lia.
    induction p; cbn; lia.
  Qed.

  Lemma log2_eq n :
    BinNat.N.to_nat (BinNat.N.log2 n) = Nat.log2 (BinNat.N.to_nat n).
  Proof.
    unfold BinNat.N.log2.
    destruct n.
    - reflexivity.
    -  cbn. symmetry. induction p; cbn; try reflexivity.
      + rewrite Pnat.Pos2Nat.inj_xI.
        replace (S (2 * Pos.to_nat p)) with (2 * Pos.to_nat p + 1) by lia.
        rewrite PeanoNat.Nat.log2_succ_double; [ | lia].
        rewrite IHp. destruct p; cbn; try rewrite Pnat.Pos2Nat.inj_succ; reflexivity.
      + rewrite Pnat.Pos2Nat.inj_xO.
        rewrite Nat.log2_double; [ | lia].
        rewrite IHp. destruct p; cbn; try rewrite Pnat.Pos2Nat.inj_succ; reflexivity.
  Qed.

  Lemma ofnat_tonat l :
    ofnat (tonat l) = l.
  Proof.
    unfold tonat, ofnat.
    replace (1 + (Pos.to_nat (list_to_pos l) - 1))
      with (Pos.to_nat (list_to_pos l)) by lia.
    now rewrite Pnat.Pos2Nat.id, pos_to_list_iff.
  Qed.

  Lemma tonat_ofnat n :
    tonat (ofnat n) = n.
  Proof.
    unfold tonat, ofnat.
    rewrite list_to_pos_iff, Pnat.Nat2Pos.id_max.
    lia.
  Qed.

  Lemma length_log n :
    length (ofnat n) <= Nat.log2 n + 1.
  Proof.
    unfold ofnat.
    eapply le_S_n.
    rewrite length_pos_to_list.
    change (Pos.size_nat (Pos.of_nat (1 + n))) with
      (BinNat.N.size_nat (Npos (Pos.of_nat (1 + n))) ).
    rewrite size_eq.
    pose proof (BinNat.N.size_log2 (Npos (Pos.of_nat (1 + n)))) as H.
    rewrite <- Pos.of_nat_succ in H |- *.
    rewrite H. 2: congruence. clear H.
    change (Npos (Pos.of_succ_nat n)) with (BinNat.N.of_nat (S n)).
    rewrite Nnat.N2Nat.inj_succ.
    rewrite log2_eq.
    rewrite Nnat.Nat2N.id.
    eapply le_n_S. rewrite PeanoNat.Nat.log2_succ_le. lia.
  Qed.

End axioms_consistent.

Hint Rewrite ofnat_tonat tonat_ofnat : length.
Hint Rewrite List.app_length : length.

Notation "| n |" := (length (ofnat n)) (at level 10).

Notation "⟨ x , y ⟩" := (tonat (ofnat x ++ ofnat y)) (at level 0).

Lemma size_pair x y : | ⟨x,y⟩ | = |x| + |y|.
Proof.
  now autorewrite with length.
Qed.

Lemma size_sublinear d : ~ forall n, n <= |n| + d.
Proof.
  intros H.
  pose (n := 1 + 2 * S d).
  assert (2 ^ n > n + S d).
  { subst n. rewrite Nat.pow_add_r, Nat.pow_mul_r.
    generalize (S d). cbn. induction n; cbn; lia.
  }
  specialize (H (2 ^ n)).
  pose proof (length_log (2 ^ n)).
  rewrite Nat.log2_pow2 in *; lia.
Qed.

Lemma bitlist_for_k k :
  exists l : list (list bool), (forall x, In x l <-> length x = k) /\ NoDup l /\ length l = 2 ^ k.
Proof.
  induction k.
  - exists (nil :: nil). split; [ | split ].
    + cbn. intros []; cbn in *; firstorder congruence. all: congruence.
    + repeat econstructor; eauto.
    + reflexivity.
  - destruct IHk as (L & IH1 & IH2 & IH3).
    exists (map (cons true) L ++ map (cons false) L).
    split; [ | split].
    + intros l.
      rewrite in_app_iff, !in_map_iff.
      setoid_rewrite IH1.
      destruct l as [ | ].
      * cbn. split. 2:lia.
        intros [(? & [=] & ?) | (? & [=] & ?)].
      * cbn. split. 
        -- intros [(? & [=] & ?) | (? & [=] & ?)]; subst; lia.
        -- destruct b; intros [=]; eauto.
    + eapply NoDup_app; try eapply map_NoDup; [firstorder congruence .. |].
      intros ? (? & <- & ?) % in_map_iff (? & ? & ?) % in_map_iff.
      congruence.
    + rewrite app_length, !map_length, IH3. cbn. lia.
Qed.

Section Kolmogorov.

Variable Θ : nat ↛ nat.

Definition C := the_least (fun x s => exists c, s = |c| /\ Θ c ▷ x).

Variable Θ_total : forall x, exists y, Θ y ▷ x.

Lemma C_weakly_total :
  forall x,~~ exists y, C x y.
Proof.
  intros x. destruct (Θ_total x) as [y Hy].
  eapply the_least_ex. eauto.
Qed.

Definition N (x : nat) :=
  exists y, Θ y ▷ x /\ |y| < |x|.

Definition N1 (x : nat) := exists y, C x y /\ y < |x|.
Definition N3 (x : nat) := forall y, C x y -> y < |x|.

Fact N_equiv x :
  (N1 x -> N x) /\ (N x -> N3 x) /\ (N3 x -> ~~ N1 x).
Proof.
  repeat split.
  - intros (y & ((c & -> & H2) & H3) & H4).
    firstorder.
  - intros (y & H1 & H2) y' ((c & -> & ?) & ?).
    eapply le_lt_trans with (m := |y|); eauto.
  - firstorder using C_weakly_total.
Qed.

Lemma par_enum_ϕ :
  enumerable (fun '(x, y) => Θ y ▷ x).
Proof.
  eapply ReducibilityFacts.enumerable_red.
  4: eapply enumerable_graph_part; eauto.
  all: eauto.
  exists (fun '(x,y) => (y, x)). intros [].  cbn. reflexivity.
Qed.

Lemma enumerable_N :
  enumerable N.
Proof.
  destruct (par_enum_ϕ) as [f Hf].
  exists (fun n => if f n is Some (x,y) then if Nat.ltb (|y|) (|x|) then Some x else None else None).
  red. intros x. split.
  - intros (y & H1 & H2).
    eapply (Hf (x, y)) in H1 as [n Hn].
    exists n. rewrite Hn.
    destruct (Nat.ltb_spec (|y|) (|x|)).
    + reflexivity.
    + lia.
  - intros [n Hn]. destruct (f n) as [[x' y] | ] eqn:E; inversion Hn.
    destruct (Nat.ltb_spec (|y|) (|x'|)).
    + inversion Hn. subst. exists y. split; eauto.
      eapply (Hf (x, y)). eauto.
    + congruence.
Qed.

Definition R (x : nat) :=
  forall y, Θ y ▷ x -> |y| >= |x|.

Definition R1 (x : nat) := exists y, C x y /\ y >= |x|.
Definition R3 (x : nat) := forall y, C x y -> y >= |x|.

Lemma R_neg_N x :
  R x <-> ~ N x.
Proof.
  split.
  - intros H (y & H1 % H & H2). lia.
  - intros H y H1.
    assert (|y| >= |x| \/ |y| < |x|) as [ Ha | Ha ] by lia; [ auto | ].
    destruct H. exists y. eauto.
Qed.

Fact R_equiv x :
  (R1 x -> R x) /\ (R x -> R3 x) /\ (R3 x -> ~~ R1 x).
Proof.
  repeat split.
  - intros (y & ((c & -> & H2) & H3) & H4) y' H.
    red. transitivity (|c|); eauto.
  - intros H1 y ((c & -> & H2) & H3). firstorder.
  - firstorder using C_weakly_total.
Qed.

Lemma list_for_k k :
  exists l, (forall x, In x l <-> | x | = k) /\ NoDup l /\ length l = 2 ^ k.
Proof.
  destruct (bitlist_for_k k) as (l & H1 & H2 & H3).
  exists (map tonat l). split; [ | split].
  - intros x. cbn. rewrite in_map_iff.
    setoid_rewrite H1. split.
    + intros (y & <- & <-). now autorewrite with length.
    + intros <-. exists (ofnat x). now autorewrite with length. 
  - eapply map_NoDup; auto. intros ? ? E % (f_equal ofnat).
    now rewrite !ofnat_tonat in E.
  - now rewrite map_length.
Qed.

Lemma list_for_le_k k :
  exists l, (forall x, In x l <-> | x | <= k) /\ NoDup l /\ length l = 2 ^ (S k) - 1.
Proof.
  induction k.
  - cbn. exists [ tonat nil ]. 
    split; [ | split ].
    + cbn. split.
      * intros [ <- | []]. now autorewrite with length.
      * intros H. left. destruct (ofnat x) eqn:E; inversion H.
        rewrite <- E. now autorewrite with length.
    + repeat econstructor. firstorder.
    + reflexivity.
  - cbn. destruct IHk as (l1 & IH1 & IH2 & IH3).
    destruct (list_for_k (S k)) as (l2 & H1 & H2 & H3).
    exists (l1 ++ l2). split; [ | split].
    + intros. rewrite in_app_iff, IH1, H1.
      lia.
    + eapply NoDup_app; firstorder lia.
    + rewrite app_length, IH3, H3. cbn; lia.
Qed.

Lemma at_most k : 
  forall l, (forall x, In x l -> | x | < k) -> NoDup l -> length l <= 2^ k - 1.
Proof.
  intros l H1 H2. unfold lt in H1.
  destruct k.
  - cbn. destruct l; cbn in *.
    + lia.
    + inversion H2 as [| x l_ H3 H4]; subst.
      unshelve epose proof (H1 n _).
      * eauto.
      * lia.
  - setoid_rewrite <- Nat.succ_le_mono in H1.
    destruct (list_for_le_k k) as (l2 & H3 & H4 & H5).
    assert (length l <= length l2). {
      eapply NoDup_incl_length; firstorder.
    }
    enough (length l2 <= 2 ^ (S k) - 1) by lia.
    rewrite H5. lia.
Qed.

(* TODO move *)
Definition injective {X Y} (R : X -> Y -> Prop) :=
  forall x1 x2 y, R x1 y -> R x2 y -> x1 = x2.

Lemma Forall2_ex_r {X Y} (R : X -> Y -> Prop) l1 l2 y :
  Forall2 R l1 l2 ->
  In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  induction 1; repeat firstorder subst.
Qed.

Lemma functional_NoDup (R : nat -> nat -> Prop) l :
  injective R ->
  (forall x, In x l -> exists y, R x y) ->
  NoDup l ->
  exists l', NoDup l' /\ Forall2 R l l'.
Proof.
  intros HR Htot Hl. induction Hl.
  - exists []. split; econstructor. 
  - destruct IHHl as (l' & H1 & H2).
    + firstorder.
    + destruct (Htot x) as [y Hy].
      1: firstorder.
      exists (y :: l'). split.
      * econstructor; [ | eauto].
        intros Hin.
        edestruct @Forall2_ex_r as (x' & H3 & H4); eauto.
        eapply H. eapply HR in H4 as <-; eauto.
      * econstructor; eauto.
Qed.

Lemma nonrandom_k k :
  ~ forall x, |x| = k -> N x.
Proof.
  intros H.
  destruct (list_for_k k) as (l & H1 & H2 & H3).
  eapply (functional_NoDup (fun x y => Θ y ▷ x ∧ | y | < | x |)) in H2 as (l' & H4 & H5).
  - assert (Forall (fun y => |y| < k) l'). {
      eapply list.Forall2_Forall_r; eauto.
      cbn. eapply Forall_forall.
      intros ? ? % H1. lia.
    } 
    assert (length l' = 2 ^ k). { erewrite <- list.Forall2_length; eauto. }
    unshelve epose proof (@at_most k l' _ _).
    * eapply Forall_forall. eauto.
    * eauto.
    * rewrite H2 in H6.
      enough (2 ^ k > k) by lia.
      eapply Nat.pow_gt_lin_r. lia.
  - intros x1 x2 y [Hx1 Hx11] [Hx2 Hx22]. eapply hasvalue_det; eauto.
  - now intros x ? % H1 % H. 
Qed.

Lemma non_finite_length (p : nat -> Prop) :
  ~ exhaustible p -> forall x, ~~ exists y, x < | y | /\ p y.
Proof.
  intros H.
  unshelve epose proof (non_finite_unbounded_fun _ (fun x => |x|) _ H).
  - cbn. intros n.
    destruct (@list_for_le_k n) as [L HL].
    exists L. intros. eapply HL. eauto.
  - intros x. specialize (H0 (S x)). cunwrap.
    destruct H0 as (y & H1 & H2). cprove exists y.
    split. 1:lia. assumption.
Qed.

Lemma classical_finite {X} (p q : X -> Prop):
  listable p -> (forall x, p x -> ~~ q x) -> ~~ forall x, p x -> q x.
Proof.
  intros [l Hl]. red in Hl.
  setoid_rewrite Hl. clear p Hl.
  induction l.
  - firstorder.
  - cbn. intros H.
    specialize (IHl ltac:(firstorder)).
    cunwrap. ccase (q a) as [Ha | Ha].
    + cprove intros ? [-> | ]; eauto.
    + specialize (H a); firstorder.
Qed.

Lemma non_finite_R :
  ~ exhaustible R.
Proof.
  eapply unbounded_non_finite_fun with (f := fun x => |x|).
  intros k G.
  assert (forall x, |x| = k -> ~~ N x).
  { intros x Hx GG. eapply G. exists x. split. 1:lia. now eapply R_neg_N. }
  eapply classical_finite in H.
  1:{ eapply H. clear H. intros H.
      now eapply (nonrandom_k k).
  }
  destruct (list_for_k k) as (L & H1 & _ & _).
  exists L. firstorder.
Qed.

Variable dist : forall f,
  exists d, forall x, exists y_x, Θ y_x ▷ f x /\ | y_x| < |x| + d.

Lemma desc_surjective x : exists y, Θ y ▷ x.
Proof.
  destruct (dist (fun x => x)) as [d H].
  specialize (H x) as [y [H _]].
  eauto.
Qed.

Lemma enum_size_lt :
  forall q : nat -> Prop, enumerable q -> enumerable (fun p => fst p < | snd p | /\ q (snd p)).
Proof.
  intros q Hq.
  eapply enumerable_conj; [ eauto | .. ].
  - eapply decidable_enumerable; eauto.
    eapply DecidabilityFacts.decidable_iff; econstructor; eauto.
  - eapply ReducibilityFacts.enumerable_red.
    4: eapply Hq. all: eauto. 
    exists snd. firstorder.
Qed.

Lemma subset :
  MP -> forall q : nat -> Prop, (forall x, q x -> R x) -> enumerable q -> ~ exhaustible q -> False.
Proof.
  intros mp q H1 H2 H3.
  unshelve epose proof (MP_choice _ mp _ (non_finite_length _ H3)) as [f Hf].
  1:{ eapply Proper_enumerable. 2: eapply enum_size_lt, H2. intros []; reflexivity. }
  assert (forall k y, Θ y ▷ f k -> |f k| <= |y|). {
    intros. destruct (Hf k) as [Hk1 Hk2]. 
    eapply H1; eauto.
  }
  destruct (dist f) as [d Hd].
  eapply (size_sublinear d). intros k.
  transitivity (|f k|). 1:eapply Nat.lt_le_incl, Hf.
  destruct (Hd k) as (y_k & Hk1 & Hk2).
  transitivity (|y_k|). 1: eauto.
  lia.
Qed.

Variable dist_part :
    forall f : nat ↛ nat,  exists d, forall x, forall v_x, f x ▷ v_x -> exists y_x, Θ y_x ▷ v_x /\ |y_x| < |x| + d.

Lemma dist_lem : forall f,
  exists d, forall x, exists y_x, Θ y_x ▷ f x /\ | y_x| < |x| + d.
Proof.
  intros f.
  destruct (dist_part (fun x => ret (f x))) as [d Hd].
  exists d. intros x.
  destruct (Hd x (f x)) as [y_x Hy].
  - eapply ret_hasvalue.
  - eauto.
Qed.

Lemma dist_rel : forall R,
  weakly_total R -> enumerable (fun '(x,y) => R x y) ->
  exists d, forall x, ~~ exists y_x, exists v_x, R x v_x /\ Θ y_x ▷ v_x /\ | y_x| < |x| + d.
Proof.
  intros R Htot [f Hf] % get_partial_choice.
  destruct (dist_part f) as [d Hd].
  - exists d. intros x.
    specialize (Htot x). cunwrap. destruct Htot as [v_x Hvx].
    eapply Hf in Hvx as [v_x' Hvx]. destruct (Hd x v_x') as [y_x H]; [eauto | ].
     cprove exists y_x. exists v_x'.
    firstorder.
Qed.

Lemma subset_strong :
  forall q : nat -> Prop, (forall x, q x -> R x) -> enumerable q -> ~ exhaustible q -> False.
Proof.
  intros q H1 H2 H3.
  destruct (dist_rel (fun k x => k < |x| /\ q x)) as [d Hd].
  - exact (non_finite_length _ H3).
  - eapply Proper_enumerable. 2: eapply enum_size_lt, H2. intros []; reflexivity.
  - eapply (size_sublinear d). intros k.
    specialize (Hd k).
    unshelve cstart. 1:eapply le_dec.
    cunwrap. destruct Hd as [y_k H].
    destruct H as (x_k & [H4 H5] & H6 & H7).
    cprove idtac.
    transitivity (|x_k|). 1:eapply Nat.lt_le_incl, H4.
    transitivity (|y_k|). 1: eapply H1; eauto. lia.
Qed.

Lemma exhaustible_ext {X} (p q : X -> Prop) :
  exhaustible p -> (forall x, p x <-> q x) -> exhaustible q.
Proof.
  firstorder.
Qed.

Lemma simple_N : MP -> simple N.
Proof.
  split. 2: split.
  - eapply enumerable_N.
  - intros ?. eapply non_finite_R, exhaustible_ext. 1: eauto.
    intros. now rewrite R_neg_N.
  - intros (q & H1 & H2 & H3). eapply subset; try eassumption.
    intros. eapply R_neg_N; eauto. firstorder.
Qed.

Lemma simple_N_strong : simple N.
Proof.
  split. 2: split.
  - eapply enumerable_N.
  - intros ?. eapply non_finite_R, exhaustible_ext. 1: eauto.
    intros. now rewrite R_neg_N.
  - intros (q & H1 & H2 & H3). eapply subset_strong; try eassumption.
    intros. eapply R_neg_N; eauto. firstorder.
Qed.

Lemma dist_again :
  forall f : nat -> nat, exists d, forall x y, C (f x) y -> y <= |x| + d.
Proof.
  intros f.
  destruct (dist f) as [d Hd]. exists d.
  intros x y H. destruct (Hd x) as (y_x & H1 & H2).
  etransitivity.
  - eapply H; eauto.
  - lia.
Qed.

Lemma unboundedR :
  forall k, ~~ exists x, | x | = k /\ R x.
Proof.
  setoid_rewrite R_neg_N. intros k G.
  assert (forall x, |x| = k -> ~~ N x) by firstorder. clear G.
  pose proof (nonrandom_k k).
  pose proof (list_for_k k) as (l & H1 & H2 & H3).
  setoid_rewrite <- H1 in H.
  setoid_rewrite <- H1 in H0.
  eapply classical_finite in H; [ tauto | ].
  exists l. red. reflexivity.
Qed.

Lemma R_undecidable :
  MP -> ~ decidable R.
Proof.
  intros mp Hdec.
  unshelve epose proof (MP_choice _ mp _ unboundedR) as [g Hg].
  - cbn. eapply decidable_enumerable. 2:eauto.
    eapply DecidabilityFacts.decidable_iff.
    eapply DecidabilityFacts.decidable_iff in Hdec. destruct Hdec.
    econstructor. intros (x, y).
    exact _.
  - destruct (dist_again g) as [d].
    eapply size_sublinear with (d := d).
    intros k.
    unshelve cstart.  1:eapply le_dec.
    pose proof (C_weakly_total (g k)) as Hk. cunwrap.
    destruct Hk as [C_u_k Hcuk].
    cprove idtac.
    transitivity (| g k|).
    1:{ eapply Nat.eq_le_incl. symmetry. eapply Hg. }
    destruct Hcuk as ([? [-> H1]] & H2).
    etransitivity.
    1:{ eapply Hg. eapply H1. }
    eapply H. cbn. firstorder.
Qed.

Lemma dist_again_strong R :
  weakly_total R -> enumerable (fun '(x,y) => R x y) ->
  exists d, forall x, ~~ exists v_x, R x v_x /\ forall y, C (v_x) y -> y <= |x| + d.
Proof.
  intros H1 H2.
  destruct (dist_rel R H1 H2) as [d Hd].
  exists d. intros x.
  specialize (Hd x).
  cunwrap. destruct Hd as [y_x Hyx]. destruct Hyx as (v_x & H3 & H4 & H5).
  cprove exists v_x. split; eauto.
  intros.
  etransitivity. 1:eapply H; eauto.
  lia.
Qed.

Lemma R_undecidable_strong :
  ~ decidable R.
Proof.
  intros Hdec.
  destruct (dist_again_strong (fun k x => |x| = k /\ R x)) as [d Hd].
  - exact unboundedR.
  - cbn. eapply decidable_enumerable. 2:eauto.
    eapply DecidabilityFacts.decidable_iff.
    eapply DecidabilityFacts.decidable_iff in Hdec. destruct Hdec.
    econstructor. intros (x, y).
    exact _.
  - eapply size_sublinear with (d := d).
    intros k.
    specialize (Hd k).
    unshelve cstart.  1:eapply le_dec. cunwrap.
    destruct Hd as (x_k & [H1 H2] & H3).
    rewrite <- H1 at 1.
    pose proof (C_weakly_total x_k) as Hk. cunwrap.
    destruct Hk as [C_u_k Hcuk].
    destruct Hcuk as ([? [-> H4]] & H5).
    cprove idtac.
    etransitivity. 1:{ eapply H2. eauto. }
    eapply H3. cbn. firstorder.
Qed.

End Kolmogorov.

Theorem Invariance Θ :
  (forall f, exists d, forall x, forall v_x, f x ▷ v_x -> exists y_x, Θ y_x ▷ v_x /\ | y_x| < |x| + d) ->
  forall Θ', exists d, forall x y, C Θ x y -> forall y', C Θ' x y' -> y < y' + d.
Proof.
  intros Hopt Θ'.
  destruct (Hopt Θ') as [d Hd].
  exists d.
  intros x ? ((y & -> & H) & Hleast) _ ((y' & -> & H2) & Hleast2).
  eapply Hd in H2 as [v_x [H1 H2]].
  eapply Nat.le_lt_trans with (2 := H2), Hleast. eauto.
Qed.

Axiom ϕ : nat -> nat ↛ nat.
Axiom EPF : forall f : nat -> nat ↛ nat,
    exists γ, forall i, ϕ (γ i) ≡{_} f i.

Theorem optimal_total Θ :
  (forall f, exists d, forall x, forall v_x, f x ▷ v_x -> exists y_x, Θ y_x ▷ v_x /\ | y_x| < |x| + d) ->
  forall x, exists y, Θ y ▷ x.
Proof.
  intros Hopt x.
  destruct (Hopt (@ret _ nat)) as [d Hd].
  specialize (Hd x x (ret_hasvalue x)) as [y [H1 _]].
  eauto.
Qed.

Module universal.

  Definition C_ u := the_least (fun x s => exists y, s = |y| /\ ϕ u y ▷ x).

  Definition universal u := forall c, exists x, forall y, ϕ c y ≡{_} (ϕ u ⟨x,y⟩).

  Section fix_u.

  Variable u : nat.
  Variable univ_u : universal u.

  Definition N (x : nat) :=
    exists y, ϕ u y ▷ x /\ |y| < |x|.

  Lemma optimal :
    ∀ f : nat ↛ nat, ∃ d : nat, ∀ x : nat, ∀ v_x : nat, f x ▷ v_x → ∃ y_x : nat, ϕ u y_x ▷ v_x ∧ | y_x | < | x | + d.
  Proof.
    intros f.
    specialize (EPF (fun _ => f)) as [γ H].
    destruct (univ_u (γ 0)) as [c Hc].
    exists (|c| + 1). intros x v_x Hvx.
    exists (⟨ c, x ⟩). split.
    + eapply Hc, H, Hvx.
    + autorewrite with length. lia.
  Qed.

  Lemma simple_N :
    simple N.
  Proof.
    eapply simple_N_strong, optimal.
  Qed.

  End fix_u.

  Definition strongly_universal u := forall c i, ϕ c i ≡{_} ϕ u ⟨c,i⟩.

  Module universal_ex.

    Definition info x := tonat (repeat true (|x|) ++ [false]).

    Definition invert x :=
      let l := ofnat x in
      if list.list_find (fun x => x = false) l is Some (n, _)
      then
        let l := skipn (n + 1) l in
        (tonat (firstn n l), tonat (skipn n l))
      else
        (0, 0).

    Hint Rewrite repeat_length : list.

    Lemma info_spec : forall x y, invert ⟨⟨info x, x⟩, y⟩ = (x, y).
    Proof.
      intros x y.
      unfold invert, info.
      autorewrite with length.
      erewrite list.list_find_app_l.
      2:{ eapply list.list_find_app_l.
          etransitivity.
          1:{ eapply list.list_find_app_r.
              eapply list.list_find_None.
              eapply Forall_forall.
              intros ? ? % repeat_spec. congruence.
          }
          cbn. destruct decide; try congruence.
          unfold prod_map. cbn.
          now rewrite repeat_length.
      }
      replace (|x| + 1) with (length (repeat true (|x|) ++ [false])) by now autorewrite with list.
      rewrite list.drop_app_le. 2: autorewrite with list; lia.
      rewrite list.drop_app, list.take_app, list.drop_app.
      now autorewrite with length.
    Qed.

    Lemma universal_ex :
      exists u, universal u.
    Proof.
      destruct (EPF (fun _ => fun ci => let '(c,i) := invert ci in ϕ c i)) as [γ Hγ].
      exists (γ 0). intros c. exists ⟨info c,c⟩. intros i.
      specialize (Hγ 0 ⟨⟨info c,c⟩,  i⟩). cbn in *.
      rewrite info_spec in Hγ. symmetry. eapply Hγ.
    Qed.

  End universal_ex.

  Variable invert : nat -> nat * nat.
  Variable invert_spec :     (forall x y, invert ⟨x, y⟩ = (x,y)).

  Lemma strongly_universal_universal u :
    strongly_universal u -> universal u.
  Proof.
    intros H c'. red in H. setoid_rewrite <- H. exists c'. reflexivity.
  Qed.

  Lemma strongly_universal_ex :
    exists u, strongly_universal u.
  Proof.
    destruct (EPF (fun _ => fun ci => let '(c,i) := invert ci in ϕ c i)) as [γ Hγ].
    exists (γ 0). intros c i.
    specialize (Hγ 0 ⟨c,i⟩). cbn in *.
    rewrite invert_spec in Hγ. symmetry. exact Hγ.
  Qed.

  Definition C := the_least (fun x s => exists c e, s = |c| + |e| /\ ϕ c e ▷ x).
  
  Lemma strongly_universal_equivalence u :
    strongly_universal u -> forall x y, C x y <-> C_ u x y.
  Proof.
    intros Huniv x y. rename u into c.  eapply the_least_pred_equiv.
    intros e. split.
    - intros (e' & i & -> & HH).
      eexists. eexists. 1:now rewrite <- size_pair.
      edestruct Huniv as [H _]. now eapply H.
    - intros (i & -> & Hn). exists (tonat nil), i.
      split. 1:now autorewrite with length.
      eapply Huniv. now autorewrite with length.
  Qed.

  Definition N_again x :=
    exists c e, ϕ c e ▷ x /\ |c| + |e| < |x|.

  Lemma strongly_universal_equivalence_N u :
    strongly_universal u -> forall x, N u x <-> N_again x.
  Proof.
    intros Huniv x. split.
    - intros (c & H1 & H2). exists (tonat nil), c. split; autorewrite with length.
      + eapply Huniv. now autorewrite with length.
      + eauto.
    - intros (c & e & H1 & H2).
      exists ⟨c,e⟩. split.
      + edestruct Huniv as [H _]. now eapply H.
      + now autorewrite with length.
  Qed.

End universal.

Module fixed_input.

  Variable input : nat.

  Definition C := the_least (fun x s => exists c, s = |c| /\ ϕ c input ▷ x).

  Lemma Θ_total x :
    exists c, ϕ c input ▷ x.
  Proof.
    destruct (EPF (fun _ _ => ret x)) as [γ H].
    exists (γ 0). eapply H, ret_hasvalue.
  Qed.

  Definition N (x : nat) :=
    exists c, ϕ c input ▷ x /\ |c| < |x|.

  Variable dist_part :
    forall f : nat ↛ nat, exists γ d, forall x, ϕ (γ x) input ≡{_} f x /\ (ter (f x) ->  |γ x| < |x| + d).

  Lemma simple_N : simple N.
  Proof.
    eapply simple_N_strong.
    intros f.
    destruct (dist_part f) as (γ & d & H). exists d.
    intros x. exists (γ x). firstorder.
  Qed.

End fixed_input.
