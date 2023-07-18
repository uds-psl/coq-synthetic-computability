From SyntheticComputability Require Import Definitions.
From SyntheticComputability Require Import mu_nat partial equiv_on.

From SyntheticComputability Require Import simple principles EnumerabilityFacts.

Require Import Nat Arith Lia.

Notation least' p n k := (n <= k /\ p k /\ forall i, n <= i -> p i -> k <= i)%nat.

Section WO.

  Variable p : nat -> Prop.

  (* Guardedness predicate *)
  Inductive G (n: nat) : Prop :=
  | GI : (~ p n -> G (S n)) -> G n.

  Lemma G_sig n :
    G n -> ~~ exists k, least' (fun k => p k) n k.
  Proof.
    induction 1 as [n _ IH].
    intros G.
    assert (~~ (p n \/ ~ p n)) as H by tauto. apply H. clear H. intros [H | H].
    - apply G. exists n. repeat split; eauto.
    - apply (IH H). intros (k & Hle & Hk & Hleast'). apply G.
      exists k. repeat split.
      + lia.
      + exact Hk.
      + intros i Hi. inversion Hi.
        * congruence.
        * eapply Hleast'; eauto. lia.
  Defined.

  Lemma G_zero n :
    G n -> G 0.
  Proof.
    induction n as [|n IH].
    - intros H. exact H.
    - intros H. apply IH. constructor. intros _. exact H.
  Defined.

  Theorem mu_nat :
    (exists n, p n) -> ~~ exists n, least' p 0 n.
  Proof.
    intros H. apply (G_sig 0).
    destruct H as [n H].  
    apply (G_zero n).
    constructor. tauto.
  Defined.

End WO.

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
  intros [H2 H3] H1. eapply H1 in H2. split. exact H2. intros y'. rewrite <- H1. apply H3.
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
  assert (exists x, Q x) as H by eauto. clear x H2. eapply mu_nat in H.
  intros G. apply H. intros (x & H1 & H2 & H3).  apply G.
  exists x. split. auto. intros. eapply H3. 1:lia. auto.
Qed.

Lemma the_least_ex (P : nat -> Prop) :
  (exists n, P n) -> ~~ exists n, the_least_pred P n.
Proof.
  intros H % mu_nat.
  intros G. apply H. intros (n & H1 & H2 & H3).
  apply G. exists n. split; auto with arith.
Qed.

Record FunRel X Y := {
  the_rel :> X -> Y -> Prop ;
  is_fun : (forall x y1 y2, the_rel x y1 -> the_rel x y2 -> y1 = y2) (* ; *)
  (* is_wtotal : (forall x, ~~ exists y, the_rel x y) *) }.

Definition on_value {X Y} (R : FunRel X Y) (P : Y -> Prop) x :=
  forall y, R x y -> P y.

Definition on_value' {X Y} (R : FunRel X Y) (P : Y -> Prop) x :=
  exists y, R x y /\ P y.

Lemma on_value_iff1 {X Y} (R : FunRel X Y) (P : Y -> Prop) x :
  on_value' R P x -> on_value R P x.
Proof.
  intros (y & H1 & H2) y' H.
  now rewrite <- (is_fun _ _ R _ _ _ H1 H).
Qed.

Definition total {X Y} (R : X -> Y -> Prop) :=
  forall x, exists y, R x y.

Lemma on_value_iff2 {X Y} (R : FunRel X Y) (P : Y -> Prop) x :
  total R ->
  on_value R P x -> on_value' R P x.
Proof.
  intros Htot H.
  destruct (Htot x) as [y Hy].
  exists y. split; [ assumption | ].
  eapply (H _ Hy).
Qed.

Definition weakly_total {X Y} (R : X -> Y -> Prop) :=
  forall x, ~~ exists y, R x y.

Lemma on_value_iff2' {X Y} (R : FunRel X Y) (P : Y -> Prop) x :
  weakly_total R ->
  on_value R P x -> ~~ on_value' R P x.
Proof.
  intros Htot H G.
  apply (Htot x); intros [y Hy].
  apply G.
  exists y. split; [ assumption | ].
  eapply (H _ Hy).
Qed.

Lemma on_value_imp {X Y} {P Q : Y -> Prop} R (x : X) :
  on_value R P x -> (forall y, P y -> Q y) -> on_value R Q x.
Proof.
  intros H1 H y Hy. apply H, H1, Hy.
Qed.

Lemma on_value_neg {X Y} {P : Y -> Prop} R (x : X) :
  ~ on_value R P x -> on_value R (fun y => ~ P y) x.
Proof.
  intros H y Hy G; cbn in *. apply H. intros y' Hy'. cbn in *.
  enough (y = y') as -> by assumption. eapply R; eauto.
Qed.

Program Definition the_least {X} (R : X -> nat -> Prop) : FunRel X nat :=
  {|
  the_rel x := the_least_pred (R x) ;
  is_fun := fun x y1 y2 H1 H2 => the_least_pred_unique H1 H2
  |}.

Axiom tonat : list bool -> nat.
Axiom ofnat : nat -> list bool.

Axiom ofnat_tonat : forall l, ofnat (tonat l) = l.
Axiom tonat_ofnat : forall n, tonat (ofnat n) = n.
Axiom length_log : forall n, length (ofnat n) <= Nat.log2 n.
Axiom length_mono : forall x y, x <= y -> length (ofnat x) <= length (ofnat y).

#[export] Hint Rewrite ofnat_tonat tonat_ofnat : length.
#[export] Hint Rewrite List.app_length : length.

Notation "| n |" := (length (ofnat n)) (at level 10).

Notation "⟨ x , y ⟩" := (tonat (ofnat x ++ ofnat y)) (at level 0).

Lemma length_pair x y : | ⟨x,y⟩ | = |x| + |y|.
Proof.
  now autorewrite with length.
Qed.

Lemma length_sublinear d : ~ forall n, n <= |n| + d.
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

Axiom Part : partiality.
#[export] Existing Instance Part.
Axiom ϕ : nat -> nat ↛ nat.

Notation "x ▷ y" := (@hasvalue Part nat x y) (at level 50).
Definition C := the_least (fun x s => exists c y, s = |c| + |y| /\ ϕ c y ▷ x).

#[export] Instance equiv_part {A} : equiv_on (part A) := {| equiv_rel := @partial.equiv _ A |}.

Definition universal u := forall c, exists x, forall y, ϕ c y ≡{_} (ϕ u ⟨x,y⟩).

Definition C_ u := the_least (fun x s => exists y, s = |y| /\ ϕ u y ▷ x).

Definition strongly_universal u := forall c i, ϕ c i ≡{_} ϕ u ⟨c,i⟩.

Lemma strongly_universal_universal u :
  strongly_universal u -> universal u.
Proof.
  intros H c'. red in H. setoid_rewrite <- H. exists c'. reflexivity.
Qed.

#[export] Hint Rewrite List.app_nil_l @list.nil_length : length.

Set Default Goal Selector "!".

Lemma strongly_universal_equivalence u :
  strongly_universal u -> forall x y, C x y <-> C_ u x y.
Proof.
  intros Huniv x y. rename u into c.  eapply the_least_pred_equiv. 
  intros e. split.
  - intros (e' & i & -> & HH).
    eexists. eexists. 1:now rewrite <- length_pair.
    red in Huniv. unfold equiv_part in Huniv.
    do 2 red in Huniv. now  rewrite <- Huniv.
  - intros (i & -> & Hn). exists (tonat nil), i.
    split. 1:now autorewrite with length. 
    eapply Huniv. now autorewrite with length.
Qed.

Axiom EPF : forall f : nat -> nat ↛ nat,
    exists γ, forall i, ϕ (γ i) ≡{_} f i.

Lemma EPF_univ_tot {u} : universal u ->
                     forall f : nat -> nat, exists c, forall x, ϕ u ⟨c,x⟩ ▷ f x.
Proof.
  intros Hu f.
  specialize (EPF (fun _ x => ret (f x))) as [γ H].
  destruct (Hu (γ 0)) as [c Hc].
  exists c. intros. cbn in * |-. red in H, Hc.
  rewrite <- Hc, H. eapply ret_hasvalue.
Qed.

Lemma EPF_univ {u} : universal u ->
                     forall f : nat ↛ nat, exists c, forall x, ϕ u ⟨c,x⟩ ≡{_} f x.
Proof.
  intros Hu f.
  specialize (EPF (fun _ => f)) as [γ H].
  destruct (Hu (γ 0)) as [c Hc].
  exists c. intros.
  rewrite <- Hc. eapply H.
Qed.

Lemma C_weakly_total u x :
  universal u -> ~~ exists y, C_ u x y.
Proof.
  intros Hu. eapply the_least_ex.
  destruct (EPF_univ_tot Hu (fun _ => x)) as [c Hc % fun H => H 0].
  eauto. 
Qed.

Theorem Invariance u :
  universal u -> forall u', exists d,
  forall x y, C_ u x y -> forall y', C_ u' x y' -> y <= y' + d.
Proof.
  intros Hu u'.
  destruct (Hu u') as [d Hd]. exists (|d|).
  intros x ? ((y & -> & H) & Hleast) _ ((y' & -> & H2) & Hleast2).
  eapply Hd in H2.
  rewrite Hleast. 2: eauto.
  rewrite length_pair. lia.
Qed.

Axiom u : nat.
Axiom univ_u : universal u.

Definition N (x : nat) :=
  exists y, ϕ u y ▷ x /\ |y| < |x|.

Definition R (x : nat) :=
  forall y, ϕ u y ▷ x -> |y| >= |x|.

Lemma R_neg_N x :
  R x <-> ~ N x.
Proof.
  split.
  - intros H (y & H1 % H & H2). lia.
  - intros H y H1.
    assert (|y| >= |x| \/ |y| < |x|) as [ Ha | Ha ] by lia; [ auto | ].
    destruct H. exists y. eauto.
Qed.

Lemma MP_choice (R : nat -> nat -> Prop) : MP -> enumerable (fun '(x,y) => R x y) ->
  (forall x, ~~ exists y, R x y) -> exists f, forall x, R x (f x).
Proof.
  intros.
  eapply enumerable_AC; eauto.
  intros x. eapply MP_to_MP_semidecidable in H.
  red in H. eapply H with (p := fun x => exists n, R x n).
  - eapply SemiDecidabilityFacts.semi_decidable_ex.
    eapply SemiDecidabilityFacts.enumerable_semi_decidable; eauto.
    eapply ReducibilityFacts.enumerable_red.
    4: exact H0. all:eauto.
    exists (fun '(x,y) => (y, x)). intros []. firstorder.
  - eauto.
Qed.

Lemma enum_to:
  forall q : nat -> Prop, enumerable q -> enumerable (fun '(x, y) => x < | y | /\ q y).
Proof.
  intros q [f Hf].
  exists (fun nx => let (n, x) := embed_nat.unembed nx in if f n is Some y then if x <? |y| then Some (x, y) else None else None).
  intros (x, y). cbn -[Nat.ltb]. split.
  - intros [H1 [n H2] % Hf]. exists (embed_nat.embed (n, x)).
    rewrite embed_nat.embedP, H2.
    destruct (Nat.ltb_spec x (|y|)).
    + reflexivity.
    + lia.
  - intros (nx & H).
    destruct (embed_nat.unembed nx) as [n x'].
    destruct (f n) as [y'|] eqn:E; inversion H.
    destruct (Nat.ltb_spec x' (|y'|)); inversion H; subst.
    firstorder.
Qed.

Lemma par_enum_ϕ :
  enumerable (fun '(x, y) => ϕ u y ▷ x).
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

From SyntheticComputability Require Import FinitenessFacts.
From stdpp Require Import base.
Require Import List.

Lemma list_max_spec L x :
  In x L -> x <= list_max L.
Proof.
  induction L.
  - firstorder.
  - intros [-> | ]; cbn.
    + lia.
    + eapply IHL in H. unfold list_max in H. lia.
Qed.

From SyntheticComputability Require Import Pigeonhole.

From SyntheticComputability Require Import Dec.

Lemma non_finite_unbounded_fun (p : nat -> Prop) f :
  (forall n, exists L, forall x, f x <= n -> In x L) ->
  ~ exhaustible p -> forall x, ~~ exists y : nat, f y >= x /\ p y.
Proof.
  intros Hsur Hfin n. rewrite non_finite_spec in Hfin.
  2: intros; destruct (Nat.eq_decidable x1 x2); tauto.

  destruct (Hsur n) as [L HL].
  specialize (Hfin L).
  cunwrap. destruct Hfin as (y & H1 & H2).
  cprove exists y. split; [|eauto].
  unshelve cstart. 1:eapply le_dec.
  intros H. apply H2, HL. lia.
Qed.

Lemma unbounded_non_finite_fun (p : nat -> Prop) (f : nat -> nat) :
  (forall k, ~~ exists x, f x >= k /\ p x) -> ~ exhaustible p.
Proof.
  intros Hfin. eapply non_finite_nat.
  intros n H.
  pose (N := 1 + list_max (map f (seq 0 n))).
  eapply (Hfin N).
  intros (x & H1 & H2).
  apply H. eexists; split. 2: eauto.
  assert (x < n \/ x >= n) as [ | ] by lia; try lia.
  enough (f x > f x) by lia. subst N.
  unfold gt. unfold ge in H1.
  eapply Nat.lt_le_trans. 2: eauto. red. cbn.
  rewrite <- Nat.succ_le_mono.
  eapply list_max_spec.
  eapply in_map_iff. exists x. split; eauto.
  eapply in_seq. lia.
Qed.

Lemma NoDup_app {X} (l1 l2 : list X) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ (In x l2)) -> NoDup (l1 ++ l2).
Proof.
  induction 1 in l2 |- *.
  - eauto.
  - intros Hl2 Hel. cbn. econstructor. 2:eapply IHNoDup; eauto.
    + intros [ | ] % in_app_iff; firstorder.
    + firstorder.
Qed.

Lemma NoDup_map {X Y} (f : X -> Y) l :
  Inj (=) (=) f -> NoDup l -> NoDup (map f l).
Proof.
  induction 2; cbn; econstructor.
  1:intros (? & ? % H & ?) % in_map_iff.
  all: firstorder congruence.
Qed.

Lemma bitlist_for_k k :
  exists l : list (list bool), (forall x, In x l <-> length x = k) /\ NoDup l /\ length l = 2 ^ k.
Proof.
  induction k.
  - exists (nil :: nil). split; [ | split ].
    + cbn. intros []; cbn in *; firstorder congruence.
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
    + eapply NoDup_app; try eapply NoDup_map; eauto.
      intros ? (? & <- & ?) % in_map_iff (? & ? & ?) % in_map_iff.
      congruence.
    + rewrite app_length, !map_length, IH3. cbn. lia.
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
  - eapply NoDup_map; auto. intros ? ? E % (f_equal ofnat).
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

Lemma at_most k : k > 0 ->
  forall l, (forall x, In x l -> | x | < k) -> NoDup l -> length l <= 2^ k - 1.
Proof.
  intros Hk l H1 H2. unfold lt in H1.
  destruct k.
  - lia.
  - setoid_rewrite <- Nat.succ_le_mono in H1.
    destruct (list_for_le_k k) as (l2 & H3 & H4 & H5).
    assert (length l <= length l2). {
      eapply NoDup_incl_length; firstorder.
    }
    enough (length l2 <= 2 ^ (S k) - 1) by lia.
    rewrite H5. lia.
Qed.

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
  eapply (functional_NoDup (fun x y => ϕ u y ▷ x ∧ | y | < | x |)) in H2 as (l' & H4 & H5).
  - assert (Forall (fun y => |y| < k) l'). {
      eapply list.Forall2_Forall_r; eauto.
      cbn. eapply Forall_forall.
      intros ? ? % H1. lia.
    } 
    assert (length l' = 2 ^ k). { erewrite <- list.Forall2_length; eauto. }
    destruct k.
    + cbn in *. destruct H0.  1:inversion H2. cbn in *. lia.
    + unshelve epose proof (@at_most (S k) _ l' _ _).
      * lia.
      * eapply Forall_forall. eauto.
      * eauto.
      * rewrite H2 in H6.
        enough (2 ^ S k > S k) by lia.
        eapply Nat.pow_gt_lin_r. lia.
  - intros x1 x2 y [Hx1 Hx11] [Hx2 Hx22]. eapply hasvalue_det; eauto.
  - intros x (y & ? & ?) % H1 % H. eauto.
Qed.

Lemma unboundedR :
  forall k, ~~ exists x, | x | = k /\ R x.
Proof.
  setoid_rewrite R_neg_N. intros k G.
  assert (forall x, |x| = k -> ~~ N x) by firstorder. clear G.
  pose proof (nonrandom_k k).
  pose proof (list_for_k k) as (l & H1 & H2 & H3).
  setoid_rewrite <- H1 in H.
  setoid_rewrite <- H1 in H0. clear - H H0.
  induction l.
  - eapply H0. firstorder.
  - eapply H.
    + now left.
    + intros Ha. eapply IHl.
      * intros HH. eapply H0. intros. inversion H1 as [-> | ]; eauto.
      * firstorder.
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
  setoid_rewrite R_neg_N in G.
  assert (forall x, |x| = k -> ~~ N x).
  { intros x Hx GG. apply G. exists x. split. 1:lia. assumption. }
  clear G.

  eapply classical_finite in H.
  1:cstart; cunwrap; intros _; now eapply (nonrandom_k k).
  destruct (list_for_k k) as (L & H1 & _ & _).
  firstorder.
Qed.

Lemma dist f :
  exists d, forall x, exists y_x, ϕ u y_x ▷ f x /\ | y_x| < |x| + d.
Proof.
  destruct (EPF_univ_tot univ_u f) as [c Hc].
  exists (|c| + 1). intros x.
  exists (⟨ c, x ⟩). split. 1: eauto.
  autorewrite with length. lia.
Qed.

Lemma subset :
  MP -> forall q : nat -> Prop, (forall x, q x -> R x) -> enumerable q -> ~ exhaustible q -> False.
Proof.
  intros mp q H1 H2 H3.
  unshelve epose proof (MP_choice _ mp _ (non_finite_length _ H3)) as [f Hf].
  1: now eapply enum_to.
  assert (forall k y, ϕ u y ▷ f k -> |f k| <= |y|). {
    intros. destruct (Hf k) as [Hk1 Hk2]. 
    eapply H1; eauto.
  }
  destruct (dist f) as [d Hd].
  eapply (length_sublinear d). intros k.
  transitivity (|f k|). 1:eapply Nat.lt_le_incl, Hf.
  destruct (Hd k) as (y_k & Hk1 & Hk2).
  transitivity (|y_k|). 1: eauto.
  lia.
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

Lemma dist_strong R :
  weakly_total R -> enumerable (fun '(x,y) => R x y) ->
  exists d, forall x, exists y_x, ~~ exists v_x, R x v_x /\ ϕ u y_x ▷ v_x /\ | y_x| < |x| + d.
Proof.
  intros Htot [f Hf] % get_partial_choice.
  destruct (EPF_univ univ_u f) as [c Hc].
  exists (|c| + 1). intros x.
  exists (⟨ c, x ⟩).
  specialize (Htot x). cunwrap. destruct Htot as [v_x' Hvx].
  pose proof (Hvx' := Hvx).
  eapply Hf in Hvx as [v_x Hvx].
  cprove exists v_x.
  repeat split.
  - eapply Hf. eauto.
  - eapply Hc. eauto.
  - autorewrite with length. lia.
Qed.

Lemma subset_strong :
  forall q : nat -> Prop, (forall x, q x -> R x) -> enumerable q -> ~ exhaustible q -> False.
Proof.
  intros q H1 H2 H3.
  destruct (dist_strong (fun k x => k < |x| /\ q x)) as [d Hd].
  - exact (non_finite_length _ H3).
  - now eapply enum_to.
  - eapply (length_sublinear d). intros k.
    destruct (Hd k) as [y_k H].
    unshelve cstart. 1:eapply le_dec.
    cunwrap. destruct H as (x_k & [H4 H5] & H6 & H7).
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
  forall f : nat -> nat, exists d, forall x y, C_ u (f x) y -> y <= |x| + d.
Proof.
  intros f.
  destruct (dist f) as [d Hd]. exists d.
  intros x y H. destruct (Hd x) as (y_x & H1 & H2).
  etransitivity.
  - eapply H; eauto.
  - lia.
Qed.

Lemma R_undecidable :
  MP -> ~ decidable R.
Proof.
  intros mp Hdec.
  unshelve epose proof (MP_choice _ mp _ unboundedR) as [g Hg].
  - cbn. eapply decidable_enumerable. 2:eauto.
    eapply DecidabilityFacts.decidable_iff.
    rewrite DecidabilityFacts.decidable_iff in Hdec. destruct Hdec.
    econstructor. intros (x, y).
    exact _.
  - destruct (dist_again g) as [d].
    eapply length_sublinear with (d := d).
    intros k.
    unshelve cstart.  1:eapply le_dec.
    pose proof (C_weakly_total u (g k) univ_u) as Hk. cunwrap.
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
  exists d, forall x, ~~ exists v_x, R x v_x /\ forall y, C_ u (v_x) y -> y <= |x| + d.
Proof.
  intros H1 H2.
  destruct (dist_strong R H1 H2) as [d Hd].
  exists d. intros x.
  destruct (Hd x) as [y_x Hyx].
  cunwrap. destruct Hyx as (v_x & H3 & H4 & H5).
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
    rewrite DecidabilityFacts.decidable_iff in Hdec. destruct Hdec.
    econstructor. intros (x, y).
    exact _.
  - eapply length_sublinear with (d := d).
    intros k.
    specialize (Hd k).
    unshelve cstart.  1:eapply le_dec. cunwrap.
    destruct Hd as (x_k & [H1 H2] & H3).
    rewrite <- H1 at 1.
    pose proof (C_weakly_total u x_k univ_u) as Hk. cunwrap.
    destruct Hk as [C_u_k Hcuk].
    destruct Hcuk as ([? [-> H4]] & H5).
    cprove idtac.
    etransitivity. 1:{ eapply H2. eauto. }
    eapply H3. cbn. firstorder.
Qed.
