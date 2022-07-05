From stdpp Require Import prelude.
Require Import ssreflect.

From SyntheticComputability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts.
From SyntheticComputability.Shared Require Import Dec ListAutomation.
From SyntheticComputability.Synthetic Require Import reductions.

Require Import Equations.Prop.Subterm Equations.Prop.DepElim.
From Equations Require Import Equations.
    
Notation In1 x L := (In x (map fst L)).
Notation In2 y L := (In y (map snd L)).

Lemma In1_compute {X Y} {eX : eq_dec X} (x : X) L : In1 x L -> {y : Y| In (x,y) L}.
Proof.
  induction L as [ | [x' y] L IH] in x |- *.
  - inversion 1.
  - cbn. destruct (eX x' x) as [-> | He].
    + exists y. eauto.
    + intros H. destruct (IH x) as (y' & IHy').
      firstorder. exists y'. eauto.
Qed.

Lemma In2_compute {X Y} {eY : eq_dec Y} (y : Y) L : In2 y L -> {x : X| In (x,y) L}.
Proof.
  induction L as [ | [x y'] L IH] in y |- *.
  - inversion 1.
  - cbn. destruct (eY y' y) as [-> | He].
    + exists x. eauto.
    + intros H. destruct (IH y) as (x' & IHx').
      firstorder. exists x'. eauto.
Qed.

Definition correspondence {X} {Y} (p : X -> Prop) (q : Y -> Prop ) (C : list (X * Y)) :=
    (forall x y, In (x,y) C -> p x <-> q y) /\
    (forall x y1 y2, In (x,y1) C -> In (x,y2) C -> y1 = y2) /\
    (forall x1 x2 y, In (x1,y) C -> In (x2,y) C -> x1 = x2).

Lemma eq_dec_pair {X} {Y} : eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  intros. exact _.
Qed.
      
Lemma correspondence_swap {X Y} (p : X -> Prop) (q : Y -> Prop) C :
  correspondence p q C -> correspondence q p (map (fun '(x,y) => (y,x)) C).
Proof.
  intros (H1 & H2 & H3).
  split. 2:split.
  - intros ? ? ([] & [=] & ?) % in_map_iff; subst. symmetry. eapply H1; eauto.
  - intros ? ? ? ([] & [=] & ?) % in_map_iff ([] & [=] & ?) % in_map_iff; subst.
    eapply H3; eauto.
  - intros ? ? ? ([] & [=] & ?) % in_map_iff ([] & [=] & ?) % in_map_iff; subst.
    eapply H2; eauto.
Qed.

Lemma correspondence_remove {X Y} {eX : eq_dec X} `{eY: eq_dec Y} C x y p q :
  correspondence p q C ->
  correspondence p q (remove (eq_dec_pair eX eY) (x,y) C).
Proof.
  intros HC. split. 2: split.
  - intros ? ? [] % in_remove. now eapply HC.
  - intros ? ? ? [] % in_remove [] % in_remove.
    eapply HC; eauto.
  - intros ? ? ? [] % in_remove [] % in_remove.
    eapply HC; eauto.
Qed.

  
Section fixes.
  
  Variables (X Y : Type).
  
  Variable p : X -> Prop.
  Variable q : Y -> Prop.
  
  Variable f : X -> Y.
  Hypothesis inj_f : Inj (=) (=) f.
  Hypothesis f_red : reduces_o f p q.
  (* 
  Variable g : Y -> X.
  Hypothesis inj_g : Inj (=) (=) g.
  Hypothesis g_red : reduces_o g q p. *)
    
  Variable eX : eq_dec X.
  Variable eY : eq_dec Y.
  
  (* Unset Equations With Funext. *)

  (* Ltac Subterm.unfold_FixWf ::= *)
  (*   match goal with *)
  (*     |- context [ @FixWf ?A ?R ?WF ?P ?f ?x ] => *)
  (*     let step := fresh in *)
  (*     set(step := fun y (_ : R y x) => @FixWf A R WF P f y) in *; *)
  (*     unshelve erewrite (@FixWf_unfold_step A R WF P f x _ step); *)
  (*     [red; intros; simp_sigmas (* Extensionality proof *) *)
  (*     |hidebody step; DepElim.red_eq_lhs (* Unfold the functional *) *)
  (*     |reflexivity] *)
  (*   end. *)

  Equations γ (C : list (X * Y)) : X -> X by wf (length C) lt := 
    γ C x with Dec (In2 (f x) C) => {
      | left H with In2_compute _ _ H => {
          | exist _ x' H_ :=  γ (remove (eq_dec_pair eX eY) (x', f x) C) x'
          };
      | right _ := x
    }.
  Next Obligation.
    abstract (apply remove_length_lt; eauto).
  Qed.

  Arguments remove {_ _} _ _.
  
  Lemma γ_spec (C : list (X * Y)) x : 
    ~ In1 x C -> correspondence p q C ->
    (p x <-> p (γ C x)) /\ In (γ C x) (x :: map fst C) /\ ~ In2 (f (γ C x)) C.
  Proof.
    funelim (γ C x); try rename H0 into IH.
    - intros Hx HC. rewrite <- Heqcall. eauto.
    - intros Hx HC.
      specialize (IH ) as (IH1 & IH2 & IH3).
      { intros ([] & E & [] % in_remove) % in_map_iff; cbn in E; subst.
        apply H1. f_equal. eapply HC; eauto. }
      { eapply correspondence_remove; eauto. }
      split. 2:split.
      + etransitivity. eapply f_red.
        rewrite <- Heqcall. 
        rewrite <- IH1. symmetry. now eapply HC.
      + rewrite <- Heqcall.  specialize IH2 as [EE | ([] & E & [] % in_remove) % in_map_iff]; eauto.
        rewrite <- EE. right. eapply in_map_iff. eexists (_, _). eauto.
      + rewrite Heqcall in IH3, IH2, IH1 |- *.
        intros ([] & E & ?) % (in_map_iff). cbn in E. subst.
        eapply IH3. eapply in_map_iff.
        eexists (x0, _). split. cbn. reflexivity.
        eapply in_in_remove. 2:exact H0.
        intros [= -> E % inj_f]. apply Hx.
        rewrite E in IH2. 
        specialize IH2 as [-> | ([] & EE & [] % in_remove) % in_map_iff]; cbn in *; subst; eauto.
        * eapply in_map_iff. eexists (_, _). eauto.
        * eapply in_map_iff. eexists (_, _). eauto.
  Qed.
  
  Definition find C x := f (γ C x).
  
  Definition find_spec C (x : X) :
    correspondence p q C -> 
     ~ In1 x C -> 
    correspondence p q ((x, find C x) :: C).
  Proof.
    intros HC Hx. split. 2:split.
    - intros ? ? [[= <- <-] | ].
      + etransitivity. eapply γ_spec; eauto. eapply f_red.
      + now eapply HC.
    - intros ? ? ? [[= <- <-] | ] [[= <-] | ]; eauto. 3: eapply HC; eauto.
      + exfalso. apply Hx. eapply in_map_iff. eexists (_,_). eauto.
      + exfalso. apply Hx. eapply in_map_iff. eexists (_,_). eauto.
    - intros ? ? ? [[= <- <-] | ] [[= <-] | ]; eauto. 3: eapply HC; eauto.
      + exfalso. eapply γ_spec; eauto. eapply in_map_iff. eexists (_,_). eauto.
      + subst. exfalso. eapply γ_spec; eauto. eapply in_map_iff. eexists (_,_). eauto.
  Qed.
  
  Definition extendX C x := if x is Some x then 
    if Dec (In x (map fst C)) then C else (x, (find C x)) :: C else C.
  
  Lemma extendX_spec C x :
    correspondence p q C -> correspondence p q (extendX C x) /\ (forall z, In z C -> In z (extendX C x)) /\
    if x is Some x' then In x' (map fst (extendX C x)) else True.
  Proof.
    intros HC.
    destruct x as [x | ]. 2: eauto. cbn.
    decide (In x (map fst C)); cbn.
    - eauto.
    - split.
      + eapply find_spec; eauto. 
      + split; eauto.
  Qed.
  
End fixes.
  
Section fixes2.
  
  Variables (X Y : Set).
  
  Variable p : X -> Prop.
  Variable q : Y -> Prop.
  
  Variable f : X -> Y.
  Hypothesis inj_f : Inj (=) (=) f.
  Hypothesis f_red : reduces_o f p q.
  
  Variables (IX : _) (RX : _) (HX : retraction IX RX X nat) (HRX : forall x n, RX n = Some x -> n = IX x).
  Variables (IY : _) (RY : _) (HY : retraction IY RY Y nat) (HRY : forall y n, RY n = Some y -> n = IY y).
  
  Variable g : Y -> X.
  Hypothesis inj_g : Inj (=) (=) g.
  Hypothesis g_red : reduces_o g q p.
  
  Variable dX : eq_dec X.
  Variable dY : eq_dec Y.
  
  Definition extendY (C : list (X * Y)) y := 
    map (fun '(x,y) => (y,x)) (extendX Y X g dY dX (map (fun '(x,y) => (y,x)) C) y).
  
  Lemma extendY_spec C y :
    correspondence p q C -> correspondence p q (extendY C y) /\ (forall z, In z C -> In z (extendY C y)) /\
    if y is Some y' then In y' (map snd (extendY C y)) else True.
  Proof.
    intros HC. split. 2:split.
    - eapply correspondence_swap, extendX_spec; eauto.
      eapply correspondence_swap. eauto.
    - intros [x y']. intros H. unfold extendY.
      eapply in_map_iff. exists (y', x). split; eauto.
      eapply extendX_spec; eauto. now eapply correspondence_swap.
      eapply in_map_iff. exists (x, y'); eauto.
    - eapply correspondence_swap in HC. unshelve eapply (extendX_spec Y X q p) in HC; eauto.
      destruct HC as (_ & _ & HC). unfold extendY.
      destruct y; eauto.
      eapply in_map_iff in HC as ([] & <- & ?).
      eapply in_map_iff. eexists (_, _). split. eauto.
      eapply in_map_iff. eexists (_, _). split. eauto. cbn - [extendX].
      eapply H.
  Qed.
  
  Notation extendX C x := (extendX X Y f dX dY C x).
  
  Fixpoint build_corr n :=
    match n with
    | 0 => []
    | S n => extendY (extendX (build_corr n) (RX n)) (RY n)
    end.
  
  Lemma build_corr_corr (n : nat) : correspondence p q (build_corr n).
  Proof.
    induction n.
    - cbv. clear. firstorder lia.
    - cbn.
      eapply extendY_spec.
      eapply extendX_spec; eauto.
  Qed.
  
  Hint Resolve build_corr_corr : core.
  
  Lemma build_corr_mono n m z : In z (build_corr n) -> n <= m -> In z (build_corr m).
  Proof.
    induction 2.
    - eauto.
    - cbn. eapply extendY_spec; eauto.
      eapply extendX_spec; try eapply  build_corr_corr; eauto.
      eapply extendX_spec; eauto.
  Qed.
  
  Lemma build_corrX x n : IX x < n -> In x (map fst (build_corr n)).
  Proof.
    induction n; intros Hx; try lia.
    assert (IX x = n \/ IX x < n) as [<- | H % IHn] by lia.
    - cbn. rewrite HX.
      unshelve epose proof (extendX_spec _ _ _ _ _ _ _ _ _ (build_corr (IX x)) (Some x)) as (_ & _ & H); eauto.    
      eapply in_map_iff in H as ([] & E & ?); cbn in E; subst.
      eapply extendY_spec in H.
      eapply in_map_iff. exists (x,y). eauto. eapply extendX_spec; eauto.
    - eapply in_map_iff in H as ([] & E & ?); cbn in E; subst.
      eapply in_map_iff. exists (x,y). split. eauto. 
      eapply build_corr_mono; eauto.
  Qed.
  
  Lemma build_corrY y n : IY y < n -> In y (map snd (build_corr n)).
  Proof.
    induction n; intros Hy; try lia.
    assert (IY y = n \/ IY y < n) as [<- | H % IHn] by lia.
    - cbn. rewrite HY.
      unshelve epose proof (extendY_spec (extendX (build_corr (IY y)) (RX (IY y))) (Some y)) as (_ & _ & H); eauto.
      eapply extendX_spec; eauto.
    - eapply in_map_iff in H as ([] & E & ?); cbn in E; subst.
      eapply in_map_iff. exists (x,y). split. eauto. 
      eapply build_corr_mono; eauto.
  Qed.
  
  Definition f' x := proj1_sig (In1_compute _ _ (build_corrX x (S (IX x)) ltac:(abstract lia))).
  Definition g' y := proj1_sig (In2_compute _ _ (build_corrY y (S (IY y)) ltac:(abstract lia))).
  
  Lemma f'_red : reduces_m f' p q.
  Proof.
    intros x. unfold f'. destruct In1_compute. cbn.
    now apply build_corr_corr in i.
  Qed.
  
  Lemma g'_red : reduces_m g' q p.
  Proof.
    intros y. unfold g'. destruct In2_compute. cbn.
    now apply build_corr_corr in i.
  Qed.
  
  Lemma f'_g' y :
    f' (g' y) = y.
  Proof.
    unfold g', f'. destruct In1_compute, In2_compute; cbn -[build_corr] in *.
    assert (S (IY y) <= S (IX x0) \/ S (IX x0) <= S (IY y)) as [H | H] by lia.
    - eapply build_corr_mono in H; eauto. eapply build_corr_corr; eauto.
    - eapply build_corr_mono in H; eauto. eapply build_corr_corr; eauto.
  Qed.
  
  Lemma g'_f' x :
    g' (f' x) = x.
  Proof.
    unfold g', f'. destruct In1_compute, In2_compute; cbn -[build_corr] in *.
    rename x0 into y0.
    assert (S (IX x) <= S (IY y0) \/ S (IY y0) <= S (IX x)) as [H | H] by lia.
    - eapply build_corr_mono in H; eauto. eapply build_corr_corr; eauto.
    - eapply build_corr_mono in H; eauto. eapply build_corr_corr; eauto.
  Qed.
  
End fixes2.

Print Assumptions g'_f'.