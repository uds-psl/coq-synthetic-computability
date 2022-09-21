From SyntheticComputability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts.
From SyntheticComputability.Shared Require Import Dec.
Require Import PeanoNat Nat Lia.
Require Import List.

Require Import Equations.Prop.Subterm Equations.Prop.DepElim.
From Equations Require Import Equations.

Notation In1 x L := (In x (map fst L)).
Notation In2 y L := (In y (map snd L)).

Lemma map_NoDup {X Y} (f : X -> Y) l : (forall x1 x2, f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj Hl. induction Hl; cbn; econstructor; eauto.
  now intros (? & <- % Hinj & ?) % in_map_iff.
Qed.

Definition injective {X Y} (f : X -> Y) :=
  forall x1 x2, f x1 = f x2 -> x1 = x2.

Lemma In_compute {X Y} f {eX : eq_dec X} (x : X) L : In x (map f L) -> {y : Y| In y L /\ f y = x}.
Proof.
  induction L as [ | y L IH] in x |- *.
  - inversion 1.
  - cbn. intros H.
    destruct (eX (f y) x) as [He | He].
    + exists y. eauto.
    + destruct (IH x) as (y' & IHy').
      firstorder. exists y'. firstorder.
Qed.

Lemma In1_compute {X Y} {eX : eq_dec X} (x : X) L : In1 x L -> {y : Y| In (x,y) L}.
Proof.
  intros ([] & ? & ?) % In_compute; cbn in *; subst; eauto.
Qed.

Lemma In2_compute {X Y} {eY : eq_dec Y} (y : Y) L : In2 y L -> {x : X| In (x,y) L}.
Proof.
  intros ([] & ? & ?) % In_compute; cbn in *; subst; eauto.
Qed.

Definition correspondence {X} {Y} (C : list (X * Y)) :=
  NoDup (map fst C) /\ NoDup (map snd C).

Definition correspondence' {X} {Y} (C : list (X * Y)) :=
    (forall x y1 y2, In (x,y1) C -> In (x,y2) C -> y1 = y2) /\
    (forall x1 x2 y, In (x1,y) C -> In (x2,y) C -> x1 = x2).

Lemma correspondence_to {X} {Y} (C : list (X * Y)) :
  correspondence C -> correspondence' C.
Proof.
  induction C as [ | [x y] C IH].
  - firstorder.
  - intros [H1 H2]. inv H1. inv H2.
    split; intros ? ? ? [ [= -> ->] | ] [ [=] | ]; eauto.
    all: firstorder; subst.
    all: exfalso.
    1-2: eapply H3. 3-4: eapply H1.
    all: eapply in_map_iff; eexists (_, _); cbn; eauto.
Qed.

Lemma eq_dec_pair {X} {Y} : eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  intros. exact _.
Qed.

Lemma correspondence_swap {X Y} (C : list (X * Y)) :
  correspondence C -> correspondence (map (fun '(x,y) => (y,x)) C).
Proof.
  intros (H2 & H3).
  induction C as [ | [x y] C IHC]; cbn.
  - repeat econstructor.
  - inv H2. inv H3.
    split; cbn; repeat econstructor; cbn in *.
    2, 4: firstorder.
    intros ([] & ? & ([] & ? & ?) % in_map_iff) % in_map_iff; cbn in *; subst; firstorder.
    inv H0. eapply H2.
    eapply in_map_iff. exists (x0, y). cbn. firstorder.
    intros ([] & ? & ([] & ? & ?) % in_map_iff) % in_map_iff; cbn in *; subst; firstorder.
    inv H0. eapply H1.
    eapply in_map_iff. exists (x, y0). cbn. firstorder.
Qed.

Lemma NoDup_remove {X} (eX : eq_dec X) x L :
  NoDup L -> NoDup (remove eX x L).
Proof.
  induction 1; cbn.
  - econstructor.
  - destruct eX; cbn; eauto.
    econstructor; firstorder.
    intros ? % in_remove. firstorder.
Qed.

Lemma NoDup_map_remove {X Y} (eX : eq_dec X) (eY : eq_dec Y) x L (f : X -> Y) :
  NoDup (map f L) -> NoDup (map f (remove eX x L)).
Proof.
  induction L; cbn.
  - eauto.
  - inversion 1; subst. destruct eX; cbn; eauto.
    econstructor; firstorder.
    intros (? & ? & ? % in_remove) % in_map_iff.
    firstorder.
    eapply H2. eapply in_map_iff. eauto.
Qed.

Lemma correspondence_remove {X Y} {eX : eq_dec X} `{eY: eq_dec Y} C x y :
  correspondence C ->
  correspondence (remove (eq_dec_pair eX eY) (x,y) C).
Proof.
  intros HC. split.
  all: eapply NoDup_map_remove; eauto.
  all: eapply HC.
Qed.

Section fixes.

  Variables (X Y : Type).

  Variable f : X -> Y.
  Hypothesis inj_f : injective f.

  Variable eX : eq_dec X.
  Variable eY : eq_dec Y.

  Fixpoint php (l1 : list Y) (l2 : list Y) : option Y :=
    match l1 with
    | x :: l1 => if in_dec eY x l2 is left H then php l1 (remove eY x l2) else Some x
    | nil => None
    end.

  Lemma php_spec l1 l2 :
    NoDup l1 -> length l1 > length l2 ->
    exists x, php l1 l2 = Some x /\ In x l1 /\ ~ In x l2.
  Proof.
    induction 1 in l2 |- *; intros Hlen; cbn in *.
    - lia.
    - destruct (in_dec eY x l2) as [Hi | Hni].
      2: firstorder.
      destruct (IHNoDup (remove eY x l2)) as (x0 & H1 & H2 & H3).
      + eapply Nat.lt_le_trans. eapply remove_length_lt. 1: eauto. lia.
      + exists x0. firstorder. intros Hx0.
        eapply H3. eapply in_in_remove. 2: eauto.
        congruence.
  Qed.
  
  Definition find C x := if php (f x :: map (fun '(x', y) => f x') C) (map snd C) is
                              Some y then y else f x.

  Definition find_spec C (x : X) :
    correspondence C -> 
     ~ In1 x C -> 
    correspondence ((x, find C x) :: C).
  Proof.
    intros HC Hx. split.
    - cbn. econstructor; eauto.
      eapply HC.
    - cbn. econstructor; eauto. 2: eapply HC.
      unfold find.
      destruct (php_spec (f x :: map (fun '(x', _) => f x') C) (map snd C)) as (y' & E & H1 & H2).
      * econstructor. rewrite in_map_iff. intros ([] & -> % inj_f & ?).
        eapply Hx. eapply in_map_iff. firstorder.
        erewrite map_ext.
        erewrite <- map_map with (f := fst) (g := f).
        eapply map_NoDup; firstorder.
        now intros [].
      * cbn. rewrite !map_length. lia.
      * rewrite E. eauto.
  Qed.

  Definition extendX C x := if x is Some x then
    if in_dec eX x (map fst C) then C else (x, (find C x)) :: C else C.

  Lemma extendX_spec C x :
    correspondence C -> correspondence (extendX C x) /\ (forall z, In z C -> In z (extendX C x)) /\
    if x is Some x' then In x' (map fst (extendX C x)) else True.
  Proof.
    intros HC.
    destruct x as [x | ]. 2: eauto. cbn.
    destruct in_dec; cbn. 
    - eauto.
    - split.
      + eapply find_spec; eauto. 
      + split; eauto.
  Qed.

End fixes.

Section fixes2.

  Variables (X Y : Set).

  Variable f : X -> Y.
  Hypothesis inj_f : injective f.

  Variables (IX : _) (RX : _) (HX : retraction IX RX X nat) (HRX : forall x n, RX n = Some x -> n = IX x).
  Variables (IY : _) (RY : _) (HY : retraction IY RY Y nat) (HRY : forall y n, RY n = Some y -> n = IY y).
  
  Variable g : Y -> X.
  Hypothesis inj_g : injective g.
  
  Variable dX : eq_dec X.
  Variable dY : eq_dec Y.
  
  Definition extendY (C : list (X * Y)) y := 
    map (fun '(x,y) => (y,x)) (extendX Y X g dY dX (map (fun '(x,y) => (y,x)) C) y).
  
  Lemma extendY_spec C y :
    correspondence C -> correspondence (extendY C y) /\ (forall z, In z C -> In z (extendY C y)) /\
    if y is Some y' then In y' (map snd (extendY C y)) else True.
  Proof.
    intros HC. split. 2:split.
    - eapply correspondence_swap, extendX_spec; eauto.
      eapply correspondence_swap. eauto.
    - intros [x y']. intros H. unfold extendY.
      eapply in_map_iff. exists (y', x). split; eauto.
      eapply extendX_spec; eauto. now eapply correspondence_swap.
      eapply in_map_iff. exists (x, y'); eauto.
    - eapply correspondence_swap in HC. unshelve eapply (extendX_spec Y X) in HC; eauto.
      destruct HC as (_ & _ & HC). unfold extendY.
      destruct y; eauto.
      eapply in_map_iff in HC as ([] & <- & ?).
      eapply in_map_iff. eexists (_, _). split. cbn. eauto.
      eapply in_map_iff. eexists (_, _). split. eauto. cbn - [extendX].
      eapply H.
  Qed.
  
  Notation extendX C x := (extendX X Y f dX dY C x).

  Fixpoint build_corr n :=
    match n with
    | 0 => nil
    | S n => extendY (extendX (build_corr n) (RX n)) (RY n)
    end.

  Lemma build_corr_corr (n : nat) : correspondence (build_corr n).
  Proof.
    induction n.
    - cbv. clear. repeat econstructor.
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
      unshelve epose proof (extendX_spec _ _ _ _ _ _ (build_corr (IX x)) (Some x)) as (_ & _ & H); eauto.    
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
  
  Lemma f'_g' y :
    f' (g' y) = y.
  Proof.
    unfold g', f'. destruct In1_compute, In2_compute; cbn -[build_corr] in *.
    assert (S (IY y) <= S (IX x0) \/ S (IX x0) <= S (IY y)) as [H | H] by lia.
    all: eapply build_corr_mono in H; eauto.
    all: eapply (@correspondence_to X Y).
    1,4: eapply build_corr_corr. all: eauto.
  Qed.
  
  Lemma g'_f' x :
    g' (f' x) = x.
  Proof.
    unfold g', f'. destruct In1_compute, In2_compute; cbn -[build_corr] in *.
    rename x0 into y0.
    assert (S (IX x) <= S (IY y0) \/ S (IY y0) <= S (IX x)) as [H | H] by lia.
    all: eapply build_corr_mono in H; eauto.
    all: eapply (@correspondence_to X Y).
    eapply build_corr_corr. all: eauto.
  Qed.

End fixes2.

Corollary Computational_Cantor_Bernstein :
  forall X : Set, discrete X -> enumerableᵗ X ->
             forall Y : Set, discrete Y -> enumerableᵗ Y ->
                        forall f : X -> Y, (forall x1 x2, f x1 = f x2 -> x1 = x2) ->
                                     forall g : Y -> X, (forall y1 y2, g y1 = g y2 -> y1 = y2) ->
                                                  exists (f' : X -> Y) (g' : Y -> X), forall x y, f' (g' y) = y /\ g' (f' x) = x.
Proof.
  intros X [dX HdX] [eX HeX] Y [dY HdY] [eY HeY] f f_inj g g_inj.
  assert (inhabited (eq_dec X)) as [eq_dec_X]  by (eapply discrete_iff; firstorder).
  assert (inhabited (eq_dec Y)) as [eq_dec_Y]  by (eapply discrete_iff; firstorder).
  destruct (enumerator_retraction _ _ _ HdX HeX) as [IX HIX].
  destruct (enumerator_retraction _ _ _ HdY HeY) as [IY HIY].
  eexists _, _. repeat eapply conj.
  - intros. split.
    + unshelve eapply f'_g' with (f := f) (g := g); eauto.
    + eapply g'_f'.
Qed.
