From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions Limit simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith.
Require Import Vectors.VectorDef Arith.Compare_dec Lia.
Import Vector.VectorNotations.

Local Notation vec := Vector.t.


(* ########################################################################## *)
(** * Low Simple Set *)
(* ########################################################################## *)

(** This file contains the definition of low simple set and proves the
essential property of low simple, i.e. Low simple as a solution to
Post's Problem in Turing degree. **)

  (* Definition of low *)
  Definition low (P: nat -> Prop) := P´ ⪯ᴛ K.


Section LowFacts.
  (* If the turing jump of A is low, then A is not reduciable to K *)

  Lemma lowness (P: nat -> Prop) :
    low P -> ~ K ⪯ᴛ P.
  Proof.
    intros H IH.
    eapply not_turing_red_J with (Q := P).
    eapply Turing_transitive; [apply H| easy].
  Qed.

  Lemma limit_jump_lowness (A: nat -> Prop) :
    LEM_Σ 1 ->
    definite K ->
    limit_computable (A´) -> ~ K ⪯ᴛ A.
  Proof.
    intros LEM defK H IH.
    apply lowness with (P := A); [|apply IH]. 
    (* specialize (limit_turing_red_K _ _ _ _ defK H). *)
  Admitted.

End LowFacts.


Section LowSimplePredicate.

Definition low_simple P := low P /\ simple P.

Definition sol_Post's_problem (P: nat -> Prop) :=
  (~ decidable P) /\ (enumerable P) /\ ~ (K ⪯ᴛ P).

Fact low_simple_correct:
  forall P, low_simple P -> sol_Post's_problem P.
Proof.
  intros P [H1 H2]; split; [now apply simple_undecidable|].
  split; [destruct H2 as [H2 _]; eauto| now apply lowness].
Qed.

End LowSimplePredicate.


Require Import List.
Import ListNotations.
Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Section StrongInduction.

  Definition strong_induction (p: nat -> Type) :
    (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
  Proof.
      intros H x; apply H.
      induction x; [intros; lia| ].
      intros; apply H; intros; apply IHx; lia.
  Defined.

End StrongInduction.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.

Require Import SyntheticComputability.Shared.FinitenessFacts.


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

Section Construction.

  Variable W_: nat -> nat -> nat -> Prop.
  Hypothesis W_spec: forall P, semi_decidable P -> exists c, forall x, P x <-> exists n, W_ c n x.

  Definition disj {X} (A: list X) (B: X -> Prop) := forall x, In x A -> B x -> False.
  Definition intersect {X} (A B: X -> Prop) := forall x, A x -> B x -> False.
  Notation "A # B" := (disj A B) (at level 30).

  Record Extension :=
  {
      extendP: list nat -> nat -> nat -> Prop;
      extend_dec: forall l x, (Σ y, extendP l x y) + (forall y, ~ extendP l x y);
      extend_uni: forall l x y1 y2, extendP l x y1 -> extendP l x y2 -> y1 = y2
  }.

  Inductive F_ (E: Extension) : nat -> list nat -> Prop :=
    | Base : F_ E O []
    | ExtendS n l a : F_ E n l -> extendP E l n a -> F_ E (S n) (a::l)
    | ExtendN n l   : F_ E n l -> (forall a, ~ extendP E l n a) -> F_ E (S n) l.

  Require Import Coq.Program.Equality.

  Lemma F_uni E : forall n l1 l2, F_ E n l1 -> F_ E n l2 -> l1 = l2 .
  Proof.
    intros n l1 l2.
    dependent induction n.
    - intros H1 H2. inv H1. now inv H2.
    - intros H1 H2. inv H1; inv H2.
      assert(l = l0) as -> by now apply IHn.
      f_equal. apply (extend_uni H3 H4).
      assert (l = l2) as -> by now apply IHn.
      exfalso. apply (H4 a H3).
      assert (l = l1) as -> by now apply IHn.
      exfalso. apply (H3 a H4).
      now apply IHn.
  Qed.

  Lemma F_mono E n m l1 l2: F_ E n l1 -> F_ E m l2 -> n <= m -> incl l1 l2.
  Proof.
      intros H1 H2 HE.
      revert H1 H2; induction HE in l2 |-*; intros H1 H2.
      - now assert (l1 = l2) as -> by (eapply F_uni; eauto).
      - inv H2; last now apply IHHE.
        specialize (IHHE l H1 H0). eauto.
  Qed.

  Lemma F_pop E n x l: F_ E n (x::l) -> exists m, F_ E m l.
  Proof.
    intros H. dependent induction H. 
    - now exists n.
    - eapply IHF_. eauto. easy.
  Qed.
  
  Lemma F_pick E n x l: F_ E n (x::l) -> exists m, F_ E m l /\ extendP E l m x.
  Proof.
    intros H. dependent induction H.
    - exists n; eauto.
    - eapply IHF_; eauto.
  Qed.

  Lemma F_computable E : Σ f: nat -> list nat, 
    forall n, F_ E n (f n) /\ length (f n) <= n.
  Proof.
    set (F := fix f x :=
           match x with
           | O => []
           | S x => match (extend_dec E) (f x) x with
                   | inr _ => f x
                   | inl aH => (projT1 aH) :: (f x)
                   end
           end).
    exists F. induction n; simpl.
    - split. constructor. easy.
    - destruct (extend_dec E (F n) n); split.
      + eapply ExtendS; first apply IHn. now destruct s.
      + cbn. destruct IHn. lia.
      + now eapply ExtendN.
      + destruct IHn. lia.  
  Qed.

  Definition F_func E := projT1 (F_computable E).
  Lemma F_func_correctness {E}: forall n, F_ E n (F_func E n).
  Proof.
    intros n; unfold F_func. 
    destruct (F_computable E) as [f H].
    now destruct (H n).
  Qed.

  Lemma F_func_correctness' {E}: forall n, length (F_func E n) <= n.
  Proof.
    intros n; unfold F_func. 
    destruct (F_computable E) as [f H].
    now destruct (H n).
  Qed.
  

  Definition F_with E x := exists l n, In x l /\ (F_ E n l).

  Lemma F_with_semi_decidable E: semi_decidable (F_with E).
  Proof.
    unfold semi_decidable, semi_decider.
    destruct (F_computable E) as [f Hf ].
    exists (fun x n => (Dec (In x (f n)))).
    intros x. split.
    - intros (l & n & Hxl & Hl).
      exists n. rewrite Dec_auto; first easy.
      destruct (Hf n) as [Hf' _].
      now rewrite (F_uni Hf' Hl).
    - intros (n & Hn%Dec_true).
      exists (f n), n; split; eauto.
      apply Hf.
  Qed.

Section SimpleSet.

  Notation unique p := (forall x x', p x -> p x' -> x = x').
  Definition safe p n := forall k, k < n -> ~ p k.
  Definition least p n := p n /\ safe p n.

  Definition W e x := exists n, W_ e n x.
  Notation " P ↾ s" := (fun x => exists n, n <= s /\ P n x) (at level 20).


  Definition ext_intersect_W L n e := L # (W_ e) ↾ n.
  Definition ext_has_wit L n e x := (W_ e ↾ n) x /\ 2 * e < x /\ ~ In x L.

  Definition ext_pick L n x e := ext_intersect_W L n e /\ least (ext_has_wit L n e) x.
  Definition ext_least_choice L n x := exists e, least (ext_pick L n x) e.

  (* Definition extend_simple l__n n x :=
    exists e, mu e (fun α => e < n /\ 
      (l__n # W_ α n) /\ 
        mu x (fun β => W_ α n β /\ 2 * α < β /\ ~ In β l__n)). *)

  (* Definition extend_simple' l__n n x :=
    exists e, search e (fun α => (l__n # W_ α n) /\ 
        search x (fun beta => W_ α n beta /\ 2 * α < beta) n) n. *)


  Variable hy1: forall (l : list nat) (x : nat), (Σ y : nat, ext_least_choice l x y) + (forall y : nat, ~ ext_least_choice l x y).
  Variable hy2: forall (l : list nat) (x y1 y2 : nat), ext_least_choice l x y1 -> ext_least_choice l x y2 -> y1 = y2.
  Definition simple_extendsion: Extension.
  Proof.
    unshelve econstructor.
    - exact ext_least_choice.
    - apply hy1.
    - apply hy2.
  Defined.

  (* Definition E_simple P__n n x :=
    exists e, 
      mu e (fun alpha => e < n /\ (W_ alpha n # P__n) /\ mu x (fun beta => W_ alpha n beta /\ 2 * alpha < beta)). *)

(*  Definition P_ := P_templete E_simple. *)
  Definition P_ := F_ simple_extendsion.
  Definition Pf_ := F_func simple_extendsion.
  Definition P := F_with simple_extendsion.

  Definition R_simple_list L e := (~ exhaustible (W e)) -> ~ (L # (W e)).

  Definition attention e n := exists x, least (ext_pick (Pf_ n) n x) e.
  Definition active e n := ~ (Pf_ n) # ((W_ e) ↾ n).


  Lemma W_incl e n m: 
    n <= m -> forall x,  (W_ e ↾ n) x -> (W_ e ↾ m) x.
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
    intros [x H] Hcontr.
    apply (Hcontr x).
    assert (P_ (S k) (Pf_ (S k))) by apply F_func_correctness.
    inv H0. cbn in H4. assert (ext_least_choice l k x).
    exists e. assert (Pf_ k = l) as <-.
    eapply F_uni. apply F_func_correctness. apply H3.
    apply H. assert (x = a) as ->.
    eapply (@extend_uni simple_extendsion); cbn; eauto. eauto.
    exfalso. eapply H3. cbn.
    exists e. enough ((Pf_ k) = (Pf_ (S k))) as <- by apply H.
    assert (F_ simple_extendsion k (Pf_ k)) by apply F_func_correctness.
    eapply F_uni; eauto.
    firstorder.
  Qed.

  Lemma active_not_attention e k: active e k -> ~ attention e k.
  Proof.
    now intros H [x [[Hx _] _]].
  Qed.

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

  Definition spec (e x: nat) := exists k, attention e k /\ ext_least_choice (Pf_ k) k x.

  Lemma spec_uni e x1 x2: spec e x1 -> spec e x2 -> x1 = x2 .
  Proof.
    intros [k [Ht Hk]] [k' [Ht' Hk']].
    assert (k=k') as <-. eapply attention_uni; eauto.
    eapply (@extend_uni simple_extendsion); cbn; eauto.
  Qed.

  Lemma P_meet_spec x n : P x /\ x <= 2*n -> exists e, spec e x /\ e < n.
  Proof.
    intros [[L [k [Hin Hk]]] Hn].
    dependent induction L. inv Hin.
    destruct (Dec (a = x)) as [->|].
    - clear IHL Hin.
      destruct (F_pick Hk) as [k' [Hk' [e He]]].
      exists e. split. unfold spec. 
      exists k'. split; unfold attention.
      + exists x. enough (Pf_ k' = L) as -> by eauto.
        eapply F_uni. apply F_func_correctness. easy.
      + exists e. enough (Pf_ k' = L) as -> by eauto.
        eapply F_uni. apply F_func_correctness. easy.
      + destruct He. destruct H. destruct H1. destruct H1.
        lia.
    - destruct (F_pop Hk) as [m' Hm']. 
      eapply (IHL m'); eauto. firstorder. 
  Qed.

  Lemma P_extract_spec n L:
    (forall x, In x L -> P x /\ x <= 2 * n) -> 
    forall x, In x L -> exists c, spec c x /\ c < n.
  Proof.
    intros. induction L. inv H0. 
    destruct H0 as [-> | Hln]; last apply IHL; eauto.
    apply P_meet_spec. now apply H.
  Qed.

  Lemma DomC_pullback_list n L:
    NoDup L -> (forall x, In x L -> P x /\ x <= 2 * n) -> 
      exists (LC: list nat), NoDup LC /\ length LC = length L /\
        forall c, In c LC -> exists x, spec c x /\ In x L /\ c < n.
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
    intros ND [LC H] % DomC_pullback_list; intuition.
    rewrite <- H.
    assert (incl LC (seq 0 n)). unfold incl. 
    - intros c [e [x Hx]] % H2. apply in_seq. lia.
    - apply pigeonhole_length in H1.
      + now rewrite seq_length in H1.
      + intros. decide (x1 = x2); tauto.
      + exact H0.
  Qed.

  Definition R_simple P e := (~ exhaustible (W e)) -> ~ (intersect (W e) P).

  Lemma R_simple_acc e L:
    R_simple_list L e -> forall L', incl L L' -> R_simple_list L' e .
  Proof.
    intros H L' HL' h1 h2.
    apply H; first easy.
    firstorder.
  Qed.

  Lemma list_accu e:
    (forall k, k < e -> exists L, R_simple_list L k /\ exists n, F_ simple_extendsion n L) ->
    exists m L, F_ simple_extendsion m L /\ forall n, n < e -> R_simple_list L n.
  Proof.
    intros. induction e. 
    { exists 0, []; split; first econstructor. intros n Hn. lia. }
    destruct (H e) as [L [HL1 HL2]]; first lia.
    destruct IHe as [m [HL' [Hm HL2']]].
    { intros n Hn. apply H. lia. }
    destruct HL2 as [k Hk]. destruct (dec_le m k).
    + exists k, L; split; eauto.
      intros n Hn. assert (n = e \/ n < e) as [->|H'] by lia.
      apply HL1. eapply R_simple_acc. apply HL2'; first easy.
      eapply F_mono; eauto.
    + exists m, HL'; split; eauto.
      intros n Hn.  assert (n = e \/ n < e) as [->|H'] by lia.
      eapply R_simple_acc. apply HL1. eapply F_mono; eauto with lia.
      now eapply HL2'.
  Qed.


  Lemma eventually_attention e m L: 
    ~ exhaustible (W e) -> 
    (forall n : nat, n < e -> ~ exhaustible (W n) -> ~ L # W n -> F_ simple_extendsion m L) -> 
    exists k, attention e k.
  Proof.
    intros H1 H2.
    unfold attention. 
    
  Admitted.

  Hypothesis O_O: LEM.

  Lemma try2:
    forall e, exists L, R_simple_list L e /\ exists m, F_ simple_extendsion m L.
  Proof.
    strong induction e. apply list_accu in H.
    destruct H as (m & L & HL & HL').
    destruct (O_O (exhaustible (W e))).
    - exists []. split. intros H'; eauto.
      exists 0; econstructor.
    - unfold R_simple_list in HL'.
Admitted.

  Lemma P_meet_R_simple : forall e, R_simple P e.
  Proof.
    intros e.
    destruct (try2 e) as [L [H1 [m H]]].
    unfold R_simple. intros H3.
    intros Hin. destruct (H1 H3).
    intros x Hx Hx'.
    apply (Hin x Hx').
    unfold P. unfold F_with.
    exists L, m. now split.
  Qed.

  Lemma P_semi_decidable : semi_decidable P.
  Proof.
    apply F_with_semi_decidable.
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

  Lemma ComplP_Listing:
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
    intros n H. eapply ComplP_Listing with (n := n).
    intros (l & ? & ? & H2).
    eapply H.
    exists (firstn n l).
    repeat split.
    - rewrite firstn_length. lia.
    - now eapply firstn_NoDup.
    - intros ? ? % firstn_In. now eapply H2.
    Qed.

  Lemma P_simple : simple P.
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
      rewrite <- HWq in HWcx. apply (Hq x HWcx HPx).
  Qed.

  End SimpleSet.

End Construction.
