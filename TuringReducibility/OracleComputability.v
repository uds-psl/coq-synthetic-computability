From SyntheticComputability Require Import partial.
From stdpp Require Import list.
Import PartialTactics.

Lemma list_find_repeat_not {Y} P D x n :
  ~ P x ->
  @list_find Y P D (repeat x n) = None.
Proof.
  induction n; cbn.
  - reflexivity.
  - intros. destruct (decide (P x)); try tauto. now rewrite IHn.
Qed.

Lemma ex_iff_forall {X} (P1 P2 : X -> Prop) :
  (forall x, P1 x <-> P2 x) ->
  (exists x, P1 x) <-> (exists x, P2 x).
Proof.
  firstorder; do 2 eexists; eapply H; eauto.
Qed.

Section part.

Context {Part : partiality}.

(** ** Extensional dialogue trees *)

Definition tree  (Q A O : Type) := (list A) ↛ (Q + O).

Notation Ask q := (inl q).
Notation Output o := (inr o).

Inductive interrogation {Q A O} (τ : (list A) ↛ (Q + O)) (f : Q -> A -> Prop) : list Q -> list A -> Prop :=
| NoQuestions : interrogation τ f [] []
| Interrogate qs ans q a : interrogation τ f qs ans ->
                           τ ans =! inl q ->
                           f q a ->
                           interrogation τ f (qs ++ [q]) (ans ++ [a]).

(** ** Oracle Functionals and Turing Reducibility *)

Definition FunRel := True.
Definition Rel A B := A -> B -> Prop.

Definition Functional Q A I O := (Q -> A -> Prop) -> (I -> O -> Prop).

Definition OracleComputable {Q A I O} (r : (Q -> A -> Prop) -> I -> O -> Prop) :=
  exists τ : I -> tree Q A O, forall R x o, r R x o <-> exists qs ans, interrogation (τ x) R qs ans /\ τ x ans =! Output o.

Definition char_rel {X} (p : X -> Prop) : Rel X bool :=
  fun x b => if (b : bool) then p x else ~ p x.

Lemma char_rel_functional {X} (p : X -> Prop) :
  functional (char_rel p).
Proof.
  intros ? [] [] ? ?; firstorder congruence.
Qed.

Definition red_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :=
  exists r : Functional Y bool X bool, OracleComputable r /\ forall x b, char_rel p x b <-> r (char_rel q) x b.

(** ** Lemmas about extensional dialogue trees  *)

Lemma interrogation_length  {Q A O : Type} {tau f qs ans} :
  @interrogation Q A O tau f qs ans -> length qs = length ans.
Proof.
  induction 1; try reflexivity. now rewrite !app_length, IHinterrogation.
Qed.

Lemma interrogation_app_iff {Q A O} q1 q2 a1 a2 (τ : tree Q A O) f :
  (interrogation τ f q1 a1 /\ interrogation (fun l => τ (a1 ++ l)) f q2 a2) <->
    length q2 = length a2 /\ interrogation τ f (q1 ++ q2) (a1 ++ a2).
Proof.
  induction q2 in a1, q1, a2, τ |- * using rev_ind; cbn; split.
  - intros [H1 H2]. inversion H2; subst.
    + rewrite !app_nil_r. split; eauto.
    + destruct qs; cbn in *; congruence.
  - intros [Hlen H]. destruct a2; cbn in *; try lia.
    split. rewrite !app_nil_r in *; eauto. econstructor.
  - intros [H1 H2]. inversion H2. { destruct q2; cbn in *; congruence. }
    subst. eapply app_inj_2 in H. 2: cbn; lia.
    destruct H. subst. inversion H5. subst. clear H5.
    split. { rewrite !app_length. eapply interrogation_length in H0. cbn; lia. }
    rewrite !app_assoc. econstructor; eauto.
    edestruct IHq2 as [IH _].
    apply IH. split; eauto. 
  - rewrite app_length. intros [Hlen H].
    destruct a2 using rev_ind.
    + cbn in *; lia.
    + clear IHa2. rewrite app_length in *. cbn in *.
      rewrite app_assoc in *. inversion H.
      * destruct q1, q2; cbn in *; congruence.
      * eapply app_inj_2 in H0. 2: cbn; lia.
        rewrite app_assoc in H1.
        eapply app_inj_2 in H1. 2: cbn; lia.
        destruct H0, H1. subst. inversion H5; subst; clear H5.
        inversion H6; subst; clear H6.
        edestruct IHq2 as [_ IH].
        unshelve epose proof (IH _).
        2:{ split. eapply H0. econstructor. eapply H0. all: eauto. }
        split. lia. eauto.
Qed.

Lemma interrogation_ext {Q A O} τ τ' (f f' : Rel Q A) q a :
  (forall l v, τ l =! v <-> τ' l =! v) ->
  (forall q_ a, In q_ q -> f q_ a <-> f' q_ a) ->
  interrogation τ f q a <-> @interrogation Q A O τ' f' q a.
Proof.
  enough (forall τ τ' (f f' : Rel Q A) q a,
             (forall l v, τ l =! v <-> τ' l =! v) ->
             (forall q_ a, In q_ q -> f q_ a <-> f' q_ a) ->
             interrogation τ f q a -> @interrogation Q A O τ' f' q a).
  { split; eapply H; firstorder. }
  clear. intros ? ? ? ? ? ? Heq ?.
  induction 1; econstructor; eauto.
  - eapply IHinterrogation. intros. eapply H. rewrite in_app_iff. firstorder.
  - eapply Heq; eauto.
  - eapply H. rewrite in_app_iff; firstorder. firstorder.
Qed.

Lemma interrogation_det {A Q O} qs1 ans1 qs2 ans2 τ f :
  functional f ->
  @interrogation Q A O τ f qs1 ans1 ->
  interrogation τ f qs2 ans2 ->
  length qs1 <= length qs2 ->
  prefix qs1 qs2 /\ prefix ans1 ans2.
Proof.
  intros Hfun.
  revert τ ans1 qs2 ans2. induction qs1; intros τ ans1 qs2 ans2 Hi1 Hi2 Hlen.
  - inversion Hi1; subst.
    split; eapply prefix_nil.
    destruct qs; cbn in *; congruence.
  - destruct ans1.
    + inversion Hi1. destruct ans; cbn in *; congruence.
    + epose proof (interrogation_app_iff [a] qs1 [a0] ans1).
      cbn in H. edestruct H as [_ [H1 H2]]. clear H.
      * split; eauto. eapply interrogation_length in Hi1; cbn in *; lia.
      * inversion H1; subst. assert (qs = nil /\ ans = nil) as [-> ->]. { eapply (f_equal length) in H0, H3. rewrite app_length in *; cbn in *. destruct qs, ans; cbn in *; try lia. eauto. }
        cbn in *. inversion H0; subst. inversion H3; subst.
        destruct qs2.
        -- inversion Hi2; cbn in *; lia.
        -- destruct ans2. inversion Hi2; cbn in *; try congruence. destruct ans; cbn in *; congruence.
           clear H.
           epose proof (interrogation_app_iff [q] qs2 [a1] ans2) as H.
           cbn in H. edestruct H as [_ [H1' H2']]. clear H.
           ++ split; eauto. eapply interrogation_length in Hi2; cbn in *; lia.
           ++ inversion H1'; subst. assert (qs = nil /\ ans = nil) as [-> ->]. { eapply (f_equal length) in H7, H8. rewrite app_length in *; cbn in *. destruct qs, ans; cbn in *; try lia. eauto. }
              cbn in *. inversion H7; subst. inversion H8; subst.
              assert (inl (B := O) a = inl q) as [= ->]. eapply hasvalue_det; eauto.
              assert (a1 = a0) as ->. eapply Hfun; eauto.
              split; eapply prefix_cons; eapply IHqs1; eauto.
              lia. lia.
Qed.

Lemma interrogation_app_inv {Q A O} q1 q2 a1 a2 (τ : tree Q A O) f :
  interrogation τ f (q1 ++ q2) (a1 ++ a2) ->
  length q2 = length a2 ->
  interrogation τ f q1 a1 /\ interrogation (fun l => τ (a1 ++ l)) f q2 a2.
Proof.
  intros.
  eapply interrogation_app_iff; firstorder.
Qed.

Lemma interrogation_output_det_le :
  ∀ A O (X Y : Type) (τ : X → tree Y A O) (R :  Y -> A -> Prop) (x : X) (y1 y2 : O) (qs1 : list Y) (ans1 : list A),
    functional R ->
    interrogation (τ x) R qs1 ans1
    → τ x (ans1) =! Output y1
    → ∀ (qs2 : list Y) (ans2 : list A), interrogation (τ x) R qs2 ans2 → τ x (ans2) =! Output y2 → length qs1 ≤ length qs2 → y1 = y2.
Proof.
  intros A O X Y τ R x y1 y2 qs1 ans1 Hfun H1 H2 qs2 ans2 H1' H2' l.
  eapply interrogation_det in l; eauto.
  destruct l as [[qs3 ->] [ans3 ->]].
  eapply interrogation_app_inv in H1' as [].
  + destruct qs3.
    -- inversion H0; subst.
       rewrite !app_nil_r in *.
       eapply hasvalue_det in H2. 2:{ eassumption. } congruence.
       destruct qs; cbn in *; congruence.
    -- destruct ans3.
       inversion H0; subst.
       destruct ans; cbn in *; congruence.
       eapply (interrogation_app_inv [y] qs3 [a] ans3) in H0 as [].
       2:{ eapply interrogation_length in H0. cbn in *; lia. }
       cbn in *. inversion H0.
       assert (qs = nil /\ ans = nil) as [-> ->]. { eapply (f_equal length) in H4, H5. rewrite app_length in *; cbn in *. destruct qs, ans; cbn in *; try lia. eauto. }
       cbn in *. inversion H4. inversion H5. subst.
       rewrite app_nil_r in *.
       eapply hasvalue_det in H2. 2: eauto. congruence.
  + eapply interrogation_length in H1, H1'. rewrite !app_length in *. lia.
Qed.

Lemma interrogation_output_det :
  ∀ A O (X Y : Type) (τ : X → tree Y A O) (R :  Y -> A -> Prop) (x : X) (y1 y2 : O) (qs1 : list Y) (ans1 : list A),
    functional R ->
    interrogation (τ x) R qs1 ans1
    → τ x (ans1) =! Output y1
    → ∀ (qs2 : list Y) (ans2 : list A), interrogation (τ x) R qs2 ans2 → τ x (ans2) =! Output y2 → y1 = y2.
Proof.
  intros.
  assert (length qs1 <= length qs2 \/ length qs2 <= length qs1) as [Hlen | Hlen] by lia.
  - eapply interrogation_output_det_le. eauto. exact H0. eauto. exact H2. eauto. lia.
  - symmetry. eapply interrogation_output_det_le. eauto. exact H2. eauto. exact H0. eauto. lia.
Qed.

Lemma OracleComputable_ext Q A I O F F' :
  @OracleComputable Q A I O F ->
  (forall R i o, F R i o <-> F' R i o) ->
  @OracleComputable Q A I O F'.
Proof.
  intros [tau H] He. exists tau.
  intros. now rewrite <- H, He.
Qed.

Lemma OracleComputable_extensional {Q A I O F} {R R' : Rel Q A} :
  @OracleComputable Q A I O F ->
  (forall q a, R q a <-> R' q a) ->
  forall i o, F R i o <-> F R' i o.
Proof.
  intros [tau H] He.
  intros. rewrite !H.
  eapply ex_iff_forall. intros qs. eapply ex_iff_forall. intros ans.
  erewrite interrogation_ext. reflexivity. reflexivity. firstorder.
Qed.

Lemma OracleComputable_functional {Q A I O F} {R : Rel Q A} :
  @OracleComputable Q A I O F ->
  functional R -> functional (F R).
Proof.
  intros [tau H] Hfun i o1 o2 (qs1 & ans1 & Hint1 & Hend1) % H (qs2 & ans2 & Hint2 & Hend2) % H.
  eapply interrogation_output_det.
  3,5: eauto. all: eauto.
Qed.

Definition modulus_continuous {Q A I O} (F : Rel Q A -> Rel I O) :=
  forall (R : Rel Q A) (i : I) (o : O), F R i o -> exists L, (forall i', In i' L -> exists o', R i' o') /\ (forall R' : Rel Q A, (forall i' o' , In i' L -> R i' o' -> R' i' o') -> F R' i o).

Lemma cont_to_cont {P : partiality} {Q A I O} (F : Rel Q A -> Rel I O) :
  OracleComputable F -> modulus_continuous F.
Proof.
  intros [τ H] R i v Hv.
  eapply H in Hv.
  setoid_rewrite H. clear - Hv.
  destruct Hv as (qs & ans & H1 & H2).
  exists qs. split.
  - clear - H1. induction H1; cbn; intros.
    + tauto.
    + rewrite in_app_iff in H2.
      destruct H2; firstorder.
      subst. eauto.
  - intros. exists qs, ans. split; eauto.
    clear - H1 H. induction H1; econstructor; firstorder.
    all: setoid_rewrite in_app_iff in H.
    all: firstorder.
Qed.

(** *** Interrogations with accumulator argument E  *)

Definition etree E Q A O := E -> list A ↛ (E * Q + O).

Inductive einterrogation {E Q A O} (τ : etree E Q A O) (f : Q -> A -> Prop) : list Q -> list A -> E -> E -> Prop :=
| eNoQuestions e : einterrogation τ f [] [] e e
| einterrogate qs ans q a e1 e1' e2 : einterrogation τ f qs ans e1 e1' ->
                                      τ e1' ans =! inl (e2, q) ->
                                      f q a ->
                                      einterrogation τ f (qs ++ [q]) (ans ++ [a]) e1 e2.

Definition eOracleComputable {Q A I O} (r : Rel Q A -> I -> O -> Prop) :=
  exists E, exists e : E, exists τ : I -> etree E Q A O, forall R x o, r R x o <-> exists qs ans e', einterrogation (τ x) R qs ans e e' /\ τ x e' ans =! Output o.

Fixpoint alles {E Q A O} (τ : etree E Q A O) e (acc : list A) (l : list A) : part (E * Q + O) :=
  match l with
    [] => τ e acc
  | a :: l =>  bind (τ e acc) (fun q => match q with inl (e'', q) => alles τ e'' (acc ++ [a]) l | inr o => ret (inr o) end)
  end.

Lemma unzip_nil_e_ {E A Q O} (tau : etree E A Q O) acc (es : list E) ans x e e' :
  (forall k e e' a, nth_error es k = Some e ->
               nth_error es (S k) = Some e' ->
               nth_error (acc ++ ans) k = Some a ->
               exists q, tau e (take k (acc ++ ans)) =! (inl (e', q))) ->
  length es = 1 + length acc + length ans ->
  nth_error es (length acc) = Some e ->
  nth_error es (length acc + length ans) = Some e' ->
  alles tau e acc ans =! x <-> tau e' (acc ++ ans) =! x.
Proof.
  intros Hacc Hlen Hbeg Hend.
  induction ans in acc, Hacc, Hlen, Hbeg, Hend, e, e' |- *; cbn.
  - rewrite app_nil_r.  cbn in *.
    rewrite <- plus_n_O in Hend. firstorder congruence.
  - replace (acc ++ a ::  ans) with ((acc ++ [a]) ++ ans).
    2:{ now rewrite <- !app_assoc. }
    assert (exists e', nth_error es (S (length acc)) = Some e') as (eend & Heend).
    { destruct (nth_error es (S (length acc))) eqn:Eq; eauto.
      eapply nth_error_None in Eq.
      pose proof (nth_error_Some  es (length acc + length (a :: ans))) as [HH _].
      unshelve epose proof (HH _). rewrite Hend. congruence.
      cbn in H. lia.
    }
    rewrite <- IHans.
    3:{ cbn in *. rewrite !app_length in *. cbn in *. lia. }
    + epose proof (Hacc (length acc) e _ a) as (q & HH).
      4:{
        rewrite bind_hasvalue_given.
        2: rewrite take_app in HH.
        2: eapply HH. cbn. reflexivity. }
      eauto.
      2:{ rewrite nth_error_app2. 2: lia.
          now rewrite minus_diag. }
      eauto.
    + intros. cbn in Hacc.
      rewrite <- app_assoc in H1 |- *. cbn. eapply Hacc; eauto.
    + rewrite app_length. cbn. rewrite <- Heend. f_equal. lia.
    + rewrite app_length in *; cbn in *. rewrite <- Hend. f_equal. lia.
Qed.

Lemma unzip_nil_e {E Q A O} (tau : etree E Q A O) f qs ans e e' x :
  einterrogation tau f qs ans e e' ->
  alles tau e [] ans =! x <-> tau e' ans =! x.
Proof.
  intros; cbn.
  enough (exists es,
             (∀ (k : nat) (e0 e'0 : E) (a : A),
                 nth_error es k = Some e0 → nth_error es (S k) = Some e'0 → nth_error ans k = Some a → ∃ q : Q, tau e0 (take k ([] ++ ans)) =! inl (e'0, q)) /\
               length es = 1 + length ans
             /\
               nth_error es 0 = Some e /\
               nth_error es (length ans) = Some e'
         ) as (? & ? & ? & ? & ?).
  { eapply unzip_nil_e_; eauto. }
  induction H.
  - exists [e]; cbn; firstorder. all: destruct k; cbn in *; congruence.
  - destruct IHeinterrogation as (es & IH1 & IH2 & IH3 & IH4).
    exists (es ++ [e2]). repeat split.
    3:{ rewrite nth_error_app1; eauto. destruct es; cbn in *; lia. }
    2:{ rewrite !app_length. cbn. lia. }
    2:{ rewrite nth_error_app2; rewrite app_length; cbn; try lia.
        rewrite IH2.
        replace (length ans + 1 - (1 + length ans)) with 0 by lia.
        reflexivity. }
    intros. cbn.
    assert (S k < length es \/ S k = length es) as [Hl | Hl].
    { pose proof (nth_error_Some (es ++ [e2]) (S k)) as [HH _].
      rewrite H3 in HH. unshelve epose proof (HH _). congruence.
      rewrite app_length in H5. cbn in *. lia. }
    * rewrite nth_error_app1 in H3. 2: lia.
      rewrite nth_error_app1 in H2. 2: lia.
      rewrite nth_error_app1 in H4. 2: lia.
      eapply IH1 in H3; eauto.
      rewrite take_app_le. 2: lia. eauto.
    * rewrite Hl in H3.
      rewrite nth_error_app2 in H3. 2: lia.
      rewrite minus_diag in H3. cbn in H3. inversion H3; subst; clear H3.
      assert (k = length ans) by lia. subst.
      rewrite take_app.
      rewrite nth_error_app2 in H4. 2: lia.
      rewrite nth_error_app1 in H2. 2: lia.
      rewrite minus_diag in H4. inversion H4; subst; clear H4.
      rewrite H2 in IH4. inversion IH4; subst. eauto.
Qed.

Lemma einterrogation_equiv:
  ∀ (Q A I O E : Type) (e : E) (tau : I → etree E Q A O),
  ∃ τ : I → (list A) ↛ (Q + O),
  ∀ (R : Rel Q A) (x : I) (o : O),
    (∃ (qs : list Q) (ans : list A) (e' : E), einterrogation (tau x) R qs ans e e' ∧ tau x e' ans =! Output o)
      ↔ (∃ (qs : list Q) (ans : list A), interrogation (τ x) R qs ans ∧ τ x ans =! Output o).
Proof.
  intros Q A I O E e tau.
  exists (fun i l => bind (alles (tau i) e [] l) (fun x => match x with inl (_, q) => ret (inl q) | inr o => ret (inr o) end)).
  intros f i o.
  apply ex_iff_forall. intros qs. apply ex_iff_forall. intros ans. symmetry. split.
  + intros [H1 H2].
    assert (∃ e' : E, einterrogation (tau i) f qs ans e e').
    { clear H2. induction H1.
      - eexists. econstructor.
      - psimpl. destruct x as [ [] | ]; psimpl.
        destruct IHinterrogation. eexists. econstructor; eauto. eapply unzip_nil_e; eauto.
    }
    destruct H as (e' & H). exists e'. split; eauto.
    psimpl. destruct x as [ [] | ]; psimpl. eapply unzip_nil_e; eauto.
  + intros (e' & H1 & H2). split.
    * clear H2. induction H1; constructor; trivial. eapply unzip_nil_e in H; eauto.
      psimpl.
    * psimpl. eapply unzip_nil_e; eauto. cbn. psimpl.
Qed.

Lemma eOracleComputable_equiv {Q A I O} R :
  eOracleComputable R <-> @OracleComputable Q A I O R.
Proof.
  split.
  - intros (E & e & tau & Ht).
    red. setoid_rewrite Ht. clear Ht.
    eapply einterrogation_equiv.
  - intros [tau Ht]. exists unit, tt, (fun i e l => bind (tau i l) (fun x => match x with inl q => ret (inl (tt, q)) | inr o => ret (inr o) end)). intros f i o.
    rewrite Ht. apply ex_iff_forall. intros qs. apply ex_iff_forall. intros ans. firstorder.
    + exists tt. split.
      * clear - H. induction H; econstructor; eauto.
        psimpl.
      * psimpl.
    + clear - H. induction H; econstructor; eauto.
      psimpl. destruct x; psimpl.
    + psimpl; destruct x0; psimpl.
Qed.

(** *** Stalling interrogations with silent steps  *)

Hint Constructors interrogation.

Definition stree E Q A O := E -> list A ↛ (E * option Q + O).

Inductive sinterrogation {E Q A O} (τ : stree E Q A O) (f : Q -> A -> Prop) : list Q -> list A -> E -> E -> Prop :=
| sNoQuestions e : sinterrogation τ f [] [] e e
| stall qs ans e1 e1' e2 : sinterrogation τ f qs ans e1 e1' ->
                           τ e1' ans =! inl (e2, None) ->
                           sinterrogation τ f qs ans e1 e2
| sinterrogate qs ans q a e1 e1' e2 : sinterrogation τ f qs ans e1 e1' ->
                                      τ e1' ans =! inl (e2, Some q) ->
                                      f q a ->
                                      sinterrogation τ f (qs ++ [q]) (ans ++ [a]) e1 e2.

Lemma sinterrogation_ext {E Q A O} τ τ' (f : Q -> A -> Prop) q a (e1 e2 : E) :
  (forall e l v, τ e l =! v <-> τ' e l =! v) ->
  sinterrogation τ f q a e1 e2 <-> @sinterrogation E Q A O τ' f q a e1 e2 .
Proof.
  enough (forall τ τ' f q a,
             (forall e l v, τ e l =! v <-> τ' e l =! v) ->
             sinterrogation τ f q a e1 e2 -> @sinterrogation E Q A O τ' f q a e1 e2).
  { split; eapply H; firstorder. }
  clear. intros ? ? ? ? ? Heq.
  induction 1.
  - econstructor 1; eauto.
  - econstructor 2; eauto. firstorder.
  - econstructor 3; eauto. firstorder.
Qed.

Lemma sinterrogation_length {E Q A O} {tau f qs ans} {e e' : E} :
  @sinterrogation E Q A O tau f qs ans e e' -> length qs = length ans.
Proof.
  induction 1; try reflexivity. eauto.
  now rewrite !app_length, IHsinterrogation.
Qed.

Lemma sinterrogation_cons {E Q A O} q1 q2 a1 a2 (τ : stree E Q A O) (f : Q -> A -> Prop) e1 e2 e3 :
  τ e1 [] =! inl (e2, Some q1) ->
  f q1 a1 ->
  sinterrogation (fun e l => τ e (a1 :: l)) f q2 a2 e2 e3 ->
  sinterrogation τ f (q1 :: q2) (a1 :: a2) e1 e3.
Proof.
  intros H1 H2 H. induction H.
  - eapply sinterrogate with (qs := []) (ans := []). econstructor. eauto. eauto.
  - econstructor 2; eauto.
  -   replace (q1 :: qs ++ [q]) with ((q1 :: qs) ++ [q]) by reflexivity.
      replace (a1 :: ans ++ [a]) with ((a1 :: ans) ++ [a]) by reflexivity.
      econstructor 3; eauto.
Qed.

Fixpoint iterate {E Q O} (τ : E -> part (E * option Q + O)) (n : nat) (e : E) : part (option (E * option Q + O)) :=
  match n with
  | 0 => ret None
  | S n => bind (τ e) (fun res => match res with
                              | inl (e, None) => iterate τ n e
                              | x => ret (Some x)
                              end)
  end.

Lemma sinterrogation_scons {E Q A O} q a (τ : stree E Q A O) f e1 e2 e3 :
  τ e1 [] =! inl (e2, None) ->
  sinterrogation τ f q a e2 e3 ->
  sinterrogation τ f q a e1 e3.
Proof.
  intros H1 H.
  induction H.
  - econstructor 2; eauto. econstructor.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma sinterrogation_app {E Q A O} q1 q2 a1 a2 (τ : stree E Q A O) f e1 e2 e3 :
  sinterrogation τ f q1 a1 e1 e2 ->
  sinterrogation (fun e l => τ e (a1 ++ l)) f q2 a2 e2 e3 ->
  sinterrogation τ f (q1 ++ q2) (a1 ++ a2) e1 e3.
Proof.
  induction 1 in q2, a2, e3 |- *; cbn.
  - eauto.
  - intros. eapply IHsinterrogation.
    eapply sinterrogation_scons; eauto.
    rewrite app_nil_r. eauto.
  - intros. rewrite <- !app_assoc.
    eapply IHsinterrogation.
    eapply sinterrogation_cons.
    + rewrite app_nil_r. exact H0.
    + eauto.
    + eapply sinterrogation_ext; eauto. intros. cbn. now rewrite <- app_assoc.
Qed.

Definition sOracleComputable {Q A I O} (r : Rel Q A -> I -> O -> Prop) :=
  exists E, exists e : E, exists τ : I -> stree E Q A O, forall R x o, r R x o <-> exists qs ans e', sinterrogation (τ x) R qs ans e e' /\ τ x e' ans =! Output o.

Lemma sinterrogation_equiv:
  ∀ (Q A I O E : Type) (e : E) (tau : I → stree E Q A O),
  ∃ τ : I → etree E Q A O,
  ∀ (R : Rel Q A) (x : I) (o : O),
    (∃ (qs : list Q) (ans : list A) (e' : E), sinterrogation (tau x) R qs ans e e' ∧ tau x e' ans =! Output o)
      ↔ (∃ (qs : list Q) (ans : list A) (e' : E), einterrogation (τ x) R qs ans e e' ∧ τ x e' ans =! Output o).
Proof.
  intros Q A I O E e tau.

  pose (t := fun i e l => bind (mu (fun n => bind (iterate (fun e => tau i e l) n e) (fun x => match x with Some _ => ret true | _ => ret false end)))
                         (fun n => bind (iterate (fun e => tau i e l) n e)
                                  (fun x => match x with Some (inl (e, Some q)) => ret (inl (e, q))
                                                 | Some (inr o) => ret (inr o)
                                                 | _ => undef
                                         end))).
  exists t.
  intros f i o.
  do 2 (eapply ex_iff_forall; intros). rename x into qs, x0 into ans.
  symmetry. split.
  - subst t. intros (e' & H1 & H2). psimpl. destruct x0; psimpl. destruct s; psimpl.
    destruct p; psimpl. destruct o0; psimpl. rename x into n.
    enough (sinterrogation (tau i) f qs ans e e') as HH.
    enough (exists e'', sinterrogation (fun e l => tau i e (ans ++ l)) f [] [] e' e'' /\ tau i e'' ans =! inr o).
    { destruct H2 as (e'' & H2 & ?). exists e''.
      split; eauto.
      rewrite <- (app_nil_r qs).
      rewrite <- (app_nil_r ans).
      eapply sinterrogation_app; eauto.
    }
    {
      clear - H0. revert H0. generalize ( @inr (E * option Q) O o). intros res H0.
      induction n in res, H0, e' |- *; cbn in *; psimpl.
      destruct x as [[? []]|]; psimpl.
      + exists e'. split. econstructor. eauto.
      + edestruct IHn as (e'' & IH1 & IH2). eauto.
        eexists. split; eauto.
        eapply (sinterrogation_app [] [] [] []). 2: eauto.
        econstructor. econstructor.
        rewrite app_nil_r. eauto.
      + exists e'. split. econstructor. eauto.
    }
    {
      clear - H1. induction H1.
      + econstructor.
      + psimpl. destruct x0; psimpl.
        destruct s; psimpl.
        destruct p; psimpl.
        destruct o; psimpl.
        eapply sinterrogation_app. eapply IHeinterrogation. rename x into n.
        * clear - H2 H0. induction n in H2, e1' |- *; cbn in *; psimpl.
          destruct x as [ [? []] |]; psimpl.
          -- eapply (sinterrogate _ _ [] []); eauto.
             econstructor.
             rewrite app_nil_r; eauto.
          -- eapply IHn in H1.
             eapply (sinterrogation_app [] [q] [] [a]).
             2: eauto.
             econstructor 2.
             econstructor. now rewrite app_nil_r.
    }
  - intros (e' & H1 & H2).
    assert (t i e' ans =! inr o).
    {
      unfold t. psimpl.
      instantiate (1 := 1).
      eapply mu_hasvalue. split.
      psimpl. cbn. psimpl.
      cbn. psimpl.
      intros. destruct m; try lia.
      psimpl. cbn. psimpl.
      cbn. psimpl. cbn. psimpl.
    }
    clear H2.
    revert H. generalize (inr (A := E * Q) o).
    induction H1.
    + intros. eexists. split. econstructor. eauto.
    + intros.
      unfold t in H0.
      psimpl.
      eapply mu_hasvalue in H0 as [].
      psimpl. destruct x0; psimpl.
      destruct x1; psimpl.
      destruct s0; psimpl.
      destruct p; psimpl.
      destruct o0; psimpl.
      * edestruct IHsinterrogation as (e' & IH1 & IH2).
        2:{ exists e'. split. eauto.
            eauto. }
        subst t. cbn. psimpl.
        2:{ instantiate (2 := S x).
            clear H0.
            cbn. psimpl. }
        2: cbn; psimpl.
        eapply mu_hasvalue. split.
        psimpl. cbn. psimpl.
        intros. destruct m; psimpl.
        -- assert (m < x) by lia. eapply H4 in H6.
           psimpl. destruct x0; psimpl.
        -- psimpl.
      * edestruct IHsinterrogation as (e' & IH1 & IH2).
        2:{ exists e'. split. eauto.
            eauto. }
        subst t. cbn. psimpl.
        2:{ instantiate (2 := S x).
            clear H0.
            cbn. psimpl. }
        2: cbn; psimpl.
        eapply mu_hasvalue. split.
        psimpl. cbn. psimpl.
        intros. destruct m; psimpl.
        -- assert (m < x) by lia. eapply H4 in H6.
           psimpl. destruct x0; psimpl.
        -- psimpl.
    + intros. edestruct IHsinterrogation as (e' & IH1 & IH2).
      subst t. cbn. psimpl.
      instantiate (1 := 1).
      eapply mu_hasvalue. split.
      psimpl. cbn. psimpl.
      cbn. psimpl.
      intros. destruct m; try lia.
      psimpl. cbn. psimpl.
      cbn. psimpl. cbn. psimpl.
      eexists. split.
      econstructor; eauto.
      eauto.
Qed.

Lemma sOracleComputable_equiv Q A I O F :
  sOracleComputable F -> @eOracleComputable Q A I O F.
Proof.
  intros (E & e & tau & Ht). exists E. exists e.
  setoid_rewrite Ht. clear Ht.
  eapply sinterrogation_equiv.
Qed.

(** ** Trees give rise to partial functions *)

(** Function computed by a tree *)
Fixpoint evalt {Q A O} (τ : list A ↛ (Q + O)) (f : Q ↛ A) (n : nat) : part (Q + O) :=
    bind (τ []) (fun x =>
                   match n, x with
                   | 0, inl q => ret (inl q)
                   | S n, inl q => bind (f q) (fun a => evalt (fun l => τ (a :: l)) f n)
                   | _, inr o => ret (inr o)
                   end).

Lemma evalt_ext {Q A O} τ τ' f n v :
  (forall l v, τ l =! v <-> τ' l =! v) ->
  evalt τ f n =! v <-> @evalt Q A O τ' f n =! v.
Proof.
  enough (forall τ τ' f n v,
             (forall l v, τ l =! v <-> τ' l =! v) ->
             evalt τ f n =! v -> @evalt Q A O τ' f n =! v).
  { split; eapply H; firstorder. }
  clear. intros ? ? ? ? ? Heq.
  induction n in τ, τ', Heq |- *.
  - cbn. intros. psimpl. eapply Heq; eauto.
  - cbn. intros. psimpl; destruct x; psimpl.
    * eapply Heq; eauto.
    * eapply Heq; eauto.
    * psimpl. firstorder.
    * psimpl.
Qed.

Lemma interrogation_plus {Q A O} τ f n l lv v2 :
  @interrogation Q A O τ (fun x y => f x =! y) l lv ->
  evalt (fun l' => τ (lv ++ l')) f n =! v2 ->
  evalt τ f (length l + n) =! v2.
Proof.
  intros H. induction H in n |- *.
  - cbn. eauto.
  - intros. cbn in H2.
    cbn -[evalt]. rewrite app_length. cbn -[evalt].
    replace (length qs + 1 + n) with (length qs + (S n)) by lia.
    eapply IHinterrogation.
    cbn. psimpl. rewrite app_nil_r. eassumption.
    cbn. psimpl. eapply evalt_ext; eauto.
    cbn. intros. now rewrite <- app_assoc.
Qed.

Lemma interrogation_cons {Q A O} q1 q2 a1 a2 τ (f : Q -> A -> Prop) :
  τ [] =! inl q1 ->
  f q1 a1 ->
  @interrogation Q A O (fun l => τ (a1 :: l)) f q2 a2 ->
  interrogation τ f (q1 :: q2) (a1 :: a2).
Proof.
  intros H1 H2.
  induction q2 in a1, a2, H1, H2 |- * using rev_ind.
  - inversion 1; subst.
    + eapply Interrogate with (qs := []) (ans := []). econstructor. eauto. eauto.
    + destruct qs; cbn in *; congruence.
  - inversion 1.
    + destruct q2; cbn in *; congruence.
    + subst. assert (qs = q2 /\ q = x) as [<- <-].
      { eapply app_inj_2 in H0. 2: reflexivity. firstorder congruence. }
      replace (q1 :: qs ++ [q]) with ((q1 :: qs) ++ [q]) by reflexivity.
      replace (a1 :: ans ++ [a]) with ((a1 :: ans) ++ [a]) by reflexivity.
      econstructor. eapply IHq2; eauto. eauto. eauto.
Qed.

Lemma interrogation_app {Q A O} q1 q2 a1 a2 τ f :
  @interrogation Q A O τ f q1 a1 ->
  interrogation (fun l => τ (a1 ++ l)) f q2 a2 ->
  interrogation τ f (q1 ++ q2) (a1 ++ a2).
Proof.
  induction 1 in q2, a2 |- *; cbn.
  - eauto.
  - intros. rewrite <- !app_assoc.
    eapply IHinterrogation.
    eapply interrogation_cons.
    + now rewrite app_nil_r.
    + eauto.
    + eapply interrogation_ext; eauto. cbn. intros. now rewrite <- app_assoc.
Qed.

Lemma evalt_to_interrogation:
  ∀ (Q A I O : Type) (τ : I → (list A) ↛ (Q + O)) (f : Q ↛ A) (i : I) (o : O) (n : nat),
    evalt (τ i) f n =! Output o → ∃ (qs : list Q) (ans : list A), length qs <= n /\ interrogation (τ i) (λ (x : Q) (y : A), f x =! y) qs ans ∧ τ i ans =! Output o.
Proof.
  intros Q A I O τ f i o n H.
  induction n in τ, H |- *.
  * cbn in *. psimpl. destruct x; psimpl.
    exists [], []. repeat split. eauto. econstructor. eauto.
  * cbn in *. psimpl. destruct x; psimpl.
    -- eapply (IHn (fun i l => τ i (x :: l))) in H1 as (qs & ans & H3 & H1 & H2).
       exists (q :: qs), (x :: ans). split; eauto. cbn; lia. repeat split.
       eapply interrogation_app with (q1 := [q]) (a1 := [x]).
       eapply Interrogate with (qs := []) (ans := []); eauto.
       eauto. eauto.
    -- exists [], []. repeat split. cbn. lia. eauto. eauto.
Qed.

Lemma interrogation_equiv_evalt Q A I O :
  forall (τ : I -> list A ↛ (Q + O)) (f : Q ↛ A) (i : I) (o : O),
    (exists (qs : list Q) (ans : list A), interrogation (τ i) (fun x y => f x =! y) qs ans /\ τ i ans =! inr o) <-> (exists n : nat, evalt (τ i) f n =! inr o).
Proof.
  intros τ f i o. split.
  + intros (qs & ans & Hi & Hout).
    exists (length qs + 1). eapply interrogation_plus; eauto.
    cbn. rewrite app_nil_r. psimpl.
  + intros [n H]. eapply evalt_to_interrogation in H as (? & ? & ? & ? & ?); eauto.
Qed.

(** ** Closure properties of Oracle computability  *)

(** Computability of precomposition *)
Lemma computable_precompose A Q I O I' F g :
  @OracleComputable A Q I O F ->
  @OracleComputable A Q I' O (fun r x => F r (g x)).
Proof using.
  intros [tau H].
  exists (fun i l => tau (g i) l). intros. eapply H.
Qed.

(** Computability of any partial function *)
Lemma computable_partial_function {Q A I O : Type} (f : I ↛ O) :
  OracleComputable (λ (_ : Rel Q A) (i : I) (o : O), f i =! o).
Proof.
  intros.
  exists (fun x l => bind (f x) (fun o => ret (inr o))).
  intros. psimpl.
  intros (? & ? & ? & ? & ? & ?). psimpl.
Qed.

(** Computability of the empty relation *)
Lemma computable_nothing {Q A I O} :
  @OracleComputable Q A I O (fun R i o => False).
Proof.
  eapply OracleComputable_ext.
  eapply (computable_partial_function (fun _ => undef)).
  cbn. intros. split. intros. psimpl.
  firstorder.
Qed.

(** Computability of any total function *)
Lemma computable_function {Q A I O} f :
  @OracleComputable Q A I O (fun R i o => f i = o).
Proof.
  eapply OracleComputable_ext.
  eapply computable_precompose with (g := f).
  eapply (computable_partial_function (@ret _ _)).
  cbn. firstorder subst; psimpl.
Qed.

(** Computability of constant functions *)
Lemma computable_ret A Q I O v :
  @OracleComputable Q A I O (fun f i o => o = v).
Proof.
  eapply OracleComputable_ext.
  eapply (computable_function (fun _ => v)).
  firstorder.
Qed.

(** Computability of the identity  *)
Lemma computable_id {X Y} :
  OracleComputable (fun R : Rel X Y => R).
Proof.
  exists (fun i l => match l with [] => ret (inl i) | b :: _ => ret (inr b) end).
  intros. split.
  - intros H. exists [x], [o]. split. 2: psimpl.
    eapply (Interrogate _ _ [] []); eauto.
    psimpl.
  - intros (qs & ans & H1 & H2).
    inversion H1; subst.
    + cbn in *. psimpl.
    + assert (length qs0 = length ans0) by (eapply interrogation_length; eauto).
      destruct qs0, ans0; cbn in *; try congruence; psimpl.
Qed.

(** Computability of unbounded search -- note that R has to return false and cannot be undefined before finding n *)
Lemma computable_search I :
  OracleComputable (fun R (i : I) n => R (i, n) true /\ forall m, m < n -> R (i, m) false).
Proof.
  exists (fun i l => ret (match list_find (fun b => b = true) l with Some (i, _) => inr i | _ => inl (i, length l) end)).
  intros f i v. symmetry. split.
  - intros (qs & ans & H1 & H2).
    destruct list_find as [ [] | ] eqn:E; next.
    inversion H1; subst.
    + cbn in E. congruence.
    + destruct (list_find (λ b : bool, b = true) ans0) as [ [] | ] eqn:E_; next.
      rewrite list_find_app_r in E; eauto.
      cbn in E. destruct (decide (a = true)); cbn in *; inversion E; subst; clear E.
      split; eauto.
      clear H1 H2.
      set (n := length ans0).
      assert (qs0 = map (pair i) (seq 0 n) /\ ans0 = repeat false n).
      { induction H.
        - split; reflexivity.
        - subst n. rewrite !app_length, repeat_app, seq_app, map_app.
          cbn. eapply list_find_app_None in E_ as [E1 E2].
          rewrite E1 in H0. next. cbn in E2. destruct (decide (a = true)); inversion E2.
          destruct a; try congruence.
          destruct IHinterrogation as [IH1 IH2]; eauto.
          split; congruence.
      }
      subst n.
      destruct H0 as [-> ->].
      induction H.
      * cbn. intros. lia.
      * rewrite app_length. cbn.
        rewrite repeat_length.
        intros.
        assert (m = length ans \/ m < length ans) as [-> | HH] by lia.
        -- eapply list_find_app_None in E_ as [E1 E2].
           rewrite E1 in H0. next. cbn in E2. destruct a; cbv in E2; inversion E2.
           eauto.
        -- eapply IHinterrogation. eapply list_find_app_None in E_. firstorder.
           now rewrite repeat_length.
  - intros (Hv & Hl).
    exists (map (pair i) (seq 0 (v + 1))), (repeat false v ++ [true]).
    split.
    + rewrite seq_app, map_app. econstructor.
      * clear Hv.
        induction v.
        -- econstructor.
        -- replace (S v) with (v + 1) by lia. rewrite seq_app, repeat_app, map_app.
           cbn. econstructor; eauto.
           rewrite list_find_repeat_not; try congruence.
           rewrite repeat_length. psimpl.
      * rewrite list_find_repeat_not; try congruence.
        rewrite repeat_length. psimpl.
      * eauto.
    + rewrite list_find_app_r.
      2:{ rewrite list_find_repeat_not; try congruence. }
      cbn. unfold decide, decide_rel. cbn. rewrite repeat_length. psimpl.
Qed.

(** Computability of sequential execution (bind)  *)
Lemma computable_bind A Q Y Z I (F1: Rel Q A -> _ -> _ -> Prop) F2 :
  OracleComputable (I := I) F1 ->
  OracleComputable (O := Z) F2 ->
  OracleComputable (fun f x z => exists y : Y, F1 f x y /\ F2 f (x, y) z).
Proof using.
  intros [tau1 H1] [tau2 H2].
  eapply eOracleComputable_equiv.
  eapply sOracleComputable_equiv.
  exists (option (Y * nat)), None.
  unshelve eexists.
  { intros r b l.
    refine (match b with Some (y, n) => bind (tau2 (r, y) (drop n l)) (fun res => match res with inl q => ret (inl (Some (y, n), Some q)) | inr o => ret (inr o) end)
                    | None => bind (tau1 r l) (fun res => match res with inl q => ret (inl (None, Some q)) | inr y => ret (inl (Some (y, length l), None)) end) end).
  } cbn.
  intros.
  setoid_rewrite H1. setoid_rewrite H2. clear. symmetry. split.
  - intros (qs & ans & info & H1 & H2).
    destruct info as [ [y n] |  ]; simpl_assms.
    all: destruct x0; simpl_assms.
    exists y. rename R into f. rename x into i.
    enough (n <= length ans /\ interrogation (tau1 i) f (take n qs) (take n ans) ∧ tau1 i (take n ans) =! inr y /\  interrogation (tau2 (i, y)) f (drop n qs) (drop n ans))
      by firstorder. clear H.
    generalize (eq_refl (@None (prod Y nat))).
    revert H1. generalize (@None (prod Y nat)) at 2 3. intros none H1 Heqnone.
    change (match Some (y,n) with Some (y, n) =>
                                    n ≤ length ans ∧
                                      interrogation (tau1 i) f (take n qs) (take n ans) ∧ tau1 i (take n ans) =! inr y /\  interrogation (tau2 (i, y)) f (drop n qs) (drop n ans)
                             | None =>
                                 interrogation (tau1 i) f qs ans
            end).

    revert H1. (generalize (Some (y, n))). intros.
    induction H1 in Heqnone |- *.
    + subst. econstructor.
    + destruct e1' as [ [] | ]. psimpl. destruct x; psimpl.
      psimpl. destruct x; psimpl. repeat split.
      all: assert (length qs = length ans) as Hlen by (eapply sinterrogation_length; eauto).
      * eauto.
      * rewrite firstn_all. rewrite <- Hlen. rewrite firstn_all. eauto.
      * rewrite firstn_all. eauto.
      * rewrite !drop_all. rewrite <- Hlen. rewrite drop_all. econstructor.
    + destruct e1' as [ [] | ].
      * simpl_assms. destruct x; simpl_assms. destruct IHsinterrogation as (IH1 & IH2 & IH3 & IH4). reflexivity.
        assert (length qs = length ans) as Hlen by (eapply sinterrogation_length; eauto).
        repeat split.
        -- rewrite app_length; cbn. lia.
        -- rewrite !take_app_le; try lia. eauto.
        -- rewrite !take_app_le; try lia. eauto.
        -- rewrite !drop_app_le; try lia. econstructor; eauto.
      * simpl_assms.  destruct x; simpl_assms.
  - intros (y & (qs1 & ans1 & H1 & H1') & (qs2 & ans2 & H2 & H2')).
    exists (qs1 ++ qs2).
    exists (ans1 ++ ans2).
    exists (Some (y, length qs1)). split.
    2:{ assert (length qs1 = length ans1) as Hlen by (eapply interrogation_length; eauto).
        psimpl. rewrite Hlen. rewrite drop_app. eauto. cbn. psimpl. }
    eapply sinterrogation_app. instantiate (1 := None).
    + clear - H1.
      induction H1.
      * econstructor.
      * econstructor 3; eauto. cbn. psimpl.
    + eapply sinterrogation_scons. psimpl. rewrite app_nil_r. eauto. cbn.
      rewrite app_nil_r. cbn. psimpl.
      assert (length qs1 = length ans1) as -> by (eapply interrogation_length; eauto).
      clear - H2.
      induction H2.
      * econstructor.
      * econstructor 3; eauto.
        cbn. psimpl. rewrite drop_app. eauto. cbn. psimpl.
Qed.

(** Computability of case analysis  *)
Lemma computable_if A Q I O (F1: (Rel Q A)  -> _ -> _ -> Prop) F2 test :
  @OracleComputable Q A I O F1 ->
  @OracleComputable Q A I O F2 ->
  @OracleComputable _ _ _ _ (fun f (x : I) => if test x : bool then F1 f x else F2 f x).
Proof using.
  intros [tau1 H1] [tau2 H2].
  unshelve eexists. intros i.
  destruct (test i). exact (tau1 i).
  exact (tau2 i). intros. cbn. destruct test; cbn; eauto.
Qed.

(** Computability of the identity  *)
Lemma computable_ident Q A O :
  @OracleComputable Q A O O (fun R x o => x = o).
Proof.
  eapply (computable_function (fun i => i)).
Qed.

(** ** Lemmas about Turing reducibility *)

Definition lastn {T} n (l : list T) :=
  (skipn (length l - n) l).

Lemma lastn_S {T} n (l : list T) x :
  lastn (S n) (l ++ [x]) = lastn n l ++ [x].
Proof.
  unfold lastn.
  rewrite app_length. cbn.
  replace (length l + 1 - S n) with (length l - n) by lia.
  rewrite drop_app_le; eauto. lia.
Qed.

(** Closure under composition *)
Lemma computable_comp A X  Q Y I O (F1 : Rel Q A -> Rel X Y) (F2 : Rel X Y -> I -> O -> Prop) :
  OracleComputable F1
  -> OracleComputable F2
  -> OracleComputable (fun r x => F2 (F1 r) x).
Proof.
  intros [t1 H1] [t2 H2].
  eapply eOracleComputable_equiv.
  eapply sOracleComputable_equiv.
  eexists (list (X * Y) * option (X * nat))%type.
  exists ([], None).
  pose (t := fun i '(trace_F1_r, last_x_requested) ans_of_r =>
               match last_x_requested with
               | Some (x, n) => bind (t1 x (lastn n ans_of_r))
                                 (λ res : Q + Y, match res with
                                                 | inl q => ret (inl (trace_F1_r, Some (x, S n), Some q))
                                                 | inr y => ret (inl (trace_F1_r ++ [(x, y)], None, None))
                                                 end)
               | None => bind (t2 i (map snd trace_F1_r))
                          (λ res : X + O, match res with
                                          | inl x => ret (inl (trace_F1_r, Some (x, 0), None))
                                          | inr o => ret (inr o)
                                          end)
               end).
  exists t.
  intros. setoid_rewrite H2. clear F2 H2. symmetry. split.
  - intros (qs & ans & [ans' qs'] & Hint & Hend).
    destruct qs' as [ [ ] | ]; unfold t in Hend; simpl_assms. destruct x1; simpl_assms.
    destruct x0; simpl_assms.
    rename R into f. rename x into i.
    enough (interrogation (t2 i) (F1 f) (map fst ans') (map snd ans')).
    firstorder. clear H.
    enough (forall h, sinterrogation (t i) f qs ans ([], None) h ->
                 (interrogation (t2 i) (F1 f) (map fst (fst h))) (map snd (fst h)) /\
                   match snd h with
                     None => True
                   | Some (x, n) => t2 i (map snd (fst h)) =! inl x /\ interrogation (t1 x) f (lastn n qs) (lastn n ans)
                   end
           ).
    { eapply H in Hint. cbn in Hint. eapply Hint. }
    clear - H1. intros h H.
    remember ([], None) as e0.
    revert Heqe0.
    induction H; intros Heqe0.
    + subst. cbn. split; econstructor.
    + destruct IHsinterrogation as [IH1 IH2]; eauto.
      destruct e1' as (qs_ans & [ (x & n) | ]); cbn in *.
      * simpl_assms. destruct x0; simpl_assms. destruct IH2 as [IH2 IH3]. cbn.
        split; eauto. rewrite !map_app. cbn.
        econstructor; eauto.
        eapply H1. eauto.
      * psimpl.  destruct x; simpl_assms.
        unfold lastn. cbn.
        repeat split; eauto.
        rewrite !Nat.sub_0_r, !drop_all.
        econstructor.
    + destruct IHsinterrogation as [IH1 IH2]; eauto.
      destruct e1' as (qs_ans & [ (x & n) | ]); cbn in *.
      * psimpl. destruct x0; psimpl.
        rewrite !lastn_S.
        firstorder. 
      * psimpl. destruct x; psimpl.
  - intros (xs & ys & Hint & Hend).
    rename x into i. rename R into f.
    enough (∃ (qs : list Q) (ans : list A), sinterrogation (t i) f qs ans ([], None) (zip xs ys, None)).
    { firstorder. exists x, x0. eexists. split. eauto. cbn. psimpl.
      rewrite snd_zip. eauto. eapply interrogation_length in Hint. lia.
      cbn. psimpl. }
    clear Hend. induction Hint; cbn.
    + exists [], []. econstructor.
    + rename qs into xs. rename ans into ys.
      destruct IHHint as (qs & ans & IH).
      rewrite zip_with_app. 2: eapply interrogation_length; eauto.
      eapply H1 in H0 as (qs' & ans' & Hint' & Hend'). cbn.
      exists (qs ++ qs'), (ans ++ ans').
      assert (sinterrogation (t i) f qs ans  ([], None) (zip xs ys, Some (q, 0))).
      { econstructor 2. eauto. cbn. psimpl. rewrite snd_zip. eauto.
        eapply interrogation_length in Hint; lia. cbn.
        psimpl.
      }
      eapply sinterrogation_app. eauto.
      econstructor 2.
      instantiate (1 := (zip xs ys, Some (q, length ans'))).
      2:{ cbn. psimpl.
          unfold lastn. rewrite app_length.
          replace ((length ans + length ans' - length ans')) with (length ans) by lia.
          rewrite drop_app. eauto.
          cbn. psimpl.
      }
      clear - Hint'.
      induction Hint'.
      * econstructor.
      * econstructor 3; eauto.
        cbn. psimpl.
        unfold lastn. rewrite app_length.
        replace ((length ans + length ans0 - length ans0)) with (length ans) by lia.
        rewrite drop_app. eauto.
        cbn. eapply ret_hasvalue_iff. repeat f_equal.
        rewrite app_length. cbn. lia.
Qed.

(** ** Central results regarding Turing reducibility *)

Notation "P ⪯ᴛ Q" := (red_Turing P Q) (at level 50).

(** The relational layer can be dropped *)
Lemma Turing_reducible_without_rel X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ᴛ q <-> exists τ, forall x b, char_rel p x b ↔ (∃ qs ans, interrogation (τ x) (char_rel q) qs ans ∧ τ x (ans) =! Output b).
Proof.
  split.
  - intros [R [[τ Ht] HR]].
    exists τ. intros. rewrite HR, Ht. reflexivity.
  - intros [τ Ht].
    exists (fun R x o => ∃ (qs : list Y) (ans : list bool), interrogation (τ x) R qs ans ∧ τ x (ans) =! Output o).
    cbn. split.
    + exists τ. reflexivity.
    + eapply Ht.
Qed.

Lemma Turing_refl {X} (p : X -> Prop) :
  p ⪯ᴛ p.
Proof.
  exists (fun R => R). split. eapply computable_id.
  reflexivity.
Qed.

Lemma Turing_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ᴛ q -> q ⪯ᴛ r -> p ⪯ᴛ r.
Proof.
  intros (r1 & Hr1 & H1) (r2 & Hr2 & H2).
  exists (fun R => r1 (r2 R)). split.
  - eapply computable_comp with (F2 := r1). eapply Hr2. eapply Hr1.
  - intros. rewrite H1.
    eapply (OracleComputable_extensional Hr1).
    firstorder.
Qed.

Definition join {X Y} (p : X -> Prop) (q : Y -> Prop) xy :=
 match xy with
 | inl x => p x
 | inr y => q y
 end.

Lemma Turing_upper_semi_lattice {X Y Z} (p : X -> Prop) (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ᴛ join p q /\ q ⪯ᴛ join p q /\ (p ⪯ᴛ r -> q ⪯ᴛ r -> join p q ⪯ᴛ r).
Proof.
  repeat split.
  - eexists. split; cbn. 
    eapply computable_precompose with (g := inl).
    eapply computable_id. reflexivity.
  - eexists. split; cbn. 
    eapply computable_precompose with (g := inr).
    eapply computable_id. reflexivity.
  - intros (F1 & [tau1 Htau1] & H1') (F2 & [tau2 Htau2] & H2').
    exists (fun R xy b => match xy with inl x => F1 R x b | inr y => F2 R y b end). split.
    + exists (fun xy l => match xy with inl x => tau1 x l | inr y => tau2 y l end). intros R [] o; cbn.
      eapply Htau1.
      eapply Htau2.
    + intros []; cbn; firstorder.
Qed.

(** Turing reduction transports partial computability - relying on the evalt function from above *)
Lemma Turing_transports_computable_strong {Q A I O} F tau :
  (∀ (R : Q → A → Prop) (x : I) (o : O), F R x o ↔ (∃ (qs : list Q) (ans : list A), interrogation (tau x) R qs ans ∧ tau x ans =! Output o)) ->
  {F' | forall f R, pcomputes f R -> pcomputes (F' f) (F R)}.
Proof.
  intros H.
  exists (fun f i => bind (mu (fun n => bind (evalt (tau i) f n) (fun res => match res with inl _ => ret false | inr _ => ret true end))) (fun n => bind (evalt (tau i) f n) (fun res => match res with inl _ => undef | inr o => ret o end))).
  intros f R HfR. unfold pcomputes in *. intros.
  rewrite H.
  setoid_rewrite interrogation_ext.
  2: reflexivity. 2:{ intros. split. intros hf % HfR. eapply hf. firstorder. }
  setoid_rewrite interrogation_equiv_evalt.
  rewrite !bind_hasvalue. split.
  - intros (? & ? & ?). simpl_assms. destruct x1; simpl_assms.
  - intros (n & Hn).
    edestruct mu_ter.
    2:{ exists x0. split. eauto.
        eapply mu_hasvalue in H0 as [].
        simpl_assms. destruct x1; psimpl.
        eapply ret_hasvalue_iff.
        assert (exists n, evalt (tau x) f n =! Output y) by eauto.
        assert (exists n, evalt (tau x) f n =! Output o) by eauto.
        eapply interrogation_equiv_evalt in H2, H3.
        destruct H2 as (? & ? & H2 & ?).
        destruct H3 as (? & ? & H3 & ?).
        eapply interrogation_output_det with (τ := tau).
        2: eapply H3. 3: eapply H2. all: eauto.
        intros ?; intros. eapply hasvalue_det; eauto.
    }
    exists n. split. psimpl. intros.
    unfold ter.
    setoid_rewrite bind_hasvalue.
    enough (∃ (a0 : Q + O), evalt (tau x) f x0 =! a0) as []. {
      destruct x1; repeat eexists; psimpl.
    }
    clear H0.
    eapply evalt_to_interrogation in Hn as (qs & ans & H1 & H2 & H3).
    assert (x0 < length qs \/ length qs <= x0) as [|] by lia.
    + eapply interrogation_length in H2 as Hlen.
      rewrite <- (take_drop x0 qs) in H2.
      rewrite <- (take_drop x0 ans) in H2.
      eapply interrogation_app_inv in H2 as [].
      replace x0 with (length (take x0 qs) + 0). 2:{ rewrite firstn_length. lia. }
      2:{ rewrite !skipn_length. lia. }
      destruct (drop x0 qs) eqn:E.
      { eapply (f_equal length) in E. cbn in E. rewrite skipn_length in E. lia. }
      destruct (drop x0 ans) eqn:E'.
      { eapply (f_equal length) in E'. cbn in E'. rewrite skipn_length in E'. lia. }
      eapply (interrogation_app_inv [q] _ [a]) in H4 as [].
      inversion H4.
      assert (qs0 = nil /\ ans0 = nil) as [-> ->]. { eapply (f_equal length) in H6, H7. rewrite app_length in *; cbn in *. destruct qs0, ans0; cbn in *; try lia. eauto. }
      inversion H6.  inversion H7. subst.
      eexists. eapply interrogation_plus. eauto.
      cbn. psimpl.
      eapply (f_equal length) in E, E'. rewrite !skipn_length in E, E'. cbn in *. lia.
    + eapply nat_le_sum in H0 as (k & ->).
      eexists. eapply interrogation_plus. eauto.
      destruct k; cbn. psimpl. rewrite app_nil_r. eauto.
      cbn. psimpl. psimpl.
      rewrite app_nil_r. psimpl. cbn. psimpl.
Qed.

Lemma Turing_transports_computable {Q A I O} F :
  @OracleComputable Q A I O F ->
  exists F', forall f R, pcomputes f R -> pcomputes (F' f) (F R).
Proof.
  intros [tau H].
  destruct (Turing_transports_computable_strong F tau) as [F' ]; eauto.
Qed.

(** Transport of decidability -- which is equivalent to Markov's principle *)
Definition char_rel_fun {X Y} (f : X -> Y) := (fun x b => f x = b).

Lemma char_rel_fun_functional {X Y} (f : X -> Y) :
  functional (char_rel_fun f).
Proof.
  firstorder congruence.
Qed.

Lemma partial_total X Y (f : X ↛ Y) :
  (forall x, (ter (f x))) -> { g : X -> Y | forall x, f x =! g x}.
Proof.
  intros H. unshelve eexists.
  - intros x. specialize (H x). exact (eval H).
  - intros x. cbn. eapply eval_hasvalue.
Qed.

From SyntheticComputability Require Import DecidabilityFacts.

Lemma partial_decidable {X} (p : X -> Prop) (f : X ↛ bool) :
  (forall x, ter (f x)) -> (forall x, f x =! true <-> p x) -> decidable p.
Proof.
  intros Hter He.
  destruct (partial_total _ _ _ Hter) as [g Hg].
  exists g. intros x. red. rewrite <- He. specialize (Hg x).
  destruct (g x); firstorder. eapply hasvalue_det; eauto.
Qed.

From SyntheticComputability Require Import principles Pigeonhole.

Lemma transport_decidable : forall X Y (p : X -> Prop) (q : Y -> Prop),
    MP ->
    p ⪯ᴛ q -> decidable q -> decidable p.
Proof.
  intros X Y p q mp [F [Hc H]] [f Hf].
  eapply Turing_transports_computable in Hc as [F' HF'].
  specialize (HF' (fun x => ret (f x)) (char_rel q)).
  cbn in *.
  eapply (@Proper_decidable X) with (y := fun x => F (char_rel q) x true).
  intros x. eapply (H x true).
  unshelve epose proof (HF' _) as hF'.
  + intros x b. rewrite <- ret_hasvalue_iff.
    specialize (Hf x). clear - Hf. destruct b, (f x); firstorder.
  + eapply partial_decidable. 2:{ intros x. apply hF'. }
    intros. eapply (MP_to_MP_partial mp). intros Hx.
    ccase (p x) as [Hp | Hp].
    -- eapply Hx. exists true. eapply hF'. now eapply (H _ true).
    -- eapply Hx. exists false. eapply hF'. now eapply (H _ false).
Qed.

Record oracle (X : Type) : Type :=
  {
  S0 : X -> Prop;
  S1 : X -> Prop;
  H_oracle : forall x, S0 x -> S1 x -> False
  }.
Arguments S0 {_} _.
Arguments S1 {_} _.

Program Definition char_oracle {X} (p : X -> Prop) :=
  {| S0 := p ; S1 := fun x => ~ p x ; H_oracle := ltac:(abstract firstorder) |}.

From SyntheticComputability Require Import Dec.

Section equivalence.

  Variable X : Type.
  Variable eX : eq_dec X.
  Implicit Type o : oracle X.
  Implicit Type R : partial.FunRel X bool.

  Program Definition of_o (o : oracle X) :=
    @Build_FunRel _ _ (fun x b => if (b : bool) then S0 o x else S1 o x) _.
  Next Obligation.
    destruct o; intros ? [] [] ? ?; cbn in *; firstorder.
  Qed.

  Lemma of_o_enumerator o f0 f1 :
    enumerator f0 (S0 o) -> enumerator f1 (S1 o) ->
    pcomputes (fun x => bind (mu_tot (fun n => Dec (f0 n = Some x) || Dec (f1 n = Some x)))
                          (fun n => if Dec (f0 n = Some x) then ret true else ret false)) (of_o o).
  Proof.
    intros H0 H1 x b. split.
    - intros (? & [] % mu_tot_hasvalue & ?) % bind_hasvalue.
      unfold Dec in *.
      do 2 destruct Dec.option_eq_dec; cbn in *; eapply ret_hasvalue_inv in H3 as <-.
      + cbn. eapply H0. eauto.
      + cbn. eapply H0. eauto.
      + cbn. eapply H1. eauto.
      + congruence.
    - intros Ho. destruct b; cbn in *.
      + eapply H0 in Ho as [n Ho].
        assert ((λ n : nat, Dec (f0 n = Some x) || Dec (f1 n = Some x) : bool) n = true) as [n' Hn] % mu_tot_ter by (destruct Dec; firstorder).
        pose proof Hn as [Hn' _] % mu_tot_hasvalue.
        eapply bind_hasvalue.
        eexists; split; eauto.
        destruct (Dec (f0 n' = Some x)). eapply ret_hasvalue.
        cbn in Hn'. destruct Dec; cbn in *; try congruence.
        edestruct H_oracle.
        eapply H0. eauto. eapply H1; eauto.
      + eapply H1 in Ho as [n Ho].
        assert ((λ n : nat, Dec (f0 n = Some x) || Dec (f1 n = Some x) : bool) n = true) as [n' Hn] % mu_tot_ter. {
          do 2 destruct Dec; cbn; firstorder. }
        pose proof Hn as [Hn' _] % mu_tot_hasvalue.
        eapply bind_hasvalue.
        eexists; split; eauto.
        destruct (Dec (f0 n' = Some x)). 2:eapply ret_hasvalue.
        cbn in Hn'.  edestruct H_oracle.
        eapply H0. eauto. eapply H1; eauto.
  Qed.

  Lemma of_o_char (q : X -> Prop) :
    forall x y, of_o (char_oracle q) x y <-> char_rel q x y.
  Proof.
    firstorder.
  Qed.

End equivalence.

Lemma bienumerable_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :
  eq_dec X ->
  enumerable p -> enumerable (fun x => ~ p x) ->
  p ⪯ᴛ q.
Proof.
  intros HX [f Hf] [g Hg].
  exists (fun R => char_rel p). split. 2: reflexivity.
  exists (fun x _ =>
       bind (mu_tot (fun n => Dec (f n = Some x) || Dec (g n = Some x)))
                          (fun n => if Dec (f n = Some x) then ret (inr true) else ret (inr false))).
  - intros.
    rewrite <- of_o_char; eauto.
    pose proof (of_o_enumerator _ HX (char_oracle p) _ _ Hf Hg). unfold pcomputes in H.
    rewrite <- H. split. intros.
    + exists [], []. split. econstructor. psimpl. destruct Dec; psimpl.
    + intros (_ & _ & _ & HH). psimpl. destruct Dec; psimpl.
Qed.

Lemma decidable_Turing_MP :
  (forall  (p : nat -> Prop) (q : nat -> Prop), p ⪯ᴛ q -> decidable q -> decidable p) ->
  MP.
Proof.
  intros H. eapply (Post_nempty_to_MP 0).
  intros p ? % halting.semi_decidable_enumerable_iff_nat ? % halting.semi_decidable_enumerable_iff_nat.
  eapply H with (q := fun x => True).
  eapply bienumerable_Turing; eauto.
  exists (fun _ => true). cbv. firstorder.
Qed.

Definition stable {X} (p : X -> Prop) := forall x, ~~ p x -> p x.
Notation compl p := (fun x => ~ p x).

Lemma Turing_red_compl {X} (P : X -> Prop): 
  stable P -> P ⪯ᴛ compl P.
Proof.
  intros DN.
  exists (fun R x b => R x (negb b)).
  split.
 - eapply OracleComputable_ext. eapply computable_bind.
   eapply computable_id.
   eapply computable_precompose with (g := snd).
   eapply computable_function with (f := negb).
   cbn. firstorder subst. now destruct x; cbn in *.
   exists (negb o). now destruct o; cbn in *.
 - intros ? []; cbn; firstorder congruence.
Qed.

Lemma compl_Turing_red {X} (P : X -> Prop): 
  stable P -> (compl P) ⪯ᴛ P.
Proof.
  intros DN.
  exists (fun R x b => R x (negb b)).
  split.
 - eapply OracleComputable_ext. eapply computable_bind.
   eapply computable_id.
   eapply computable_precompose with (g := snd).
   eapply computable_function with (f := negb).
   cbn. firstorder subst. now destruct x; cbn in *.
   exists (negb o). now destruct o; cbn in *.
 - intros ? []; cbn; firstorder congruence.
Qed.

Lemma decidable_compl_stable {X} (P : X -> Prop) :
  (forall P : X -> Prop, decidable (compl P) -> decidable P) -> stable P.
Proof.
  intros H x Hx.
  destruct (H (fun _ => P x)) as [f Hf].
  - exists (fun _ => false). firstorder congruence.
  - specialize (Hf x). destruct (f x); firstorder congruence.
Qed.

Lemma rev {X} (P : X -> Prop) :
  MP ->
  (forall P : X -> Prop, P ⪯ᴛ compl P) -> stable P.
Proof.
  intros mp H.
  eapply decidable_compl_stable.
  intros Q. eapply transport_decidable; eauto.
Qed.

(** Truth-table reducibility is included in Turing reducibility  *)

Lemma truthtable_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) : (forall y, q y \/ ¬ q y) ->
  reductions.red_tt p q -> p ⪯ᴛ q.
Proof.
  intros dq [f Hf]. red in Hf.
  exists (fun R x b => exists L : list bool, List.Forall2 R (projT1 (f x)) L /\
                               (truthtables.eval_tt (projT2 (f x)) L = b)).
  split.
  - clear dq. cbn.
    exists (fun x l => match nth_error (projT1 (f x)) (length l) with
               | Some a => ret (Ask a)
               | None => ret (inr (truthtables.eval_tt (projT2 (f x)) (l)))
               end).
    intros R x o. split.
    + intros (L & H1 & <-). exists (projT1 (f x)). exists L. split.
      2:{ eapply Forall2_length in H1.
          rewrite <- H1. 
          edestruct nth_error_None as [_ H].
          rewrite H. 2: lia.
          eapply ret_hasvalue.
      }
      assert (prefix (projT1 (f x)) (projT1 (f x))) by eauto.
      revert H.
      revert H1. generalize (projT1 (f x)) at 1 2 5.
      induction L using rev_ind; intros.
      * inversion H1. econstructor.
      * destruct l using rev_ind. eapply Forall2_length in H1. rewrite app_length in H1.
        cbn in H1. lia. clear IHl.
        eapply Forall2_app_inv in H1 as [].
        2:{ eapply Forall2_length in H1; rewrite !app_length in H1. cbn in *. lia. }
        inversion H1; subst.
        econstructor.
        { eapply IHL; eauto. destruct H as [ll]. exists (x1 :: ll).
          rewrite H. now rewrite <- app_assoc.
        }
        destruct H as [ll ->].
        eapply Forall2_length in H0. rewrite <- H0.
        rewrite nth_error_app1. 2: rewrite app_length; cbn; lia.
        rewrite nth_error_app2. 2: lia. rewrite minus_diag. cbn. psimpl.
        eauto.
    + intros (qs & ans & H1 & H2).
      eapply interrogation_length in H1 as Hlen. rewrite <- Hlen in H2.
      destruct nth_error eqn:E; psimpl.
      exists ans. split; eauto.
      eapply nth_error_None in E.
      enough (Forall2 R (take (length qs) (projT1 (f x))) ans). { rewrite firstn_all2 in H. eauto. eauto. }
      clear - H1. induction H1.
      * econstructor.
      * rewrite app_length. cbn.
        destruct nth_error eqn:E; psimpl.
        eapply interrogation_length in H1 as Hlen.
        rewrite <- Hlen in E. 
        rewrite <- (firstn_skipn (length qs) (projT1 (f x))).
        rewrite firstn_app.
        rewrite take_length.
        assert (length qs < length (projT1 (f x))). eapply nth_error_Some. rewrite E. congruence.
        rewrite Nat.min_l. 2: lia.
        rewrite firstn_all2.
        2:{ rewrite take_length. lia. }
        enough (take (length qs + 1 - length qs) (drop (length qs) (projT1 (f x))) = [q]) as ->.
        eapply Forall2_app; eauto.
        replace (length qs + 1 - length qs) with 1 by lia.
        rewrite <- (firstn_skipn (length qs) (projT1 (f x)) ) in E.
        rewrite nth_error_app2 in E.
        2: rewrite take_length; lia.
        rewrite take_length in E. rewrite Nat.min_l in E. 2: lia.
        rewrite minus_diag in E.
        destruct drop; cbn in *; try congruence.
        inversion E. subst. rewrite take_0. reflexivity.
  - cbn. intros x b. split.
    + intros.
      enough (exists L, Forall2 reflects L (map q (projT1 (f x)))) as [L HL].
      { exists L. split.
        - revert HL. generalize (projT1 (f x)). induction L; cbn in *; intros.
          + destruct l; cbn in *; inversion HL. econstructor.
          + destruct l; cbn in *; inversion HL. subst. econstructor.
            eapply reflects_iff; eauto.
            eauto.
        - eapply Hf in HL.
          unfold reflects in *.
          destruct b; try firstorder congruence.
          cbn in *.
          rewrite HL in H.
          destruct truthtables.eval_tt; firstorder congruence.
      }
      clear - dq.
      induction (projT1 (f x)).
      * exists []. econstructor.
      * destruct IHl as [L IH].
        destruct (dq a) as [Ha | Ha].
        -- exists (true :: L). econstructor; eauto.
           firstorder congruence.
        -- exists (false :: L). econstructor; eauto.
           firstorder congruence.
    + clear dq. intros (L & IL & HL).
      eapply reflects_iff. unfold reflects. unfold reflects in *.
      rewrite Hf, <- HL.
      reflexivity.
      eapply Forall2_fmap_r, Forall2_flip, Forall2_impl. eauto.
      intros. cbn in *. destruct y; firstorder congruence.
Qed.

(** The halting problem is Turing reducible to its (hypersimple) index set, distinguishing Turing reducibility from truth-table reducibility  *)

From SyntheticComputability Require Import hypersimple_construction.

Lemma non_finite_to {p : nat -> Prop} (f : nat -> nat) :
  Inj (=) (=) f ->
  ~ exhaustible p ->
  forall z, ~~ exists x, p x /\ f x >= z.
Proof.
  intros Hf Hp. intros z.
  assert (~~ exists L, forall x, In x L <-> f x < z). {
    clear - Hf.
    induction z.
    - cprove exists []. firstorder lia.
    - cunwrap. destruct IHz as (L & HL).
      ccase (exists x, f x = z) as [[x H] | H].
      + cprove exists (x :: L). cbn. intros y. rewrite HL.
        firstorder subst. lia. lia.
        ccase (f y < f x) as [H | H].
        eauto. left. eapply Hf. lia.
      + cprove exists L. intros y. rewrite HL.
        split. intros. lia.
        intros. assert (f y = z \/ f y < z) as [ | ] by lia.
        firstorder. lia.
  }
  cunwrap. destruct H as (L & HL).
  intros H. apply Hp. exists L.
  intros x Hx. eapply HL.
  cstart. intros Hfx.
  apply H. exists x. split. eauto. lia.
Qed.

Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
Proof.
  intros H x. apply H.
  induction (f x).
  - intros y. lia.
  - intros y. intros [] % le_lt_or_eq.
    + apply IHn; lia.
    + apply H. injection H0. now intros ->.
Qed.

Lemma neg_neg_least {X} p (f : X -> nat) :
  (~~ exists x, p x (f x)) -> ~~ exists x, p x (f x) /\ forall y, p y (f y) -> f x <= f y.
Proof.
  intros H. cunwrap. destruct H as (x & Hx).
  revert Hx. pattern x. eapply size_ind with (f := f). clear. intros x IH H.
  destruct (f x) eqn:E.
  - cprove exists x. split. congruence. intros. rewrite E. lia.
  - ccase (exists y, f y <= n /\ p y (f y)) as [Hf | Hf].
    + destruct Hf as (y & H1 & H2).
      eapply IH in H2. 2: lia. cunwrap.
      destruct H2 as (x' & Hx' & Hx'').
      cprove exists x'. split. eauto. firstorder.
    + cprove exists x. split. rewrite E. eauto. intros.
      cstart. intros Hx. apply Hf. exists y. split; eauto. lia.
      Unshelve. eapply nat_le_dec.
Qed.

Lemma non_finite_to_least {p : nat -> Prop} (f : nat -> nat) :
  Inj (=) (=) f ->
  ~ exhaustible p ->
  forall z, ~~ exists x, p x /\ f x >= z /\ forall y, p y /\ f y >= z -> f x <= f y.
Proof.
  intros Hf Hp. intros z.
  assert (~~ exists L, forall x, In x L <-> f x < z). {
    clear - Hf.
    induction z.
    - cprove exists []. firstorder lia.
    - cunwrap. destruct IHz as (L & HL).
      ccase (exists x, f x = z) as [[x H] | H].
      + cprove exists (x :: L). cbn. intros y. rewrite HL.
        firstorder subst. lia. lia.
        ccase (f y < f x) as [H | H].
        eauto. left. eapply Hf. lia.
      + cprove exists L. intros y. rewrite HL.
        split. intros. lia.
        intros. assert (f y = z \/ f y < z) as [ | ] by lia.
        firstorder. lia.
  }
  cunwrap. destruct H as (L & HL).
  intros H. apply Hp. exists L.
  intros x Hx. eapply HL.
  cstart. intros Hfx. eapply neg_neg_least with (p := fun x fx => p x /\ f x >= z). cprove exists x. split. eauto. lia.
  intros (x' & [] & Hx''). apply H. exists x'. split. eauto. split. eauto.
  intros ? []. eapply Hx''. firstorder.
Qed.

From SyntheticComputability Require Import reductions ReducibilityFacts EnumerabilityFacts.
From SyntheticComputability Require Import ListAutomation.

Lemma computable_Dec Q A I (P : I -> Prop) :
        (forall i, dec (P i)) -> OracleComputable (fun (R : Rel Q A) i o => reflects o (P i)).
Proof.
  intros D.
  eapply OracleComputable_ext. eapply computable_if with (test := fun i => D i).
  eapply computable_ret with (v := true). eapply computable_ret with (v := false). cbn.
  intros. destruct (D i), o; cbn; firstorder congruence.
Qed.

Section HS.
  Import  Coq.Init.Nat.

  Variable I : nat -> Prop.

  Variable E_I: nat -> nat.

  Variable E_I_injective: injective E_I.

  Variable E_I_enum: strong_enumerator E_I I.

  Variable I_undec: ~ decidable I.

  Lemma I_iff:
    ∀ z x : nat, ¬ HS E_I x → E_I x > z → I z ↔ In z (map E_I (seq 0 (x + 1))).
  Proof.
    intros z x Hcx Hxz.

    split.
    * intros [n Hn] % E_I_enum. eapply in_map_iff. eexists. split. eauto.
      eapply in_seq. split. lia. cstart. intros HH. apply Hcx. exists n. split.
      lia. lia.
    * intros (? & ? & ?) % in_map_iff. subst. eapply E_I_enum. eauto.
  Qed.

  Lemma red : DNE -> I ⪯ᴛ HS E_I.
  Proof.
    intros dne.
    exists (fun R z b => exists x, R x false /\ E_I x > z /\ (forall x', x' < x -> (R x' true \/ R x' false /\ E_I x' <= z)) /\ reflects b (In z (map E_I (seq 0 (x + 1))))).
    cbn. split.
    2:{ intros z b. cbn.
      split.
      + intros Hz. eapply dne.
        pose proof (non_finite_to_least E_I_injective (@HS_co_infinite I E_I I_undec) (z := S z)).
        cunwrap. destruct H as (x & Hcx & Hzx & Hleast). cprove exists x.
        split. eauto. split. lia. split.
        { intros. eapply dne. ccase (HS E_I x') as [Hx' | Hx']. eauto. cprove right.
          split. eauto. assert (E_I x' >= S z \/ E_I x' <= z) as [] by lia; try lia.
          exfalso. unshelve epose proof (Hleast x' _). eauto.
          assert (E_I x < E_I x' \/ E_I x = E_I x') as [] by lia.
          2: eapply E_I_injective in H2; lia.
          eapply Hx'. exists x. eauto.
        }
        eapply reflects_iff in Hz. unfold reflects in *.
        rewrite <- I_iff; eauto.
      + intros.
        destruct H as (x & Hcx & Hxz & Hle & Hb).
        setoid_rewrite reflects_iff. unfold reflects in *.
        rewrite I_iff; eauto.
    }

    eapply OracleComputable_ext.
    eapply computable_bind with (Y := nat).
    refine (computable_comp _ (nat * nat) _ _ _ _ _ _ _ _).
    2: eapply computable_search. 3: cbn.
    eapply computable_bind.
    eapply computable_precompose with (g := snd).
    eapply computable_id. 3: cbn. 
    eapply computable_Dec with (P := fun '(i, b) => (b = false /\ E_I (snd i) > ((fst i)))).
    intros []. exact _.
    eapply computable_Dec with (P := fun i => (@In nat (fst i) (@map nat nat E_I (seq 0 (snd i + 1))))).
    intros. exact _. cbn. intros.
    split.
    - intros H. decompose [ex and] H. subst.
      eapply reflects_iff in H4 as []. subst.
      eexists. split. 2: split. 3: split.
      all: eauto. intros ? ? % H3.
      decompose [ex and] H1. eapply reflects_iff in H7. destruct x0; eauto.
      right. split. eauto. lia.
    - intros. decompose [ex and] H. eexists. split. split. eexists. split. 2: eapply reflects_iff. 2: split.
      all: eauto.
      intros. eapply H2 in H3. destruct H3 as [ | []].
      + exists true. split. eauto. eapply reflects_false. clear. firstorder congruence.
      + exists false. split; eauto. eapply reflects_false. lia.
  Qed.

End HS.

End part.

Notation "P ⪯ᴛ Q" := (red_Turing P Q) (at level 50).
