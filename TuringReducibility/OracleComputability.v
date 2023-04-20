From SyntheticComputability Require Import partial.
From stdpp Require Import list.

Section part.

Context {Part : partiality}.

(** ** Tactics to deal with partial functions *)

Ltac decomp x :=
  let x1 := fresh "x" in
  let x2 := fresh "x" in
  try match type of x with
    | prod ?A ?B => destruct x as [x1 x2]; decomp x1; decomp x2
    end.

Ltac next :=
  (try now eauto);
  match goal with
  | [ H : bind ?x ?f =! ?v |- _ ] =>
      let x := fresh "x" in
      eapply bind_hasvalue in H as (x & ? & ?);
      decomp x
  | [ H : ret ?x =! ?v |- _ ] =>
      eapply ret_hasvalue_inv in H;
      inversion H;
      subst;
      clear H
  | [ H : context [ match ?l ++ [_] with nil => _ | _ :: _ => _  end ] |- _ ] => destruct l; cbn in *
  | [ H : ?l ++ [_] = nil |- _] => destruct l; cbn in *; congruence
  | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst; clear H
  | [ H : undef =! _ |- _ ] => eapply undef_hasvalue in H; tauto
  end.

Ltac simpl_assms :=
  repeat next.

Ltac simpl_goal :=
  try (progress (setoid_rewrite bind_hasvalue + eapply ret_hasvalue);
       repeat (setoid_rewrite bind_hasvalue + eexists + eapply ret_hasvalue));
  eauto.

Ltac psimpl := repeat progress (cbn; simpl_assms; simpl_goal).

(** ** Extensional dialogue trees *)

Definition tree  (Q A O : Type) := (list (Q * A)) ↛ (Q + O).

Notation Ask q := (inl q).
Notation Output o := (inr o).

Inductive interrogation {Q A O : Type} (τ : tree Q A O) (R : FunRel Q A) : list Q -> list A -> Prop :=
    qNoQuestions : interrogation τ R [] []
  | Interrogate : forall (qs : list Q) (ans : list A) (q : Q) (a : A),
                     interrogation τ R qs ans -> τ (zip qs ans) =! Ask q -> R q a -> interrogation τ R (qs ++ [q]) (ans ++ [a]).

(** ** Oracle Functionals and Turing Reducibility *)

Definition Functional Q A I O := FunRel Q A -> FunRel I O.

Definition OracleComputable {Q A I O} (r : FunRel Q A -> I -> O -> Prop) :=
  exists τ : I -> tree Q A O, forall R x o, r R x o <-> exists qs ans, interrogation (τ x) R qs ans /\ τ x (zip qs ans) =! Output o.

Definition char_rel {X} (p : X -> Prop) : FunRel X bool.
  exists (fun x b => if (b : bool) then p x else ~ p x).
  abstract (intros ? [] [] ? ?; firstorder congruence).
Defined.

Definition red_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :=
  exists r : Functional Y bool X bool, OracleComputable r /\ forall x b, char_rel p x b <-> r (char_rel q) x b. 

(** ** Lemmas about extensional dialogue trees  *)

Lemma interrogation_length  {Q A O : Type} {tau f qs ans} :
  @interrogation Q A O tau f qs ans -> length qs = length ans.
Proof.
  induction 1; try reflexivity. now rewrite !app_length, IHinterrogation. 
Qed.

Definition etree E Q A O := E -> list A ↛ (E * Q + O).

Inductive einterrogation {E Q A O} (τ : etree E Q A O) (f : Q -> A -> Prop) : list Q -> list A -> E -> E -> Prop :=
| eNoQuestions e : einterrogation τ f [] [] e e
| einterrogate qs ans q a e1 e1' e2 : einterrogation τ f qs ans e1 e1' ->
                                      τ e1' ans =! inl (e2, q) ->
                                      f q a ->
                                      einterrogation τ f (qs ++ [q]) (ans ++ [a]) e1 e2.

Definition eOracleComputable {Q A I O} (r : FunRel Q A -> I -> O -> Prop) :=
  exists E, exists e : E, exists τ : I -> etree E Q A O, forall R x o, r R x o <-> exists qs ans e', einterrogation (τ x) R qs ans e e' /\ τ x e' ans =! Output o.

Lemma bind_hasvalue_given :
  ∀ {Part : partial.partiality} [A B : Type] (x : part A) (f : A ↛ B) (b : B) a,
    x=! a -> bind (B:=B) x f =! b ↔ f a =! b.
Proof.
  intros; split; intros.
  - psimpl. replace a with x0; eauto.
    eapply hasvalue_det; eauto.
  - psimpl.
Qed.


Fixpoint allqs {Q A O} (τ : (list (Q * A)) ↛ (Q + O)) (acc : list (Q * A)) (l : list A) : part (Q + O) :=
  match l with
  | [] => τ acc
  | a :: l =>  bind (τ acc) (fun q => match q with inl q => allqs τ (acc ++ [(q,a)]) l | inr o => ret (inr o) end)
  end.

Lemma zip_nil_left {X Y} {l : list X} :
  zip l (@nil Y) = nil.
Proof.
  destruct l; reflexivity.
Qed.

Lemma unzip_nil_ {Q A O} (tau : tree Q A O) acc qs ans x :
  (forall k q a, nth_error (acc ++ zip qs ans) k = Some (q, a) -> tau (take k (acc ++ zip qs ans)) =! (inl q)) ->
  length qs = length ans ->
  allqs tau acc ans =! x <-> tau (acc ++ zip qs ans) =! x.
Proof.
  intros Hacc Hlen.
  induction ans in acc, qs, Hacc, Hlen |- *; cbn.
  - rewrite zip_nil_left, app_nil_r. reflexivity.
  - cbn.
    destruct qs as [ | q qs _ ]. { destruct ans; cbn in Hlen; congruence. }
    cbn.
    replace (acc ++ (q, a) :: zip qs ans) with ((acc ++ [(q, a)]) ++ zip qs ans).
    2:{ now rewrite <- !app_assoc. }
    rewrite <- IHans.
    3:{ cbn in *; lia. }
    + specialize (Hacc (length acc) q a).
      rewrite take_app in Hacc.
      rewrite bind_hasvalue_given.
      2:{ eapply Hacc. cbn. rewrite nth_error_app2. 2: lia.
          now rewrite minus_diag. }
      cbn. reflexivity.
    + intros. cbn in Hacc.
      rewrite <- app_assoc in H |- *. cbn. eapply Hacc.
      exact H.
Qed.

Lemma unzip_nil {Q A O} (tau : tree Q A O) f qs ans x :
  interrogation tau f qs ans ->
  allqs tau [] ans =! x <-> tau (zip qs ans) =! x.
Proof.
  intros.
  apply unzip_nil_ with (qs := qs) (acc := []).
  - cbn. induction H; intros.
    + cbn. destruct k; cbn in *; congruence.
    + replace (zip (qs ++ [q]) (ans ++ [a])) with (zip qs ans ++ [(q,a)]) in *.
      2:{ rewrite zip_with_app. reflexivity. eapply interrogation_length; eauto. }
      assert (length (zip qs ans) = length qs) as Hlen1. { eapply zip_with_length_l_eq, interrogation_length; eauto. }
      assert (length (zip qs ans) = length ans) as Hlen2. { eapply interrogation_length in H. lia. }
      assert (k < length ans \/ k = length ans) as [Hl | Hl].
      { pose proof (nth_error_Some (zip qs ans ++ [(q, a)]) k) as [HH _].
        rewrite H2 in HH. unshelve epose proof (HH _). congruence.
        rewrite app_length in H3. cbn in *. lia. }
      * rewrite nth_error_app1 in H2. 2: lia.
        eapply IHinterrogation in H2.
        rewrite take_app_le. 2: lia.
        eauto.
      * subst.
        rewrite <- Hlen2.
        rewrite nth_error_app2 in H2. 2: lia.
        rewrite Hlen2, minus_diag in H2. cbn in H2. inversion H2; subst; clear H2.
        rewrite take_app. eauto.
  - eapply interrogation_length; eauto.
Qed.

Inductive noqinterrogation {Q A O} (τ : (list A) ↛ (Q + O)) (f : Q -> A -> Prop) : list Q -> list A -> Prop :=
| noqNoQuestions : noqinterrogation τ f [] []
| noqinterrogate qs ans q a : noqinterrogation τ f qs ans ->
                           τ ans =! inl q ->
                           f q a ->
                           noqinterrogation τ f (qs ++ [q]) (ans ++ [a]).

Fixpoint allqse {E Q A O} (τ : etree E Q A O) e (acc : list A) (l : list A) : part (E * Q + O) :=
  match l with
    [] => τ e acc
  | a :: l =>  bind (τ e acc) (fun q => match q with inl (e'', q) => allqse τ e'' (acc ++ [a]) l | inr o => ret (inr o) end)
  end.

Lemma unzip_nil_e_ {E A Q O} (tau : etree E A Q O) acc (es : list E) ans x e e' :
  (forall k e e' a, nth_error es k = Some e ->
               nth_error es (S k) = Some e' ->
               nth_error (acc ++ ans) k = Some a ->
               exists q, tau e (take k (acc ++ ans)) =! (inl (e', q))) ->
  length es = 1 + length acc + length ans ->
  nth_error es (length acc) = Some e ->
  nth_error es (length acc + length ans) = Some e' ->
  allqse tau e acc ans =! x <-> tau e' (acc ++ ans) =! x.
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
  allqse tau e [] ans =! x <-> tau e' ans =! x.
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

Definition noqOracleComputable {Q A I O} (r : FunRel Q A -> I -> O -> Prop) :=
  exists τ : I -> (list A) ↛ (Q + O), forall R x o, r R x o <-> exists qs ans, noqinterrogation (τ x) R qs ans /\ τ x ans =! Output o.

Lemma helper {X} (P1 P2 : X -> Prop) :
  (forall x, P1 x <-> P2 x) ->
  (exists x, P1 x) <-> (exists x, P2 x).
Proof.
  firstorder; do 2 eexists; eapply H; eauto.
Qed.

Lemma noqinterrogation_length {Q A O} {tau f qs ans} :
  @noqinterrogation Q A O tau f qs ans -> length qs = length ans.
Proof.
  induction 1; try reflexivity. now rewrite !app_length, IHnoqinterrogation. 
Qed.

Lemma noqOracleComputable_equiv {Q A I O} F :
  OracleComputable F <-> @noqOracleComputable Q A I O F.
Proof.
  split.
  - intros [tau Ht]. exists (fun i l => allqs (tau i) [] l). intros f i o.
    rewrite Ht. apply helper. intros qs. apply helper. intros ans. split; intros [H1 H2]; split.
    + clear H2. induction H1; constructor; trivial. eapply unzip_nil; eassumption. 
    + cbn in H2. eapply unzip_nil; eauto.       
    + clear H2. induction H1; constructor; trivial. eapply unzip_nil in H; eauto.
    + eapply unzip_nil in H2; eauto.
      instantiate (1 := f).
      clear - H1. induction H1.
      * econstructor.
      * econstructor; eauto. eapply unzip_nil; eauto.
  - intros [tau Ht]. exists (fun i l => tau i (map snd l)). intros f i o.
    rewrite Ht. apply helper. intros qs. apply helper. intros ans. symmetry. split; intros [H1 H2]; split.
    + clear H2. induction H1; constructor; trivial.
      rewrite snd_zip in H; trivial. now rewrite (interrogation_length H1).
    + rewrite snd_zip in H2; trivial. now rewrite (interrogation_length H1).
    + clear H2. induction H1; constructor; trivial.
      rewrite snd_zip; trivial. now rewrite (noqinterrogation_length H1).
    + rewrite snd_zip; trivial. now rewrite (noqinterrogation_length H1).
Qed.  

Lemma eOracleComputable_equiv {Q A I O} R :
  eOracleComputable R <-> @OracleComputable Q A I O R.
Proof.
  rewrite noqOracleComputable_equiv.
  split.
  - intros (E & e & tau & Ht). exists (fun i l => bind (allqse (tau i) e [] l) (fun x => match x with inl (_, q) => ret (inl q) | inr o => ret (inr o) end)).
    intros f i o.
    rewrite Ht. apply helper. intros qs. apply helper. intros ans. symmetry. split.
    + intros [H1 H2].
      assert (∃ e' : E, einterrogation (tau i) f qs ans e e').
      { clear H2. induction H1.
        - eexists. econstructor.
        - psimpl. destruct x as [ [] | ]; psimpl. 
          destruct IHnoqinterrogation. eexists. econstructor; eauto. eapply unzip_nil_e; eauto.
      }
      destruct H as (e' & H). exists e'. split; eauto.
      psimpl. destruct x as [ [] | ]; psimpl. eapply unzip_nil_e; eauto.
    + intros (e' & H1 & H2). split.
      * clear H2. induction H1; constructor; trivial. eapply unzip_nil_e in H; eauto.
        psimpl. eapply unzip_nil_e; eauto. cbn. psimpl.
      * psimpl. eapply unzip_nil_e; eauto. cbn. psimpl.
  - intros [tau Ht]. exists unit, tt, (fun i e l => bind (tau i l) (fun x => match x with inl q => ret (inl (tt, q)) | inr o => ret (inr o) end)). intros f i o.
    rewrite Ht. apply helper. intros qs. apply helper. intros ans. firstorder.
    + exists tt. split.
      * clear - H. induction H; econstructor; eauto.
        psimpl. 
      * psimpl.
    + clear - H. induction H; econstructor; eauto.
      psimpl. destruct x; psimpl.
    + psimpl; destruct x0; psimpl.

Qed.

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

Definition sOracleComputable {Q A I O} (r : FunRel Q A -> I -> O -> Prop) :=
  exists E, exists e : E, exists τ : I -> stree E Q A O, forall R x o, r R x o <-> exists qs ans e', sinterrogation (τ x) R qs ans e e' /\ τ x e' ans =! Output o.

Lemma sOracleComputable_equiv Q A I O F :
  sOracleComputable F -> @eOracleComputable Q A I O F.
Proof.
  intros (E & e & tau & Ht). exists E. exists e.
  pose (t := fun i e l => bind (mu (fun n => bind (iterate (fun e => tau i e l) n e) (fun x => match x with Some _ => ret true | _ => ret false end)))
                         (fun n => bind (iterate (fun e => tau i e l) n e)
                                  (fun x => match x with Some (inl (e, Some q)) => ret (inl (e, q))
                                                 | Some (inr o) => ret (inr o)
                                                 | _ => undef
                                         end))).
  exists t.
  intros f i o.
  rewrite Ht. clear Ht. do 2 (eapply helper; intros). rename x into qs, x0 into ans.
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

(** ** Lemmas about Turing reducibility *)

(* Lemma mkTuring {X Y} {p : X -> Prop} {q : Y -> Prop} (r : FunRel Y bool -> FunRel X bool) (τ : X -> tree Y bool bool) : *)
(*   (forall R x b, r R x b <-> exists qs ans, interrogation (τ x) R qs ans /\ τ x (zip qs ans) =! inr b) -> *)
(* char_rel p = r (char_rel q).  *)
(*   red_Turing p q. *)
(* Proof. *)
(*   intros Hcont Hpq. *)
(*   exists r. split. exists τ. all: eauto. *)
(* Qed. *)

Lemma computable_precompose A Q I O I' F g :
  @OracleComputable A Q I O F ->
  @OracleComputable A Q I' O (fun r x => F r (g x)).
Proof using.
  intros [tau H].
  exists (fun i l => tau (g i) l). intros. eapply H.
Qed.

Lemma computable_id {X Y} :
  OracleComputable (fun R : FunRel X Y => R).
Proof.
  exists (fun i l => match l with [] => ret (inl i) | (_, b) :: _ => ret (inr b) end).
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

Lemma computable_comp A X  Q Y I O (F1 : FunRel Q A -> FunRel X Y) (F2 : FunRel X Y -> FunRel I O) :
  OracleComputable F1
  -> OracleComputable F2
  -> OracleComputable (fun r x => F2 (F1 r) x).
Proof.
  intros [t1 H1] % noqOracleComputable_equiv [t2 H2] % noqOracleComputable_equiv.
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
    enough (noqinterrogation (t2 i) (F1 f) (map fst ans') (map snd ans')).
    firstorder. clear H.
    enough (forall h, sinterrogation (t i) f qs ans ([], None) h ->
                 (noqinterrogation (t2 i) (F1 f) (map fst (fst h))) (map snd (fst h)) /\
                   match snd h with
                     None => True
                   | Some (x, n) => t2 i (map snd (fst h)) =! inl x /\ noqinterrogation (t1 x) f (lastn n qs) (lastn n ans)
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
        firstorder. econstructor; eauto. 
      * psimpl. destruct x; psimpl.
  - intros (xs & ys & Hint & Hend).
    rename x into i. rename R into f.
    enough (∃ (qs : list Q) (ans : list A), sinterrogation (t i) f qs ans ([], None) (zip xs ys, None)).
    { firstorder. exists x, x0. eexists. split. eauto. cbn. psimpl.
      rewrite snd_zip. eauto. eapply noqinterrogation_length in Hint. lia.
      cbn. psimpl. }
    clear Hend. induction Hint; cbn.
    + exists [], []. econstructor.
    + rename qs into xs. rename ans into ys.
      destruct IHHint as (qs & ans & IH).
      rewrite zip_with_app. 2: eapply noqinterrogation_length; eauto.
      eapply H1 in H0 as (qs' & ans' & Hint' & Hend'). cbn.
      exists (qs ++ qs'), (ans ++ ans').
      assert (sinterrogation (t i) f qs ans  ([], None) (zip xs ys, Some (q, 0))).
      { econstructor 2. eauto. cbn. psimpl. rewrite snd_zip. eauto.
        eapply noqinterrogation_length in Hint; lia. cbn.
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

Lemma OracleComputable_ext Q A I O F F' :
  @OracleComputable Q A I O F ->
  (forall R i o, F R i o <-> F' R i o) ->
  @OracleComputable Q A I O F'.
Proof.
  intros [tau H] He. exists tau.
  intros. now rewrite <- H, He.
Qed.

Lemma interrogation_ext {Q A O} τ τ' (f f' : FunRel Q A) q a :
  (forall l v, τ l =! v <-> τ' l =! v) ->
  (forall q a, f q a <-> f' q a) ->
  interrogation τ f q a <-> @interrogation Q A O τ' f' q a.
Proof.
  enough (forall τ τ' (f f' : FunRel Q A) q a,
             (forall l v, τ l =! v <-> τ' l =! v) ->
             (forall q a, f q a <-> f' q a) ->
             interrogation τ f q a -> @interrogation Q A O τ' f' q a).
  { split; eapply H; firstorder. }
  clear. intros ? ? ? ? ? ? Heq ?.
  induction 1; econstructor; eauto.
  all: firstorder.
Qed.

Lemma OracleComputable_extensional {Q A I O F} {R R' : FunRel Q A} :
  @OracleComputable Q A I O F ->
  (forall q a, R q a <-> R' q a) ->
  forall i o, F R i o <-> F R' i o.
Proof.
  intros [tau H] He.
  intros. rewrite !H.
  eapply helper. intros qs. eapply helper. intros ans.
  erewrite interrogation_ext. reflexivity. reflexivity. firstorder.
Qed.

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
  @noqinterrogation Q A O τ (fun x y => f x =! y) l lv ->
  evalt (fun l' => τ (lv ++ l')) f n =! v2 ->
  evalt τ f (length l + n) =! v2.
Proof.
  intros H. induction H in n |- *.
  - cbn. eauto.
  - intros. cbn in H2.
    cbn -[evalt]. rewrite app_length. cbn -[evalt].
    replace (length qs + 1 + n) with (length qs + (S n)) by lia.
    eapply IHnoqinterrogation.
    cbn. psimpl. rewrite app_nil_r. eassumption.
    cbn. psimpl. eapply evalt_ext; eauto.
    cbn. intros. now rewrite <- app_assoc.
Qed.

Lemma noqinterrogation_cons {Q A O} q1 q2 a1 a2 τ (f : Q -> A -> Prop) :
  τ [] =! inl q1 ->
  f q1 a1 ->
  @noqinterrogation Q A O (fun l => τ (a1 :: l)) f q2 a2 ->
  noqinterrogation τ f (q1 :: q2) (a1 :: a2).
Proof.
  intros H1 H2.
  induction q2 in a1, a2, H1, H2 |- * using rev_ind.
  - inversion 1; subst.
    + eapply noqinterrogate with (qs := []) (ans := []). econstructor. eauto. eauto.
    + destruct qs; cbn in *; congruence.
  - inversion 1.
    + destruct q2; cbn in *; congruence.
    + subst. assert (qs = q2 /\ q = x) as [<- <-].
      { eapply app_inj_2 in H0. 2: reflexivity. firstorder congruence. }
      replace (q1 :: qs ++ [q]) with ((q1 :: qs) ++ [q]) by reflexivity.
      replace (a1 :: ans ++ [a]) with ((a1 :: ans) ++ [a]) by reflexivity.
      econstructor. eapply IHq2; eauto. eauto. eauto.
Qed.

Lemma noqinterrogation_ext {Q A O} τ τ' (f f' : Q -> A -> Prop) q a :
  (forall l v, τ l =! v <-> τ' l =! v) ->
  (forall q a, f q a <-> f' q a) ->
  noqinterrogation τ f q a <-> @noqinterrogation Q A O τ' f' q a.
Proof.
  enough (forall τ τ' (f f' : Q -> A -> Prop) q a,
             (forall l v, τ l =! v <-> τ' l =! v) ->
             (forall q a, f q a <-> f' q a) ->
             noqinterrogation τ f q a -> @noqinterrogation Q A O τ' f' q a).
  { split; eapply H; firstorder. }
  clear. intros ? ? ? ? ? ? Heq ?.
  induction 1; econstructor; eauto.
  all: firstorder.
Qed.

Lemma noqinterrogation_app {Q A O} q1 q2 a1 a2 τ f :
  @noqinterrogation Q A O τ f q1 a1 ->
  noqinterrogation (fun l => τ (a1 ++ l)) f q2 a2 ->
  noqinterrogation τ f (q1 ++ q2) (a1 ++ a2).
Proof.
  induction 1 in q2, a2 |- *; cbn.
  - eauto.
  - intros. rewrite <- !app_assoc.
    eapply IHnoqinterrogation.
    eapply noqinterrogation_cons.
    + now rewrite app_nil_r.
    + eauto.
    + eapply noqinterrogation_ext; eauto. cbn. intros. now rewrite <- app_assoc.
Qed.

Lemma noqinterrogation_equiv_evalt Q A I O :
  forall (τ : I -> list A ↛ (Q + O)) (f : Q ↛ A) (i : I) (o : O),
    (exists (qs : list Q) (ans : list A), noqinterrogation (τ i) (fun x y => f x =! y) qs ans /\ τ i ans =! inr o) <-> (exists n : nat, evalt (τ i) f n =! inr o).
Proof.
  intros τ f i o. split.
  + intros (qs & ans & Hi & Hout).
    exists (length qs + 1). eapply interrogation_plus; eauto.
    cbn. rewrite app_nil_r. psimpl.
  + intros [n H]. induction n in τ, H |- *.
    * cbn in *. psimpl. destruct x; psimpl.
      exists [], []. split. econstructor. eauto.
    * cbn in *. psimpl. destruct x; psimpl.
      -- eapply (IHn (fun i l => τ i (x :: l))) in H1 as (qs & ans & H1 & H2).
         exists (q :: qs), (x :: ans). split; eauto.
         eapply noqinterrogation_app with (q1 := [q]) (a1 := [x]).
         eapply noqinterrogate with (qs := []) (ans := []); eauto.
         econstructor. eauto. 
      -- exists [], []. split. econstructor. eauto.
Qed.

(** ** Central results regarding Turing reducibility *)

Notation "P ⪯ᴛ Q" := (red_Turing P Q) (at level 50).

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
  - eapply computable_comp; eauto.
  - intros. rewrite H1.
    eapply (OracleComputable_extensional Hr1).
    firstorder.
Qed.

Lemma Turing_transports_computable {Q A I O} F :
  @OracleComputable Q A I O F ->
  exists F', forall f R, pcomputes f (the_rel R) -> pcomputes (F' f) (F R).
Proof.
  intros [tau H] % noqOracleComputable_equiv.
  exists (fun f i => bind (mu (fun n => bind (evalt (tau i) f n) (fun res => match res with inl _ => ret false | inr _ => ret true end))) (fun n => bind (evalt (tau i) f n) (fun res => match res with inl _ => undef | inr o => ret o end))).
  intros f R HfR. unfold pcomputes in *. intros.
  rewrite H.
  setoid_rewrite noqinterrogation_ext.
  2: reflexivity. 2:{ intros. split. intros hf % HfR. eapply hf. firstorder. }
  setoid_rewrite noqinterrogation_equiv_evalt.
  rewrite !bind_hasvalue. split.
  - intros (? & ? & ?). simpl_assms. destruct x1; simpl_assms.
  - intros (n & Hn). 
    edestruct mu_ter.
    2:{ exists x0. split. eauto.
        eapply mu_hasvalue in H0 as [].
        simpl_assms. destruct x1; psimpl.
        eapply ret_hasvalue_iff. admit.
    }
    exists n. split. psimpl. admit.
Admitted.

From SyntheticComputability Require Import DecidabilityFacts principles Pigeonhole.

Definition char_rel_fun {X Y} (f : X -> Y) :=
  (@Build_FunRel _ _(fun x b => f x = b) ltac:(firstorder congruence)).

Lemma partial_total X Y (f : X ↛ Y) :
  (forall x, (ter (f x))) -> ∑ g : X -> Y, forall x, f x =! g x.
Proof.
  intros H. unshelve eexists.
  - intros x. specialize (H x). exact (eval H).
  - intros x. cbn. eapply eval_hasvalue.
Qed.

Lemma partial_decidable {X} (p : X -> Prop) (f : X ↛ bool) :
  (forall x, ter (f x)) -> (forall x, f x =! true <-> p x) -> decidable p.
Proof.
  intros Hter He.
  destruct (partial_total _ _ _ Hter) as [g Hg].
  exists g. intros x. red. rewrite <- He. specialize (Hg x).
  destruct (g x); firstorder. eapply hasvalue_det; eauto.
Qed.

Lemma pcomputes_decider {X} f (R : FunRel X bool) :
  pcomputes f R -> (forall x, ter (f x)) -> decidable (fun x => R x true).
Proof.
  intros Hf HR.
  eapply partial_decidable with (f := f).
  - intros x. eauto. 
  - intros x. split.
    + intros H. now eapply Hf.
    + intros H. destruct (HR x) as [b Hb].
      enough (b = true) by congruence.
      eapply Hf in Hb. eapply R; eauto.
Qed.

Goal forall X Y (p : X -> Prop) (q : Y -> Prop),
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
  + eapply pcomputes_decider. eapply hF'.
    intros. eapply (MP_to_MP_partial mp). intros Hx.
    ccase (p x) as [Hp | Hp].
    -- eapply Hx. exists true. eapply hF'. now eapply (H _ true).
    -- eapply Hx. exists false. eapply hF'. now eapply (H _ false).
Qed.
