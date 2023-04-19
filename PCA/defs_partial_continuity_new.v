From SyntheticComputability.Shared Require Import embed_nat.

From SyntheticComputability Require Import partial.
Require Import Setoid.

Require Import List Lia.
Import ListNotations EmbedNatNotations.

From stdpp Require Import list.

Section Continuity.

  Ltac decomp x :=
    let x1 := fresh "x" in
    let x2 := fresh "x" in
    try match type of x with
      (* | sum ?A ?B => destruct x as [x1 | x2]; decomp x1; decomp x2 *)
      | prod ?A ?B => destruct x as [x1 x2]; decomp x1; decomp x2
      end.

  Ltac next :=
    (* unfold beta, eta in *; *)
    (try now eauto);
    match goal with
    (* | [ H : exists n, evalt _ _ _ _ _ _ =! _ |- _ ] => destruct H *)
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
                                                             (* | [ H : evalt _ _ _ _ _ ?n =! _ |- _ ] => destruct n; cbn in * *)
    end.

  (* Notation "'beta'" := (@beta _ nat nat nat) (at level 10). *)

  Ltac simpl_assms :=
    repeat next.

  Ltac simpl_goal :=
    try (progress (setoid_rewrite bind_hasvalue + eapply ret_hasvalue);
    repeat (setoid_rewrite bind_hasvalue + eexists + eapply ret_hasvalue));
    eauto.

  Ltac psimpl := repeat progress (cbn; simpl_assms; simpl_goal).

  Context {Part : partiality}.
  Variables A Q I O : Type.

  Notation tree := (list A ↛ (Q + O)).

  Fixpoint evalt (τ : tree) (f : Q ↛ A) (n : nat) : part (Q + O) :=
    bind (τ []) (fun x =>
                   match n, x with
                   | 0, inl q => ret (inl q)
                   | S n, inl q => bind (f q) (fun a => evalt (fun l => τ (a :: l)) f n)
                   | _, inr o => ret (inr o)
                   end).

  Lemma evalt_ext τ τ' f n v :
    (forall l v, τ l =! v <-> τ' l =! v) ->
    evalt τ f n =! v <-> evalt τ' f n =! v.
  Proof.
    enough (forall τ τ' f n v,
               (forall l v, τ l =! v <-> τ' l =! v) ->
               evalt τ f n =! v -> evalt τ' f n =! v).
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

  Inductive interrogation (τ : (list A) ↛ (Q + O)) f : list Q -> list A -> Prop :=
  | NoQuestions : interrogation τ f [] []
  | interrogate qs ans q a : interrogation τ f qs ans ->
                             τ ans =! inl q ->
                             f q =! a ->
                             interrogation τ f (qs ++ [q]) (ans ++ [a]).

  (* qtrees remember the list of questions asked *)

  Definition qtree := list (Q * A) ↛ (Q + O).

  Inductive qinterrogation (τ : qtree) f : list Q -> list A -> Prop :=
  | qNoQuestions : qinterrogation τ f [] []
  | qinterrogate qs ans q a : qinterrogation τ f qs ans ->
                                       τ (zip_with pair qs ans) =! inl q ->
                                       f q =! a ->
                                       qinterrogation τ f (qs ++ [q]) (ans ++ [a]).

  (* etrees can thread extra information around *)

  Definition etree E := E -> list A ↛ (E * Q + O).

  Inductive einterrogation {E} (τ : etree E) f : list Q -> list A -> E -> E -> Prop :=
  | eNoQuestions e : einterrogation τ f [] [] e e
  | einterrogate qs ans q a e1 e1' e2 : einterrogation τ f qs ans e1 e1' ->
                                       τ e1' ans =! inl (e2, q) ->
                                       f q =! a ->
                                       einterrogation τ f (qs ++ [q]) (ans ++ [a]) e1 e2.

  (* strees can, in addition to carrying extra information like etrees, stall an interrogation and just update the extra information rather than asking a question *)

  Definition stree E := E -> list A ↛ (E * option Q + O).

  Inductive sinterrogation {E} (τ : stree E) f : list Q -> list A -> E -> E -> Prop :=
  | sNoQuestions e : sinterrogation τ f [] [] e e
  | stall qs ans e1 e1' e2 : sinterrogation τ f qs ans e1 e1' ->
                         τ e1' ans =! inl (e2, None) ->
                         sinterrogation τ f qs ans e1 e2
  | sinterrogate qs ans q a e1 e1' e2 : sinterrogation τ f qs ans e1 e1' ->
                                       τ e1' ans =! inl (e2, Some q) ->
                                       f q =! a ->
                                       sinterrogation τ f (qs ++ [q]) (ans ++ [a]) e1 e2.

  Lemma interrogation_ext τ τ' f q a :
    (forall l v, τ l =! v <-> τ' l =! v) ->
    interrogation τ f q a <-> interrogation τ' f q a.
  Proof.
    enough (forall τ τ' f q a,
               (forall l v, τ l =! v <-> τ' l =! v) ->
               interrogation τ f q a -> interrogation τ' f q a).
    { split; eapply H; firstorder. }
    clear. intros ? ? ? ? ? Heq.
    induction 1; econstructor; eauto.
    firstorder.
  Qed.

  Lemma interrogation_extf τ f f' q a :
    (forall l v, f l =! v <-> f' l =! v) ->
    interrogation τ f q a <-> interrogation τ f' q a.
  Proof.
    enough (forall τ f f' q a,
               (forall l v, f l =! v <-> f' l =! v) ->
               interrogation τ f q a -> interrogation τ f' q a).
    { split; eapply H; firstorder. }
    clear. intros ? ? ? ? ? Heq.
    induction 1; econstructor; eauto.
    firstorder.
  Qed.

  Lemma sinterrogation_ext {E} τ τ' f q a (e1 e2 : E) :
    (forall e l v, τ e l =! v <-> τ' e l =! v) ->
    sinterrogation τ f q a e1 e2 <-> sinterrogation τ' f q a e1 e2 .
  Proof.
    enough (forall τ τ' f q a,
                   (forall e l v, τ e l =! v <-> τ' e l =! v) ->
                   sinterrogation τ f q a e1 e2 -> sinterrogation τ' f q a e1 e2).
    { split; eapply H; firstorder. }
    clear. intros ? ? ? ? ? Heq.
    induction 1.
    - econstructor 1; eauto.
    - econstructor 2; eauto. firstorder.
    - econstructor 3; eauto. firstorder.
  Qed.

  Lemma interrogation_plus τ f n l lv v2 :
    interrogation τ f l lv ->
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

  Definition beta (q : part Q) (k : A -> tree) : tree :=
    fun l => match l with
          | [] => bind q (fun q => ret (inl q))
          | a :: l => k a l
          end.

  Definition eta (o : part O) : tree :=
    fun l => bind o (fun x => ret (inr x)).

  (* Definition 1, à la sequential continuity, i.e. extensional dialogue trees *)
  Definition continuous_via_extensional_dialogues F :=
    exists τ : I -> tree,
    forall f i o, (exists n, evalt (τ i) f n =! inr o) <-> F f i =! o.

  Definition continuous_via_interrogations F :=
    exists τ : I -> tree,
    forall f i o, (exists qs ans, interrogation (τ i) f qs ans /\ τ i ans =! inr o) <-> F f i =! o.

  Lemma continuous_via_interrogations_ext F F' :    
    continuous_via_interrogations F -> (forall f x v, F f x =! v <-> F' f x =! v) -> continuous_via_interrogations F'.
  Proof.
    intros [tau H] Hext. exists tau.
    intros. now rewrite <- Hext, <- H.
  Qed.
  
  Definition continuous_via_qinterrogations F :=
    exists τ : I -> qtree, 
    forall f i o, (exists qs ans, qinterrogation (τ i) f qs ans /\ τ i (zip_with pair qs ans) =! inr o) <-> F f i =! o.

  Definition continuous_via_einterrogations F :=
    exists E e, exists τ : I -> etree E, 
    forall f i o, (exists qs ans e', einterrogation (τ i) f qs ans e e' /\ τ i e' ans =! inr o) <-> F f i =! o.

  Definition continuous_via_sinterrogations F :=
    exists E e, exists τ : I -> stree E, 
    forall f i o, (exists qs ans e', sinterrogation (τ i) f qs ans e e' /\ τ i e' ans =! inr o) <-> F f i =! o.

  Lemma helper {X} (P1 P2 : X -> Prop) :
    (forall x, P1 x <-> P2 x) ->
    (exists x, P1 x) <-> (exists x, P2 x).
  Proof.
    firstorder; do 2 eexists; eapply H; eauto.
  Qed.

  Lemma interrogation_length {tau f qs ans} :
    interrogation tau f qs ans -> length qs = length ans.
  Proof.
    induction 1; try reflexivity. now rewrite !app_length, IHinterrogation. 
  Qed.
 
  Lemma qinterrogation_length {tau f qs ans} :
    qinterrogation tau f qs ans -> length qs = length ans.
  Proof.
    induction 1; try reflexivity. now rewrite !app_length, IHqinterrogation. 
  Qed.

  Lemma sinterrogation_length {E} {tau f qs ans} {e e' : E} :
    sinterrogation tau f qs ans e e' -> length qs = length ans.
  Proof.
    induction 1; try reflexivity. eauto.
    now rewrite !app_length, IHsinterrogation. 
  Qed.

  Fixpoint allqs (τ : (list (Q * A)) ↛ (Q + O)) (acc : list (Q * A)) (l : list A) : part (Q + O) :=
    match l with
    | [] => τ acc
    | a :: l =>  bind (τ acc) (fun q => match q with inl q => allqs τ (acc ++ [(q,a)]) l | inr o => ret (inr o) end)
    end.

  Lemma zip_nil_left {X Y} {l : list X} :
    zip l (@nil Y) = nil.
  Proof.
    destruct l; reflexivity.
  Qed.

  Lemma bind_hasvalue_given :
    ∀ {Part : partial.partiality} [A B : Type] (x : part A) (f : A ↛ B) (b : B) a,
      x=! a -> bind (B:=B) x f =! b ↔ f a =! b.
  Proof.
    intros; split; intros.
    - psimpl. replace a with x0; eauto.
      eapply hasvalue_det; eauto.
    - psimpl.
  Qed.

  Lemma unzip_nil_ (tau : qtree) acc qs ans x :
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

  Lemma unzip_nil (tau : qtree) f qs ans x :
    qinterrogation tau f qs ans ->
    allqs tau [] ans =! x <-> tau (zip qs ans) =! x.
  Proof.
    intros.
    apply unzip_nil_ with (qs := qs).
    - cbn. induction H; intros.
      + cbn. destruct k; cbn in *; congruence.
      + replace (zip (qs ++ [q]) (ans ++ [a])) with (zip qs ans ++ [(q,a)]) in *.
        2:{ rewrite zip_with_app. reflexivity. eapply qinterrogation_length; eauto. }
        assert (length (zip qs ans) = length qs) as Hlen1. { eapply zip_with_length_l_eq, qinterrogation_length; eauto. }
        assert (length (zip qs ans) = length ans) as Hlen2. { eapply qinterrogation_length in H. lia. }
        assert (k < length ans \/ k = length ans) as [Hl | Hl].
        { pose proof (nth_error_Some (zip qs ans ++ [(q, a)]) k) as [HH _].
          rewrite H2 in HH. unshelve epose proof (HH _). congruence.
          rewrite app_length in H3. cbn in *. lia. }
        * rewrite nth_error_app1 in H2. 2: lia.
          eapply IHqinterrogation in H2.
          rewrite take_app_le. 2: lia.
          eauto.
        * subst.
          rewrite <- Hlen2.
          rewrite nth_error_app2 in H2. 2: lia.
          rewrite Hlen2, minus_diag in H2. cbn in H2. inversion H2; subst; clear H2.
          rewrite take_app. eauto.
    - eapply qinterrogation_length; eauto.
  Qed.

  Lemma continuous_via_qinterrogations_equiv F :
    continuous_via_qinterrogations F <-> continuous_via_interrogations F.
  Proof.
    split.
    - intros [tau Ht]. exists (fun i l => allqs (tau i) [] l). intros f i o.
      rewrite <- Ht. apply helper. intros qs. apply helper. intros ans. split; intros [H1 H2]; split.
      + clear H2. induction H1; constructor; trivial. eapply unzip_nil; eassumption. 
      + cbn in H2. eapply unzip_nil; eauto. instantiate (1 := f).
        clear - H1. induction H1.
        * econstructor.
        * econstructor; eauto. eapply unzip_nil; eauto.
      + clear H2. induction H1; constructor; trivial. eapply unzip_nil in H; eauto.
      + eapply unzip_nil in H2; eauto.
    - intros [tau Ht]. exists (fun i l => tau i (map snd l)). intros f i o.
      rewrite <- Ht. apply helper. intros qs. apply helper. intros ans. split; intros [H1 H2]; split.
      + clear H2. induction H1; constructor; trivial.
        rewrite snd_zip in H; trivial. now rewrite (qinterrogation_length H1).
      + rewrite snd_zip in H2; trivial. now rewrite (qinterrogation_length H1).
      + clear H2. induction H1; constructor; trivial.
        rewrite snd_zip; trivial. now rewrite (interrogation_length H1).
      + rewrite snd_zip; trivial. now rewrite (interrogation_length H1).
  Qed.  

  Lemma interrogation_cons q1 q2 a1 a2 τ f :
    τ [] =! inl q1 ->
    f q1 =! a1 ->
    interrogation (fun l => τ (a1 :: l)) f q2 a2 ->
    interrogation τ f (q1 :: q2) (a1 :: a2).
  Proof.
    intros H1 H2.
    induction q2 in a1, a2, H1, H2 |- * using rev_ind.
    - inversion 1; subst.
      + eapply (@interrogate _ _ [] []). econstructor. eauto. eauto.
      + destruct qs; cbn in *; congruence.
    - inversion 1.
      + destruct q2; cbn in *; congruence.
      + subst. assert (qs = q2 /\ q = x) as [<- <-].
        { eapply app_inj_2 in H0. 2: reflexivity. firstorder congruence. }
        replace (q1 :: qs ++ [q]) with ((q1 :: qs) ++ [q]) by reflexivity.
        replace (a1 :: ans ++ [a]) with ((a1 :: ans) ++ [a]) by reflexivity.
        econstructor. eapply IHq2; eauto. eauto. eauto.
  Qed.

  Lemma sinterrogation_cons {E} q1 q2 a1 a2 (τ : stree E) f e1 e2 e3 :
    τ e1 [] =! inl (e2, Some q1) ->
    f q1 =! a1 ->
    sinterrogation (fun e l => τ e (a1 :: l)) f q2 a2 e2 e3 ->
    sinterrogation τ f (q1 :: q2) (a1 :: a2) e1 e3.
  Proof.
    intros H1 H2 H. induction H. 
    - eapply (@sinterrogate _ _ _ [] []). econstructor. eauto. eauto.
    - econstructor 2; eauto.
    -   replace (q1 :: qs ++ [q]) with ((q1 :: qs) ++ [q]) by reflexivity.
        replace (a1 :: ans ++ [a]) with ((a1 :: ans) ++ [a]) by reflexivity.
        econstructor 3; eauto.
  Qed.

  Lemma sinterrogation_scons {E} q a (τ : stree E) f e1 e2 e3 :
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

  Lemma interrogation_app q1 q2 a1 a2 τ f :
    interrogation τ f q1 a1 ->
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

  Lemma sinterrogation_app E q1 q2 a1 a2 (τ : stree E) f e1 e2 e3 :
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

  Lemma interrogation_equiv:
    forall (τ : I -> tree) (f : Q ↛ A) (i : I) (o : O),
      (exists (qs : list Q) (ans : list A), interrogation (τ i) f qs ans /\ τ i ans =! inr o) <-> (exists n : nat, evalt (τ i) f n =! inr o).
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
           eapply interrogation_app with (q1 := [q]) (a1 := [x]).
           eapply (@interrogate _ _ [] []); eauto. econstructor.
           cbn in *. eauto.
        -- exists [], []. split. econstructor. eauto.
  Qed.

  Lemma continuous_via_interrogations_equiv F :
    continuous_via_extensional_dialogues F <-> continuous_via_interrogations F.
  Proof.
    split.
    - intros [τ H]. exists τ. intros. rewrite <- H. clear H.
      eapply interrogation_equiv.
    - intros [τ H]. exists τ. intros. rewrite <- H. clear H.
      symmetry. eapply interrogation_equiv.
  Qed.

  Fixpoint allqse {E} (τ : etree E) e (acc : list A) (l : list A) : part (E * Q + O) :=
    match l with
      [] => τ e acc
    | a :: l =>  bind (τ e acc) (fun q => match q with inl (e'', q) => allqse τ e'' (acc ++ [a]) l | inr o => ret (inr o) end)
    end.

  Lemma unzip_nil_e_ E (tau : etree E) acc (es : list E) ans x e e' :
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

  Lemma unzip_nil_e {E} (tau : etree E) f qs ans e e' x :
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
        eapply IH1 in H2; eauto.
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

  Lemma continuous_via_einterrogations_equiv F :
    continuous_via_einterrogations F <-> continuous_via_interrogations F.
  Proof.
    split.
    - intros (E & e & tau & Ht). exists (fun i l => bind (allqse (tau i) e [] l) (fun x => match x with inl (_, q) => ret (inl q) | inr o => ret (inr o) end)).
      intros f i o.
      rewrite <- Ht. apply helper. intros qs. apply helper. intros ans. split.
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
          psimpl. eapply unzip_nil_e; eauto. cbn. psimpl.
        * psimpl. eapply unzip_nil_e; eauto. cbn. psimpl.
    - intros [tau Ht]. exists unit, tt, (fun i e l => bind (tau i l) (fun x => match x with inl q => ret (inl (tt, q)) | inr o => ret (inr o) end)). intros f i o.
      rewrite <- Ht. apply helper. intros qs. apply helper. intros ans. firstorder.
      + clear - H. induction H; econstructor; eauto.
        psimpl. destruct x; psimpl.
      + psimpl; destruct x0; psimpl.
      + exists tt. split.
        * clear - H. induction H; econstructor; eauto.
          psimpl. 
        * psimpl. 
  Qed.

  Fixpoint iterate {E} (τ : E -> part (E * option Q + O)) (n : nat) (e : E) : part (option (E * option Q + O)) :=
    match n with
    | 0 => ret None
    | S n => bind (τ e) (fun res => match res with
                                | inl (e, None) => iterate τ n e
                                | x => ret (Some x)
                                end)
    end.

  Lemma helper1 {X} (P1 P2 : X -> Prop) :
    (forall x, P1 x <-> P2 x) ->
    (exists x, P1 x) <-> (exists x, P2 x).
  Proof.
    firstorder; do 2 eexists; eapply H; eauto.
  Qed.

  Lemma continuous_via_sinterrogations_equiv F :
    continuous_via_sinterrogations F -> continuous_via_einterrogations F.
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
    rewrite <- Ht. clear Ht. do 2 (eapply helper1; intros). rename x into qs, x0 into ans.
    split.
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
          eapply (sinterrogation_app _ [] _ []). 2: eauto.
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
               eapply (sinterrogation_app _ [] _ []).
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
  
  (* Definition 2, as in Niklas Mück's BSc thesis *)
  Definition continuous_f (F : (Q ↛ A) -> (I ↛ O)) :=
    forall f i o, F f i =! o -> exists L, (forall i', In i' L -> exists o', f i' =! o') /\ (forall f', (forall y b, In y L -> f y =! b -> f' y =! b) -> F f' i =! o).

  Lemma cont_to_cont F :
    continuous_via_extensional_dialogues F -> continuous_f F.
  Proof.
    intros [τ H] f i v Hv.
    setoid_rewrite <- H in Hv.
    setoid_rewrite <- H. clear - Hv.
    destruct Hv as [n H].
    revert H. generalize (@inr (Q) _ v). clear v.
    intros v H.
    enough (  exists L : list Q,
               (forall y : Q, In y L -> exists b : A, f y =! b) /\
                 (forall f' : Q ↛ A, (forall (y : Q) (b : A), In y L -> f y =! b -> f' y =! b) -> evalt (τ i) f' n =! v)) by firstorder.
    induction n in τ, v, H |- *; cbn in *.
    - exists []. split. 1: firstorder. 
      intros. cbn. eauto.
    - eapply bind_hasvalue in H as ([q | o] & H2 & H3).
      + eapply bind_hasvalue in H3 as (a & H4 & H5).
        eapply (IHn (fun i => (fun l : list A => τ i (a :: l)))) in H5 as (L & HL & H).
        exists (L ++ [q]). split.
        * intros ? ? % in_app_iff. firstorder. subst. eauto.
        * intros. eapply bind_hasvalue.
          setoid_rewrite in_app_iff in H0. eexists.
          split. 1: firstorder.
          cbn. eauto.
          eapply bind_hasvalue. eexists. split.
          eapply H0. 1: firstorder. 1: eauto.
          eauto.
      + eapply ret_hasvalue_iff in H3; subst.
        exists []. split.
        1: firstorder.
        intros. eapply bind_hasvalue.
        eexists. split. eauto. cbn. eapply ret_hasvalue.
  Qed.

  Definition modulus_function_continuous (F : (Q ↛ A) -> (I ↛ O)) :=
    exists M, 
    forall f i o, F f i =! o ->
             exists L, M f i =! L /\
                    (forall i', In i' L -> exists o', f i' =! o') /\ (forall f', (forall y b, In y L -> f y =! b -> f' y =! b) -> F f' i =! o).

  Notation "f ≺ g" := (forall x o, f x =! o -> g x =! o) (at level 30).

  Definition directed {X Y} (P : nat -> (X ↛ Y)) :=
    forall i1 i2, exists j, P i1 ≺ P j /\ P i2 ≺ P j.

  Definition union {X Y} (P : nat -> (X ↛ Y)) :=
    fun x => bind (mu_tot (fun! ⟨n, m⟩ => match seval (P n x) m with None => false | Some _ => true end)) (fun! ⟨n, m⟩ => match seval (P n x) m with Some o => ret o | _ => undef end).

  Definition cpo_continuous (F : (Q ↛ A) -> (I ↛ O)) :=
    forall P (H : directed P) i o, (exists n, F (P n) i =! o) <-> F (union P) i =! o.

  Definition lprefixes {X Y} (d : (forall x y : X, {x = y} + {x <> y})) (e : nat -> list X) (f : X ↛ Y) : nat -> (X ↛ Y) :=
    fun n x => if in_dec d x (e n) then f x else undef.

  Lemma lprefixes_directed {X Y} d e (f : X ↛ Y) :
    (forall x : X, exists n, In x (e n)) ->
    (forall n, exists l, e (S n) = e n ++ l) ->
    directed (lprefixes d e f).
  Proof.
    intros Henum Hcumul i1 i2.
  Admitted.

  Lemma lprefixes_union {X Y} d e (f : X ↛ Y) :
    (forall x : X, exists n, In x (e n)) ->
    (forall n, exists l, e (S n) = e n ++ l) -> 
    forall x, partial.equiv (f x) (union (lprefixes d e f) x).
  Proof.
  Admitted.

  Lemma bla F (d : (forall x y : A, {x = y} + {x <> y})) e :
    (forall x : A, exists n, In x (e n)) ->
    (forall n, exists l, e (S n) = e n ++ l) ->
    continuous_f F -> cpo_continuous F.
  Proof.
    intros Henum Hcumul H f Hf i o. split.
    - intros [n [L (H1 & H2)] % H].
      eapply H2. intros.
      eapply bind_hasvalue.
      admit.
    - intros [L (H1 & H2)] % H. 
  Admitted.        

End Continuity.

Arguments beta {_ _ _ _}.
Arguments eta {_ _ _ _}.

Ltac decomp x :=
  let x1 := fresh "x" in
  let x2 := fresh "x" in
  try match type of x with
    | sum ?A ?B => destruct x as [x1 | x2]; decomp x1; decomp x2
    | prod ?A ?B => destruct x as [x1 x2]; decomp x1; decomp x2
    end.

Ltac next :=
  unfold beta, eta in *;
  (try now eauto);
  match goal with
  | [ H : exists n, evalt _ _ _ _ _ _ =! _ |- _ ] => destruct H
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
  | [ H : evalt _ _ _ _ _ ?n =! _ |- _ ] => destruct n; cbn in *
  end.

(* Notation "'beta'" := (@beta _ nat nat nat) (at level 10). *)

Ltac simpl_assms :=
  repeat next.

Ltac simpl_goal :=
  repeat (setoid_rewrite bind_hasvalue + eexists + eapply ret_hasvalue); eauto.

Ltac simpl_cont := simpl_assms; simpl_goal.

Ltac psimpl := repeat progress (cbn; simpl_assms; simpl_goal).

Ltac prove_cont f n :=
  exists f;
  split; intros H; [ | exists n ] ; simpl_cont.

Goal forall P : partiality, continuous_via_extensional_dialogues nat nat nat nat
                         (fun f i => bind (f i) (fun x => f x)).
Proof.
  intros P.
  prove_cont (fun i : nat => beta (ret i) (fun a => beta (ret a) (fun o => eta (ret o)))) 2.
Qed.

Goal forall P : partiality, continuous_via_extensional_dialogues nat nat nat nat (fun I => I).
Proof.
  intros P.
  prove_cont (fun i : nat => beta (ret i) (fun a : nat => eta (ret a))) 1.
Qed.

Ltac prove_cont' n :=
  split; intros H; [ | exists n ] ; simpl_cont.

Section Niklas.

  Context {Part : partiality}.

  Lemma niklas_4_5 A X (f : X -> A) :
    continuous_via_extensional_dialogues bool A X bool (fun r x => r (f x)).
  Proof.
    exists (fun i => beta (ret (f i)) (fun a => eta (ret a))). prove_cont' 1.
  Qed.

  Lemma niklas_4_6 A :
    continuous_via_extensional_dialogues bool A A bool (fun r x => bind (r x) (fun b => ret (negb b))).
  Proof.
    exists (fun i => beta (ret i) (fun a => eta (ret (negb a)))). prove_cont' 1.
  Qed.

  Lemma niklas_4_8 A X (f : X ↛ unit) :
    continuous_via_extensional_dialogues bool A X unit (fun r x => f x).
  Proof.
    exists (fun x => eta (f x)). prove_cont' 0.
  Qed.

  Lemma niklas_4_9 A X Y (f : A -> X) (F : (Y ↛ bool) -> X ↛ bool) :
    continuous_via_extensional_dialogues _ _ _ _ F
    -> continuous_via_extensional_dialogues _ _ _ _ (fun r x => F r (f x)).
  Proof.
    intros [t H]. exists (fun a => t (f a)). intros g i o. apply H.
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

  Lemma niklas_4_10_interrogations A X  Q Y I O (F1 : (Q ↛ A) -> X ↛ Y) (F2 : (X ↛ Y) -> I ↛ O) :
    continuous_via_interrogations _ _ _ _ F1
    -> continuous_via_interrogations _ _ _ _ F2
    -> continuous_via_interrogations _ _ _ _ (fun r x => F2 (F1 r) x).
  Proof.
    intros [t1 H1] [t2 H2].
    eapply continuous_via_einterrogations_equiv.
    eapply continuous_via_sinterrogations_equiv.
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
    intros.  setoid_rewrite <- H2. clear F2 H2. split.
    - intros (qs & ans & [ans' qs'] & Hint & Hend).
      destruct qs' as [ [ ] | ]; unfold t in Hend; simpl_assms.
      enough (interrogation Y X O (t2 i) (F1 f) (map fst ans') (map snd ans')).
      firstorder. clear H.
      enough (forall h, sinterrogation A Q O (t i) f qs ans ([], None) h ->
                     (interrogation Y X O (t2 i) (F1 f) (map fst (fst h))) (map snd (fst h)) /\
                     match snd h with
                       None => True
                     | Some (x, n) => t2 i (map snd (fst h)) =! inl x /\ interrogation A Q Y (t1 x) f (lastn n qs) (lastn n ans)
                     end
             ).
      { eapply H in Hint. eapply Hint. }
      clear - H1. intros h H.
      remember ([], None) as e0.
      revert Heqe0.
      induction H; intros Heqe0.
      + subst. cbn. split; econstructor.
      + destruct IHsinterrogation as [IH1 IH2]; eauto.
        destruct e1' as (qs_ans & [ (x & n) | ]); cbn in *.
        * simpl_assms. destruct IH2 as [IH2 IH3]. cbn.
          split; eauto. rewrite !map_app. cbn.
          econstructor; eauto.
          eapply H1. eauto. 
        * psimpl. 
          unfold lastn.
          rewrite !Nat.sub_0_r, !drop_all. 
          econstructor.
      + destruct IHsinterrogation as [IH1 IH2]; eauto.
        destruct e1' as (qs_ans & [ (x & n) | ]); cbn in *.
        * psimpl. 
          rewrite !lastn_S. 
          firstorder. econstructor; eauto. 
        * psimpl.
    - intros (xs & ys & Hint & Hend).
      enough (∃ (qs : list Q) (ans : list A), sinterrogation A Q O (t i) f qs ans ([], None) (zip xs ys, None)).
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
        assert (sinterrogation A Q O (t i) f qs ans  ([], None) (zip xs ys, Some (q, 0))).
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

  Lemma list_find_repeat_not {Y} P D x n :
    ~ P x ->
    @list_find Y P D (repeat x n) = None.
  Proof.
    induction n; cbn.
    - reflexivity.
    - intros. destruct (decide (P x)); try tauto. now rewrite IHn.
  Qed.

  Lemma cont_mu' I :
    continuous_via_interrogations bool (I * nat) I nat (fun f i => (mu (fun n => f (i, n)))).
  Proof.
    exists (fun i l => ret (match list_find (fun b => b = true) l with Some (i, _) => inr i | _ => inl (i, length l) end)).
    intros f i v. split.
    - intros (qs & ans & H1 & H2).
      eapply mu_hasvalue.
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
    - intros (Hv & Hl) % mu_hasvalue.
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
  
  Lemma cont_mu I :
    continuous_via_interrogations bool nat I nat (fun f _ => (mu f)).
  Proof.
    exists (fun i l => ret (match list_find (fun b => b = true) l with Some (i, _) => inr i | _ => inl (length l) end)).
    intros f _ v. split.
    - intros (qs & ans & H1 & H2).
      eapply mu_hasvalue.
      destruct list_find as [ [] | ] eqn:E; next.
      inversion H1; subst.
      + cbn in E. congruence.
      + destruct (list_find (λ b : bool, b = true) ans0) as [ [] | ] eqn:E_; next.
        rewrite list_find_app_r in E; eauto.
        cbn in E. destruct (decide (a = true)); cbn in *; inversion E; subst; clear E.
        split; eauto.
        clear H1 H2.
        set (n := length ans0).
        assert (qs0 = seq 0 n /\ ans0 = repeat false n).
        { induction H.
          - split; reflexivity.
          - subst n. rewrite !app_length, repeat_app, seq_app.
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
    - intros (Hv & Hl) % mu_hasvalue.
      exists (seq 0 (v + 1)), (repeat false v ++ [true]).
      split.
      + rewrite seq_app. econstructor.
        * clear Hv.
          induction v.
          -- econstructor.
          -- replace (S v) with (v + 1) by lia. rewrite seq_app, repeat_app.
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

  Lemma forward_mu (f : nat ↛ bool) (n : nat) m v :
    (forall k, k < m -> f k =! false) ->
    evalt bool nat nat (λ l : list bool,
          ret match list_find (λ b : bool, b = true) l with
            | Some (i, _) => inr (m + i)
            | None => inl (m + (length l))
            end) f n =! v ->
    match v with
    | inl _ => (forall k : nat, k < m + n -> f k =! false)
    | inr a => f a =! true /\ (forall k : nat, k < a -> f k =! false)
    end.
  Proof.
    intros Hm.
    induction n in m, Hm |- *.
    - intros. cbn in *. eapply bind_hasvalue in H as (? & ? & ?). next.
      next. intros. eapply Hm. lia.
    - intros. cbn in *. eapply bind_hasvalue in H as (? & ? & ?).
      next. clear H1.
      next. destruct x; cbn in *.
      + unfold decide, decide_rel in H0. cbn in H0.
        destruct n; cbn in H0.
        next. next. next. next. next. firstorder. eapply Hm. lia.
        next. next. next. next. next. firstorder. eapply Hm. lia.
      + unfold decide, decide_rel in H0. cbn in H0.
        eapply evalt_ext in H0.
        eapply (IHn (S m)) in H0. destruct v.
        * firstorder. eapply H0. lia.
        * eauto.
        * firstorder. inversion H1; subst; replace m with (m + 0) by lia; eauto.
        * intros; cbn. rewrite <- !ret_hasvalue_iff.
          destruct list_find as [ [] | ] eqn:E.
          -- cbn. clear. firstorder subst; f_equal; lia.
          -- cbn. clear. firstorder subst; f_equal; lia.
  Qed.

  Lemma cont_mu_dialogues :
    continuous_via_extensional_dialogues bool nat nat nat (fun f _ => (mu f)).
  Proof.
    exists (fun i l => ret (match list_find (fun b => b = true) l with Some (i, _) => inr i | _ => inl (length l) end)).
    intros f _ v. split.
    - intros [n].
      setoid_rewrite mu_hasvalue.
      eapply forward_mu with (v := inr v) (m := 0).
      + intros. lia.
      + eauto.
    - rewrite mu_hasvalue. intros [H1 H2].
      exists (v + 1).
      replace v with (length (seq 0 v)) by now rewrite seq_length.
      eapply interrogation_plus. instantiate (1 := repeat false v).
      2:{ rewrite seq_length. cbn. psimpl.
          rewrite app_nil_r.
          destruct list_find as [ [] | ] eqn:E.
          + eapply list_find_Some in E as (? & -> & _).
            exfalso. revert H. clear.
            induction v in n |- *; cbn.
            * congruence.
            * destruct n; cbn; try congruence. eauto.
          + rewrite repeat_length. cbn.
            psimpl.
            rewrite list_find_app_r.
            cbn. 
            unfold decide, decide_rel. cbn.
            rewrite repeat_length. psimpl.
            eauto. 
      }
      clear H1. induction v.
      + cbn. econstructor.
      + replace (S v) with (v + 1) by lia.
        rewrite seq_app, repeat_app. cbn.
        econstructor; eauto.
        destruct list_find as [ [] | ] eqn:E.
        * eapply list_find_Some in E as (? & -> & _).
          exfalso. revert H. clear.
          induction v in n |- *; cbn.
          -- congruence.
          -- destruct n; cbn; try congruence. eauto.
        * rewrite repeat_length. psimpl.
  Qed.

  Definition search f x :=
    mkpart (fun n => let (y, m) := unembed n in match seval (f (embed (x, y))) m with
                                             | Some true => Some tt | _ => None end).

  Definition search' f x :=
    bind (mu (fun n => let (y, m) := unembed n in match seval (f (embed (x, y))) m with
                                             | Some true => ret true | _ => ret false end))
      (fun n => ret tt).

  Lemma search_spec f x v :
    search' f x =! v <-> search f x =! v.
  Proof.
    split; destruct v; intros H; unfold search, search' in *.
    - simpl_assms. eapply mu_hasvalue in H as [].
      destruct (unembed x0).
      destruct seval as [ [] | ] eqn:E; simpl_assms.
      eapply mkpart_hasvalue2.
      { clear. intros ? ? [] []. reflexivity. }
      instantiate (1 := ⟨n,n0⟩).
      now rewrite embedP, E.
    - eapply mkpart_hasvalue1 in H as (n & H). 
      destruct (unembed n).
      destruct seval as [ [] | ] eqn:E; try congruence.
      eapply bind_hasvalue.
      assert (exists n, let (y,m) := unembed n in
                   match seval (A:=bool) (f ⟨ x, y ⟩) m with
                   | Some true => true
                   | _ => false
                   end).
      { exists ⟨n0, n1⟩. now rewrite embedP, E. }
      eapply mu_nat.mu_nat_dep_least in H0 as (l & _ & Hl1 & Hl2).
      + exists l. split; psimpl. eapply mu_hasvalue.
        split.
        * destruct (unembed l). clear E. destruct seval as [ [] | ]; psimpl.
        * intros. specialize (Hl2 m).
          destruct (unembed m). clear Hl1 E.
          destruct seval as [ [] | ]; psimpl.
          enough (l <= m) by lia. eapply Hl2; eauto. lia.
      + intros. destruct unembed. clear.
        destruct seval as [ [] | ]; firstorder.
  Qed.

  Lemma niklas_5_2 k :
    continuous_via_extensional_dialogues bool (Vector.t nat (S k)) (Vector.t nat k) unit (fun f v => bind (mu (fun x => f (Vector.cons _ x _ v))) (fun _ => ret tt)).
  Proof.
    edestruct cont_mu as [τ H].
    eapply continuous_via_interrogations_equiv.
    exists (fun v l => bind (τ v l) (fun res => match res with inl q => ret (inl (Vector.cons _ q _ v)) | inr o => ret (inr tt) end)).
    intros. split.
    - intros (qs & ans & H1 & H2). simpl_assms.
      rewrite bind_hasvalue.
      enough (∃ a : nat, mu (λ x : nat, f (Vector.cons nat x k i)) =! a). { firstorder. exists x; firstorder. psimpl. }
      setoid_rewrite <- H. instantiate (1 := i).
      exists x1.
      enough (∃ (qs0 : list nat), interrogation bool nat nat (τ i) (λ x : nat, f (Vector.cons nat x k i)) qs0 ans) by firstorder.
      clear H0.
      induction H1.
      + exists []; econstructor.
      + destruct IHinterrogation as (? & ? ). simpl_assms.
        eexists. econstructor; eauto.
    - intros. simpl_assms. clear H2.
      eapply H in H0 as (qs & ans & H1 & H2).
      enough ( ∃ (qs0 : list (Vector.t nat (S k))),
                 interrogation bool (Vector.t nat (S k)) ()
                   (λ l : list bool,
                       bind (B:=Vector.t nat (S k) + ()) (τ i l) (λ res : nat + nat, match res with
                                                                               | inl q => ret (inl (Vector.cons nat q k i))
                                                                               | inr _ => ret (inr ())
                                                                               end)) f qs0 ans).
      { firstorder. exists x0, ans. firstorder. psimpl. }
      clear H2. induction H1.
      + exists []; econstructor.
      + destruct IHinterrogation as (? & ? ). simpl_assms.
        eexists. econstructor; eauto.
        psimpl.
  Qed.

  Lemma continuous_precompose A Q I O I' F g :
    continuous_via_interrogations A Q I O F ->
    continuous_via_interrogations A Q I' O (fun r x => F r (g x)).
  Proof using.
    intros [tau H].
    exists (fun i l => tau (g i) l). intros. eapply H.
  Qed.

  Lemma continuous_if A Q I O (F1: (Q ↛ A)  -> _ ↛ _) F2 test :
    continuous_via_interrogations A Q I O F1 ->
    continuous_via_interrogations A Q I O F2 ->
    continuous_via_interrogations _ _ _ _ (fun f (x : I) => if test x : bool then F1 f x else F2 f x).
  Proof using.
    intros [tau1 H1] [tau2 H2].
    unshelve eexists. intros i.
    destruct (test i). exact (tau1 i).
    exact (tau2 i). intros. cbn. destruct test; cbn; eauto.
  Qed.

  Lemma continuous_ret A Q I O v :
    continuous_via_interrogations A Q I O (fun f x => ret v).
  Proof using.
    exists (fun _ _ => ret (inr v)). intros.
    firstorder. psimpl.
    exists [], []. psimpl. econstructor.
  Qed.

  Lemma continuous_id A Q I :
    continuous_via_interrogations A Q I I (fun f x => ret x).
  Proof using.
    exists (fun v _ => ret (inr v)). intros.
    firstorder. psimpl.
    exists [], []. psimpl. econstructor.
  Qed.

  Lemma continuous_bind A Q Y Z R (F1: (Q ↛ A) -> _ ↛ _) F2 :
    continuous_via_interrogations _ _ R _ F1 ->
    continuous_via_interrogations _ _ _ _ F2 ->
    continuous_via_interrogations _ _ _ _ (fun f x => @bind _ Y Z (F1 f x) (fun y => F2 f (x, y))).
  Proof using.
    intros [tau1 H1] [tau2 H2].
    eapply continuous_via_einterrogations_equiv.
    eapply continuous_via_sinterrogations_equiv.
    exists (option (Y * nat)), None.
    unshelve eexists.
    { intros r b l.
      refine (match b with Some (y, n) => bind (tau2 (r, y) (drop n l)) (fun res => match res with inl q => ret (inl (Some (y, n), Some q)) | inr o => ret (inr o) end)
                      | None => bind (tau1 r l) (fun res => match res with inl q => ret (inl (None, Some q)) | inr y => ret (inl (Some (y, length l), None)) end) end).
    } cbn.
    intros. rewrite bind_hasvalue.
    setoid_rewrite <- H1.
    setoid_rewrite <- H2. clear. split.
    - intros (qs & ans & info & H1 & H2).
      destruct info as [ [y n] |  ]; simpl_assms. exists y.
      enough (n <= length ans /\ interrogation A Q Y (tau1 i) f (take n qs) (take n ans) ∧ tau1 i (take n ans) =! inr y /\  interrogation A Q Z (tau2 (i, y)) f (drop n qs) (drop n ans))
        by firstorder. clear H.
      generalize (eq_refl (@None (prod Y nat))).
      revert H1. generalize (@None (prod Y nat)) at 2 3. intros none H1 Heqnone.
      change (match Some (y,n) with Some (y, n) =>
                                      n ≤ length ans ∧ 
                                        interrogation A Q Y (tau1 i) f (take n qs) (take n ans) ∧ tau1 i (take n ans) =! inr y /\  interrogation A Q Z (tau2 (i, y)) f (drop n qs) (drop n ans)
                               | None =>
                                   interrogation A Q Y (tau1 i) f qs ans 
              end).

      revert H1. (generalize (Some (y, n))). intros.
      induction H1 in Heqnone |- *.
      + subst. econstructor.
      + destruct e1' as [ [] | ]. psimpl.
        psimpl.
        all: assert (length qs = length ans) as Hlen by (eapply sinterrogation_length; eauto).
        * rewrite firstn_all. rewrite <- Hlen. rewrite firstn_all. eauto.
        * rewrite firstn_all. eauto.
        * rewrite !drop_all. rewrite <- Hlen. rewrite drop_all. econstructor.
      + destruct e1' as [ [] | ].
        * simpl_assms. destruct IHsinterrogation as (IH1 & IH2 & IH3 & IH4). reflexivity.
          assert (length qs = length ans) as Hlen by (eapply sinterrogation_length; eauto).
          repeat split.
          -- rewrite app_length; cbn. lia.
          -- rewrite !take_app_le; try lia. eauto.
          -- rewrite !take_app_le; try lia. eauto.
          -- rewrite !drop_app_le; try lia. econstructor; eauto.
        * simpl_assms. 
          assert (length qs = length ans) as Hlen by (eapply sinterrogation_length; eauto).
          econstructor; eauto.
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

  Lemma continuous_mu A Q Y (F1: (Q ↛ A)  -> _ ↛ _) :
    continuous_via_interrogations A Q (Y * nat) bool F1 ->
    continuous_via_interrogations _ _ _ _ (fun f x => mu (fun n => F1 f (x, n))).
  Proof using.
    intros.
    eapply continuous_via_interrogations_ext.
    eapply niklas_4_10_interrogations.
    2: eapply cont_mu'. all: cbn. exact H. reflexivity.
  Qed.

  Lemma PT_cont Q X A (F1 : (Q ↛ A) -> (X * nat) ↛ bool) (F2 : (Q ↛ A) -> (X * nat) ↛ bool) :
    continuous_via_interrogations _ _ _ _ F1
    -> continuous_via_interrogations _ _ _ _ F2
    -> continuous_via_interrogations _ _ _ _ (fun r x => bind (mu (fun n => bind (F1 r (x, n)) (fun b => if b then ret true else
                                                                                            bind (F2 r (x, n)) (fun b => ret b))))
                                                          (fun n => bind (F1 r (x,n)) (fun b => if b then ret true else ret false))).
   Proof.
     intros.
     eapply continuous_via_interrogations_ext.
     eapply continuous_bind. all: cbn. 
     eapply continuous_mu.
     eapply continuous_bind. all: cbn.
     eapply H.
     eapply continuous_if. all:cbn.
     eapply continuous_ret with (v := true). all: cbn.
     eapply continuous_bind. all: cbn.
     eapply continuous_precompose.
     eapply H0.
     eapply continuous_precompose.
     eapply continuous_id. all: cbn.
     eapply continuous_bind. all: cbn.
     exact H.
     eapply continuous_if. all: cbn.
     eapply continuous_ret with (v := true).
     eapply continuous_ret with (v := false).
     cbn. intros.
     Unshelve.
     4:{ intros [ [ [ ]] ]. exact b0. }
     all: try tauto.
     cbn. reflexivity.
   Qed.

   Print Assumptions PT_cont.

End Niklas.
