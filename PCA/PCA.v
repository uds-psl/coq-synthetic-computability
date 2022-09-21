Require Import List Lia PeanoNat.
Import ListNotations.

Require Import ConstructiveEpsilon.

Section fix_types.

Variable Q A I O : Type.

Variable F : (Q -> A) -> (I -> O).

Definition modulus_on (f : Q -> A) (L : list Q) :=
  forall g, Forall (fun q => f q = g q) L -> forall i, F f i = F g i.

Definition modulus_continuous :=
  forall f, exists L, modulus_on f L.

Definition modulus (M : (Q -> A) -> I -> list Q) :=
  forall f i g, Forall (fun q => f q = g q) (M f i) -> F f i = F g i.

Inductive dialogue :=
  eta (o : O)
| beta (q : Q) (k : A -> dialogue).

Fixpoint eval (f : Q -> A) (d : dialogue) :=
  match d with
  | eta o => o
  | beta q k => eval f (k (f q)) 
  end.

Definition eloquency d :=
  forall f : Q -> A, forall i : I, F f i = eval f (d i).

Lemma eloquency_to_modulus d :
  eloquency d -> {M | modulus M}.
Proof.
  intros He.
  pose (M' :=
          fix M' d f :=
            match d with
            | eta o => []
            | beta q k => q :: M' (k (f q)) f
            end).
  exists (fun f i => M' (d i) f).
  intros f i g H.
  erewrite !He. clear - H.
  induction (d i) as [ | ? ? IH]; cbn in *.
  - reflexivity.
  - inversion H as [|? ? Heq]; subst.
    rewrite Heq. rewrite IH; eauto.
    now rewrite <- Heq.
Qed.

Record is_total_tree (τ : list A -> option (Q + O)) :=
  {
    is_prefix_closed : forall l l', τ (l ++ l') <> None -> τ l <> None ;
    is_valid_nodes : forall l,
      match τ l with
      | None => l <> nil
      | Some (inl q) => forall a, τ (l ++ [a]) <> None
      | Some (inr o) => forall a, τ (l ++ [a]) = None
      end
  }.

Definition well_founded (τ : list A -> option (Q + O)) :=
  forall f : nat -> A, exists n o,
    τ (map f (seq 0 n)) = Some (inr o).

Notation tree := (list A -> option (Q + O)).

Fixpoint evalt (τ : tree) (f : Q -> A) (n : nat) : option ((list A * Q) + O) :=
  match n with
  | 0 =>  match τ [] with
         | None => None
         | Some (inr o) => Some (inr o)
         | Some (inl q) => Some (inl ([], q))
         end
  | S n => match evalt τ f n with
          | None => None
          | Some (inr o) => Some (inr o)
          | Some (inl (l, q)) =>
              match τ (l ++ [f q]) with
              | None => None
              | Some (inr o) => Some (inr o)
              | Some (inl q') => Some (inl (l ++ [f q], q'))
              end
          end
  end.

Lemma evalt_det' τ f n1 n2 o :
  n2 >= n1 ->
  evalt τ f n1 = Some (inr o) ->
  evalt τ f n2 = Some (inr o).
Proof.
  induction 1; intros H1; cbn in *.
  - congruence. 
  - destruct (evalt τ f m)  as [ [[] | ] | ] eqn:E1.
    all: try now firstorder congruence.
Qed.

Lemma evalt_det τ f n1 n2 o1 o2 :
  evalt τ f n1 = Some (inr o1) ->
  evalt τ f n2 = Some (inr o2) ->
  o1 = o2.
Proof.
  intros H1 H2.
  assert (n1 <= n2 \/ n2 <= n1) as [H | H] by lia.
  all: eapply evalt_det' in H; eauto; congruence.
Qed.

Lemma evalt_inv_inl_length τ f n l q :
  is_total_tree τ ->
  evalt τ f n = Some (inl (l, q)) ->
  length l = n.
Proof.
  intros [Hpref Hnode].
  induction n in l, q |- *.
  - cbn. specialize (Hnode []). destruct (τ []) as [ [] | ]; inversion 1; now subst.
  - cbn. destruct evalt as [ [[] | ] | ] eqn:E.
    1: specialize (Hnode (l0 ++ [f q0])); destruct (τ (l0 ++ [f q0])) as [ [] | ] eqn:E'.
    all: inversion 1; subst.
    rewrite app_length. specialize (IHn _ _ eq_refl). cbn. lia.
Qed.

(* Lemma firstn_length_all {X : Type} (l : list X) n : *)
(*   length (firstn n l) = length l -> firstn n l = l. *)
(* Proof. *)
(*   induction n in l |- *; cbn. *)
(*   - destruct l; cbn; congruence. *)
(*   - destruct l; cbn; try congruence. *)
(*     inversion 1. f_equal. eauto. *)
(* Qed. *)

(* Lemma eval_inv_inl τ f n l q : *)
(*   is_total_tree τ -> *)
(*   evalt τ f n = Some (inl (l, q)) -> *)
(*   forall k, k <= n -> exists q, evalt τ f k = Some (inl (firstn (S k) l, q)). *)
(* Proof. *)
(*   intros [Hpref Hnode]. *)
(*   induction n in l, q |- *. *)
(*   - intros. inversion H0. subst. cbn in *. *)
(*     destruct τ as [ [] | ]; inversion H; subst. eauto.     *)
(*   - cbn - [firstn]. destruct evalt as [ [[] | ] | ] eqn:E.  *)
(*     1: specialize (Hnode (l0 ++ [f q0])) as Hnd; destruct (τ (l0 ++ [f q0])) as [ [] | ] eqn:E'. *)
(*     all: inversion 1; subst. *)
(*     intros. inversion H0; subst. *)
(*     + eapply eval_inv_inl_length in E as E_. 1: rewrite <- E_. 2: split; eauto. *)
(*       rewrite firstn_all2. 2: rewrite app_length; cbn; lia. *)
(*       rewrite E_. cbn. rewrite E, E'. eauto. *)
(*     + destruct (IHn _ _ eq_refl k) as (q' & Hq). 1:lia. *)
(*       eapply eval_inv_inl_length in Hq as Hlen. 2: split; eauto. *)
(*       exists q'. rewrite firstn_app. *)
(*       assert (S k - length l0 = 0) as ->. { *)
(*         pose proof (firstn_length (S k) l0). lia. *)
(*       } *)
(*       now rewrite firstn_O, app_nil_r. *)
(* Qed. *)

(* Lemma eval_inv_inr τ f n o : *)
(*   is_total_tree τ -> *)
(*   evalt τ f n = Some (inr o) -> *)
(*   exists m, m <= n /\ evalt τ f m = Some (inr o) *)
(*            /\ exists l, forall k, k < m -> exists q, evalt τ f k = Some (inl (firstn (S k) l, q)). *)
(* Proof. *)
(*   intros [Hpref Hnode]. *)
(*   induction n. *)
(*   - exists 0. repeat split; eauto. exists []. intros. lia. *)
(*   - cbn. destruct evalt as [ [[] | ] | ] eqn:E. *)
(*     1: specialize (Hnode (l ++ [f q])) as Hn; destruct τ as [ [] | ] eqn:E'. *)
(*     all: inversion 1; subst. *)
(*     + exists (S n). repeat split; eauto. *)
(*       * cbn. rewrite E, E'; eauto. *)
(*       * exists l. intros. eapply eval_inv_inl; eauto. *)
(*         -- split; eauto. -- lia. *)
(*     + destruct IHn as (m & H1 & H2 &H3); eauto. *)
(* Qed. *)

Inductive interrogation (f : Q -> A) : list A -> (list A -> option (Q + O)) -> Prop :=
  NoQuestions τ : interrogation f [] τ
| Ask l τ q a : f q = a ->
                interrogation f l τ ->
                τ l = Some (inl q) ->
                interrogation f (l ++ [a]) τ.

(* Lemma τ_inv f τ l : *)
(*   is_total_tree τ -> *)
(*   interrogation f l τ -> *)
(*   match τ l with *)
(*   | None => evalt τ f (length l) = None *)
(*   | Some (inl q) => evalt τ f (length l) = Some (inl (l, q)) *)
(*   | Some (inr o) => evalt τ f (length l) = Some (inr o) *)
(*   end. *)
(* Proof. *)
(*   intros [Hpref Hnode]. *)
(*   induction 1. *)
(*   - cbn. specialize (Hnode []). *)
(*     destruct (τ []) as [ [] | ] eqn:E ; try congruence. *)
(*   - specialize (Hnode (l ++ [f q])) as Hn. *)
(*     unshelve epose proof (IHinterrogation _ _) as IH; clear IHinterrogation; eauto. *)
(*     rewrite app_length; cbn. rewrite Nat.add_comm. cbn. subst. *)
(*     rewrite H1 in IH; rewrite IH. *)

(*     destruct (τ (l ++ [f q])) as [ [] | ] eqn:E; eauto. *)
(* Qed. *)

(* Lemma himmel τ q q' f n l : *)
(*   is_total_tree τ -> *)
(*   evalt τ f n = Some (inl (l, q')) -> *)
(*   (map *)
(*      (fun n : nat => *)
(*         match evalt τ f (n + 1) with *)
(*         | Some (inl (a1, q1)) => nth n a1 (f q1) *)
(*         | _ => f q *)
(*         end) (seq 0 n)) = l. *)
(* Proof. *)
(*   intros [Hpref Hnode]. *)
(*   induction n in q', l |- *. *)
(*   - cbn. specialize (Hnode []). destruct (τ []) as [ [] | ]; try congruence. *)
(*   - rewrite seq_S, map_app. cbn. *)
(*     destruct (evalt τ f n) as [ [[] | ] | ] eqn:E; try congruence. *)
(*     specialize (IHn _ _ eq_refl). *)
(*     destruct τ as [ [] | ] eqn:E'; intros H; inversion H; subst; clear H. *)
(*     repeat f_equal. *)
(*     rewrite Nat.add_comm. cbn. rewrite E, E'. *)
(*     rewrite app_nth2; rewrite map_length, seq_length. *)
(*     2: lia. now rewrite Nat.sub_diag. *)
(* Qed. *)
(* Ltac reset l := *)
(*   let x := eval red in l in *)
(*     subst l; set (l := x) in *. *)

Fixpoint get (τ : tree) (f : Q -> A) n :=
  match n with
  | 0 => []
  | S n => let l := (get τ f n) in
          match τ l with
          | Some (inl q) => l ++ [f q]
          | _ => []
          end
  end.

Lemma hammer τ f n q q' :
  let l := map
         (fun n : nat =>
          nth n
            match τ (get τ f n) with
            | Some (inl q) => get τ f n ++ [f q]
            | _ => []
            end (f q)) (seq 0 n) in
  is_total_tree τ ->
  τ l = Some (inl q') ->
  evalt τ f n = Some (inl (l, q')) /\
  interrogation f l τ /\
  get τ f n = l.
Proof.
  intros l [Hpref Hnode] Ht.
  induction n in q, q', l, Ht |- *; specialize (Hnode l) as Hnl.
  - subst l; cbn in *. split; try now econstructor.
    now rewrite Ht. split. econstructor. eauto.
  - subst l.
    rewrite seq_S, map_app in *.  set (l := map
       (fun n0 : nat =>
        nth n0
          match τ (get τ f n0) with
          | Some (inl q0) => get τ f n0 ++ [f q0]
          | _ => []
          end (f q)) (seq 0 n)) in *. specialize (Hnode l) as Hn.
    clear Hnl Hn.
    cbn in *.
    destruct (τ l) as [ [] | ] eqn:E.
    + eapply IHn in E as IH. destruct IH as (IH1 & IH2 & IH3).
      rewrite !IH1 in *. rewrite !IH3 in *. subst l. rewrite !E in *.
      revert Ht. rewrite app_nth2; rewrite map_length, seq_length.
      rewrite Nat.sub_diag. 2: lia.
      cbn. intros ->. firstorder.
      econstructor; eauto.
    + specialize (Hnode l). rewrite E in Hnode.
      congruence.
    + exfalso. eapply Hpref. rewrite Ht. congruence.
      eauto.
Qed.

Lemma evalt_wellfounded_ex τ f :
  is_total_tree τ ->
  well_founded τ ->
  exists n o, evalt τ f n = Some (inr o).
Proof.
  intros [Hprf Hnode] Hwf.
  red in Hwf.
  destruct (τ []) as [ [] | ] eqn:E; cycle 1.
  { exists 1, o. cbn. now rewrite E. }
  { specialize (Hnode nil). rewrite E in Hnode. congruence. }
  unshelve edestruct Hwf as [n [o Hno]].
  - intros n. exact (nth n (get τ f (S n)) (f q)).
  - cbn in *. exists n, o.
    destruct n.
    * cbn in *. rewrite Hno. reflexivity.
    * rewrite seq_S, map_app in Hno.
      cbn in Hno. 
      set (l := (map
             (fun n : nat =>
              nth n
                match τ (get τ f n) with
                | Some (inl q) => get τ f n ++ [f q]
                | _ => []
                end (f q)) (seq 0 n))) in *.
      specialize (Hnode l) as Hnl.
      destruct (τ l) as [ [] | ] eqn:Et; try congruence.
      2:{ destruct n. cbn in *. congruence.
          exfalso. eapply Hprf, Et. rewrite Hno. congruence. }
      cbn. 
      eapply hammer in Et as H.
      2: split; eauto.
      destruct H as (H1 & H2 & H3).
      subst l.
      rewrite H1. rewrite <- H3 in *.
      rewrite Et in Hno.
      eapply evalt_inv_inl_length in H1 as H. 
      rewrite app_nth2 in Hno; rewrite H in *.
      rewrite Nat.sub_diag in Hno.
      cbn in *. now rewrite Hno. lia. econstructor; eauto. 
Qed.

Definition tofun (τ : tree) (H : is_total_tree τ) (wf : well_founded τ) (f : Q -> A) : O.
  edestruct epsilon_smallest as [n [Hn _]].
  2: eapply evalt_wellfounded_ex with (f := f); eauto.
  intros n. cbn. destruct evalt as [ [ [] | ] | ]; clear; try abstract firstorder (congruence || eauto).
  cbn in *.
  destruct evalt as [ [ [] | ] | ].
  - exfalso. abstract firstorder congruence.
  - exact o.
  - exfalso. abstract (clear - Hn; firstorder congruence).
Defined.

Fixpoint extension (d : dialogue) (l : list A) : option (Q + O).
Proof.
  destruct d.
  - destruct l.
    + exact (Some (inr o)).
    + exact None.
  - destruct l.
    + exact (Some (inl q)).
    + eapply (extension (k a) l).
Defined.

Lemma extension_is_total_tree d :
  is_total_tree (extension d).
Proof.
  induction d.
  - cbn. split.
    + intros. destruct l; cbn in *; congruence. 
    + intros l. destruct l; cbn in *; congruence.
  - cbn. split.
    + intros. destruct l; cbn in *. congruence.
      now eapply H in H0.
    + intros l. destruct l.
      * cbn. intros a. destruct (H a) as [_ Hn].
        specialize (Hn []). destruct extension as [ [] | ]; congruence.
      * cbn.  destruct (H a) as [_ Hn].  specialize (Hn l).
        destruct extension; eauto. congruence.
Qed.

Lemma extension_well_founded d :
  well_founded (extension d).
Proof.
  induction d.
  - cbn. intros f. now exists 0, o.
  - cbn. intros f. destruct (H (f 0) (fun n => f (S n))) as [n [o Hn]].
    exists (S n), o. cbn.
    now rewrite <- map_map, seq_shift in Hn.
Qed.

Lemma evalt_subtree (τ : tree) f n l1 :
  interrogation f l1 τ ->
  evalt (fun l2 => τ (l1 ++ l2)) f (n - length l1) = 
  match evalt τ f n with
    None => None
  | Some (inl (l, q)) => Some (inl (l1 ++ l, q))
  | Some (inr o) => Some (inr o)
  end.
Proof.
Proof.
  induction l1 using rev_ind in n, τ |- *.
  - cbn. inversion 1. subst.
    rewrite Nat.sub_0_r. admit. admit.
  - cbn. inversion 1. destruct l1; cbn in *; congruence.
    assert (l1 = l) by admit. assert (a = x) by admit. subst.
    specialize (IHl1 (fun l2 => τ (l2 ++ [f q])) n).
    cbn in IHl1.

(*   assert (n = 5) as -> by admit. *)
(*   assert (q : Q) by admit. *)
(*   assert (l1 = [f q]) as -> by admit. *)
(*   cbn. *)
(*   destruct (τ [f q]) as [ [] | ], (τ []). *)
(*   cbn. *)


(*   induction n in l1 |- *. *)
(*   - cbn. rewrite app_nil_r. induction 1. *)
(*     + now destruct τ as [ [] | ]. *)
(*     + subst. *)
(*       destruct (τ l) as [ [] | ] eqn:E, (τ []) as [ [] | ] eqn:E'; inversion IHinterrogation; cbn in *; repeat rewrite app_nil_r in *; subst; cbn in *. *)
(*       * inversion H1; subst. admit. *)
(*       *(* induction n in l1 |- *; cbn. *) *)
(*   (* - rewrite app_nil_r. *) *)
(*   (*   intros H. now rewrite H. *) *)
(*   (* - intros H. eapply IHn in H as H'. rewrite H'. cbn. clear H' IHn. *) *)
(*   (*   destruct evalt as [ [ [] | ] | ] eqn:E. *) *)
(*   (*   + destruct l; cbn. *) *)
(*   (*     * destruct n; cbn in E. *) *)
(*   (*       -- rewrite H in E. inversion E; subst. *) *)
(*   (*   + reflexivity. *) *)
(*   (*   + reflexivity. *) *)
(* Admitted. *)

(* Lemma evalt_subtree (τ : tree) q f n : *)
(*   τ [] = Some (inl q) -> *)
(*   evalt (fun l => τ ([] ++ f q :: l)) f n =  *)
(*   match evalt τ f n with *)
(*     None => None *)
(*   | Some (inl (a :: l, r)) => Some (inl (l, r)) *)
(*   | Some (inl ([], r)) => match τ [f q] with *)
(*   | Some (inl q0) => Some (inl ([], q0)) *)
(*   | Some (inr o) => Some (inr o) *)
(*   | None => None *)
(*   end *)
(*   | Some (inr o) => Some (inr o) *)
(*   end. *)
(* Proof. *)
(*   generalize (@nil A). *)
(*   induction n; cbn. *)
(*   - intros H. now rewrite H.  *)
(*   - intros H. eapply IHn in H as H'. rewrite H'. cbn. clear H' IHn. *)
(*     destruct evalt as [ [ [] | ] | ] eqn:E. *)
(*     + destruct l; cbn. *)
(*       * destruct n; cbn in E. *)
(*         -- rewrite H in E. inversion E; subst.  *)
(*     + reflexivity. *)
(*     + reflexivity. *)
(* Admitted. *)

(* Lemma evalt_subtree (τ : tree) q f n : *)
(*   evalt (fun l => τ (f q :: l)) f n =  *)
(*   match evalt τ f n with *)
(*     None => None *)
(*   | Some (inl (l, r)) => Some (inl (f q :: l, r)) *)
(*   | Some (inr o) => Some (inr o) *)
(*   end. *)
(* Proof. *)
(*   induction n; cbn. *)
  
(* Admitted. *)

Lemma diag_seq (d : dialogue) (f : Q -> A) :
  eval f d = tofun (extension d) (extension_is_total_tree d) (extension_well_founded d) f.
Proof.
  unfold tofun. destruct epsilon_smallest as [n [Hn _]].
    destruct evalt as [ [ [] | ] | ] eqn:E.
    1: destruct tofun_subproof2.
    2: destruct tofun_subproof3. clear Hn.
    induction d in f, n, E |- *.
    - cbn in *. induction n; cbn in *; try congruence.
      destruct evalt as [ [ [] | ] | ] eqn:E'.
      + destruct l; cbn in *; try congruence.
      + eauto.
      + eauto.
    - cbn in *.
      pose proof (evalt_subtree ( (fun l : list A =>
         match l with
         | [] => Some (inl q)
         | a :: l0 => extension (k a) l0
         end)) f n).
      specialize (H0 [f q]).
      rewrite E in H0.
      eapply H. eapply H0.
      eapply Ask with (l := []); eauto.
      econstructor.
Qed.
