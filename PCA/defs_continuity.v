Require Import List Lia PeanoNat.
Import ListNotations.

Require Import ConstructiveEpsilon.

Section fix_types.

Variable Q A I O : Type.

(* Definition 1: Dialogue continuity à la PMP *)
Inductive C : ((Q -> A) -> O) -> Type :=
  etaC o : C (fun _ => o)
| betaC (q : Q) (k : A -> (Q -> A) -> O) (H : forall a, C (k a)) 
        : C (fun f => k (f q) f).

Definition continuous_via_C (F : (Q -> A) -> I -> O) :=
  forall i, C (fun f => F f i).

(* Definition 2: inductive dialogue trees *)
Inductive dialogue :=
  eta (o : O)
| beta (q : Q) (k : A -> dialogue).

Fixpoint eval (f : Q -> A) (d : dialogue) :=
  match d with
  | eta o => o
  | beta q k => eval f (k (f q)) 
  end.

Definition eloquency F (d : I -> dialogue) :=
  forall f : Q -> A, forall i : I, F f i = eval f (d i).

Definition continuous_via_dialogues F :=
  exists d, forall f : Q -> A, forall i : I, F f i = eval f (d i).

(* Definition 3: extensional dialogues *)

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

Record is_total_tree' (τ : list A -> option (Q + O)) :=
  {
    is_not_empty : τ [] <> None ;
    is_valid_nodes' : forall l a,
      τ (l ++ [a]) <> None <-> exists q, τ l = Some (inl q) ;
  }.

(* TODO: prove they agree *)

Definition is_total_tree_with_input (τ : I -> list A -> option (Q + O)) :=
  forall i : I, is_total_tree (τ i).

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

Definition continuous_via_extensional_dialogues F :=
  exists τ : I -> tree, is_total_tree_with_input τ
                  /\ (forall i, well_founded (τ i))
                  /\ forall f i, exists n, evalt (τ i) f n = Some (inr (F f i)).

(* Definition 4: modulus definition *)

Definition modulus_on (F : (Q -> A) -> I -> O) (f : Q -> A) (L : list Q) :=
  forall g, Forall (fun q => f q = g q) L -> forall i, F f i = F g i.

Definition modulus_continuous (F : (Q -> A) -> I -> O) :=
  forall f, exists L, modulus_on F f L.

Definition modulus (F : (Q -> A) -> I -> O) (M : (Q -> A) -> I -> list Q) :=
  forall f i g, Forall (fun q => f q = g q) (M f i) -> F f i = F g i.

Definition continuous_via_modulus F :=
  exists M, modulus F M.

Lemma C_to_dialogues:  forall F,
    C F -> { d | forall f, eval f d = F f }.
Proof.
  intros. induction X.
  - unshelve eexists. eapply eta. exact o.
    cbn. reflexivity.
  - unshelve eexists. eapply beta. exact q.
    intros a. destruct (X a) as [d ?]. exact d.
    intros; cbn. destruct X as [d Hd].
    eapply Hd.
Qed.

Corollary continous_via_C_to_via_dialogue F :
  continuous_via_C F -> continuous_via_dialogues F.
Proof.
  intros H. unshelve eexists.
  - intros i. specialize (H i). eapply C_to_dialogues in H.
    exact (proj1_sig H).
  - intros. cbn. destruct C_to_dialogues as [d Hd]; cbn.
    now rewrite Hd.
Qed.

Lemma dialogues_to_extensional_dialogues F :
  continuous_via_dialogues F -> continuous_via_extensional_dialogues F.
Proof.

  Fixpoint extension (d : dialogue) (l : list A) : option (Q + O) :=
    match d, l with
    | eta o, [] => Some (inr o)
    | eta o, _ => None
    | beta q k, [] => Some (inl q)
    | beta q k, a :: l => extension (k a) l
    end.
  intros [d Hd].
  exists (fun i => extension (d i)).

  (*
    Yannick got stuck here with a different definition of
       continuous_via_extensional_dialogues
    where first the tree was turned into a total function (Q -> A) -> O and then this function had to agree with F.

    With the new definition of just asking exists n, evalt ...
    the proof might be easier.
    
    The intuition is still that the dialogue has to be turned into its extension:

   For the first two parts of the proof, see lemmas below.
   *)

Abort.

(* Conjecture:  
   (forall F, continuous_via_extensional_dialogues F ->   continuous_via_dialogues F) -> FAN theorem
   Proof in paper by Herbelin, Brede at LICS 21
*)

Lemma extensional_dialogues_to_modulus F :
  continuous_via_extensional_dialogues F -> modulus_continuous F.
Proof.
  intros (τ & τ_is_total_tree & τ_is_well_founded & τ_agrees_with_F).
  (* idea: similar to evalt, but return the list of Qs asked rather than O, which requires remembering all the Qs *)
Abort.

(* Conjecture:
   Q has decidable equality and A is finite (exists l, forall a : A, In a l)
   then we can prove
  forall F, modulus_continuous F -> continuous_via_extensional_dialogues F

let l = [a0 , ... an ]

intuition: search for the finite prefix of f that matters, which can be found by trying M many times. something like

τ [] := let L := M (fun _ => a0) in
        if this is [], then return F (fun _ => a0)
        if this is q :: L', then ask M (fun q' => if q = q' then f q else a0)

*)

Lemma eloquency_to_modulus F :
  continuous_via_dialogues F -> continuous_via_modulus F.
Proof.
  intros [d He].
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

(* from here on lemmas that might become helpful, but probably are irrelevant *)

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

Inductive interrogation (f : Q -> A) : list A -> (list A -> option (Q + O)) -> Prop :=
  NoQuestions τ : interrogation f [] τ
| Ask l τ q a : f q = a ->
                interrogation f l τ ->
                τ l = Some (inl q) ->
                interrogation f (l ++ [a]) τ.

Fixpoint get (τ : tree) (f : Q -> A) n :=
  match n with
  | 0 => []
  | S n => let l := (get τ f n) in
          match τ l with
          | Some (inl q) => l ++ [f q]
          | _ => []
          end
  end.
About get.

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
About tofun.

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

(* Lemma diag_seq (d : dialogue) (f : Q -> A) : *)
(*   eval f d = tofun (extension d) (extension_is_total_tree d) (extension_well_founded d) f. *)
(* Proof. *)
(*   unfold tofun. destruct epsilon_smallest as [n [Hn _]]. *)
(*     destruct evalt as [ [ [] | ] | ] eqn:E. *)
(*     1: destruct tofun_subproof2. *)
(*     2: destruct tofun_subproof3. clear Hn. *)
(*     induction d in f, n, E |- *. *)
(*     - cbn in *. induction n; cbn in *; try congruence. *)
(*       destruct evalt as [ [ [] | ] | ] eqn:E'. *)
(*       + destruct l; cbn in *; try congruence. *)
(*       + eauto. *)
(*       + eauto. *)
(*     - cbn in *. *)
(*       pose proof (evalt_subtree ( (fun l : list A => *)
(*          match l with *)
(*          | [] => Some (inl q) *)
(*          | a :: l0 => extension (k a) l0 *)
(*          end)) f n). *)
(*       specialize (H0 [f q]). *)
(*       rewrite E in H0. *)
(*       eapply H. eapply H0. *)
(*       eapply Ask with (l := []); eauto. *)
(*       econstructor. *)
(* Qed. *)
