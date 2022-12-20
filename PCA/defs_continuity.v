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

Definition modulus_on (F : (Q -> A) -> I -> O) (f : Q -> A) i (L : list Q) :=
  forall g, Forall (fun q => f q = g q) L -> F f i = F g i.

Definition modulus_continuous (F : (Q -> A) -> I -> O) :=
  forall f i, exists L, modulus_on F f i L.

Definition modulus (F : (Q -> A) -> I -> O) (M : (Q -> A) -> I -> list Q) :=
  forall f i g, Forall (fun q => f q = g q) (M f i) -> F f i = F g i.

Definition continuous_via_modulus F :=
  exists M, modulus F M.

Fixpoint δ (F' : (Q -> A) -> O) (d : C F') :=
  match d with
  | etaC o => eta o
  | betaC q k d => beta q (fun a => δ (k a) (d a))
  end.

Lemma C_to_dialogues:  forall F,
    C F -> { d | forall f, eval f d = F f }.
Proof.
  intros F d. exists (δ F d). induction d; cbn; intros; eauto.
Qed.

Definition functional_extensionality_on A B :=
  forall f g : A -> B, (forall x, f x = g x) -> f = g.

Corollary continous_via_C_to_via_dialogue F :
  continuous_via_C F -> continuous_via_dialogues F.
Proof.
  intros H. unshelve eexists.
  - intros i. specialize (H i). eapply C_to_dialogues in H.
    exact (proj1_sig H).
  - intros. cbn. destruct C_to_dialogues as [d Hd]; cbn.
    now rewrite Hd.
Qed.

Fixpoint extension (d : dialogue) (l : list A) : option (Q + O) :=
  match d, l with
  | eta o, [] => Some (inr o)
  | eta o, _ => None
  | beta q k, [] => Some (inl q)
  | beta q k, a :: l => extension (k a) l
  end.

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

Lemma evalt_plus' τ f n1 n2 l q :
  evalt τ f n1 = Some (inl (l, q)) ->
  match evalt (fun l' => τ (l ++ [f q] ++ l')) f n2 with
  | Some (inr o) => evalt τ f (S n1 + n2) = Some (inr o)
  | Some (inl (l', q')) => evalt τ f (S n1 + n2) = Some (inl (l ++ [f q] ++ l', q'))
  | None => evalt τ f (S n1 + n2) = None
  end.
Proof.
  induction n2 in n1, l, q |- *.
  - rewrite <- plus_n_O. cbn. intros ->. destruct τ as [ [] | ]; congruence.
  - intros. cbn.
    eapply IHn2 in H. cbn [app] in *. destruct evalt as [ [ [] | ] | ] eqn:E; try congruence.
    + replace (n1 + S n2) with (S n1 + n2) by lia. rewrite H.
      rewrite <- app_assoc. cbn.
      destruct τ as [ [] | ]; eauto.
    + replace (n1 + S n2) with (S n1 + n2) by lia. now rewrite H.
    + replace (n1 + S n2) with (S n1 + n2) by lia. now rewrite H.
Qed.

Lemma evalt_plus τ f n1 n2 l q o :
  evalt τ f n1 = Some (inl (l, q)) ->
  evalt (fun l' => τ (l ++ [f q] ++ l')) f n2 = Some (inr o) ->
  evalt τ f (S n1 + n2) = Some (inr o).
Proof.
  intros.
  eapply evalt_plus' in H.
  now rewrite H0 in H.
Qed.

Lemma dialogues_to_extensional_dialogues F :
  continuous_via_dialogues F -> continuous_via_extensional_dialogues F.
Proof.
  intros [d Hd].
  exists (fun i => extension (d i)).
  repeat eapply conj.
  - intros i. eapply extension_is_total_tree.
  - intros i. eapply extension_well_founded.
  - setoid_rewrite Hd. clear F Hd. intros f i. generalize (d i).
    clear i d. intros d.
    induction d.
    + cbn. exists 0. reflexivity.
    + destruct (H (f q)) as [n Hn].
      cbn [eval]. specialize (H (f q)) as [m IH].
      exists (S m).
      erewrite evalt_plus with (n1 := 0); cbn; [ reflexivity .. | ].
      now rewrite <- IH. 
Qed.

(* Conjecture:  
   (forall F, continuous_via_extensional_dialogues F ->   continuous_via_dialogues F) -> FAN theorem
   Proof in paper by Herbelin, Brede at LICS 21
*)

Fixpoint evalt' (τ : tree) (f : Q -> A) (n : nat) : option ((list Q * Q) + (list Q * O)) :=
  match n with
  | 0 =>  match τ [] with
         | None => None
         | Some (inr o) => Some (inr ([], o))
         | Some (inl q) => Some (inl ([], q))
         end
  | S n => match evalt' τ f n with
          | None => None
          | Some (inr o) => Some (inr o)
          | Some (inl (l, q)) =>
              match τ (map f l ++ [f q]) with
              | None => None
              | Some (inr o) => Some (inr (l ++ [q], o))
              | Some (inl q') => Some (inl (l ++ [q], q'))
              end
          end
  end.

Lemma evalt'_spec τ f n :
  evalt τ f n = match evalt' τ f n with
                | None => None
                | Some (inr (l, o)) => Some (inr o)
                | Some (inl (l, q)) => Some (inl (map f l, q))
                end.
Proof.
  induction n; cbn.
  - destruct τ as [ [] | ]; reflexivity.
  - rewrite IHn. destruct evalt' as [ [ [] | [] ] | ]; eauto.
    destruct τ as [ [] | ]; eauto.
    now rewrite map_app.
Qed.

Lemma evalt_det' τ f n1 n2 o :
  n2 >= n1 ->
  evalt' τ f n1 = Some (inr o) ->
  evalt' τ f n2 = Some (inr o).
Proof.
  induction 1; intros H1; cbn in *.
  - congruence.
  - destruct (evalt' τ f m)  as [ [[] | ] | ] eqn:E1.
    all: try now firstorder congruence.
Qed.

Lemma evalt_det τ f n1 n2 o1 o2 :
  evalt' τ f n1 = Some (inr o1) ->
  evalt' τ f n2 = Some (inr o2) ->
  o1 = o2.
Proof.
  intros H1 H2.
  assert (n1 <= n2 \/ n2 <= n1) as [H | H] by lia.
  all: eapply evalt_det' in H; eauto; congruence.
Qed.

Lemma evalt'_Forall (τ : tree) (f : Q -> A) (n : nat) g :
  match evalt' τ f n with
  | Some (inr (l, o)) => Forall (fun q : Q => f q = g q) l -> evalt' τ g n = Some (inr (l, o))
  | Some (inl (l, q)) => Forall (fun q : Q => f q = g q) l -> evalt' τ g n = Some (inl (l, q)) 
  | None => True
  end.
Proof.
  induction n; cbn.
  - destruct τ as [ [] | ] eqn:E; eauto.
  - destruct (evalt' τ f n) as [ [ [] | [] ] | ]; eauto.
    + destruct τ as [ [] | ] eqn:E.
      * intros [H1 H2] % Forall_app. inversion H2; subst; clear H2. clear H4.
        rewrite IHn; eauto.
        erewrite <- map_ext_Forall; eauto.
        now rewrite <- H3, E.
      * intros [H1 H2] % Forall_app. inversion H2; subst; clear H2. clear H4.
        rewrite IHn; eauto. rewrite <- H3.
        erewrite <- map_ext_Forall; eauto.
        now rewrite E.
      * eauto.
    + intros Hl. now rewrite IHn.
Qed.

Lemma extensional_dialogues_to_modulus F :
  continuous_via_extensional_dialogues F -> modulus_continuous F.
Proof.
  intros (τ & τ_is_total_tree & τ_is_well_founded & τ_agrees_with_F).
  intros f i.

  destruct (τ_agrees_with_F f i) as [n H].
  rewrite evalt'_spec in H.
  destruct evalt' as [ [ [] | [] ] | ] eqn:E; inversion H; subst; clear H.

  exists l. intros g.

  destruct (τ_agrees_with_F g i) as [n2 H].
  rewrite evalt'_spec in H.
  destruct (evalt' (τ i) g n2) as [ [ [] | [] ] | ] eqn:E2; inversion H; subst; clear H.

  intros H.
  enough (evalt' (τ i) g n = Some (inr (l, F f i))).
  { eapply evalt_det in E2; eauto. congruence. }

  epose proof (evalt'_Forall _ _ _ _) as H0. rewrite E in H0.
  now eapply H0 in H.
Qed.

(* From Equations Require Import Equations. *)

Lemma extensional_dialogues_to_modulus' F :
  (forall (x y : A), {x = y} + {x <> y}) ->
  (forall (x y : O), {x = y} + {x <> y}) ->
  (forall (x y : Q), {x = y} + {x <> y}) -> 
  continuous_via_extensional_dialogues F -> continuous_via_modulus F.
Proof.
  intros EA EO EQ (τ & τ_is_total_tree & τ_is_well_founded & τ_agrees_with_F).

  unshelve eexists.

  {
    intros f i.

    pose proof (τ_agrees_with_F f i).
    eapply constructive_indefinite_ground_description_nat in H as [n H].
    rewrite evalt'_spec in H.
    destruct evalt' as [ [ [] | [] ] | ] eqn:E; inversion H; subst; clear H.

    exact l.
    { intros n. repeat decide equality. }


  }

  intros f i g.

  destruct (τ_agrees_with_F f i) as [n_ H_].
  cbn in *.
  destruct constructive_indefinite_ground_description_nat as [n H]; cbn in *.
  pose proof (H' := H). 
  rewrite evalt'_spec in H'. cbn in *.
  generalize ((eq_ind (evalt (τ i) f n)
               (fun o : option (list A * Q + O) => o = Some (inr (F f i))) H
               match evalt' (τ i) f n with
               | Some (inl (l, q)) => Some (inl (map f l, q))
               | Some (inr (_, o)) => Some (inr o)
               | None => None
               end (evalt'_spec (τ i) f n))).
  destruct (evalt' (τ i) f n) as [ [ [] | [] ] | ] eqn:E; inversion H; subst; clear H.
  { intros. clear H. inversion e. }

  destruct (τ_agrees_with_F g i) as [n2 H].
  rewrite evalt'_spec in H.
  destruct (evalt' (τ i) g n2) as [ [ [] | [] ] | ] eqn:E2; inversion H; subst; clear H.

  intros Heq Hl.
  enough (evalt' (τ i) g n = Some (inr (l, F f i))).
  { eapply evalt_det in E2; eauto. congruence. }

  epose proof (evalt'_Forall _ _ _ _) as H0. rewrite E in H0.
  inversion Heq. subst.
  eapply H0. revert Hl.

  unshelve erewrite (Eqdep_dec.UIP_dec _ Heq eq_refl).
  1: repeat decide equality.

  cbn. eauto.
  intros. exfalso. congruence.
Qed.

(* Conjecture:
   If Q has decidable equality and A is finite (exists l, forall a : A, In a l)
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

Lemma tofun_continuous (τ : I -> tree) (H : forall i, is_total_tree (τ i)) (wf : forall i, well_founded (τ i)) :
  continuous_via_extensional_dialogues (fun f i => tofun (τ i) (H i) (wf i) f).
Proof.
  exists τ. repeat eapply conj; [ eauto.. | ].
  intros f i.
  unfold tofun.
  destruct epsilon_smallest as [n [[o H1] H2]].
  exists n. now rewrite H1.
Qed.

End fix_types.
