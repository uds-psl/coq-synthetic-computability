From SyntheticComputability.Shared Require Import embed_nat.

From SyntheticComputability Require Import partial.
Require Import Setoid.

Require Import List.
Import ListNotations EmbedNatNotations.

Section Continuity.

    Context {Part : partiality}.
    Variables A Q I O : Type.

    Notation tree := (list A ↛ (Q + O)).

    Fixpoint evalt (τ : tree) (f : Q ↛ A) (n : nat) : part ((list A * Q) + O) :=
      match n with
      | 0 =>  bind (τ []) (fun x => match x with
                                | (inr o) => ret (inr o)
                                | (inl q) => ret (inl ([], q))
                                end)
      | S n => bind (evalt τ f n) (fun x => match x with
                                        | (inr o) => undef
                                        | (inl (l, q)) =>
                                            bind (f q) (fun v => 
                                            bind (τ (l ++ [v])) (fun x => match x with
                                                                       | (inr o) => ret (inr o)
                                                                       | (inl q') => ret (inl (l ++ [v], q'))
                                                                       end))
                                        end)
      end.

    Definition beta (q : part Q) (k : A -> tree) : tree :=
      fun l => match l with
            | [] => bind q (fun q => ret (inl q))
            | a :: l => k a l
            end.

    Definition eta (o : part O) : tree :=
      fun l => bind o (fun x => ret (inr x)).

    (* Definition 1, à la sequential continuity, i.e. extensional dialogue trees *)
    Definition continuous_via_extensional_dialogues F :=
      exists τ : I -> tree, forall f i o, (exists n, evalt (τ i) f n =! inr o) <-> F f i =! o.

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
      revert H. generalize (@inr (list A * Q) _ v). clear v.
      intros v H.
      enough (  exists L : list Q,
                 (forall y : Q, In y L -> exists b : A, f y =! b) /\
                   (forall f' : Q ↛ A, (forall (y : Q) (b : A), In y L -> f y =! b -> f' y =! b) -> evalt (τ i) f' n =! v)) by firstorder.
      induction n in v, H |- *; cbn in *.
      - exists []. split. 1: firstorder. 
        intros. cbn. eauto.
      - eapply bind_hasvalue in H as ([(l & q) | o] & H2 & H3).
        + eapply bind_hasvalue in H3 as (a & H4 & H5).
          eapply IHn in H2 as (L & HL & H).
          eapply bind_hasvalue in H5 as (x & H6 & H7).
          exists (L ++ [q]). split.
          * intros ? ? % in_app_iff. firstorder. subst. eauto.
          * intros. eapply bind_hasvalue.
            setoid_rewrite in_app_iff in H0. eexists.
            split. 1: firstorder.
            cbn.
            eapply bind_hasvalue. eexists. split.
            eapply H0. 1: firstorder. 1: eauto.
            eapply bind_hasvalue. eexists. split. eauto.
            eapply H7.
        + eapply undef_hasvalue in H3. tauto. 
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

(* From SyntheticComputability Require defs_continuity. *)

(* Definition factors (F : ((Q -> A) -> I -> O)) (F' : ((Q ↛ A) -> (I ↛ O))) := *)
(*   forall f : Q -> A, forall i : I, *)
(*     F' (fun q => ret (f q)) i =! F f i. *)

(* Lemma bla F F' (a0 : A) (o0 : O) : *)
(*   factors F F' -> *)
(*   continuous_via_extensional_dialogues F' -> *)
(*   defs_continuity.continuous_via_extensional_dialogues Q A I O F. *)
(* Proof. *)
(*   intros Hfac (τ & H). *)
(*   red. *)
(*   assert (forall (f : Q -> A) (i : I) (o : O), *)
(*              (exists n : nat, evalt (τ i) (fun q => ret (f q)) n =! inr (F f i))). *)
(*   { intros. setoid_rewrite H. eapply Hfac. } *)

(*   unshelve epose (fix τ (i : I) (l : list A) n := *)
(*        match n, l with *)
(*        | 0, nil => _ *)
(*        | S n, _ => match τ i (firstn n l) n with *)
(*                   | Some (inl (qs, q)) => _ *)
(*                   | Some (inr o) => Some (inr o) *)
(*                   | None => None *)
(*                   end *)
(*        | _, _ => None *)
(*        end). *)

(*   1:{ specialize (H0 (fun _ => a0) i o0). *)
(*       eapply mu_nat.mu_nat_dep in H0 as [k Hk]. *)
(*       destruct k; cbn in Hk. *)
(*       - eapply bid *)


(*   (* compute the index in H0, then use it in the def of τ *) *)
