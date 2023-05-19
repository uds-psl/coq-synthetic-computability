Require Import List Lia Arith.
Import ListNotations.

Set Default Goal Selector "!".

Section pos.

  Context {X : Type}.
  Variable d : forall x y : X, {x = y} + {x <> y}.

  Fixpoint pos (x : X) (l : list X) : nat :=
    match l with
      [] => 0
    | x' :: l => if d x x' then 0 else S (pos x l)
    end.

  Lemma nth_error_pos : forall x (l : list X), In x l -> nth_error l (pos x l) = Some x.
  Proof.
    induction l as [ | x' l IH]; cbn; [ tauto | ].
    intros [? | Hl];  destruct (d x x'); subst; firstorder.
  Qed.

  Lemma pos_app : forall (x : X) A B,  In x A -> pos x (A ++ B) = pos x A.
  Proof.
    induction A as [ | a]; cbn; [tauto | ].
    intros B [? | Hl]; destruct (d x a); subst; firstorder.
  Qed.

  Lemma pos_length : forall (x : X) l, In x l -> pos x l < length l.
  Proof.
    intros. eapply nth_error_Some. rewrite nth_error_pos; congruence.
  Qed.

  Lemma pos_prop (x : X) l1 l2 : In x (l1 ++ l2) -> length l1 > pos x (l1 ++ l2) -> In x l1.
  Proof.
    intros H Hlen.
    destruct (in_dec d x l1) as [| Hl1]; eauto.
    eapply in_app_iff in H as H'. destruct H' as [ | Hl2]; eauto.
    eapply nth_error_pos in H.
    rewrite nth_error_app1 in H; eauto.
    eapply nth_error_In; eauto.
  Qed.

End pos.

Class good X :=
  {
    e : nat -> list X ;                                      (* a list enumerator *)
    e_prefix : forall n1 n2, n1 <= n2 -> exists l, e n2 = e n1 ++ l ; (* which is cumulative *)
    e_spec : forall n, NoDup (e n) ;                            (* and duplicate-free *)
    occ : X -> nat ;                                         (* an occurrence function *)
    occ_spec : forall x, In x (e (occ x)) ;                    (* which indicates where elements occur in the list enumerator *)
  }.

Class better X (g : good X) :=
  {
    index : X -> nat ;             (* an index function *)
    index_spec : forall x n, In x (e n) \/ length (e n) > index x -> nth_error (e n) (index x) = Some x ;
       (* which specifies at which _position_ in the enumerator e an element occurs *)
  
    gen : list X -> nat ;          (* a generator function used to produce a long enough sequence *)
    gen_spec : forall l, NoDup l -> length (e (gen l)) >= length l
  }.

Lemma index_spec' {X} (g : good X) (b : better X g)  :
  forall m n (x : X), nth_error (e m) n = Some x -> n = index x.
Proof.
  intros m n x H.
  unshelve epose proof (index_spec x m _) as E. 1: eauto using nth_error_In.
  eapply NoDup_nth_error.
  - eapply e_spec.
  - eapply nth_error_Some. rewrite H. congruence.
  - congruence.
Qed.

Lemma list_max_max x l : In x l -> x <= list_max l.
Proof.
  induction l; cbn. 1: firstorder.
  intros [-> | H].
  - lia.
  - eapply IHl in H. unfold list_max in *. lia.
Qed.

Lemma NoDup_map {X Y} (f : X -> Y) l :
  ( forall x1 x2, f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
  induction 2; cbn; econstructor.
  1: intros (? & ? % H & ?) % in_map_iff.
  all: firstorder congruence.
Qed.

(* Every good type can be made better *)
Section get_better.

  Variables (X : Type) (gX : good X).

  Definition gen_ (l : list X) :=
    list_max (map occ l).

  Lemma gen_spec_ : forall l, NoDup l -> length (e (gen_ l)) >= length l.
  Proof.
    intros l Hl. eapply NoDup_incl_length; eauto.
    intros x Hx.
    pose proof (occ_spec x).
    unfold gen_.
    assert (occ x <= list_max (map occ l)) as Hle. { eapply list_max_max, in_map_iff; eauto. }
    eapply e_prefix in Hle as [l' ->].
    eapply in_app_iff; eauto.
  Qed.
  
  Variable (d : forall x0 y : X, {x0 = y} + {x0 <> y}).

  Definition index_ (x : X) :=
    pos d x (e (occ x)).

  Lemma index_spec_ : forall x n, In x (e n) \/ length (e n) > index_ x -> nth_error (e n) (index_ x) = Some x.
  Proof.
    intros x n [H | H]; unfold index_ in *.
    - pose proof (occ_spec x).
      destruct (Nat.le_ge_cases n (occ x)).
      + eapply e_prefix in H1 as [l' E]. rewrite E in *. clear E.
        rewrite pos_app; eauto. now eapply nth_error_pos.
      +eapply e_prefix in H1 as [l' E]. rewrite E in *. clear E.
       rewrite nth_error_app1. 1: now eapply nth_error_pos.
       now eapply pos_length.
    - pose proof (occ_spec x).
      destruct (Nat.le_ge_cases n (occ x)).
      + eapply e_prefix in H1 as [l' E]. rewrite E in *. clear E.
        eapply pos_prop in H; eauto.
        rewrite pos_app; eauto. now eapply nth_error_pos.
      + eapply e_prefix in H1 as [l' E]. rewrite E in *. clear E.
        rewrite nth_error_app1. 1: now eapply nth_error_pos.
        now eapply pos_length.
  Qed.

  Lemma index_spec'_ :
    forall m n x, nth_error (e m) n = Some x -> n = index_ x.
  Proof. 
    intros m n x H. eapply NoDup_nth_error.
    3:{ rewrite H. symmetry. eapply index_spec_. left. eapply nth_error_In; eauto. }
    - eapply e_spec.
    - eapply nth_error_Some. rewrite H; congruence.
  Qed.

End get_better.

#[export] Hint Resolve occ_spec e_spec.

Notation injective f := (forall x1 x2, f x1 = f x2 -> x1 = x2).

(*
  Given x, the bijection gets the element at the index n of x in the enumeration of Y,
  which exists because there are more than n elements of X, and via the injection more than n elements of Y
 *)

Section Def_F.

  Variables (X Y : Type) (gX : good X) (gY : good Y) (bX : better X gX) (bY : better Y gY).

  Variable f : X -> Y.
  Variable f_spec : injective f.

  Lemma index_length :
    forall x : X, index x < length (e (gen (map f (e (occ x))))).
  Proof.
    intros x.
    eapply lt_le_trans.
    2: eapply gen_spec. 2:eapply NoDup_map; eauto.
    rewrite map_length.
    eapply nth_error_Some.
    rewrite index_spec. 1:congruence.
    left. eauto.
  Qed.

  Lemma always_Some (x : X) :
    nth_error (e (gen (map f (e (occ x))))) (index x) <> None.
  Proof.
    intros E. eapply nth_error_None in E. revert E.
    eapply lt_not_le, index_length.
  Qed.
    
  Definition F_ (x : X) : Y :=
    match nth_error (e (gen (map f (e (occ x))))) (index x) with
    | Some y => y
    | None => f x
    end.

End Def_F.

Section Cantor_Bernstein.

  Variables (X Y : Type) (gX : good X) (gY : good Y) (bX : better X gX) (bY : better Y gY).

  Variables (f : X -> Y) (f_spec : injective f).
  Variables (g : Y -> X) (g_spec : injective g).

  Definition F (x : X) := F_ X Y gX gY bX bY f x.
  Definition G (y : Y) := F_ Y X gY gX bY bX g y.

  Lemma FG x :
    G (F x) = x.
  Proof.
    unfold F, F_.
    destruct (nth_error (e (gen (map f (e (occ x))))) (index x) ) eqn:E. 
    2: now eapply always_Some in E; eauto.
    unfold G, F_.
    destruct (nth_error (e (gen (map g (e (occ y))))) (index y)) eqn:E'.
    2: now eapply always_Some in E'; eauto.
    eapply index_spec' in E. rewrite <- E in E'.
    rewrite index_spec in E'. 1: congruence.
    right. rewrite E. eapply index_length. eauto.
  Qed.

End Cantor_Bernstein.

Lemma Cantor_Bernstein  (X Y : Type) (dX: forall x0 y : X, {x0 = y} + {x0 <> y})
      (dY : forall x0 y : Y, {x0 = y} + {x0 <> y})
      (gX : good X) (gY : good Y)
      (f : X -> Y) (f_spec : injective f)
      (g : Y -> X) (g_spec : injective g) :
  exists (F : X -> Y) (G : Y -> X), (forall x, G (F x) = x) /\ (forall y, F (G y) = y).
Proof.
  assert (better X gX * better Y gY) as [].
  { split; econstructor; unshelve eauto using index_spec_, index_spec'_, gen_spec_; eauto. }
  do 2 eexists. split; unshelve eapply FG; eauto.
Qed.
