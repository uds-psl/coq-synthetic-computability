From stdpp Require Import prelude.
Require Import List Lia.

Import ListNotations.

Local Notation "x 'el' L" := (In x L) (at level 60).

Section Positions.
  Variables (X: Type) (d: forall x y : X, {x = y} + {x <> y}).
  Implicit Types (x y: X) (A B : list X).

  Fixpoint pos x A : option nat :=
    match A with
    | nil => None
    | y :: A' => if d x y then Some 0
                else match pos x A' with
                     | Some n => Some (S n)
                     | None => None
                     end
    end.  

  Lemma el_pos x A :
    x el A -> { n | pos x A = Some n }.
  Proof.
    induction A as [|y A IH]; cbn; intros H.
    - destruct H as [].
    - destruct (d x y) as [<-|H1].
      + now exists 0.
      + destruct IH as [n IH].
        * destruct H as [->|H]; tauto.
        * rewrite IH. now exists (S n).
  Qed.

  Notation nthe n A := (nth_error A n).
  
 Lemma pos_nthe x A n :
    pos x A = Some n -> nthe n A = Some x.
 Proof.
   revert n.
   induction A as [|y A IH]; cbn; intros n.
   - intros [=].
    - destruct (d x y) as [<-|H1].
      + now intros [= <-].
      + destruct (pos x A) as [k|]; intros [= <-]; cbn.
        now apply IH.
 Qed.

 Lemma pos_app_1 x A1 A2 :
   ~ x el A2 ->
   pos x (A1 ++ A2) = pos x A1.
 Proof.
   intros H.
   induction A1.
   - cbn. destruct (pos x A2) eqn:E; try congruence.
     eapply pos_nthe in E as ? % nth_error_In. firstorder.
   - cbn. destruct d.
     + reflexivity.
     + rewrite IHA1. reflexivity.
 Qed.

 Lemma pos_app_2 x A1 A2 :
   ~ x el A1 ->
   pos x (A1 ++ A2) = match pos x A2 with Some n => Some (length A1 + n) | _ => None end.
 Proof.
   intros H.
   induction A1.
   - cbn. destruct (pos x A2) eqn:E; try congruence.
   - cbn. destruct d.
     + subst. firstorder.
     + rewrite IHA1; firstorder. destruct (pos x A2); firstorder. 
 Qed.

 Lemma pos_map (f : X -> X) x l:
   Inj (=) (=) f -> pos (f x) (map f l) = pos x l.
 Proof.
   intros Hf.
   induction l; cbn.
   - reflexivity.
   - destruct d as [-> % Hf | E].
     + destruct d; try congruence.
     + destruct d; try congruence.
       now rewrite IHl.
 Qed.

 Lemma NoDup_nth_error l n1 n2 x :
   NoDup l ->
   nth_error l n1 = Some x -> nth_error l n2 = Some x -> n1 = n2.
 Proof.
   induction 1 in n1, n2 |- *.
   - destruct n1, n2; cbn; congruence.
   - destruct n1, n2; cbn.
     + try congruence.
     + now intros [= ->] ? % nth_error_In. 
     + now intros ? % nth_error_In [= ->].
     + intros. f_equal; eauto.
 Qed.

End Positions.

Arguments pos {_ _} _ _.

Fixpoint gen_lists (n : nat) : list (list bool).
Proof.
  destruct n.
  - exact [ [] ].
  - exact (map (cons true) (gen_lists n) ++ map (cons false) (gen_lists n)).
Defined.

Lemma gen_list_spec n l : length l = n <-> l el gen_lists n.
Proof.
  induction n in l |- *.
  - destruct l; cbn; firstorder (lia || congruence).
  - split.
    + destruct l; intros [= <-]. eapply in_app_iff.
      destruct b; [ left | right]; eapply in_map_iff;
        exists l; firstorder.
    + cbn. intros [(? & <- & ?) % in_map_iff | (? & <- & ?) % in_map_iff ] % in_app_iff; cbn; firstorder.
Qed.

Lemma NoDup_app {X} (l1 l2 : list X) :
  NoDup l1 -> NoDup l2 -> (forall x, x el l1 -> ~ (x el l2)) -> NoDup (l1 ++ l2).
Proof.
  induction 1 in l2 |- *.
  - eauto.
  - intros Hl2 Hel. cbn. econstructor. 2:eapply IHNoDup; eauto.
    + intros [ | ] % in_app_iff; firstorder.
    + firstorder.
Qed.

Lemma NoDup_map {X Y} (f : X -> Y) l :
  Inj (=) (=) f -> NoDup l -> NoDup (map f l).
Proof.
  induction 2; cbn; econstructor.
  intros (? & ? % H & ?) % in_map_iff.
  all: firstorder congruence.
Qed.

Lemma gen_list_NoDup n : NoDup (gen_lists n).
Proof.
  induction n; cbn.
  - repeat econstructor; firstorder.
  - eapply NoDup_app.
    + eapply NoDup_map; firstorder congruence.
    + eapply NoDup_map; firstorder congruence.
    + intros ? (? & <- & ?) % in_map_iff (? & ? & ?) % in_map_iff.
      congruence.
Qed.

Definition truthtable : Type := 
  list bool.

Definition eq_dec_list_bool : forall l1 l2 : list bool, {l1 = l2} + {l1 <> l2}.
Proof.
  intros. repeat decide equality.
Defined.

Definition eval_tt : forall t : truthtable, forall l : list bool, bool.
Proof.
  intros t l.
  destruct (@pos (list bool) (eq_dec_list_bool) l (gen_lists (length l))) as [i | ].
  + destruct (nth_error t i) as [b | ].
    * exact b.
    * exact false.
  + exact false.  
Defined.

Definition mk_tt : (list bool -> bool) -> nat -> truthtable.
Proof.
  intros f n.
  refine (map f (gen_lists n)).
Defined.

Lemma eval_tt_mk_tt : forall l f, eval_tt (mk_tt f (length l)) l = f l.
Proof.
  intros l f.
  unfold eval_tt.
  pose proof (gen_list_spec (length l) l) as [H % (fun H => H eq_refl) _].
  eapply el_pos in H as [i Hi].
  rewrite Hi.
  eapply pos_nthe in Hi.
    unfold mk_tt.
  now erewrite map_nth_error.
Qed.

Lemma eval_tt_mk_tt' : forall n l f, length l = n -> eval_tt (mk_tt f n) l = f l.
Proof.
  intros n l f <-; now eapply eval_tt_mk_tt. 
Qed.

Arguments mk_tt _ _, _ {_}.

Lemma nth_error_eq {X} (l1 l2 : list X) :
  length l1 = length l2 ->
  (forall n, n < length l1 -> nth_error l1 n = nth_error l2 n) ->
  l1 = l2.
Proof.
  induction l1 as [ | a l1 IH  ]in l2 |- *; intros Hle Heq.
  - destruct l2; cbn in *; congruence.
  - destruct l2 as [ | b l2]; cbn in *; try congruence.
    f_equal.
    + specialize (Heq 0 ltac:(lia)). cbn in Heq. congruence.
    + eapply IH.
      * lia.
      * intros. eapply (Heq (S n)). lia.
Qed.

From Equations Require Import Equations.

Fixpoint ext_eval_tt' (n : nat) (t : truthtable) (l : Vector.t Prop n) : Prop.
Proof.
  induction n.
  - destruct t.
    + exact False.
    + exact (is_true b).
  - exact ((~ ext_eval_tt' n t (Vector.tl l) -> ~ @Vector.hd Prop _ l) /\
           (~ ext_eval_tt' n (drop (length (gen_lists n)) t) (Vector.tl l) -> @Vector.hd Prop _ l)).
Defined.

(* (* From Undecidability.Shared.Libs.PSL Require Import Vectors. *) *)
Lemma nth_error_drop:
  ∀ (t : truthtable) (n0 m : nat), nth_error (drop m t) n0 = nth_error t (m + n0).
Proof.
  intros t n0 m.
  assert (m <= length t \/ m > length t) as [H | H] by lia.
  - rewrite <- (firstn_skipn m t).
    rewrite nth_error_app2.
    rewrite drop_app_le. rewrite skipn_firstn_comm.
    rewrite minus_diag. rewrite firstn_O. cbn. f_equal.
    assert (length (take m t) = m). rewrite take_length. lia. lia. rewrite take_length. lia. rewrite take_length. lia.
  - rewrite drop_ge. 2: lia.
    assert (nth_error [] n0 = None) as -> by now destruct n0.
    symmetry. eapply nth_error_None. lia.
Qed.

Lemma truthtable_extension' n t :
    forall l, ext_eval_tt' n t (Vector.map (eq true) l) <-> eval_tt t (Vector.to_list l) = true.
Proof.
  intros. 
  induction l in t |- *.
  + cbn. destruct t. firstorder congruence. reflexivity.
  + cbn. fold (Vector.to_list l). rewrite !IHl. clear.
    unfold eval_tt. cbn.
    destruct h.
    * cbn. rewrite pos_app_1. 2: intros (? & [= [=]] & ?) % in_map_iff. 
      rewrite pos_map. 2: firstorder congruence.
      destruct pos. destruct nth_error eqn:E. 2,3 : firstorder congruence.
      split.
      -- intros []. destruct b. firstorder. destruct H; congruence.
      -- intros ->. split. firstorder. firstorder.
    * cbn. rewrite pos_app_2. 2: intros (? & [= [=]] & ?) % in_map_iff. 
      rewrite pos_map. 2: firstorder congruence.
      destruct pos. destruct nth_error eqn:E. all: try now firstorder congruence.
      all: rewrite map_length.
      all: replace (length (Vector.to_list l)) with n.
      2, 4: clear; induction l; cbn in *; now f_equal.
      all: generalize (length (gen_lists n)); intros m.
      all: rewrite nth_error_drop.
      - destruct (nth_error t (m + n0)) eqn:E2.
        destruct b, b0; firstorder congruence.
        destruct b; firstorder congruence.
      - destruct (nth_error t (m + n0)) eqn:E2.
        destruct b; firstorder congruence.
        firstorder congruence.
Qed.

Definition ext_eval (t : truthtable) (l : list Prop) :=
  ext_eval_tt' (length l) t (Vector.of_list l).

Lemma truthtable_extension t :
    forall l, ext_eval t (map (eq true) l) <-> eval_tt t l = true .
Proof.
  intros l. unfold ext_eval.
  pose proof (truthtable_extension' (length l) t (Vector.of_list l)).
  rewrite Vector.to_list_of_list_opp in H. rewrite <- H.
  clear. 
  induction l in t |- *.
  - cbn. reflexivity.
  - cbn. rewrite <- !IHl. now rewrite (map_length (eq true) l) at 3.
Qed.

(* 
Require Import Eqdep_dec.

Lemma ext_tt {n} (t1 t2 : truthtable n) :
  (forall l, length l = n -> eval_tt t1 l = eval_tt t2 l)
  -> t1 = t2.
Proof.
  intros. destruct t1 as [t1 Ht1], t2 as [t2 Ht2].
  enough (t1 = t2). subst. f_equal. eapply UIP_dec. decide equality.
  eapply nth_error_eq. congruence.
  intros i Hi. rewrite Ht1 in Hi.
  destruct (nth_error (gen_lists n) i) eqn:Eq. 2:{ 
    eapply nth_error_Some in Hi. congruence.
  } 
  assert (Hl : length l = n). {
    eapply gen_list_spec, nth_error_In; eauto.
  }
  specialize (H l Hl). unfold eval_tt in H.
  destruct nat_eq_dec; try congruence.
  destruct pos eqn:Epos.
  - cbn in *. eapply pos_nthe in Epos.
    eapply NoDup_nth_error in Epos; eauto. 2:eapply gen_list_NoDup.
    subst.
    destruct (nth_error t1 n0) eqn:E1, (nth_error t2 n0) eqn:E2.
    + congruence.
    + eapply nth_error_None in E2. enough (n0 < length t1) by lia.
      eapply nth_error_Some. congruence.
    + eapply nth_error_None in E1. enough (n0 < length t2) by lia.
      eapply nth_error_Some. congruence.
    + reflexivity.
  - exfalso. eapply nth_error_In, el_pos in Eq as [? He].
    rewrite He in Epos. congruence.
Qed.
 *)
