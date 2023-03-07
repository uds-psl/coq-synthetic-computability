Require Import Setoid.
Set Default Goal Selector "!".

Definition MP_prop:= forall A : nat -> Prop, (forall n, A n \/ ~ A n) -> ~~ (exists n, A n) -> exists n, A n.

Definition Sigma_0_1 {X} (p : X -> Prop) :=
  exists A : X -> nat -> Prop, (forall x n, A x n \/ ~ A x n) /\ forall x, p x <-> exists n, A x n.

Definition MP_pred :=
  forall X, forall p : X -> Prop, Sigma_0_1 p ->
              forall x, ~~ p x -> p x.

Definition MP_funrel :=
  forall R : nat -> bool -> Prop, (forall x, exists y, R x y) ->
                    (forall x y1 y2, R x y1 -> R x y2 -> y1 = y2) ->
                    ~~ (exists n, R n true) -> exists n, R n true.

Definition Post :=
  forall p : nat -> Prop, Sigma_0_1 p ->
                Sigma_0_1 (fun n => ~ p n) ->
                forall n, p n \/ ~ p n.

Lemma MP_to_MP_semidecidable :
  MP_prop-> MP_pred.
Proof.
  intros mp X p [A [HA H]] x Hx.
  rewrite H in *. eapply mp; eauto.
Qed.

Lemma MP_to_MP_funrel :
  MP_prop-> MP_funrel.
Proof.
  intros mp R Htot Hfun H.
  eapply mp. 2: auto.
  intros n. destruct (Htot n) as [ [] Hb].
  - eauto.
  - right. intros Ht. enough (true = false) by congruence. eapply Hfun; eauto.
Qed.

Lemma MP_funrel_to_MP_pred :
  MP_funrel -> MP_prop.
Proof.
  intros mp A HA H.
  destruct (mp (fun x b => b = true <-> A x)) as [n Hn].
  - intros n. destruct (HA n) as [Hn | Hn].
    + exists true. firstorder.
    + exists false. clear - Hn. firstorder congruence.
  - clear. intros. destruct y1, y2; firstorder congruence.
  - firstorder.
  - firstorder.
Qed.

Lemma MP_pred_MP_prop:
  MP_pred -> MP_prop.
Proof.
  intros mp A HA.
  red in mp. eapply (mp unit (fun _ => exists n, A n)). 2: exact tt.
  exists (fun _ => A). firstorder.
Qed.

Lemma MP_pred_Post :
  MP_pred -> Post.
Proof.
  intros mp p [A1 [HA1 H1]] [A2 [HA2 H2]].
  intros n. rewrite H2, H1. pattern n. eapply mp.
  - exists (fun x n => A1 x n \/ A2 x n). split.
    + intros x n0. destruct (HA1 x n0), (HA2 x n0); tauto.
    + firstorder.
  - rewrite <- H1, <- H2. tauto.
Qed.

Lemma Post_MP_prop:
  Post -> MP_prop.
Proof.
  intros post A HA H.
  destruct (post (fun m : nat => exists n, A n)) with (n := 0).
  - exists (fun x n => A n). firstorder.
  - exists (fun x n => False). firstorder.
  - tauto.
  - tauto.
Qed.

