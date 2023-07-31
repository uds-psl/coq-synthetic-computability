Local Set Implicit Arguments.
Local Unset Strict Implicit.

Require Import List Lia.
Import ListNotations.

Definition functional {X Y} (R : X -> Y -> Prop) :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

Record FunRel X Y := {the_rel :> X -> Y -> Prop ; the_func_proof : functional the_rel}.
Arguments the_rel {_ _}.

Notation "R <<= S" := (forall x y, R x y -> S x y) (at level 30).
Notation "R == S" := (forall x y, R x y <-> S x y) (at level 30).

Section Cont.

  Variable X Y I O : Type.

  Hypothesis FRE : forall (R S : FunRel X Y), R == S -> R = S.

  Implicit Type f g R : FunRel X Y.

  Definition directed (P : FunRel X Y -> Prop) :=
    forall f g, P f -> P g -> exists h, P h /\ f <<= h /\ g <<= h.

  Definition union (P : FunRel X Y -> Prop) : X -> Y -> Prop :=
    fun n b => exists f, P f /\ f n b.

  Definition directed_union (P : FunRel X Y -> Prop) :
    directed P -> FunRel X Y.
  Proof.
    intros H. exists (union P). intros n b b' [f Hf] [g Hg].
    destruct (H f g) as (h & H1 & H2 & H3); try tauto.
    apply (@the_func_proof _ _ h n); intuition.
  Defined.

  (* notions related to continuity *)

  Variable r : FunRel X Y -> FunRel I O.

  Definition is_monotone :=
    forall f g, f <<= g -> r f <<= r g.

  Definition modulus_continuous := let F := r in
    forall (R : FunRel X Y) (i : I) (o : O), F R i o -> exists L, (forall i', In i' L -> exists o', R i' o') /\ (forall R', (forall i' o' , In i' L -> R i' o' -> R' i' o') -> F R' i o).

  Definition Bauer_continuous :=
    forall P (H : directed P) n b, (exists f, P f) -> (exists f, P f /\ r f n b) <-> r (directed_union H) n b.

  (* preservation of directed suprema implies existence of moduli *)

  Lemma sub_union f (P : FunRel X Y -> Prop) :
    P f -> f <<= union P.
  Proof.
    firstorder eauto.
  Qed.

  Lemma domain_directed_prefix P (HP : directed P) alpha L :
    P alpha -> (forall n, In n L -> exists b, (directed_union HP) n b)
    -> exists f, P f /\ forall n b, In n L -> (directed_union HP) n b -> f n b.
  Proof.
    intros HA HL. induction L.
    - exists alpha. cbn. split; tauto.
    - destruct (HL a) as [b[f Hf]]; try now left.
      destruct IHL as [f' Hf']; try (intros; apply HL; cbn; tauto).
      destruct (HP f f') as [g Hg]; try tauto.
      exists g. split; try apply Hg. intros n b'. intros [->|Hn] Hb'.
      + destruct Hg as [_[Hg _]]. apply Hg. 
        assert (Hb : (directed_union HP) n b) by (apply sub_union with f; tauto).
        assert (b = b') as <- by (eapply the_func_proof; [apply Hb | apply Hb']). tauto.
      + now apply Hg, Hf'.
  Qed.

  Lemma modulus_continuous_to_Bauer_continuous :
    modulus_continuous -> Bauer_continuous.
  Proof.
    intros HM P HP n b [alpha Ha]. split.
    - intros (f & Hf1 & Hf2). destruct (HM _ _ _ Hf2) as [L HL].
      apply HL. intros n' b' _. now apply sub_union.
    - intros Hr. destruct (HM _ _ _ Hr) as [L[HL1 HL2]].
      destruct (domain_directed_prefix Ha HL1) as [f Hf].
      exists f. split; try tauto. now apply HL2.
  Qed.

  (* converse *)

  Lemma Bauer_continuous_monotone :
    Bauer_continuous -> is_monotone.
  Proof.
    intros r_cont f g H. pose (P h := h = f \/ h = g).
    assert (HP : directed P).
    - intros f' g' H1 H2. exists g. split; try now right.
      destruct H1 as [->| ->], H2 as [->| ->]; intuition.
    - assert (Hg : g = directed_union HP).
      + apply FRE. intros b' n'. split; intros H'; try (exists g; firstorder congruence).
        destruct H' as [h [[->| ->] Hh]]; auto.
      + intros n b Hn. rewrite Hg. apply (r_cont P HP n b).
        * exists f. now left.
        * exists f. split; trivial. now left.
  Qed.

  Lemma frlprefix (f : FunRel X Y) (L : list X) :
    FunRel X Y.
  Proof.
    exists (fun n b => In n L /\ f n b).
    unfold functional. abstract intuition eauto using (@the_func_proof _ _ f).
  Defined.

  Definition lprefixes f : FunRel X Y -> Prop :=
    fun g => exists L, (forall n, In n L -> exists b, f n b) /\ frlprefix f L = g.

  Lemma lprefixes_directed f :
    directed (lprefixes f).
  Proof.
    intros g h [L [HL <-]] [L' [HL' <-]]. exists (frlprefix f (L ++ L')). split.
    + exists (L ++ L'). setoid_rewrite in_app_iff. intuition.
    + cbn. setoid_rewrite in_app_iff. tauto.
  Qed.

  Lemma lprefixes_union f :
    f = (directed_union (@lprefixes_directed f)).
  Proof.
    apply FRE. intros n b. split.
    - intros H. exists (frlprefix f [n]). cbn. split; try tauto.
      exists [n]. cbn. intuition. subst. now exists b.
    - intros [g [[L [HL <-]] HL']]. apply HL'.
  Qed.

  Lemma Bauer_continuous_to_continuous :
    Bauer_continuous -> modulus_continuous.
  Proof.
    intros r_cont f n b Hf. rewrite (lprefixes_union f) in Hf.
    apply r_cont in Hf as [g[[L [HL <-]] Hg]].
    - exists L. split; try apply HL. intros f' Hf.
      refine (Bauer_continuous_monotone r_cont _ Hg).
      cbn. intuition.
    - exists (frlprefix f nil). exists nil. cbn. tauto.
  Qed.

  Theorem equivalence :
    Bauer_continuous <-> modulus_continuous.
  Proof.
    split.
    - apply Bauer_continuous_to_continuous.
    - apply modulus_continuous_to_Bauer_continuous.
  Qed.

  Print Assumptions equivalence.

End Cont.
 

