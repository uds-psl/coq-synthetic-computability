Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.Shared.Pigeonhole.
Require Import SyntheticComputability.Shared.FinitenessFacts.
Require Import SyntheticComputability.Synthetic.reductions SyntheticComputability.Synthetic.truthtables.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Import SyntheticComputability.Shared.ListAutomation.
Require Import List Arith.

Import Assume_EA.
Import ListNotations ListAutomationNotations.

Definition majorizes (f: nat -> nat) (p: nat -> Prop): Prop
  := forall n, ~~ exists L, length L = n /\ NoDup L /\
               forall x, In x L -> x <= f n /\ p x.

Definition exceeds f (p : nat -> Prop) :=
  forall n, ~~ exists i, n < i <= f n /\ p i.

Lemma exceeds_majorizes f p :
  exceeds f p -> majorizes (fun n => Nat.iter n f 0) p.
Proof.
  intros He n. induction n.
  - cprove exists []. repeat split. 
    + econstructor.
    + inversion H.
    + inversion H.
  - cunwrap. destruct IHn as (l & <- & IH1 & IH2).
    specialize (He (Nat.iter (length l) f 0)). cunwrap.
    destruct He as (i & [H1 H2] & H3).
    cprove exists (i :: l).
    split; [ | split].
    + reflexivity.
    + econstructor. intros [] % IH2. 2:eauto. lia.
    + intros m [-> | [H4 H5] % IH2]; split; eauto.
      rewrite numbers.Nat_iter_S in *. lia.
Qed.

Lemma cantor_infinite_exceeds (p q : nat -> Prop) :
  (forall x, q x -> p x) -> cantor_infinite q -> exists f, exceeds f p.
Proof.
  intros Hq [F] % cantor_infinite_spec. 2: exact _.
  exists (fun n => proj1_sig (F (seq 0 (S n)))).
  intros n. destruct F as [i [Hi1 Hi2]]; cbn.
  cprove exists i; repeat split; eauto.
  destruct (lt_dec n i); eauto.
  destruct Hi1. eapply in_seq. split. lia. cbn. lia.
Qed.

Definition ttId := Assume_EA.TT.

Lemma IsFilter_NoDup {X} l l' (p : X -> Prop) :
  IsFilter p l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; inversion 1; subst.
  - eauto.
  - econstructor. eapply IsFilter_spec in H as (? & ? & ?).  firstorder. eauto.
  - eauto.
Qed.

From SyntheticComputability.Shared.Libs.PSL Require Import Power EqDec.

Definition gen (n : nat) : list (list nat) := power (seq 0 (S n)).

Lemma dupfree_Nodup {X} (A : list X) :
  Dupfree.dupfree A <-> NoDup A.
Proof.
  induction A;split;intros H;inv H;repeat econstructor;tauto.
Qed.

Lemma dupfree_rep {X : eqType} (A : list X) U : Dupfree.dupfree U -> Dupfree.dupfree (rep A U).
Proof.
  induction 1.
  - cbn. econstructor.
  - cbn. destruct Dec; cbn.
    + econstructor. intros ? % in_filter_iff. 1:firstorder.
      exact IHdupfree.
    + exact IHdupfree.
Qed.

Lemma gen_spec' n l : NoDup l -> list_max l <= n -> exists l', NoDup l' /\ (forall z, In z l <-> In z l') /\ In l' (gen n).
Proof.
  intros H1 % dupfree_Nodup H2.
  exists (@rep (EqDec.EqType nat) l (seq 0 (S n))). split; [ | split].
  - eapply dupfree_Nodup, dupfree_rep, dupfree_Nodup, seq_NoDup.
  - intros z. rewrite rep_equi. reflexivity. intros x Hx.
    eapply list_max_le, Forall_forall in H2. eapply in_seq. 2:eauto. cbn. lia.
  - eapply (@rep_power (EqDec.EqType nat)).
Qed.

Lemma power_length {X : eqType} (l : list X) : length (power l) = 2 ^ (length l).
Proof.
  induction l; cbn.
  - reflexivity.
  - rewrite app_length, map_length, <- IHl. lia.
Qed.

Lemma gen_length n : length (gen n) = 2 ^ (S n).
Proof.
  unfold gen.
  now rewrite power_length, seq_length.
Qed.

Definition star_of p n := (fun z => (~~ p z /\ z <= n) \/ z > n).

Lemma star_of_nnex n p : (* listable until *)
  ~~ exists i, i < 2^(S n) /\ forall z, ~ In z (nth i (gen n) []) <-> star_of p n z.
Proof.
  enough (~~ exists l, list_max l <= n /\ NoDup l /\ forall z, ~ In z l <-> star_of p n z).
  - cunwrap. destruct H as (l & H1 & H2 & H3).
    epose proof (@gen_spec' n l) as H.
    specialize (H ltac:(firstorder) ltac:(firstorder)) as (l' & H4 & H5 & H6).
    eapply In_nth in H6 as (i & ? & ?).
    cprove exists i. split. rewrite <- gen_length. eauto.
    rewrite H0. setoid_rewrite <- H5. eassumption.
  - pose proof (IsFilter_nnex (seq 0 (S n)) (compl p)). cunwrap.
    destruct H as (l' & Hf). pose proof Hf as (H1 & H2 & H3) % IsFilter_spec.
    cprove exists l'. split. 2:split.
    + eapply list_max_le, Forall_forall. intros ? [? % in_seq _] % H3. lia.
    + eapply IsFilter_NoDup; eauto. eapply seq_NoDup.
    + intros. rewrite H3. unfold star_of. rewrite in_seq. split.
      * intros ?. assert (z <= n \/ z > n) as [Hz | Hz] by lia.
        -- left. split; eauto. intros Hp. eapply H. split. cbn. lia. eauto.
        -- right. eauto.
      * intros [[] | ] [ ]. tauto. lia.
Qed.

(* instead: listable quantification *)
Lemma finite_quant_DN n m (p : nat -> Prop) : (forall i, n < i <= m -> ~~ p i) -> ~~ (forall i, n < i <= m -> p i).
Proof.
  assert (n < m \/ m <= n) as [Hnm | ] by lia. 2:{ intros. cprove intros. lia. } 
  intros H. induction m in n, Hnm, H |- *.
  - cprove intros. lia.
  - ccase (p (S m)) as [Hp | Hp].
    + assert (n = m \/ n < m) as [] by lia.
      * subst. cprove intros. assert (i = S m) as ->  by lia. eauto.
      * intros ?. eapply IHm.
        -- eassumption.        
        -- intros. destruct (Nat.eqb_spec i (S m)); subst. eauto. eapply H. lia.
        -- intros IH. eapply H1. intros. destruct (Nat.eqb_spec i (S m)); subst. eauto. eapply IH. lia.
    + exfalso. eapply H. 2: eauto. lia.
Qed.

Lemma nnex_forall_class n m p :
  ~~ (exists i, n < i <= m /\ ~ p i) <-> ~ forall i, n < i <= m -> p i.
Proof.
  split.
  - intros H Hi. apply H. intros (i & ? & ?). eauto.
  - intros H Hi. apply finite_quant_DN in H. apply H. intros ? ? ?.
    apply Hi. eauto.
Qed.

Notation "p ⊨ QT" := (forall L, Forall2 reflects L (map p (projT1 QT)) -> eval_tt (projT2 QT) L = true) (at level 50).
Notation "l ⊫ QT" := (eval_tt QT l = true) (at level 50).

Lemma list_reflects L : ~~ exists l, Forall2 reflects l L.
Proof.
  induction L as [ | P L].
  - cprove exists []. econstructor.
  - cunwrap. destruct IHL as (l & IH).
    ccase P as [H | H].
    + cprove exists (true :: l). econstructor; firstorder.
    + cprove exists (false :: l). econstructor; firstorder.
Qed.

Lemma reflects_ext b1 b2 p q : reflects b1 p -> reflects b2 q -> p <-> q -> b1 = b2.
Proof.
  destruct b1, b2; firstorder congruence.
Qed.

Lemma list_max_in x l : In x l -> x <= list_max l.
Proof.
  induction l; cbn.
  - firstorder.
  - intros [-> | ]. lia. eapply IHl in H. unfold list_max in H. lia.
Qed.

Theorem tt_complete_exceeds p :
  K0 ⪯ₜₜ p -> exists f, exceeds f (compl p).
Proof.
  intros [g Hg].
  destruct (ttId g) as [c Hc].
  pose (a n i := c (nth i (gen n) [])).
  exists (fun n => 1 + list_max (concat [ projT1 (g (a n i)) | i ∈ seq 0 (2^(S n))])).
  intros n. eapply nnex_forall_class. intros H.
  eapply (@star_of_nnex n p). intros (i & Hi1 & Hi2).
  assert (forall j, n < j /\ In j (projT1 (g (a n i))) -> p j). {
    intros j (H1 & H2). eapply H. split.
    - lia.
    - match goal with [ |- _ <= 1 + ?J] => enough (j <= J) by lia end.
      eapply list_max_in. eapply in_concat_iff. eexists. split. eassumption.
      eapply in_map_iff. exists i. split. eauto. eapply in_seq. lia.
   }
   assert (forall x, In x (projT1 (g (a n i))) -> ~~ p x <-> star_of p n x). {
     intros x Hx.
     assert (x <= n \/ n < x) as [HH | HH] by lia.
    - unfold star_of. split. intros ?. left. eauto. intros [[]|]. eauto. lia.
    - unfold star_of. split; eauto.
   } red in Hg. unfold reflects in Hg.
   apply (@list_reflects (map p (projT1 (g (a n i))))).
   intros (lp & Hlp). 
   pose proof (Hg _ _ Hlp) as H2.
   enough (lp ⊫ projT2 (g (a n i)) <-> ~ lp ⊫ projT2 (g (a n i))) by tauto.
   rewrite <- H2 at 1.
   unfold K0.
   unfold a at 1.
   rewrite Hc. fold (a n i).
   rewrite <- Bool.not_true_iff_false.
   unfold not.
   match goal with [ |- (?l1 ⊫ _ -> False) <-> (?l2 ⊫ _ -> False)] => enough (l1 = l2) by now subst end.
   clear - Hlp H1 Hi2.
   revert H1 Hlp Hi2. generalize (projT1 (g (a n i))) as L. clear. 
   induction lp; intros L Hpstar Hlp Hlist; cbn -[nth].
   - destruct L; inv Hlp. reflexivity.
   - destruct L; inv Hlp. cbn -[nth].
     f_equal.
     + specialize (Hpstar n0 ltac:(firstorder)). rewrite <- Hlist in Hpstar.
       eapply reflects_ext. eapply decider_complement. 2: eapply H2.
       intros l.
       eapply (inb_spec _ (uncurry Nat.eqb) (decider_eq_nat) (n0 , l)).
       unfold reflects in H2. rewrite H2 in *. rewrite Bool.not_true_iff_false, Bool.not_false_iff_true in Hpstar. 
       symmetry. eapply Hpstar.
     + eapply IHlp. intros. eapply Hpstar. eauto. eauto. eauto.
Qed.

From SyntheticComputability Require Import principles.

Definition hypersimple (p: nat -> Prop) : Prop
  := enumerable p /\ ~ exhaustible (compl p) /\
      ~ exists f, majorizes f (compl p).

Lemma hyperimmune_immune p :
  MP -> ~ (exists f, majorizes f p) -> ~ exists q : nat -> Prop, (forall x, q x -> p x) /\ ~ exhaustible q /\ enumerable q.
Proof.
  intros mp Hi (q & Hsub & Hinf & Henum).
  eapply MP_non_finite_generative in Hinf; eauto.
  eapply MoreEnumerabilityFacts.generative_cantor_infinite in Hinf; eauto.
  eapply cantor_infinite_exceeds in Hinf as (f & Hexc); eauto.
  eapply Hi. eexists. eapply exceeds_majorizes; eauto.
Qed.

Lemma hypersimple_tt_incomplete p :
  hypersimple p -> ~ (forall q : nat -> Prop, enumerable q -> q ⪯ₜₜ p).
Proof.
  intros (He & Hinf & Himm) H.
  specialize (H _ K0_enum).
  eapply tt_complete_exceeds in H as (f & H).
  eapply Himm. eexists. eapply exceeds_majorizes; eauto.
Qed.

From SyntheticComputability Require Import simple.

Lemma hypersimple_simple p :
  MP -> hypersimple p -> simple p.
Proof.
  intros mp (He & Hinf & Himm). repeat split; eauto.
  intros (q & Heq & Hinfq & Hsub).
  eapply hyperimmune_immune; eauto.
Qed.
