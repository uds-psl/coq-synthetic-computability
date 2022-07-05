Require SyntheticComputability.Shared.Dec.
Require Import Setoid Morphisms.
Require Export Lia List NPeano.
Import ListNotations.

Fact ldec_stable P :
  P \/ ~ P -> ~~ P -> P.
Proof.
  tauto.
Qed.

Definition DNE := forall P, ~~ P -> P.
Definition LEM := forall P, P \/ ~ P.

Lemma LEM_DNE : LEM <-> DNE.
Proof.
  split.
  - intros lem P. destruct (lem P); intuition.
  - intros dne P. eapply dne. tauto.
Qed.

Lemma DNI (P : Prop) : P -> ~~ P.
Proof.
  tauto.
Qed.

Lemma DN (P : Prop) : P -> ~~ P. Proof. tauto. Qed.
Lemma DN_impl (P Q : Prop) : (P -> ~~Q) -> ~~ P -> ~~ Q. Proof. tauto. Qed.
Lemma neg_impl (P Q : Prop) : (P -> ~Q) -> ~~ P -> ~ Q. Proof. tauto. Qed.

Lemma negative_dn (P Q : Prop) :
  (~~Q -> Q) -> (P -> Q) -> ~~ P -> Q.
Proof.
  tauto.
Qed.

Lemma negative_ca P Q :
  (~~Q -> Q) -> (P \/ ~ P -> Q) -> Q.
Proof.
  intros H1 H2. eapply (negative_dn (P \/ ~P) Q H1 H2). 
  tauto.
Qed.

Definition MP := forall f : nat -> bool, ~~ (exists n, f n = true) -> exists n, f n = true.

Lemma MP_ca (f : nat -> bool) P Q :
  MP ->
  (Q <-> (exists n, f n = true)) ->
  ((P \/ ~ P) -> Q) -> Q.
Proof.
  intros mp ->. eapply negative_ca, mp.
Qed.

Fact computational_explosion (A : Type) : False -> A.
Proof.
  tauto.
Qed.

Fact typecast X (A : X -> Type) (x1 x2 : X) :
  x1 = x2 -> A x1 -> A x2.
Proof.
  now intros ->.
Qed.
  

Tactic Notation "cprove" tactic3(tac) := apply DN; tac.

Lemma DN_dec (P : Prop) `{Dec.dec P} : ~~ P -> P.
Proof.
destruct H as [H | H1]; tauto.
Qed.

Tactic Notation "cunwrap" hyp(H) := 
(revert H; (apply DN_impl || apply neg_impl); intros H).

Tactic Notation "cunwrap" "one" := match goal with [H : ~~ ?P |- _ ] => cunwrap H end.

Tactic Notation "cunwrap" := repeat (cunwrap one).

Lemma ccase_neg P Q : ((P \/ ~ P) -> ~ Q) -> ~ Q.
Proof.
  intros H. assert (H1 : ~~ (P \/ ~P)) by tauto.
  intros q. apply H1. intros [Hp | Hp]; eapply H; eauto.
Qed.

Tactic Notation "ccase" constr(P) "as" intropattern(pat) := 
match goal with
| [ |- ~ ?G ] => eapply (ccase_neg P); intros pat
  (* let H := fresh "H" in assert (H : ~~ (P \/ ~P)) by tauto; cunwrap H; revert H; intros pat *)
| [ |- ?G ] => eapply (@DN_dec _ _); eapply (ccase_neg P); intros pat; apply DN
  (* let H := fresh "H" in assert (H : ~~ (P \/ ~P)) by tauto; cunwrap H; revert H; intros pat;
  apply DN *)
end.

Tactic Notation "cstart" := eapply (@DN_dec _ _).

Inductive IsFilter {X} (p : X -> Prop) : list X -> list X -> Prop :=
  IsFilter_nil : IsFilter p [] []
| IsFilter_cons1 l x l' : IsFilter p l l' -> p x -> IsFilter p (x :: l) (x :: l')
| IsFilter_cons2 l x l' : IsFilter p l  l' -> ~ p x  -> IsFilter p (x :: l) l'.

Lemma IsFilter_spec {X} l l' (p : X -> Prop) :
IsFilter p l l' -> length l' <= length l /\ (forall x0, In x0 l -> ~ p x0 -> length l' < length l) /\ forall x, In x l' <-> In x l /\ p x.
Proof.
  induction 1; cbn; firstorder try congruence; lia.
Qed.

Require Import SyntheticComputability.Shared.Dec SyntheticComputability.Shared.ListAutomation.

Lemma IsFilter_filter {X} p (D : forall x : X, {p x} + {~ p x}) l :
  IsFilter p l (filter (fun x => if D x then true else false) l).
Proof.
  induction l; cbn.
  - econstructor.
  - destruct (D a) as [Ha | Ha]; econstructor; eauto.
Qed.

Lemma IsFilter_nnex {X} l (p : X -> Prop) :
~~ exists l', IsFilter p l l'.
Proof.
induction l as [ | x l IH].
- cprove exists []. econstructor.
- cunwrap. destruct IH as (l' & IH).
  ccase (p x) as [Hx | Hx].
  + cprove exists (x :: l'). now econstructor.
  + cprove exists l'. now econstructor.  
Qed.

Lemma IsFilter_ex {X} l (p : X -> Prop) (H : forall x, p x \/ ~ p x) :
 exists l', IsFilter p l l'.
Proof.
induction l as [ | x l IH].
- exists []. econstructor.
- destruct IH as (l' & IH).
  destruct (H x) as [Hx | Hx].
  + exists (x :: l'). now econstructor.
  + exists l'. now econstructor.
Qed.

Instance dec_lt {n m} : Dec.dec (n < m).
Proof.
  eapply Compare_dec.lt_dec.
Qed.

Lemma remove_Sigma {X} (l : list X) x0 (H : forall x1 x2 : X, dec (x1 <> x2)) :
 { l' | length l' <= length l /\ (~~ In x0 l -> length l' < length l) /\ forall x, In x l' <-> In x l /\ x <> x0}.
Proof.
  unshelve epose proof (IsFilter_filter (fun x => x <> x0) _ l) as (H1 & H2 & H3) % IsFilter_spec.
  - abstract (firstorder).
  - eexists. split. exact H1. firstorder. cstart. ccase (In x0 l) as [Hx | Hx]; firstorder.
Qed.

Lemma remove_ex {X} (l : list X) x0 (H : forall x1 x2 : X, (x1 <> x2) \/ ~ x1 <> x2) :
exists l', length l' <= length l /\ (~~ In x0 l -> length l' < length l) /\ forall x, In x l' <-> In x l /\ x <> x0.
Proof.
  destruct (IsFilter_ex l (fun x => x <> x0)) as [l' (H1 & H2 & H3) % IsFilter_spec]; eauto.
  exists l'. firstorder. cstart. ccase (In x0 l) as [Hx | Hx]; firstorder.
Qed. 

Lemma remove_nnex {X} (l : list X) x0 :
~~ exists l', length l' <= length l /\ (In x0 l -> length l' < length l) /\ forall x, In x l' <-> In x l /\ x <> x0.
Proof.
  pose proof (IsFilter_nnex l (fun x => x <> x0)) as H. cunwrap.
  destruct H as [l' (H1 & H2 & H3) % IsFilter_spec].
  cprove exists l'. eauto 7.
Qed.

Lemma in_ldec {X} (x : X) l (H : forall x1 x2 : X, x1 <> x2 \/ ~ x1 <> x2) :
~~ In x l \/ ~ In x l.
Proof. 
  induction l as [ | x' l [IH |IH]]; firstorder.
Qed.

Lemma in_dec {X} (x : X) l (H : forall x1 x2 : X, dec (x1 <> x2)) :
  dec ( ~ In x l ).
Proof. 
  induction l as [ | x' l [IH |IH]]; firstorder.
Qed.

Lemma pigeonhole_Sigma {X} (l1 l2 : list X) (H : forall x1 x2 : X, dec (x1 <> x2)) :
  NoDup l1 -> length l1 > length l2 -> { x | In x l1 /\ ~ In x l2}.
Proof.
  intros Hd. revert l2. induction l1 as [ | x l1 IH]; cbn; intros.
  - lia.
  - destruct (in_dec x l2 H) as [Hx | Hx].
    + exists x. firstorder.
    + destruct (remove_Sigma l2 x H) as (l2_no_x & H1 & H2 % (fun H2 => H2 Hx) & H3).
      edestruct (IH ltac:(now inversion Hd) l2_no_x) as (x0 & H4 & H5).
      * lia.
      * exists x0. inversion Hd. split. eauto. firstorder congruence.
Qed.

Lemma pigeonhole {X} (l1 l2 : list X) (H : forall x1 x2 : X, x1 <> x2 \/ ~ x1 <> x2) :
  NoDup l1 -> length l1 > length l2 -> exists x, In x l1 /\ ~ In x l2.
Proof.
intros Hd. revert l2.
induction Hd; cbn; intros l2 Hle.
- lia.
- destruct (in_ldec x l2 H) as [Hx | Hx].
  + destruct (remove_ex l2 x H) as (l2_no_x & H1 & H2 % (fun H2 => H2 Hx) & H3).
    edestruct (IHHd l2_no_x) as (x0 & H4 & H5).
    * lia.
    * exists x0. split. eauto. firstorder congruence.
  + exists x. firstorder.
Qed.

Lemma pigeonhole_constructive {X} (l1 l2 : list X) :
  NoDup l1 -> length l1 > length l2 -> ~~ exists x, In x l1 /\ ~ In x l2.
Proof.
intros Hd. revert l2.
induction Hd; cbn; intros l2 Hle.
- lia.
- ccase (In x l2) as [Hx | Hx].
  + pose proof (remove_nnex l2 x) as H0. cunwrap. destruct H0 as (l2_no_x & H1 & H2 % (fun H2 => H2 Hx) & H3).
    unshelve epose proof (IHHd l2_no_x _) as H0. 1:lia. cunwrap. destruct H0 as (x0 & H4 & H5).
    cprove exists x0. split. eauto. firstorder congruence.
  + cprove exists x. firstorder.
Qed.
 
Lemma pigeonhole_length {X} (L1: list X) (Heq : forall x1 x2 : X, x1 <> x2 \/ ~ x1 <> x2) :
  NoDup L1 -> forall L2, incl L1 L2 -> length L1 <= length L2. 
Proof.
  intros H L2 H1.
  destruct (Nat.le_gt_cases (length L1) (length L2)) as [H0 | H0].
  - assumption.
  - eapply pigeonhole in H0.
   + destruct H0 as (x & H2 & H3). firstorder.
   + eassumption.
   + eauto.
Qed.
