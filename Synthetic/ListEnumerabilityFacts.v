From SyntheticComputability.Synthetic Require Import DecidabilityFacts SemiDecidabilityFacts EnumerabilityFacts.
From SyntheticComputability Require Import Shared.embed_nat.
Require Import List Lia.
Import ListNotations EmbedNatNotations.

(** ** List enumerability *)

Definition cumulative {X} (L: nat -> list X) :=
  forall n, exists A, L (S n) = L n ++ A.
Hint Extern 0 (cumulative _) => intros ?; cbn; eauto : core.

Lemma cum_ge {X} {L: nat -> list X} {n m} :
  cumulative L -> m >= n -> exists A, L m = L n ++ A.
Proof.
  induction 2 as [|m _ IH].
  - exists nil. now rewrite app_nil_r.
  - destruct (H m) as (A&->), IH as [B ->].
    exists (B ++ A). now rewrite app_assoc.
Qed.

Lemma cum_ge' {X} {L: nat -> list X} {x n m} :
  cumulative L -> In x (L n) -> m >= n -> In x (L m).
Proof.
  intros ? H [A ->] % (cum_ge (L := L)). apply in_app_iff. eauto. eauto.
Qed.

Definition list_enumerator {X} (L: nat -> list X) (p : X -> Prop) :=
  forall x, p x <-> exists m, In x (L m).
Definition list_enumerable {X} (p : X -> Prop) :=
  exists L, list_enumerator L p.

Definition list_enumeratorᵗ' X f := forall x : X, exists n : nat, In x (f n).
Notation list_enumeratorᵗ f X := (list_enumeratorᵗ' X f).
Definition list_enumerableᵗ X := exists f : nat -> list X, list_enumeratorᵗ f X.

Lemma list_enumerator_list_enumeratorᵗ X f :
  list_enumerator f (fun _ : X => True) <-> list_enumeratorᵗ f X.
Proof.
  split; intros Hf x.
  - destruct (Hf x) as [[n H] _]; eauto.
  - destruct (Hf x) as [n H]; firstorder.
Qed.

Lemma list_enumerable_list_enumerableᵗ X :
  list_enumerable (fun _ : X => True) <-> list_enumerableᵗ X.
Proof.
  split; intros [f Hf]; eapply ex_intro, list_enumerator_list_enumeratorᵗ, Hf.
Qed.

Section enumerator_list_enumerator.

  Variable X : Type.
  Variable p : X -> Prop.
  Variables (e : nat -> option X).

  Let T (n : nat) : list X :=  if e n is Some x then [x] else [].

  Lemma enumerator_to_list_enumerator : forall x, (exists n, e n = Some x) <-> (exists n, In x (T n)).
  Proof.
    split; intros [n H].
    - exists n. unfold T. rewrite H. firstorder.
    - unfold T in *. destruct (e n) eqn:E. inversion H; subst. eauto. inversion H0. inversion H.
  Qed.
End enumerator_list_enumerator.

Lemma enumerator_list_enumerator {X} {p : X -> Prop} f :
  enumerator f p -> list_enumerator (fun n => if f n is Some x then [x] else []) p.
Proof.
  intros Hf x. rewrite (Hf x). now rewrite <- enumerator_to_list_enumerator.
Qed.

Lemma enumerable_list_enumerable {X} {p : X -> Prop} :
  enumerable p -> list_enumerable p.
Proof.
  intros [f Hf]. eapply ex_intro, enumerator_list_enumerator, Hf.
Qed.

Lemma enumerableᵗ_list_enumerableᵗ {X} :
  enumerableᵗ X -> list_enumerableᵗ X.
Proof.
  intros [f Hf]. eapply ex_intro, list_enumerator_list_enumeratorᵗ, enumerator_list_enumerator, enumerator_enumeratorᵗ, Hf.
Qed.

Section enumerator_list_enumerator.

  Variable X : Type.
  Variables (T : nat -> list X).

  Let e := fun! ⟨ n , m ⟩ => nth_error (T n) m.

  Lemma list_enumerator_to_enumerator : forall x, (exists n, e n = Some x) <-> (exists n, In x (T n)).
  Proof.
    split; intros [k H].
    - unfold e in *.
      destruct (unembed k) as (n, m).
      exists n. eapply (nth_error_In _ _ H).
    - unfold e in *.
      eapply In_nth_error in H as [m].
      exists (embed (k, m)). now rewrite embedP, H.
  Qed.

End enumerator_list_enumerator.

Lemma list_enumerator_enumerator {X} {p : X -> Prop} {L} :
  list_enumerator L p -> enumerator (fun! ⟨ n , m ⟩ => nth_error (L n) m) p.
Proof.
  unfold list_enumerator.
  intros H x. rewrite list_enumerator_to_enumerator. eauto.
Qed.

Lemma list_enumeratorᵗ_enumeratorᵗ {X} {L} :
  list_enumeratorᵗ L X -> enumeratorᵗ (fun! ⟨ n , m ⟩ => nth_error (L n) m) X.
Proof.
  unfold list_enumerator.
  intros H x. rewrite list_enumerator_to_enumerator. eauto.
Qed.

Lemma list_enumerable_enumerable {X} {p : X -> Prop} :
  list_enumerable p -> enumerable p.
Proof.
  intros [T HT]. eapply ex_intro, list_enumerator_enumerator, HT.
Qed.

Lemma list_enumerableᵗ_enumerableᵗ {X} :
  list_enumerableᵗ X -> enumerableᵗ X.
Proof.
  intros [T HT]. 
  eapply ex_intro, enumerator_enumeratorᵗ, list_enumerator_enumerator, list_enumerator_list_enumeratorᵗ, HT.
Qed.

Lemma enum_enumT {X} :
  enumerableᵗ X <-> list_enumerableᵗ X.
Proof.
  split.
  eapply enumerableᵗ_list_enumerableᵗ.
  eapply list_enumerableᵗ_enumerableᵗ.
Qed.

Definition to_cumul {X} (L : nat -> list X) := fix f n :=
  match n with 0 => L 0 | S n => f n ++ L (S n) end.

Lemma to_cumul_cumulative {X} (L : nat -> list X) :
  cumulative (to_cumul L).
Proof.
  eauto.
Qed.

Lemma to_cumul_spec {X} (L : nat -> list X) x :
  (exists n, In x (L n)) <-> exists n, In x (to_cumul L n).
Proof.
  split.
  - intros [n H].
    exists n. destruct n. eassumption. cbn. eapply in_app_iff. eauto.
  - intros [n H].
    induction n; cbn in *.
    + exists 0. exact H.
    + eapply in_app_iff in H as [H | H]; eauto.
Qed.

Lemma cumul_In {X} (L : nat -> list X) x n :
  In x (L n) -> In x (to_cumul L n).
Proof.
  intros H. destruct n. eassumption. cbn. eapply in_app_iff; eauto.
Qed.

Lemma In_cumul {X} (L : nat -> list X) x n :
  In x (to_cumul L n) -> exists n, In x (L n).
Proof.
  intros H. eapply to_cumul_spec. eauto.
Qed.

Hint Resolve cumul_In In_cumul : core.

Lemma list_enumerator_to_cumul {X} {p : X -> Prop} {L} :
  list_enumerator L p -> list_enumerator (to_cumul L) p. 
Proof.
  unfold list_enumerator.
  intros. rewrite H.
  eapply to_cumul_spec.
Qed.

Lemma cumul_specᵗ {X} {L} :
  list_enumeratorᵗ L X -> list_enumeratorᵗ (to_cumul L) X.
Proof.
  unfold list_enumeratorᵗ.
  intros. now rewrite <- to_cumul_spec.
Qed.

Lemma cumul_spec {X} {L} {p : X -> Prop} :
  list_enumerator L p -> list_enumerator (to_cumul L) p.
Proof.
  unfold list_enumerator.
  intros. now rewrite <- to_cumul_spec.
Qed.

Require Import SyntheticComputability.Shared.ListAutomation.
Import ListAutomationNotations.

Notation cumul := (to_cumul).

Section L_list_def.
  Context {X : Type}.
  Variable (L : nat -> list X).

Fixpoint L_list (n : nat) : list (list X) :=
  match n
  with
  | 0 => [ [] ]
  | S n => L_list n ++ [ x :: L | (x,L) ∈ (cumul L n × L_list n) ]
  end.
End L_list_def.

Lemma L_list_cumulative {X} L : cumulative (@L_list X L).
Proof.
  intros ?; cbn; eauto. 
Qed.

(** # <a id="enumerator__T_list" /> #*)
Lemma enumeratorᵗ_list {X} L :
  list_enumeratorᵗ L X -> list_enumeratorᵗ (L_list L) (list X).
Proof.
  intros H l.
  induction l.
  - exists 0. cbn. eauto.
  - destruct IHl as [n IH].
    destruct (cumul_specᵗ H a) as [m ?].
    exists (1 + n + m). cbn. intros. in_app 2.
    in_collect (a,l).
    all: eapply cum_ge'; eauto using L_list_cumulative; lia.
Qed.

Lemma  enumerable_list {X} : list_enumerableᵗ X -> list_enumerableᵗ (list X).
Proof.
  intros [L H].
  eexists. now eapply enumeratorᵗ_list.
Qed.

(** Typeclasses  *)

Definition L_T {X : Type} {f : nat -> list X} {H : list_enumeratorᵗ f X} : nat -> list X.
  exact (cumul f).
Defined.
Arguments L_T _ {_ _} _, {_ _ _}.

Hint Unfold L_T : core.
Hint Resolve cumul_In : core.

Existing Class list_enumeratorᵗ'.

Definition el_T {X} {f} `{list_enumeratorᵗ f X} : list_enumeratorᵗ L_T X.
Proof.
  now eapply cumul_specᵗ.
Defined.

Existing Instance enumeratorᵗ_list.

Instance enumeratorᵗ_to_list {X} {f} :
  list_enumeratorᵗ f X -> enumeratorᵗ (fun n => let (n, m) := unembed n in nth_error (f n) m) X | 100.
Proof.
  intros H x. eapply list_enumerator_to_enumerator in H. exact H.
Qed.

Instance enumeratorᵗ_of_list {X} {f} :
  enumeratorᵗ f X -> list_enumeratorᵗ (fun n => match f n with Some x => [x] | None => [] end) X | 100.
Proof.
  intros H x. eapply enumerator_to_list_enumerator. eauto.
Qed.
(* 
Existing Class inf_list_enumerableᵗ.
Instance inf_to_enumerator {X} :
  forall H : inf_list_enumerableᵗ X, list_enumeratorᵗ (proj1_sig H) X | 100.
Proof.
  intros [? H]. eapply H.
Defined. *)

(** Compatibility  *)

Hint Unfold enumerable list_enumerable : core.

Hint Resolve enumerable_list_enumerable
     list_enumerable_enumerable : core.

Lemma enumerable_enum {X} {p : X -> Prop} :
  enumerable p <-> list_enumerable p.
Proof.
  split; eauto.
Qed.

(** Predicate embedability *)

(* Definition infinite {X} (sz : X -> nat) (p : X -> Prop) := forall n, exists x, sz x >= n /\ p x. *)

(* Lemma enumerable_infinite {X} (p : X -> Prop) sz : *)
(*   discrete X -> *)
(*   infinite sz p -> *)
(*   enumerable p -> *)
(*   exists e : nat -> X, (forall x, p x <-> exists n, e n = x) /\ (forall n1 n2, e n1 = e n2 -> n1 = n2). *)
(* Proof. *)
(*   intros [D] % discrete_iff inf_p [e He]. *)
(*   assert (gen : forall L, exists x, p x /\ ~ In x L) by admit. *)
(*   pose (g := fix g n := match n with *)
(*                           0 => nil *)
(*                         | S n => g n ++ [proj1_sig (gen (g n))] *)
(*                         end). *)
(*   exists (fun n => proj1_sig (gen (g n))). *)
(*   red in He. split. *)
(*   - intros x. *)


(* Definition tight_retraction' {X} {Y} (I : X -> Y) R := forall x : X, R (I x) = x. *)
(* Notation tight_retraction I R X Y := (@tight_retraction' X Y I R). *)

(* Definition tight_retract X Y := exists I R, retraction I R X Y. *)
(* Definition countable X := retract X nat. *)


