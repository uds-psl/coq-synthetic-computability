From SyntheticComputability Require Import ArithmeticalHierarchySemantic PostsTheorem reductions SemiDec TuringJump OracleComputability Definitions.

Require Import Vectors.VectorDef Arith.Compare_dec Lia.
Import Vector.VectorNotations.

Local Notation vec := Vector.t.


(* ########################################################################## *)
(** * Limit Lemma *)
(* ########################################################################## *)

(** This file contains the definition of limit computable and proves the
Limit Lemma, i.e., limit computable is equivalence to reduciable to halting
problem.

Convention:

   limit: limit computable
   semi_dec(_K): semi decidable (on K)
   turing_red_K: turing reduciable to halting problem
   char[_X]: extensionality of X

**)


(* definition of limit ciomputable *)

  Definition limit_computable {X} (P: X -> Prop) :=
    exists f: X -> nat -> bool, forall x,
      (P x <-> exists N, forall n, n > N -> f x n = true) /\
        (~ P x <-> exists N, forall n, n > N -> f x n = false).

(* Naming the halting problem as K *)
  Notation K := (­{0}^(1)).


Section LimitLemma1.
  (* Limit computable predicate P is reduciable to K *)

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat (nat_to_vec k n) = n.

  Variable list_vec_to_nat : forall k, list (vec nat k) -> nat.
  Variable nat_to_list_vec : forall k, nat -> list (vec nat k).
  Variable list_vec_nat_inv : forall k v, nat_to_list_vec k (list_vec_to_nat v) = v.
  Variable nat_list_vec_inv : forall k n, list_vec_to_nat (nat_to_list_vec k n) = n.

  Variable nat_to_list_bool : nat -> list bool.
  Variable list_bool_to_nat : list bool -> nat.
  Variable list_bool_nat_inv : forall l, nat_to_list_bool (list_bool_to_nat l) = l.
  Variable nat_list_bool_inv : forall n, list_bool_to_nat (nat_to_list_bool n) = n.

  (* Extensionality of Σ2, i.e. P t iff ∃ x. ∀ y. f(x, y, t) = true *)

  Lemma char_Σ2 {k: nat} (P: vec nat k -> Prop) :
    (exists f: nat -> nat -> vec nat k -> bool, forall x, P x <-> (exists n, forall m, f n m x = true)) ->
    isΣsem 2 P.
  Proof.
    intros [f H].
    eapply isΣsemS_ with (p := fun v => forall y, f (hd v) y (tl v) = true).
    eapply isΠsemS_ with (p := fun v => f (hd (tl v)) (hd v) (tl (tl v)) = true).
    eapply isΣsem0. all: easy.
  Qed.

  Lemma limit_Σ2 {k: nat} (P: vec nat k -> Prop) :
    limit_computable P -> isΣsem 2 P /\ isΣsem 2 (compl P).
  Proof.
    intros [f H]; split; eapply char_Σ2.
    - exists (fun N n x => if le_dec n N then true else f x n).
      intro w. destruct (H w) as [-> _]; split; intros [N Hn]; exists N.
      + intro m. destruct (le_dec m N); try apply Hn; lia.
      + intros n He. specialize (Hn n); destruct (le_dec n N); auto; lia.
    - exists (fun N n x => if le_dec n N then true else negb (f x n)).
      intro w. destruct (H w) as [_ ->]; split; intros [N Hn]; exists N.
      + intro m. destruct (le_dec m N); [auto| rewrite (Hn m); lia].
      + intros n He. specialize (Hn n).
        destruct (le_dec n N); auto; [lia|destruct (f w n); easy].
  Qed.

  Lemma limit_semi_dec_K {k: nat} (P: vec nat k -> Prop) :
    LEM_Σ 1 ->
    limit_computable P ->
    OracleSemiDecidable K P /\
    OracleSemiDecidable K (compl P).
  Proof.
    intros LEM H%limit_Σ2.
    rewrite <- !(Σ_semi_decidable_jump).
    all: eauto.
  Qed.

  (** TODO: LEM_Σ 1 <-> definite K **)
  (* First part of limit lemma *)

  Lemma limit_turing_red_K {k: nat} (P: vec nat k -> Prop) :
    LEM_Σ 1 ->
    definite K ->
    limit_computable P ->
    P ⪯ᴛ K.
  Proof.
    intros LEM D H % (limit_semi_dec_K LEM); destruct H as [h1 h2].
    apply PT; try assumption.
    apply Dec.nat_eq_dec.
  Qed.

(*
  (** Move to lowsimple.v **)

  Definition low (P: nat -> Prop) := P´ ⪯ᴛ ­{0}^(1).

  Lemma lowness (P: nat -> Prop) :
    low P -> ~ ­{0}^(1) ⪯ᴛ P.
  Proof.
    intros H IH.
    eapply not_turing_red_J with (Q := P).
    eapply Turing_transitive; [apply H| easy].
  Qed.

  Lemma limit_jump_lowness (A: nat -> Prop) :
    LEM_Σ 1 ->
    definite (­{0}^(1)) ->
    LimitComputable (A´) -> ~ ­{0}^(1) ⪯ᴛ A.
  Proof.
    intros LEM defK H IH.
    apply lowness with (P := A); [|apply IH].
    pose (P := fun (v: vec nat 1) => A´ (hd v)).
    eapply Turing_transitive; [|apply (@limit_turing_red _ P LEM defK)].
  Admitted.
  *)

End LimitLemma1.


Section Σ1Approximation.

  (* Turing jump of a trivial decidable problem is semi decidable *)

  Lemma semi_dec_halting : semi_decidable K.
  Proof.
    eapply OracleSemiDecidable_semi_decidable with (q := ­{0}).
    - exists (fun n => match n with | O => true | _ => false end); intros [|n]; easy.
    - eapply semidecidable_J.
  Qed.


  (* Stabilizing the semi decider allows the semi decider
     to be used as a Σ1 approximation *)

  Definition stable (f: nat -> bool) := forall n m, n <= m -> f n = true -> f m = true.

  Fixpoint stabilize_step {X} (f: X -> nat -> bool) x n :=
    match n with
    | O => false
    | S n => if f x n then true else stabilize_step f x n
    end.

  Lemma stabilize {X} (P: X -> Prop) :
    semi_decidable P -> exists f, semi_decider f P /\ forall x, stable (f x).
  Proof.
    intros [f Hf].
    exists (fun x n => stabilize_step f x n); split.
    - intro x; split; intro h.
      rewrite (Hf x) in h.
      destruct h as [c Hc].
      now exists (S c); cbn; rewrite Hc.
      rewrite (Hf x).
      destruct h as [c Hc].
      induction c; cbn in Hc; [congruence|].
      destruct (f x c) eqn: E; [now exists c|now apply IHc].
    - intros x n m Lenm Hn.
      induction Lenm; [trivial|].
      cbn; destruct (f x m) eqn: E; [trivial|assumption].
  Qed.

  (* The Σ1 approximation output correct answers for arbitray list of questions *)

  Lemma semi_dec_char_Σ1 {X} (P: X -> Prop) :
    semi_decidable P ->
    exists K_: X -> nat -> bool,
    forall l: list X,
    definite P ->
    exists c: nat, forall e, List.In e l -> K_ e c = true <-> P e.
  Proof.
    intros semi_P.
    destruct (stabilize semi_P)  as [h [Hh HS]].
    exists h; intros l defP. induction l as [|a l [c Hc]].
    - exists 42; eauto.
    - destruct (defP a) as [h1| h2].
      + destruct (Hh a) as [H _].
        destruct (H h1) as [N HN].
        exists (max c N); intros e [->| He].
        split; [easy|intros _].
        eapply HS; [|eapply HN]; lia.
        rewrite <- Hc; [|assumption].
        split; intro h'.
        rewrite Hc; [|exact He].
        unfold semi_decider in Hh.
        rewrite Hh; now exists (Nat.max c N).
        eapply HS; [|apply h']; lia.
      + exists c; intros e [->| He].
        split; [intro h'|easy].
        unfold semi_decider in Hh.
        now rewrite Hh; exists c.
        rewrite Hc; eauto.
  Qed.

End Σ1Approximation.


Section LimitLemma2.

  (* A predicate P is reduciable to K if P is limit computable *)

  Theorem turing_red_K_lim (P: nat -> Prop) :
    P ⪯ᴛ K -> limit_computable P.
  Proof.
  Admitted.

End LimitLemma2.
