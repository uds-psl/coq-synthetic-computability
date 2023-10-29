From SyntheticComputability Require Import ArithmeticalHierarchySemantic PostsTheorem reductions SemiDec TuringJump OracleComputability Definitions partial.

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

  Definition limit_computable' {X} (P: X -> bool -> Prop) :=
    exists f: X -> nat ↛ bool, forall x y, P x y <-> exists N, forall n, n > N -> f x n =! y.


  (* Definition of limit ciomputable *)

  Definition limit_computable {X} (P: X -> Prop) :=
    exists f: X -> nat -> bool, forall x,
      (P x <-> exists N, forall n, n > N -> f x n = true) /\
        (~ P x <-> exists N, forall n, n > N -> f x n = false).

  Definition limit_computable'' {X} (P: X -> bool -> Prop) :=
    exists f: X -> nat -> bool, forall x y, P x y <-> exists N, forall n, n > N -> f x n = y.

  Lemma limit''_limit {X} (P: X -> Prop): limit_computable'' (char_rel P) -> limit_computable P.
  Proof.
    intros [f Hf].
    exists f; intros x; split.
    - now rewrite (Hf x true).
    - now rewrite (Hf x false).
  Qed.

  Definition Post := forall X (p : X -> Prop), semi_decidable p -> semi_decidable (compl p) -> decidable p.

  Lemma try {X} (f: X ↛ bool) (P: X -> Prop): Post ->
                                        (forall x y, (char_rel P) x y <-> f x =! y) ->
                                        (exists f, forall x y, (char_rel P) x y <-> f x = y).
  Proof.
    intros PT H2.
    assert (decidable P).
  { apply PT.
    unfold semi_decidable, semi_decider.
    exists (fun x n => if seval (f x ) n is Some t then t else false).
    intro x. rewrite (H2 x true); split.
    - intros H'%seval_hasvalue.  destruct H' as [n1 Hn1].
      exists n1. now rewrite Hn1.
    - intros [n1 Hn1]; rewrite seval_hasvalue.
      exists n1. destruct (seval (f x) n1) as [|[]]; try congruence.
    - exists (fun x n => if seval (f x) n is Some t then negb t else false).
      intro x. rewrite (H2 x false); split.
      intros H'%seval_hasvalue.  destruct H' as [n1 Hn1].
      exists n1. now rewrite Hn1.
      intros [n1 Hn1]; rewrite seval_hasvalue.
      exists n1. destruct (seval (f x) n1) as [|[]]; try congruence.
      destruct b; easy. }
      destruct H as [g Hg].
  exists g; intros x []. cbn; apply Hg.
  cbn. split; intro h1; destruct (g x) eqn: E; try easy.
  now apply Hg in E. intro E'. apply Hg in E'. congruence.
  Qed.

  Lemma limit_impl {X} (P: X -> Prop) : limit_computable' (char_rel P) -> limit_computable P.
  Proof.
    intros [f Hf].
    unfold limit_computable''.
  Admitted.










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
  Definition approximation_list {A} (P: A -> Prop) (f: A -> bool) L :=
    forall i, List.In i L -> P i <-> f i = true.

  Definition approximation_Σ1 {A} (P: A -> Prop) :=
    exists P_ : nat -> A -> bool,
    forall L, exists c, forall c', c' >= c -> approximation_list P (P_ c') L.

  Lemma semi_dec_approximation_Σ1 {X} (P: X -> Prop) :
    definite P ->
    semi_decidable P -> approximation_Σ1 P.
  Proof.
    intros defP semiP; unfold approximation_Σ1, approximation_list.
    destruct (stabilize semiP)  as [h [Hh HS]].
    exists (fun n x => h x n). intro l. induction l as [|a l [c Hc]].
    - exists 42; eauto.
    - destruct (defP a) as [h1| h2].
      + destruct (Hh a) as [H _].
        destruct (H h1) as [N HN].
        exists (max c N); intros c' Hc' e [->| He].
        split; [intros _|easy].
        eapply HS; [|eapply HN]; lia.
        rewrite <- (Hc c'); [trivial|lia | assumption].
      + exists c; intros c' Hc' e [->| He].
        split; [easy| intros h'].
        unfold semi_decider in Hh.
        now rewrite Hh; exists c'.
        rewrite Hc; eauto.
  Qed.

  Lemma approximation_Σ1_halting : definite K -> approximation_Σ1 K.
  Proof. now intros H; apply semi_dec_approximation_Σ1, semi_dec_halting. Qed.

End Σ1Approximation.


Section LimitLemma2.

  (* A predicate P is reduciable to K if P is limit computable *)

  Section Construction.

    Variable f : nat -> nat -> bool.
    Variable tau : nat -> tree nat bool bool.
    Hypothesis Hf: forall L, exists c, forall c', c' >= c -> approximation_list K (f c') L.

    Definition K_ n := fun i o => f n i = o.
    Definition char_K_ n := fun i => ret (f n i).

    Lemma dec_K_ n : decidable (fun i => f n i = true).
    Proof.
      exists (f n). easy.
    Qed.

    Lemma pcomputes_K_ n: pcomputes (char_K_ n) (fun i o => f n i = o).
    Proof.
      intros i o; split; intro H.
      now apply ret_hasvalue_inv.
      now apply ret_hasvalue'.
    Qed.

    Variable F: nat ↛ bool -> nat ↛ bool.

    Definition Phi x n := if (seval (F (char_K_ n) x) n) is Some t then t else true.

    Check cont_to_cont.

  End Construction.

  Theorem turing_red_K_lim (P: nat -> Prop) :
    P ⪯ᴛ K ->
    definite K ->
    definite P ->
    limit_computable'' (char_rel P).
  Proof.
    intros [F [H HF]] defK defP.
    remember H as H'; remember defK as defK'.
    destruct (approximation_Σ1_halting defK') as [k_ Hk_].
    destruct H' as [tau Htau].
    specialize (Turing_transports_computable F H) as [F' HPhi].
    pose (char_K_ n := char_K_ k_ n).
    pose (K_ n := K_ k_ n).
    pose (Phi := Phi k_ F').
    specialize (fun n => HPhi (char_K_ n) (K_ n) (pcomputes_K_ _ _)).
    unfold pcomputes in HPhi.
(*
    assert ({g : nat -> nat -> bool |
              forall n x y, (forall s, s >= n -> g x s = y) <->  }) as Lemma1.
    {
      exists (fun x s => if (seval (Phi (char_K_ s) x) s) is Some t then t else true).
      intros n x y; split.
      - intros. apply HPhi.
        rewrite seval_hasvalue. admit.
      - intros. 
    }


    apply limit_impl.
    exists (fun x n => Phi (char_K_ n) x).
*)
    assert (forall x y, char_rel P x y -> exists N : nat, forall n : nat, n > N -> Phi x n = y) as HL.
    { intros x y H1. rewrite HF in H1.
      destruct (cont_to_cont _ H _ _ _ H1) as [lm Hlm].
      destruct (Hk_ lm) as [nth_K Hnth_K].
      assert (forall n, n > nth_K -> F (K_ n) x y); [intros n1 Hn1|].
      apply Hlm; intros i' o' h1 h2.
      assert (approximation_list K (k_ n1) lm).
      apply Hnth_K; lia. unfold approximation_list in H0.
      specialize (H0 i' h1).
      cbn in h2. destruct o'.
      now apply H0. destruct (k_ n1 i') eqn: E; [|easy].
      now exfalso; apply h2; rewrite H0.
      (** TODO **)
      (*
      exists nth_K; intros n1 Hn1.
      unfold pcomputes in HPhi.
      rewrite (HPhi n1 x y).
      now apply H0. } *)
      admit.
    }
    exists Phi. intros x y; split; intro H1.
    - now apply HL.
    - destruct y; cbn.
      destruct (defP x); [easy|].
      assert (char_rel P x false); [easy|].
      apply HL in H2.
      destruct H1 as [N1 HN1].
      destruct H2 as [N2 HN2].
      specialize (HN1 (S (max N1 N2))).
      specialize (HN2 (S (max N1 N2))).
      enough (true = false) by congruence.
      rewrite <- HN1, HN2; lia.
      destruct (defP x); [|easy].
      assert (char_rel P x true); [easy|].
      apply HL in H2.
      destruct H1 as [N1 HN1].
      destruct H2 as [N2 HN2].
      specialize (HN1 (S (max N1 N2))).
      specialize (HN2 (S (max N1 N2))).
      enough (true = false) by congruence.
      rewrite <- HN2, HN1; lia.
  Qed.




End LimitLemma2.
