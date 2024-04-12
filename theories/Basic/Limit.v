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


  (* Definition of limit ciomputable *)

  Definition limit_computable {X} (P: X -> Prop) :=
    exists f: X -> nat -> bool, forall x,
      (P x <-> exists N, forall n, n >= N -> f x n = true) /\
        (~ P x <-> exists N, forall n, n >= N -> f x n = false).

  Definition char_rel_limit_computable {X} (P: X -> bool -> Prop) :=
    exists f: X -> nat -> bool, forall x y, P x y <-> exists N, forall n, n >= N -> f x n = y.

  Lemma char_rel_limit_equv {X} (P: X -> Prop):
    char_rel_limit_computable (char_rel P) <-> limit_computable P.
  Proof.
    split; intros [f Hf]; exists f; intros x.
    - split; firstorder.
    - intros []; destruct (Hf x) as [h1 h2]; eauto.
  Qed.

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
    - exists (fun N n x => if lt_dec n N then true else f x n).
      intro w. destruct (H w) as [-> _]; split; intros [N Hn]; exists N.
      + intro m. destruct (lt_dec m N); try apply Hn; lia.
      + intros n He. specialize (Hn n); destruct (lt_dec n N); auto; lia.
    - exists (fun N n x => if lt_dec n N then true else negb (f x n)).
      intro w. destruct (H w) as [_ ->]; split; intros [N Hn]; exists N.
      + intro m. destruct (lt_dec m N); [auto| rewrite (Hn m); lia].
      + intros n He. specialize (Hn n).
        destruct (lt_dec n N); auto; [lia|destruct (f w n); easy].
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

About Σ_semi_decidable_jump.
  (** TODO: LEM_Σ 1 <-> definite K **)
  (* First part of limit lemma *)

  Lemma limit_turing_red_K' {k: nat} (P: vec nat k -> Prop) :
    LEM_Σ 1 ->
    definite K ->
    limit_computable P ->
    P ⪯ᴛ K.
  Proof.
    intros LEM D H % (limit_semi_dec_K LEM); destruct H as [h1 h2].
    apply PT; try assumption.
    apply Dec.nat_eq_dec.
  Qed.

  Search (vec) "hd".

  Fact elim_vec (P: nat -> Prop):
    P ⪯ₘ (fun x: vec nat 1 => P (hd x)) .
  Proof. exists (fun x => [x]). now intros x. Qed.
  Lemma limit_turing_red_K {k: nat} (P: nat -> Prop) :
    LEM_Σ 1 ->
    definite K ->
    limit_computable P ->
    P ⪯ᴛ K.
  Proof.
    intros Hc HK [h Hh].
    eapply Turing_transitive; last eapply (@limit_turing_red_K' 1); eauto.
    eapply red_m_impl_red_T. apply elim_vec.
    exists (fun v n => h (hd v) n). 
    intros x; split; 
    destruct (Hh (hd x)) as [Hh1 Hh2]; eauto.
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

  Definition approximation_Σ1_strong {A} (P: A -> Prop) :=
     exists P_ : nat -> A -> bool,
       (forall L, exists c, forall c', c' >= c -> approximation_list P (P_ c') L) /\
       (forall tau q a, @interrogation _ _ _ bool tau (char_rel P) q a -> exists n, forall m, m >= n -> interrogation tau (fun q a => P_ m q = a) q a).

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

  Lemma semi_dec_approximation_Σ1_strong {X} (P: X -> Prop) :
    definite P ->
    semi_decidable P -> approximation_Σ1_strong P.
  Proof.
    intros defP semiP.
    destruct (semi_dec_approximation_Σ1 defP semiP) as [P_ HP_].
    exists P_; split; [apply HP_|].
    intros tau q ans Htau.
    destruct (HP_ q) as [w Hw].
    exists w. intros m Hm. rewrite interrogation_ext.
    exact Htau. eauto.
    intros q_ a H1.
    specialize (Hw m Hm q_ H1).
    unfold char_rel; cbn.
    destruct a; eauto; split; intro h2.
    intro h. rewrite Hw in h. congruence.
    firstorder.
  Qed.

  Lemma approximation_Σ1_halting : definite K -> approximation_Σ1 K.
  Proof. now intros H; apply semi_dec_approximation_Σ1, semi_dec_halting. Qed.

  Lemma approximation_Σ1_halting_strong: definite K -> approximation_Σ1_strong K.
  Proof. now intros H; apply semi_dec_approximation_Σ1_strong, semi_dec_halting. Qed.


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

  End Construction.

  Theorem turing_red_K_lim (P: nat -> Prop) :
    P ⪯ᴛ K ->
    definite K ->
    definite P ->
    limit_computable P.
  Proof.
    intros [F [H HF]] defK defP.
    rewrite <- char_rel_limit_equv.
    destruct (approximation_Σ1_halting_strong defK) as [k_ [Hk_1 Hk_2]].
    destruct H as [tau Htau].
    pose (char_K_ n := char_K_ k_ n).
    pose (K_ n := K_ k_ n).
    pose (Phi x n := evalt_comp (tau x) (k_ n) n n).
    assert (forall x y, char_rel P x y -> exists N : nat, forall n : nat, n >= N -> (evalt_comp (tau x) (k_ n)) n n = Some (inr y)) as HL.
    {
    intros x y H.
    rewrite HF in H.
    rewrite Htau in H.
    destruct H as (qs & ans & Hint & Out).
    specialize (Hk_2 (tau x) qs ans Hint).
    destruct Hk_2 as [nth Hnth].
    assert (interrogation (tau x)
              (fun (q : nat) (a : bool) => (k_ nth) q = a) qs ans) as Hnthbase.
    eapply Hnth. lia.
    edestruct (interrogation_evalt_comp_limit (tau x) k_ qs ans y) as [L Hlimt].
    exists nth. intros. eapply Hnth. easy.
    eapply Out.
    exists L. intros. now apply Hlimt.
    }
    assert (exists f, forall x y, char_rel P x y -> exists N : nat, forall n : nat, n >= N -> f x n = y) as [f HL'].
    {
    exists (fun x n => match (Phi x n) with
               | Some (inr y) => y | _ => false end).
    intros x y Hxy%HL.
    destruct (Hxy) as [N HN].
    exists N; intros.
    unfold Phi. rewrite HN; eauto.
    }
    exists f. intros x y; split.
    - now intros; apply HL'.
    - intro H0. destruct y; cbn.
      destruct (defP x); [easy|].
      assert (char_rel P x false); [easy|].
      apply HL' in H1.
      destruct H0 as [N1 HN1].
      destruct H1 as [N2 HN2].
      specialize (HN1 (S (max N1 N2))).
      specialize (HN2 (S (max N1 N2))).
      enough (true = false) by congruence.
      rewrite <- HN1, HN2; lia.
      destruct (defP x); [|easy].
      assert (char_rel P x true); [easy|].
      apply HL' in H1.
      destruct H0 as [N1 HN1].
      destruct H1 as [N2 HN2].
      specialize (HN1 (S (max N1 N2))).
      specialize (HN2 (S (max N1 N2))).
      enough (true = false) by congruence.
      rewrite <- HN2, HN1; lia.
  Qed.

End LimitLemma2.
