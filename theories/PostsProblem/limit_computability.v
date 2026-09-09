From SyntheticComputability Require Import ArithmeticalHierarchySemantic PostsTheorem reductions SemiDec TuringJump OracleComputability Definitions partial Pigeonhole embed_nat.

Import EmbedNatNotations.

Require Import stdpp.list Arith.Compare_dec Lia.
(* ########################################################################## *)
(** * Limit Computability *)
(* ########################################################################## *)

(** This file contains the definition of limit computability and proves the
forward direction of the Limit Lemma: limit computable predicates are Turing
reducible to the halting problem (also under a double-negation modality).

 **)

(* Naming the halting problem as K *)
Notation K := (­{0}^(1)).

Section AssumePartiality.

  Context {Part : partiality}.

  Context {enc : encoding ()}.

  Context {EPF_assm : EPF.EPF}.

  Section Modality.

    Variable M : Prop -> Prop.
    Variable ret : forall P, P -> M P.
    Variable bind : forall P Q, M P -> (P -> M Q) -> M Q.

    Ltac strip Hf := 
      eapply bind in Hf; [ exact Hf | clear Hf; intros Hf ].

    Definition limit_computable_modality {X} (P: X → Prop) :=
      ∃ f: X → nat → bool, ∀ x,
        M (P x ↔ ∃ N, ∀ n, n ≥ N → f x n = true) ∧
          M (¬ P x ↔ ∃ N, ∀ n, n ≥ N → f x n = false).

    Definition char_rel_limit_computable {X} (P: X → bool → Prop) :=
      ∃ f: X → nat → bool, ∀ x y, M (P x y ↔ ∃ N, ∀ n, n ≥ N → f x n = y).

    Lemma char_rel_limit_equiv {X} (P: X → Prop):
      char_rel_limit_computable (char_rel P) ↔ limit_computable_modality P.
    Proof.
      split; intros [f Hf]; exists f; intros x.
      - split; firstorder.
        + specialize (Hf x true); firstorder.
        + specialize (Hf x false); firstorder.
      - intros []; destruct (Hf x) as [h1 h2]; eauto.
    Qed.

    Variable M_impl : forall P Q,
        (P -> M Q) -> M (P -> Q).

    Lemma M_split : forall P Q,
        (P -> M Q) -> (Q -> M P) ->
        M (P <-> Q).
    Proof.
      intros P Q H1 H2.
      apply M_impl in H1, H2.
      firstorder.
    Qed.
    
    Lemma limit_turing_red_K_modality (A: nat → Prop) :
      limit_computable_modality A →
      ∃ r,
        OracleComputable r ∧ ∀ x (b : bool), M ((char_rel A x b) ↔ (r (char_rel K) x b)).
    Proof.
      intros [f Hf].
      pose (P := fun xn => exists k, f (fst xn) ((snd xn) + k) <> f (fst xn) (snd xn)).
      assert (semi_decidable P).
      {
        unfold P.
        apply SemiDecidabilityFacts.semi_decidable_ex.
        apply SemiDecidabilityFacts.decidable_semi_decidable.
        apply DecidabilityFacts.decidable_complement.
        apply DecidabilityFacts.decidable_iff.
        constructor. intros. apply EqDecInstances.bool_eqdec.
      }
      assert (exists c, forall x n, K (c x n) <-> P (x, n)) as [c Hc].
      {
        edestruct red_m_iff_semidec_jump with (P := fun! ⟨x,n⟩ => P (x,n)) as [[c Hc] _].
        apply semi_decidable_OracleSemiDecidable.
        {
          destruct H as [g Hg].
          exists (fun m => g (unembed m)).
          red. intros.
          destruct (unembed x) as [x' n].
          firstorder.
        }
        exists (fun x n => c ⟨x,n⟩).
        red in Hc. intros.
        specialize (Hc ⟨x,n⟩).
        rewrite embedP in Hc.
        rewrite Hc. unfold K. reflexivity.
      }
      exists (fun R x b => exists i,
             (R (c x i) false /\ forall m, m < i -> R (c x m) true) /\ b = f x i).
      split.
      { 
        eapply OracleComputable_ext.
        { eapply computable_bind.
          - eapply computable_comp.
            + eapply computable_bind.
              * eapply computable_precompose with (g := fun '(x, m) => c x m).
                eapply computable_id.
              * eapply computable_function with (f := fun '(_, a) => negb a).
            + eapply computable_search.
          - eapply computable_function with (f := fun '(x, n) => f x n). }
        intros R x b. cbn.
        split.
        - intros (n & (([] & ? & ?) & H2) & ?); cbn in *; try congruence.
          exists n.
          repeat split; auto.
          intros ? ([] & ? & ?) % H2; cbn in *; try congruence.
        - intros (n & ? & ->).
          exists n. firstorder.
      }
      intros x b. destruct (Hf x) as [Hx1 Hx2].
      strip Hx1. strip Hx2.
      apply M_split. 
      - intros Hxb.
        assert (HM : M (exists N, ∀ n : nat, n ≥ N → f x n = b)).
        {
          destruct b; firstorder.
        }
        strip HM; destruct HM as (N & HN). 
        assert ( D :
                 ∀ i : nat, {∀ m : nat, i ≤ m → m ≤ N → f x m = b} + {∃ m : nat, i <= m <= N ∧ f x m ≠ b}).
        {
          clear.
          induction N. intros i.
          - destruct (bool_eq_dec (f x 0) b).
            + left. firstorder. assert (m = 0) as -> by lia. auto.
            + destruct i.
              * right. eauto.
              * left. intros. lia.
          - intros i.
            destruct (IHN i) as [IH | IH].
            + destruct (bool_eq_dec (f x (S N)) b).
              * left. intros.
                inversion H0; firstorder.
              * destruct (le_dec i (S N)) as [Hi|Hi]; firstorder lia.
            + firstorder lia.
        }
        destruct dec_inh_nat_subset_has_unique_least_element
          with (P := fun i => forall m, i <= m -> m <= N -> f x m = b) as (i & (Hi & Hsmall) & Hleast).
        { intros. clear Hx1 Hx2.
          destruct (D n); firstorder lia.
        }
        { exists N. clear Hx1 Hx2. firstorder. }
        apply ret.
        exists i. cbn -[K]. repeat split.
        + rewrite Hc. unfold P.
          intros (x' & H'). cbn in *.
          apply H'.
          rewrite (Hi i). 2,3: clear Hx1 Hx2; firstorder lia.
          destruct (le_dec (i + x') N).
          { apply Hi; lia. }
          { apply HN; lia. }
        + intros m Hm. apply Hc. red. cbn.
          destruct (D m) as [ | (m' & ? & ?)].
          1: firstorder lia.
          destruct (bool_eq_dec (f x m) b).
          * exists (m' - m). intros e'.
            apply H1. rewrite <- e, <- e'.
            f_equal. lia.
          * exists (N - m).
            replace (m + (N - m)) with N by lia.
            rewrite (HN N). 2: lia. auto.
        + symmetry. apply Hi; clear Hx1 Hx2; firstorder lia.
      - intros (i & (H1 & H2) & ->).
        cbn - [K] in H1. rewrite Hc in H1.
        unfold P in *. cbn -[K] in *.
        destruct (f x i) eqn:E.
        + cbn. apply ret, Hx1. exists i.
          intros n Hn. replace n with (i + (n - i)) by lia.
          destruct (f x (i + (n - i))) eqn:E'. reflexivity.
          exfalso. apply H1. exists (n - i). rewrite E'. congruence.
        + cbn. apply ret, Hx2. exists i.
          intros n Hn. replace n with (i + (n - i)) by lia.
          destruct (f x (i + (n - i))) eqn:E'. 2: reflexivity.
          exfalso. apply H1. exists (n - i). rewrite E'. congruence.
    Qed.

  End Modality.
  
  Definition limit_computable {X} (P: X → Prop) :=
    ∃ f: X → nat → bool, ∀ x,
      (P x ↔ ∃ N, ∀ n, n ≥ N → f x n = true) ∧
        (¬ P x ↔ ∃ N, ∀ n, n ≥ N → f x n = false).

  Lemma limit_turing_red_K (A: nat → Prop) :
    limit_computable A →
    A ⪯ᴛ K.
  Proof.
    apply limit_turing_red_K_modality with (M := id).
    all: firstorder.
  Qed.

  Lemma semi_dec_halting : semi_decidable K.
  Proof.
    eapply OracleSemiDecidable_semi_decidable with (q := ­{0}).
    - exists (λ n, match n with | O => true | _ => false end); intros [|n]; easy.
    - eapply semidecidable_J.
  Qed.

(** Forward direction again, for classical variants

 **)

  Definition limit_computable_classical {X} (P: X → Prop) :=
    ∃ f: X → nat → bool, ∀ x,
      ~~ (P x ↔ ∃ N, ∀ n, n ≥ N → f x n = true) ∧
        ~~ (¬ P x ↔ ∃ N, ∀ n, n ≥ N → f x n = false).

  Lemma limit_computable_to_classical {X} (P : X -> Prop) :
    limit_computable P -> limit_computable_classical P.
  Proof.
    firstorder.
  Qed.

  Lemma limit_computable_from_classical {X} (P : X -> Prop) :
    DNE -> limit_computable_classical P -> limit_computable P.
  Proof.
    intros lem [f Hf]. exists f.
    intros x.
    specialize (Hf x).
    apply lem; tauto.
  Qed.

  Definition char_rel_limit_computable_classical {X} (P: X → bool → Prop) :=
    ∃ f: X → nat → bool, ∀ x y, ~~ (P x y ↔ ∃ N, ∀ n, n ≥ N → f x n = y).

  Lemma char_rel_limit_equiv_classical {X} (P: X → Prop):
    char_rel_limit_computable_classical (char_rel P) ↔ limit_computable_classical P.
  Proof.
    split; intros [f Hf]; exists f; intros x.
    - split; firstorder.
    - intros []; destruct (Hf x) as [h1 h2]; eauto.
  Qed.

  Lemma nn_split P Q :
    (P -> ~~ Q) -> (Q -> ~~ P) ->
    ~~ (P <-> Q).
  Proof.
    tauto.
  Qed.

    Lemma limit_turing_red_K_classical (A: nat → Prop) :
      limit_computable_classical A →
      red_Turing_classical A K. 
    Proof.
      apply limit_turing_red_K_modality with (M := fun P => ~~ P).
      all: intros; tauto.
    Qed.
    
End AssumePartiality.
