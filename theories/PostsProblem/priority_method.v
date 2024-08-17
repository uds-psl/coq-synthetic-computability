From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions Limit simple.
From stdpp Require Export list.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Import Arith Arith.Compare_dec Lia Coq.Program.Equality List.
Import ListNotations.

Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Notation unique p := (forall x x', p x -> p x' -> x = x').

  Class Extension :=
  {
      extendP: list nat -> nat -> nat -> Prop;
      extend_dec: forall l x, (Σ y, extendP l x y) + (forall y, ~ extendP l x y);
      extend_uni: forall l x, unique (extendP l x)
  }.

  Inductive F_ (E: Extension) : nat -> list nat -> Prop :=
    | Base : F_ E O []
    | ExtendS n l a : F_ E n l -> extendP l n a -> F_ E (S n) (a::l)
    | ExtendN n l   : F_ E n l -> (forall a, ~ extendP l n a) -> F_ E (S n) l.

Section Construction.

  Variable E: Extension.

  Lemma F_uni n: unique (F_ E n).
  Proof.
    intros l1 l2.
    dependent induction n.
    - intros H1 H2. inv H1. now inv H2.
    - intros H1 H2. inv H1; inv H2.
      assert(l = l0) as -> by now apply IHn.
      f_equal. apply (extend_uni H3 H4).
      assert (l = l2) as -> by now apply IHn.
      exfalso. apply (H4 a H3).
      assert (l = l1) as -> by now apply IHn.
      exfalso. apply (H3 a H4).
      now apply IHn.
  Qed.

  Lemma F_mono n m l1 l2: F_ E n l1 -> F_ E m l2 -> n <= m -> incl l1 l2.
  Proof.
      intros H1 H2 HE.
      revert H1 H2; induction HE in l2 |-*; intros H1 H2.
      - now assert (l1 = l2) as -> by (eapply F_uni; eauto).
      - inv H2; last now apply IHHE.
        specialize (IHHE l H1 H0). eauto.
  Qed.

  Lemma F_pop n x l: F_ E n (x::l) -> exists m, F_ E m l.
  Proof.
    intros H. dependent induction H. 
    - now exists n.
    - eapply IHF_. eauto.
  Qed.
  
  Lemma F_pick n x l: F_ E n (x::l) -> exists m, F_ E m l /\ extendP l m x.
  Proof.
    intros H. dependent induction H.
    - exists n; eauto.
    - eapply IHF_; eauto.
  Qed.

  Lemma F_pick' n x l: F_ E n (x::l) -> exists m, m < n ∧ F_ E m l ∧ extendP l m x.
    Proof.
      intros H. dependent induction H.
      - exists n; eauto.
      - destruct (IHF_ x l eq_refl) as [m (Hm1&Hm2&Hm3)].
        exists m; eauto.
    Qed.

  Lemma F_computable : Σ f: nat -> list nat, 
    forall n, F_ E n (f n) /\ length (f n) <= n.
  Proof.
    set (F := fix f x :=
           match x with
           | O => []
           | S x => match extend_dec (f x) x with
                   | inr _ => f x
                   | inl aH => (projT1 aH) :: (f x)
                   end
           end).
    exists F. induction n; simpl.
    - split. constructor. easy.
    - destruct (extend_dec (F n) n); split.
      + eapply ExtendS; first apply IHn. now destruct s.
      + cbn. destruct IHn. lia.
      + now eapply ExtendN.
      + destruct IHn. lia.
  Qed.

  Definition F_func := projT1 F_computable.
  Lemma F_func_correctness: forall n, F_ E n (F_func n).
  Proof.
    intros n; unfold F_func. 
    destruct F_computable as [f H].
    now destruct (H n).
  Qed.

  Lemma F_func_correctness': forall n, length (F_func n) <= n.
  Proof.
    intros n; unfold F_func. 
    destruct F_computable as [f H].
    now destruct (H n).
  Qed.

  Definition F_with x := exists l n, In x l /\ (F_ E n l).

  Lemma F_func_F_with x: F_with x ↔ ∃ n, In x (F_func n).
  Proof.
    split. intros (l&n&H1&H2).
    exists n. assert (l = F_func n) as ->.
    { eapply F_uni. apply H2. apply F_func_correctness. }
    done. intros [n Hn]. exists (F_func n), n; split; first done.
    apply F_func_correctness.
  Qed.
  

  Lemma F_with_semi_decidable: semi_decidable F_with.
  Proof.
    unfold semi_decidable, semi_decider.
    destruct F_computable as [f Hf ].
    exists (fun x n => (Dec (In x (f n)))).
    intros x. split.
    - intros (l & n & Hxl & Hl).
      exists n. rewrite Dec_auto; first easy.
      destruct (Hf n) as [Hf' _].
      now rewrite (F_uni Hf' Hl).
    - intros (n & Hn%Dec_true).
      exists (f n), n; split; eauto.
      apply Hf.
  Qed.

  Lemma F_with_top x: F_with x <-> exists l n, (F_ E n l) /\ (F_ E (S n) (x::l)) /\ extendP l n x.
  Proof.
    split; last first.
    { intros (l&n&H1&H2&H3). exists (x::l), (S n). eauto. }
    intros [l [n [Hln Hn]]].
    induction Hn. inversion Hln.
    - destruct (Dec (x=a)) as [->|Ex].
      exists l, n; split; first easy. split.
      econstructor; easy. easy.
      eapply IHHn. destruct Hln; congruence.
    - now eapply IHHn.
  Qed.

  Lemma F_with_semi_decider: Σ f, semi_decider f F_with.
  Proof.
    destruct F_computable as [f Hf ].
    exists (fun x n => (Dec (In x (f n)))).
    intros x. split.
    - intros (l & n & Hxl & Hl).
      exists n. rewrite Dec_auto; first easy.
      destruct (Hf n) as [Hf' _].
      now rewrite (F_uni Hf' Hl).
    - intros (n & Hn%Dec_true).
      exists (f n), n; split; eauto.
      apply Hf.
  Qed.

  Definition χ n x: bool := Dec (In x (F_func n)).
  Definition stable {Q} (f: nat → Q → bool) :=
    ∀ q n m, n ≤ m → f n q = true → f m q = true.
  Definition stable_semi_decider {Q} P (f: nat → Q → bool) :=
    semi_decider (λ x n, f n x) P ∧ stable f.

  Lemma F_with_χ : stable_semi_decider F_with χ.
  Proof.
    split. split. 
    - intros [n Hn]%F_func_F_with. by exists n; apply Dec_auto.
    - intros [n Hn%Dec_true]. rewrite F_func_F_with. by exists n.
    - intros x n m Hn Hm%Dec_true.
      apply Dec_auto. enough (incl (F_func n) (F_func m)). eauto.
      eapply F_mono; last exact Hn; apply F_func_correctness.
  Qed.

End Construction.

Section StrongInduction.

  Definition strong_induction (p: nat -> Type) :
    (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
  Proof.
      intros H x; apply H.
      induction x; [intros; lia| ].
      intros; apply H; intros; apply IHx; lia.
  Defined.

End StrongInduction.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.

Section EWO.
  Variable p: nat -> Prop.
  Inductive T | (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Definition T_elim (q: nat -> Type)
    : (forall n, (~p n -> q (S n)) -> q n) ->
      forall n, T n -> q n
    := fun e => fix f n a :=
      let (phi) := a in
      e n (fun h => f (S n) (phi h)).

  (*** EWO for Numbers *)

  Lemma TI n :
    p n -> T n.
  Proof.
    intros H. constructor. intros H1. destruct (H1 H).
  Qed.

  Lemma TD n :
    T (S n) -> T n.
  Proof.
    intros H. constructor. intros _. exact H.
  Qed.

  Variable p_dec: forall n, dec (p n).

  Definition TE (q: nat -> Type)
    : (forall n, p n -> q n) ->
      (forall n, ~p n -> q (S n) -> q n) ->
      forall n, T n -> q n.
  Proof.
    intros e1 e2.
    apply T_elim. intros n IH.
    destruct (p_dec n); auto.
  Qed.

  (** From now on T will only be used through TI, TD, and TE *)

  
  Lemma T_zero n :
    T n -> T 0.
  Proof.
    induction n as [|n IH].
    - auto.
    - intros H. apply IH. apply TD, H.
  Qed.

  Definition ewo_nat :
    ex p -> Σ x, p x.
  Proof.
    intros H.
    refine (@TE (fun _ => Σ x, p x) _ _ 0 _).
    - eauto.
    - easy.
    - destruct H as [n H]. apply (@T_zero n), TI, H.
  Qed.
  
End EWO.

Section LeastWitness.

  Definition safe p n := forall k, k < n -> ~ p k.
  Definition least p n := p n /\ safe p n.

  Fact least_unique p : unique (least p).
  Proof.
    intros n n' [H1 H2] [H1' H2'].
    enough (~(n < n') /\ ~(n' < n)) by lia.
    split; intros H.
    - eapply H2'; eassumption.
    - eapply H2; eassumption.
  Qed.

  Fact safe_O p :
    safe p 0.
  Proof.
    hnf. lia.
  Qed.

  Fact safe_S p n :
    safe p n -> ~p n -> safe p (S n).
  Proof.
    intros H1 H2 k H3. unfold safe in *.
    assert (k < n \/ k = n) as [H|H] by lia.
    - auto.
    - congruence.
  Qed.

  Fact safe_char p n :
    safe p n <-> forall k, p k -> k >= n.
  Proof.
    split.
    - intros H k H1.
      enough (k < n -> False) by lia.
      intros H2. apply H in H2. auto.
    - intros H k H1 H2. apply H in H2. lia.
  Qed.

  Fact safe_char_S p n :
    safe p (S n) <-> safe p n /\ ~p n.
  Proof.
    split.
    - intros H. split.
      + intros k H1. apply H. lia.
      + apply H. lia.
    - intros [H1 H2]. apply safe_S; assumption.
  Qed.

  Fact safe_eq p n k :
    safe p n -> k <= n -> p k -> k = n.
  Proof.
    intros H1 H2 H3. unfold safe in *.
    enough (~(k < n)) by lia.
    specialize (H1 k). tauto.
  Qed.

  Fact E14 x y z :
    x - y = z <-> least (fun k => x <= y + k) z.
  Proof.
    assert (H: least (fun k => x <= y + k) (x - y)).
    { split; unfold safe; lia. }
    split. congruence.
    eapply least_unique, H.
  Qed.  

  (*** Certifying LWOs *)

  Section LWO.
    Variable p : nat -> Prop.
    Variable p_dec : forall x, dec (p x).

    Definition lwo :
      forall n, (Σ k, k < n /\ least p k) + safe p n.
    Proof.
      induction n as [|n IH].
      - right. apply safe_O.
      - destruct IH as [[k H1]|H1].
        + left. exists k. destruct H1 as [H1 H2]. split. lia. exact H2.
        + destruct (p_dec n).
          * left. exists n. split. lia. easy.
          * right. apply safe_S; assumption.
    Defined.

    Definition lwo' :
      forall n, (Σ k, k <= n /\ least p k) + safe p (S n).
    Proof.
      intros n.
      destruct (lwo (S n)) as [(k&H1&H2)|H].
      - left. exists k. split. lia. exact H2.
      - right.  exact H.
    Qed.

    Definition least_sig :
      (Σ x, p x) -> Σ x, (least p) x.
    Proof.
      intros [n H].
      destruct (lwo (S n)) as [(k&H1&H2)|H1].
      - exists k. exact H2.
      - exfalso. apply (H1 n). lia. exact H.
    Qed.

    Definition least_ex :
      ex p -> ex (least p).
    Proof.
      intros [n H].
      destruct (lwo (S n)) as [(k&H1&H2)|H1].
      - exists k. exact H2.
      - exfalso. apply (H1 n). lia. exact H.
    Qed.

    Definition safe_dec n :
      dec (safe p n).
    Proof.
      destruct (lwo n) as [[k H1]|H1].
      - right. intros H. exfalso.
        destruct H1 as [H1 H2]. apply (H k). exact H1. apply H2.
      - left. exact H1.
    Defined.

    Definition least_dec n :
      dec (least p n).
    Proof.
      unfold least.
      destruct (p_dec n) as [H|H].
      2:{ right. tauto. }
      destruct (safe_dec n) as [H1|H1].
      - left. easy.
      - right. tauto.
    Qed.
  End LWO.

  Lemma exists_bounded_dec' P:
  (forall x, dec (P x)) -> forall k, dec (exists n, n < k /\ P n).
  Proof.
    intros Hp k.
    induction k. right; intros [? [? _]]; lia.
    destruct IHk as [Hw|Hw].
    - left. destruct Hw as [x [Hx1 Hx2]]. exists x; split; eauto; lia.
    - destruct (Hp k). left. exists k; split; eauto; lia.
      right. intros [x [Hx1 Hx2]].
      assert (x = k \/ x < k) as [->|Hk] by lia; firstorder.
  Qed.

  Lemma exists_bounded_dec P:
    (forall x, dec (P x)) -> forall k, dec (exists n, n <= k /\ P n).
  Proof.
    intros Hp k.
    induction k. destruct (Hp 0). left. exists 0. eauto.
    right. intros [x [Hx Hx']]. now assert (x=0) as -> by lia.
    destruct IHk as [Hw|Hw].
    - left. destruct Hw as [x [Hx1 Hx2]]. exists x; split; eauto; lia.
    - destruct (Hp (S k)). left. exists (S k); split; eauto; lia.
      right. intros [x [Hx1 Hx2]].
      assert (x = S k \/ x <= k) as [->|Hk] by lia; firstorder.
  Qed.

  Definition bounded (P: nat -> Prop) := Σ N, forall x, P x -> x < N.

  Fact bouned_le (P Q: nat -> Prop) N :
    (forall x, P x -> x < N) -> 
    (exists x, P x /\ Q x) <->  exists x, x < N /\ P x /\ Q x.
  Proof.
    intros Hn; split.
    - intros [x Hx]. exists x; intuition eauto.
    - intros (x&c&Hc). exists x; intuition eauto.
  Qed.

  Lemma bounded_dec (P Q: nat -> Prop):
    (forall x, dec (P x)) -> (forall x, dec (Q x)) -> 
    bounded P -> dec (exists n, P n /\ Q n).
  Proof.
    intros H1 H2 [N HN].
    assert (dec (exists n, n < N /\ P n /\ Q n)) as [H|H].
    - eapply exists_bounded_dec'. intro; eapply and_dec; eauto.
    - left. rewrite bouned_le; eauto.
    - right. intros H'%(@bouned_le _ _ N); easy.
  Qed.
  Lemma dec_neg_dec P: dec P -> dec (~ P).
  Proof. intros [H|H]. right; eauto. now left. Qed.

  Lemma forall_bounded_dec P e: 
    (forall x, dec (P x)) -> dec(forall i, i <= e -> P i).
  Proof.
    intros H.
    induction e. destruct (H 0); [left|right]; intros.
    now inv H0. intros H'. apply n, H'. lia.
    destruct IHe as [H1|H1].
    destruct (H (S e)); [left|right]; intros.
    inv H0; first easy. now apply H1.
    intros H0. apply n. apply H0. easy.
    right. intro H'. apply H1. intros. apply H'. lia. 
  Qed.

End LeastWitness.


Section logic.

  Definition pdec p := p ∨ ¬ p.

  Definition Π_1_lem := ∀ p : nat -> Prop,
    (∀ x, dec (p x)) -> pdec (∀ x, p x).
  Definition Σ_1_dne := ∀ p : nat -> Prop,
    (∀ x, dec (p x)) -> (¬¬ ∃ x, p x) → ∃ x, p x.
  Definition Σ_1_lem := ∀ p: nat → Prop,
    (∀ x, dec (p x)) -> pdec (∃ x, p x).

  Hypothesis LEM1: LEM_Σ 1.

  Fact assume_Σ_1_lem: Σ_1_lem .
  Proof.
    intros p Hp.
    destruct level1 as (_&H2&_).
    assert principles.LPO as H by by rewrite <- H2.
    destruct (H Hp) as [[k Hk]|H1].
    - left. exists k. destruct (Hp k); eauto.
      cbn in Hk. congruence.
    - right. intros [k Hk]. apply H1. 
      exists k. destruct (Hp k); eauto.
  Qed.

  Fact assume_Σ_1_dne: Σ_1_dne.
  Proof.
    intros p Hp H.
    destruct (assume_Σ_1_lem Hp) as [H1|H1]; eauto.
    exfalso. by apply H.
  Qed.

  Fact assume_Π_1_lem: Π_1_lem.
  Proof.
    intros p Hp.
    destruct level1 as (_&H2&_).
    assert principles.LPO as H by by rewrite <- H2.
    apply principles.LPO_to_WLPO in H.
    assert (∀ x : nat, dec (¬ p x)) as Hp' by eauto.
    destruct (H Hp') as [H1|H1].
    - left. intro x.
      specialize (H1 x).
      apply Dec_false in H1.
      destruct (Hp x); firstorder.
    - right. intros H3. apply H1. intros n.
      specialize (H3 n). destruct (Hp' n); firstorder.
  Qed.

End logic.
