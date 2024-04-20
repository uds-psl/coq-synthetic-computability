From SyntheticComputability Require Import ArithmeticalHierarchySemantic reductions SemiDec TuringJump OracleComputability Definitions.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.ListAutomation.
From SyntheticComputability Require Import partial Dec.
Require Import Coq.Program.Equality.
From stdpp Require Export list.
Import PartialTactics.

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
      (at level 200, x binder, right associativity,
      format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition inf_forall (P: nat -> Prop) := exists n, forall m, n ≤ m → P m.
  Notation "'∞∀' x .. y , p" :=
    (inf_forall (fun x => .. (inf_forall (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' '∞∀'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Lemma list_cons_or {X} (A B: list X) a :
    A `prefix_of` B ++ [a] → A `prefix_of` B ∨ A = B ++ [a].
Proof.
  induction A in B |-*; intros.
  { left. eapply prefix_nil. }
  destruct B.
  { right. list_simplifier.
  set (H' := H).
  apply prefix_cons_inv_2, prefix_nil_inv in H' as ->.
  by apply prefix_cons_inv_1 in H as ->. } 
  list_simplifier.
  set (H' := H).
  apply prefix_cons_inv_2 in H'.
  apply prefix_cons_inv_1 in H as ->.
  destruct (IHA _ H') as [h1 | ->].
  + left. by eapply prefix_cons.
  + by right.
Qed.

Section Step_Eval.

  Context {Part : partiality}.
  Context {Q A O: Type}.
  Definition tree := (list A) ↛ (Q + O).

  Notation Ask q := (inl q).
  Notation Output o := (inr o).

  Lemma prefix_lookup_Some {X} (l1 l2: list X)i x :
  l1 !! i = Some x → l1 `prefix_of` l2 → l2 !! i = Some x.
  Proof. intros ? [k ->]. rewrite lookup_app_l; eauto using lookup_lt_Some. Qed.

  Lemma prefix_length_eq {X} (l1 l2: list X) :
    l1 `prefix_of` l2 → length l2 ≤ length l1 → l1 = l2.
  Proof.
    intros Hprefix Hlen. assert (length l1 = length l2).
    { apply prefix_length in Hprefix. lia. }
    eapply list_eq_same_length with (length l1); [done..|].
    intros i x y _ ??. assert (l2 !! i = Some x) by eauto using prefix_lookup_Some.
    congruence.
  Qed.

  Lemma interrogation_le_eq (q: Q) (a: A) (τ: tree) R use use' ans ans' v : 
    functional R →
    interrogation τ R use ans → τ ans =! Output v →
    interrogation τ R use' ans' → τ ans' =! Output v →
    length use ≤ length use' →
    use = use'.
  Proof.
    intros funR H1 H1a H2 H2a E.
    specialize (interrogation_det _ _ _ _ _ _ funR H1 H2 E) as [HE1 HE2].
    enough (length use' ≤ length use). 
    { eapply prefix_length_eq; eauto. }
    enough (¬ length use < length use') by lia. intros H.
    unshelve rewrite (interrogation_quantifiers) in H2; eauto. 
    destruct H2 as (H11&H12).
    assert (length ans < length ans') as H'.
    { unshelve rewrite (interrogation_quantifiers) in H1; eauto.
    destruct H1 as [-> _]. lia. } induction HE2 as [sth Hs].
    destruct (H12 _ H') as [H12' _]. rewrite Hs in H12'.
    rewrite take_app in H12'. 
    specialize (hasvalue_det H12' H1a). congruence.
  Qed.

  Lemma interrogation_eq (q: Q) (a: A) (τ: tree) R use use' ans ans' v : 
    functional R →
    interrogation τ R use ans → τ ans =! Output v →
    interrogation τ R use' ans' → τ ans' =! Output v →
    use = use'.
  Proof.
    intros funR H1 H1a H2 H2a.
    assert (length use ≤ length use' ∨ length use' ≤ length use) as [E|E] by lia.
    eapply interrogation_le_eq; eauto.
    symmetry. eapply interrogation_le_eq; eauto.
  Qed.

  Fixpoint evalt_comp (τ : tree) (f : Q → A) (step depth: nat): option (Q + O) :=
    match (seval (τ []) depth) with
    | Some x => 
      match step, x with
      | 0, Ask q => Some (Ask q)
      | S n, Ask q => evalt_comp (λ l, τ (f q :: l)) f n depth
      | _, Output o => Some (Output o) 
      end
    | None => None 
    end.

  Lemma evalt_comp_ext (τ τ': tree) f n m:
      (∀ l n, seval (τ l) n = seval (τ' l) n) → 
      evalt_comp τ f n m = evalt_comp τ' f n m.
  Proof.
    intro Heq; induction n in τ, τ', Heq |- *; cbn.
    - by rewrite <- Heq.
    - rewrite <- Heq.
      destruct (seval (A:=Q + O) (τ []) m); eauto.
      destruct s; eauto.
  Qed.

  Lemma interrogation_ter (τ: tree) f l lv v:
      interrogation τ (λ x y, f x = y) l lv → τ lv =! v →
      ∃ m, ∀ ans_, ans_ `prefix_of` lv → ∃ v, seval (τ ans_) m = Some v.
  Proof.  
    intros H1 H2.
    induction H1 in H2, v |-*. 
    - rewrite seval_hasvalue in H2.
      destruct H2 as [m Hm]. exists m.
      intros ans_ Hans_. exists v.
      apply prefix_nil_inv in Hans_.
      rewrite Hans_. easy.
    - rewrite seval_hasvalue in H2.
      destruct H2 as [m Hm].
      destruct (IHinterrogation (Ask q) H) as [m' Hm'].
      exists (max m m').
      intros ans_ Hans_.
      destruct (list_cons_or Hans_) as [h| ->].
      + destruct (Hm' ans_ h) as [v' Hv'].
      exists v'. eapply seval_mono.
      eauto. lia.
      + exists v. eapply seval_mono; [eauto| lia].
  Qed.

  (** Basic property of evalt_comp **)

  Lemma evalt_comp_depth_mono (τ: tree) f n m o:
      evalt_comp τ f n m = Some o →
      ∀ m', m ≤ m' → evalt_comp τ f n m' = Some o.
  Proof.
    intros H m' Hm'.
    induction n in H, τ, o |-*; cbn in *.
    - destruct (seval (A:=Q + O) (τ []) m) eqn: E; try congruence.
      assert (seval (A:=Q + O) (τ []) m' = (Some s)) as ->.
      eapply seval_mono. exact E. lia. done.
    - destruct (seval (A:=Q + O) (τ []) m) eqn: E; last congruence.
      assert (seval (A:=Q + O) (τ []) m' = Some s) as ->.
      eapply seval_mono. exact E. lia.
      destruct s. by apply IHn. exact H.
  Qed.

  Lemma interrogation_plus_evalt_comp (τ: tree) f n m l lv v2:
      interrogation τ (λ x y, f x = y) l lv →
      (∀ ans_, ans_ `prefix_of` lv -> ∃ v, seval (τ ans_) m = Some v) →
      evalt_comp (λ l', τ (lv ++ l')) f n m = Some v2 ↔ 
      evalt_comp τ f (length l + n) m = Some v2.
  Proof.
    intros H H1. split; revert n; dependent induction H; try eauto.
    - intros. cbn -[evalt]. rewrite app_length. cbn -[evalt].
      replace (length qs + 1 + n) with (length qs + (S n)) by lia.
      eapply IHinterrogation. intros; apply H2.
      etransitivity. exact H4. by eapply prefix_app_r.
      cbn. rewrite app_nil_r.
      destruct (H2 ans); first by eapply prefix_app_r.
      assert (exists m, seval (τ ans) m = Some x).
      by exists m. rewrite <- seval_hasvalue in H5.
      assert (x = Ask q). { eapply hasvalue_det; eauto. }
      rewrite H4, H6, H1, <- H3. eapply evalt_comp_ext.
      intros; by list_simplifier.
    - intros. rewrite app_length in H3. cbn in H3.
      replace (length qs + 1 + n) with (length qs + (S n)) in H3 by lia.
      eapply IHinterrogation in H3.
      2: { intros; apply H2. etransitivity. exact H4.
      by eapply prefix_app_r. }
      cbn in H3. rewrite app_nil_r in H3.
      destruct (H2 ans); first by eapply prefix_app_r.
      assert (exists m, seval (τ ans) m = Some x) by by exists m.
      rewrite <- seval_hasvalue in H5.
      assert (x = Ask q). { eapply hasvalue_det; eauto. }
      rewrite H4, H6, H1 in H3.
      rewrite <- H3. eapply evalt_comp_ext.
      intros; by list_simplifier.
  Qed.

  Lemma interrogation_plus_evalt_comp_1 (τ: tree) f n m l lv v:
    interrogation τ (λ x y, f x = y) l lv →
    evalt_comp τ f (length l + n) m = Some v →
    evalt_comp (λ l', τ (lv ++ l')) f n m = Some v.
  Proof.
    intros H. revert n; dependent induction H; try eauto.
    intros. rewrite app_length in H2. cbn in H2.
    replace (length qs + 1 + n) with (length qs + (S n)) in H2 by lia.
    eapply IHinterrogation in H2.
    cbn in H2. rewrite app_nil_r in H2.
    destruct (seval (τ ans) m) eqn: E; last done.
    destruct s.
    2: { exfalso. enough (Output o = Ask q) by done.
    eapply hasvalue_det; eauto.
    eapply seval_hasvalue. by exists m. }
    rewrite <- H2. eapply evalt_comp_ext.
    assert (q = q0) as [=<-].
    { assert (τ ans =! Ask q0) by (eapply seval_hasvalue; by exists m).
      by specialize (hasvalue_det H0 H3) as [=<-].  } 
    intros l_ n_. rewrite H1.
    by replace ((ans ++ [a]) ++ l_) with (ans ++ a :: l_) by by list_simplifier.
  Qed.


  Lemma evalt_comp_step_mono' τ f n m o:
    evalt_comp τ f n m = Some (Output o) →
    evalt_comp τ f (S n) m = Some (Output o) .
  Proof.
    induction n in o, τ |-*.
    - cbn. destruct (seval (τ []) m); last done.
      by destruct s.
    - intros H. cbn in H.
      cbn. destruct (seval (τ []) m); last done.
      destruct s; last done.
      apply (IHn _ _ H).
  Qed.

  Lemma evalt_comp_step_mono'' τ f n m o:
    evalt_comp τ f n m = Some (Output o) →
    ∀ n', n ≤ n' → evalt_comp τ f n' m = Some (Output o) .
  Proof.
    intros H n' Hn'.
    induction Hn'; first done.
    by eapply evalt_comp_step_mono'.
  Qed.
  

  Lemma evalt_comp_step_mono (τ: tree) f qs ans o:
      interrogation τ (λ x y, f x = y) qs ans →
      τ ans =! Output o →
      ∃ depth step, ∀ g, interrogation τ (λ x y, g x = y) qs ans →
      ∀ n', step ≤ n' → evalt_comp τ g n' depth = Some (Output o).
  Proof.
    intros H1 H2.
    destruct (interrogation_ter H1 H2) as [step Hstep].
    exists step. exists (length qs). intros g Hg n' Hn'.
    assert (exists v, seval (τ ans) step = Some v) as [v Hv].
    { eapply Hstep; naive_solver. }
    assert (v = Output o).
    { eapply hasvalue_det; [|eapply H2]. rewrite seval_hasvalue. eauto. }
    eapply Nat.le_exists_sub in Hn' as [k [-> _]].
    rewrite Nat.add_comm.
    eapply interrogation_plus_evalt_comp; eauto.
    induction k. all: cbn; rewrite app_nil_r; by rewrite Hv, H.
  Qed.


  Lemma evalt_comp_oracle_approx (τ: tree) f l lv v:
      interrogation τ (λ x y, f x = y) l lv →
      τ lv =! v →
      ∃ step depth, ∀ g, interrogation τ (λ x y, g x = y) l lv →
      evalt_comp τ g step depth = Some v.
  Proof.
    intros H1 h2.
    destruct (interrogation_ter H1 h2) as [step Hstep].
    exists (length l + 0), step.
    intros. eapply interrogation_plus_evalt_comp; eauto.
    cbn. rewrite app_nil_r.
    destruct (Hstep lv) as [v' Hv']; first done.
    assert (∃ k, seval (A:=Q + O) (τ lv) k = Some v') by by exists step.
    rewrite <- seval_hasvalue in H0.
    assert (v' = v) by by eapply hasvalue_det.
    rewrite Hv', H2. by destruct v.
  Qed.

  Lemma interrogation_evalt_comp_limit (τ: tree) f l lv v:
      (∞∀ k, interrogation τ (λ x y, f k x = y) l lv) →
      τ lv =! Output v →
      ∞∀ n, evalt_comp τ (f n) n n = Some (Output v).
  Proof.
    intros [k h1] h2.
    assert (interrogation τ (λ x y, f k x = y) l lv) as H.
    apply h1. lia.
    destruct (evalt_comp_step_mono H h2) as (a' & b' & Hs).
    destruct (evalt_comp_oracle_approx H h2) as (a & b & Hab).
    exists (max b'(max a' (max (max a b) k))).
    intros n Hn. eapply evalt_comp_depth_mono.
    eapply (Hs (f n)); eauto. eapply h1.
    all: lia.
  Qed.

  Lemma evalt_comp_to_interrogation (τ : tree) (f : Q → A) o n depth:
      eq_dec O → eq_dec Q →
      (Σ qs ans, evalt_comp τ f n depth = Some (Output o) ∧
      length qs ≤ n ∧ interrogation τ (λ q a, f q = a) qs ans ∧ τ ans =! Output o)
       + 
      (evalt_comp τ f n depth ≠ Some (Output o)).
  Proof.
    intros eq_dec_O eq_dec_Q.
    destruct (Dec (evalt_comp τ f n depth = Some (Output o))) as [H|H]; last by right.
    left. induction n in τ, H |- *.
    * cbn in *. destruct (seval (τ []) depth) eqn: E.
      exists [], []. repeat split; eauto. econstructor.
      destruct s. congruence.  rewrite seval_hasvalue.
      by exists depth; injection H as ->. congruence.
    * cbn in *.  destruct (seval (τ []) depth) eqn: E; try congruence.
      destruct s; try congruence.
      - eapply (IHn (λ l, τ (f q :: l))) in H as (qs & ans & H3 & H1 & H2 & H').
        exists (q :: qs), (f q :: ans). split; last split; eauto. cbn; lia. repeat split.
        eapply interrogation_app with (q1 := [q]) (a1 := [f q]).
        eapply Interrogate with (qs := []) (ans := []); eauto. econstructor.
        rewrite seval_hasvalue. by exists depth.
        eauto. eauto.
      - exists [], []. repeat split; try split; cbn. easy. lia. eauto. econstructor.
        rewrite seval_hasvalue.
        by exists depth; injection H as ->.
  Qed.

  Lemma evalt_comp_step (τ: tree) f n m v qs ans q:
    interrogation τ (λ x y, f x = y) qs ans →
    length qs = n →
    τ ans =! Ask q →
    evalt_comp τ f n m = Some (Ask q) ∧ seval (τ (f q::ans)) m = Some v →
    evalt_comp τ f (S n) m = Some v.
  Proof.
    intros HIn HE Hans [H1 H2].
    rewrite <- HE in *.
    replace (length qs) with (length qs + 0) in H1 by lia.
    eapply interrogation_plus_evalt_comp_1 in H1; last done.
    induction HIn.
    - simpl in *. admit.
    - admit.
  Admitted.

  Lemma evalt_comp_roll_back (τ: tree) f n m v qs ans q a:
    interrogation τ (λ x y, f x = y) (qs++[q]) (ans++[a]) →
    length qs = n →
    evalt_comp τ f (S n) m = Some v ↔ 
    evalt_comp τ f n m = Some (Ask q) ∧ seval (τ (f q::ans)) m = Some v.
  Proof.
    intro H. inv H.
    { exfalso. by apply app_cons_not_nil in H1. }
    apply app_inj_tail in H0. destruct H0 as [H61 H62].
    apply app_inj_tail in H1. destruct H1 as [H71 H72]. subst.
    intros H. subst.
    split; cbn.
  Admitted.
 
  

  Lemma final_fact_gen (τ: tree) m f g use ans:
  interrogation τ (λ x y, f x = y) use ans → 
  interrogation τ (λ x y, g x = y) use ans → 
  ∀ v n,
    evalt_comp τ f n m = Some v →
    length use = n →
    (∀ u, u ∈ use -> f u = g u) →
    evalt_comp τ g n m = Some v.
  Proof.
    induction 1; intros.
    { subst. simpl in *. done. }
    assert (interrogation τ (λ x y, f x = y) (qs ++ [q]) (ans ++ [a])) by
      (econstructor; eauto). 

    (* prepare the hypothesis *)
    rewrite last_length in *.
    destruct n; first congruence.
    destruct (evalt_comp_roll_back m v H6 eq_refl) as [Hc1 _].
    destruct (evalt_comp_roll_back m v H2 eq_refl) as [_ Hc2].
    assert (length qs = n) as H' by lia. subst.
    destruct (Hc1 H3) as (Hc&Hcq).

    inv H2. 
    (* inverse the second interrogation *)
    { exfalso. by apply app_cons_not_nil in H7. }
    apply app_inj_tail in H1. destruct H1 as [H61 H62].
    apply app_inj_tail in H7. destruct H7 as [H71 H72]. subst.
    specialize (IHinterrogation H8 (Ask q) (length qs) Hc eq_refl).

    (* inverse the goal *)
    apply Hc2. split.
    + eapply IHinterrogation. intros. eapply H5. 
      rewrite elem_of_app; by left.
    + enough (g q = f q) as -> by done.
      symmetry. eapply H5.
      rewrite elem_of_app. right.
      by rewrite elem_of_list_singleton.
  Qed.

  Lemma final_fact (τ: tree) n m f g use ans v:
    evalt_comp τ f n m = Some (Output v) →
    interrogation τ (λ x y, f x = y) use ans → 
    interrogation τ (λ x y, g x = y) use ans →
    τ ans =! Output v → 
    evalt_comp τ g n m = Some (Output v).
  Proof.
    intros Hf H1 H2 Ho.
    eapply (final_fact_gen H1 H2 Hf).
  Admitted.

End Step_Eval.

Section Use_Function.

  Lemma use_function {Q O: Type} (τ: (list bool) ↛ (Q + O)) (f: Q → bool) n m v:
    eq_dec O → eq_dec Q →
    (Σ use, 
    evalt_comp τ f n m = Some (inr v) ∧
    ∀ P, (∀ q, q ∈ use → P q ↔ f q = true) → 
      ∃ ans, interrogation τ (char_rel P) use ans ∧ τ ans =! inr v)  +
    (evalt_comp τ f n m ≠ Some (inr v)).
  Proof.
    intros h1 h2. 
    destruct (evalt_comp_to_interrogation τ f v n m) as [(qs&ans&H3&_&H1&H2)|H]; try done.
    left. exists qs. split; first easy. intros P HqP.
    exists ans; split; last done.
    eapply interrogation_ext; [eauto| |apply H1].
    intros q' [|] Hqa'%elem_of_list_In; cbn; first by rewrite HqP.
    specialize (HqP q' Hqa'). split.
    - intros H. destruct (f q') eqn: E; last done.
      enough (P q') by easy. by rewrite HqP.
    - intros H H'%HqP. congruence.
    - right. done.
  Qed.


End Use_Function.

Section Limit_Interrogation.

  Variable Q: Type.
  Variable P: Q → Prop.

  Definition stable (f: nat → Q → bool) :=
    ∀ q n m, n ≤ m → f n q = true → f m q = true.

  Fixpoint stabilize_step (f: Q -> nat -> bool) x n :=
    match n with
    | O => false
    | S n => if f x n then true else stabilize_step f x n
    end.

  Definition stable_semi_decider (f: nat → Q → bool) :=
    semi_decider (λ x n, f n x) P ∧ stable f.

  Fact semi_decider_to_stable: ∀ f, semi_decider f P → Σ g, stable_semi_decider g.
  Proof.
    intros f S_P. exists (λ n x, stabilize_step f x n); split.
    - intro x; split; intro h.
      rewrite (S_P x) in h.
      destruct h as [c Hc].
      by exists (S c); cbn; rewrite Hc.
      rewrite (S_P x).
      destruct h as [c Hc].
      induction c; cbn in Hc; [congruence|].
      destruct (f x c) eqn: E; [now exists c|now apply IHc].
    - intros x n m Lenm Hn.
      induction Lenm; [trivial|].
      cbn; destruct (f x m) eqn: E; [trivial|assumption].
  Qed.

  Definition approx_Σ1 O  (f: nat → Q → bool) :=
      ∀ (τ: list bool ↛ (Q + O)) qs ans,
        interrogation τ (char_rel P) qs ans → 
        ∞∀ m, interrogation τ (λ q a, f m q = a) qs ans.

  Definition approx_Σ1_rev O (f: nat → Q → bool) :=
      ∀ (τ: list bool ↛ (Q + O)) qs ans,
        (∞∀ m, interrogation τ (λ q a, f m q = a) qs ans) →
        interrogation τ (char_rel P) qs ans.

  Definition approx_list (f: Q → bool) L :=
      ∀ i, In i L → P i ↔ f i = true.

  Definition approx_list_func (f g: Q → bool) L :=
      ∀ i, In i L → f i ↔ g i.

  Variable g: nat → Q → bool.
  Hypothesis S_P: stable_semi_decider g.

  Definition S_approx_Σ1: ∀ O, approx_Σ1 O g.
  Proof.
    destruct S_P as [H1 H2]; intros O τ qs ans Hτ.
    induction Hτ.
    - exists 0; intros; econstructor.
    - destruct IHHτ as [w Hw].
      destruct a; cbn in H0.
      + rewrite (H1 q) in H0. destruct H0 as [m Hm].
        exists (S (max w m)). intros m' Hm'.
        econstructor. eapply Hw; first lia.
        assumption. eapply H2; last apply Hm. lia.
      + exists w; intros m Hm.
        econstructor. eapply Hw; first done.
        assumption. destruct (g m q) eqn: E; last done.
        enough (P q) by done. { rewrite (H1 q). by exists m. }
  Qed.

  Lemma approx_Σ1_list: definite P → ∀ L, ∞∀ c, approx_list (g c) L.
  Proof.
    destruct S_P as [S_p HS].
    intros def_p l. induction l as [|a l [c Hc]].
    - exists 42; firstorder.
    - destruct (def_p a) as [h1| h2].
      + destruct (S_p a) as [H _].
        destruct (H h1) as [N HN].
        exists (max c N); intros c' Hc' e [->| He].
        split; [intros _|easy].
        eapply HS; [|eapply HN]; lia.
        unfold approx_list in Hc.
        rewrite (Hc c'); [trivial|lia | assumption].
      + exists c; intros c' Hc' e [->| He].
        split; [easy| intros h'].
        unfold semi_decider in S_p.
        rewrite S_p. by exists c'.
        unfold approx_list in Hc.
        rewrite Hc; eauto.
  Qed.

  Definition S_approx_Σ1_rev: definite P → ∀ O, approx_Σ1_rev O g.
  Proof.
    intros defp O τ qs ans [w Hw].
    assert (∞∀ k, ∀ q, In q qs → P q ↔ g k q = true) as [k Hk] by by apply approx_Σ1_list.
    assert (interrogation τ (λ q a, g (max w k) q = a) qs ans) as H by (apply Hw; lia).
    clear Hw. induction H; first econstructor.
    econstructor; [|done|].
    eapply IHinterrogation.
    { intros. rewrite Hk; try done. apply in_app_iff. by left. }
    destruct a; cbn; rewrite Hk; try (done||lia).
    rewrite in_app_iff; right; econstructor. done.
    intro H'. enough (g (w`max`k) q = true) by congruence.
    destruct S_P as [H1' H2]. eapply H2; last apply H'. lia.
    rewrite in_app_iff; right; econstructor. done.
  Qed.


End Limit_Interrogation.

Section Step_Eval_Spec.

  Definition Φ_ (f: nat → nat → bool) (e x n: nat): option () :=
    match evalt_comp (ξ () e x) (f n) n n with
    | Some (inr ()) => Some ()
    | _ => None 
    end.

  Definition φ (f: nat → bool) (e x n: nat) :=
    if use_function (ξ () e x) f n n () unit_eq_dec nat_eq_dec 
      is inl H then S (list_max (projT1 H))
      else 0.

  Variable P: nat → Prop.
  Variable decider: nat → nat → bool.
  Hypothesis S_P: stable_semi_decider P decider.

  Fact phi_iff_evalt f e x n :
    Φ_ f e x n = Some () ↔ evalt_comp (ξ () e x) (f n) n n = Some (inr ()).
  Proof.
    unfold Φ_. destruct (evalt_comp (ξ () e x) (f n) n n) eqn: E; [destruct s|].
    - split; congruence.
    - destruct u. done.
    - split; congruence.
  Qed.

  Theorem Φ_spec e x:
    Ξ e (char_rel P) x → (∞∀ n, Φ_ decider e x n = Some ()).
  Proof.
    unfold Ξ, rel. intros (qs & ans & Ha & Hb).
    specialize (@S_approx_Σ1 _ _ _ S_P () (ξ _ e x) qs ans Ha) as H.
    eapply interrogation_evalt_comp_limit in H; last apply Hb.
    destruct H as [w Hw].
    exists w; intros m Hm. unfold Φ_. specialize (Hw m Hm).
    destruct (evalt_comp (ξ () e x) (decider m) m m).
    destruct s. by injection Hw.
    by destruct u. congruence.
  Qed. 

  Notation "A ≡{ k }≡ B" := (∀ x, x ≤ k → A x ↔ B x) (at level 30).
  Definition to_pred (f: nat → bool) x := f x = true.

  Theorem φ_spec e x n p:
    Φ_ decider e x n = Some () →
    p ≡{φ (decider n) e x n}≡ to_pred (decider n) →
    Ξ e (char_rel p) x.
  Proof.
    intros H2 H1. rewrite phi_iff_evalt in H2. unfold φ in H1. 
    destruct (use_function (ξ () e x) (decider n) n n _ _ _) as [(ans&Hans)|H]; last done.
    exists ans. eapply Hans.
    intros q [i Hq]%elem_of_list_lookup_1. rewrite H1; first done.
    simpl. enough (q ≤ list_max (ans)) by lia.
    eapply implementation.list_max_lookup. 
    eapply Hq.
  Qed.

  Lemma φ_spec0_1 e x n:
    φ (decider n) e x n ≠ 0 → Φ_ decider e x n = Some ().
  Proof.
    unfold φ, Φ_. intros H. 
    destruct (use_function (ξ () e x) (decider n) n n () unit_eq_dec nat_eq_dec).
    - clear H. by destruct s as (_&->&_). 
    - congruence.
  Qed.

  Lemma φ_spec0_2 e x n:
    Φ_ decider e x n = Some () → φ (decider n) e x n ≠ 0.
  Proof.
    unfold φ, Φ_. intros H. 
    destruct (use_function (ξ () e x) (decider n) n n () unit_eq_dec nat_eq_dec).
    - lia.
    - destruct (evalt_comp (ξ () e x) (decider n) n n); last eauto.
      destruct s; eauto. destruct u. congruence.
  Qed.

  Theorem φ_spec0 e x n: φ (decider n) e x n ≠ 0 ↔ Φ_ decider e x n = Some ().
  Proof. split; [apply φ_spec0_1|apply φ_spec0_2]. Qed.

  Theorem φ_spec0' e x n: φ (decider n) e x n = 0 ↔ Φ_ decider e x n = None.
  Proof.
    destruct (φ_spec0 e x n) as [H1 H2]. split; intros H.
    - destruct (φ (decider n) e x n); eauto.
      destruct (Φ_ decider e x n); eauto.
      destruct u; eauto. enough (0≠0) by congruence.
      by eapply H2.
    - destruct (Φ_ decider e x n); try congruence.
      destruct (φ (decider n) e x n); eauto.
      enough (None = Some ()) by congruence.
      by eapply H1.
  Qed.

  Fact char_rel_boring n:
    ∀ q a, char_rel (decider n) q a ↔ (λ x y, decider n x = y) q a.
  Proof. intros. unfold char_rel. destruct a, (decider n q); intuition. Qed. 

  Theorem φ_spec1 e x n k :
    φ (decider n) e x n = S k →
    to_pred (decider n) ≡{k}≡ to_pred (decider (S n)) →
    φ (decider (S n)) e x (S n) = S k.
  Proof.
    intros H H2. unfold φ in *.
    destruct (use_function (ξ () e x) (decider n) n n) 
      as [(use & Hu1 & Hu2)|]; last congruence. simpl in *.

    assert (∀ q, q ∈ use → decider (S n) q ↔ decider n q = true) as boring1.
      { intros q Hq. destruct (H2 q). apply elem_of_list_lookup_1 in Hq.
      destruct Hq as [i Hi]. injection H; intros <-.
      by eapply implementation.list_max_lookup.
      unfold to_pred in *. destruct (decider (S n) q); intuition. }

    assert (∀ q a, In q use → char_rel (decider n) q a ↔ char_rel (decider (S n)) q a) as boring2.
      { intros q a Hq. destruct (H2 q). rewrite <-elem_of_list_In in Hq.
        apply elem_of_list_lookup_1 in Hq. destruct Hq as [i Hi].
        injection H; intros <-. by eapply implementation.list_max_lookup.
        unfold to_pred, char_rel in *.  
        destruct a, (decider (S n) q), (decider n q); intuition. }

    destruct (Hu2 (decider (S n)) boring1) as [ans (Hans & Hans1)].

    destruct (use_function (ξ () e x) (decider (S n)) (S n) (S n)) as [(use' & Hu1' & Hu2')|HSn].
    + destruct (Hu2' (decider (S n))) as [ans' (Hans' & Hans1')].
      { intros; destruct (decider (S n) q); intuition. }
      enough (use = use') as Hanseq. 
      { cbn. rewrite <- Hanseq. apply H. }
      assert (functional (char_rel (decider (S n)))) as _H_. 
      { intros ?[][]; unfold to_pred, char_rel; eauto. }
      by edestruct (interrogation_eq 42 true _H_ Hans Hans1 Hans' Hans1').
    + exfalso; apply HSn. 
      assert (interrogation (ξ () e x) (λ q a, decider n q = a) use ans) as Hansn.
      { eapply interrogation_ext; last apply Hans; first done. intros.
        rewrite <- char_rel_boring. by apply boring2. }
      assert (n ≤ S n) as _H_ by lia.
      unshelve eapply (evalt_comp_depth_mono _ _H_).
      eapply (evalt_comp_step_mono').
      assert (interrogation (ξ () e x) (λ q a, decider (S n) q = a) use ans) as HansSn.
      { eapply interrogation_ext; last apply Hans; first done. intros; by rewrite char_rel_boring. }
      clear Hu2 S_P HSn boring1 boring2 H H2 _H_ Hans. 
      eapply final_fact; eauto.
  Qed.

End Step_Eval_Spec.







