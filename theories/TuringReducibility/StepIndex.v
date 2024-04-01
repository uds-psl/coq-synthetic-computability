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
    eapply interrogation_plus_evalt_comp ; eauto.
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
      evalt_comp τ f n depth = Some (Output o) →
      Σ (qs : list Q) (ans : list A),
        length qs ≤ n ∧
        interrogation τ (λ q a, f q = a) qs ans ∧ 
        τ ans =! Output o.
  Proof.
    intros H.
    induction n in τ, H |- *.
    * cbn in *. destruct (seval (τ []) depth) eqn: E.
      exists [], []. repeat split. eauto. econstructor.
      destruct s. congruence. rewrite seval_hasvalue.
      by exists depth; injection H as ->. congruence.
    * cbn in *.  destruct (seval (τ []) depth) eqn: E; try congruence.
      destruct s; try congruence.
      - eapply (IHn (λ l, τ (f q :: l))) in H as (qs & ans & H3 & H1 & H2).
        exists (q :: qs), (f q :: ans). split; eauto. cbn; lia. repeat split.
        eapply interrogation_app with (q1 := [q]) (a1 := [f q]).
        eapply Interrogate with (qs := []) (ans := []); eauto. econstructor.
        rewrite seval_hasvalue. by exists depth.
        eauto. eauto.
      - exists [], []. repeat split. cbn. lia. eauto. econstructor.
        rewrite seval_hasvalue.
        by exists depth; injection H as ->.
  Qed.

  Lemma evalt_comp_limit_interrogation (τ: tree) f v:
      (∞∀ n, evalt_comp τ (f n) n n = Some (Output v)) →
      (∞∀ k, ∃ l lv, τ lv =! Output v ∧ interrogation τ (λ x y, f k x = y) l lv).
  Proof.
    intros [w Hw].
    exists w. intros m Hm.
    specialize (Hw m Hm) as H.
    destruct (evalt_comp_to_interrogation H) as (qs&ans&Hl&Hans&Hans').
    exists qs, ans. split; eauto.
  Qed.

End Step_Eval.

Section Use_Function.

  Definition list_interp (L: list nat) (q: nat): bool := Dec (In q L).

  Lemma try (O: Type) (τ: tree)  n m (v: nat + O) L:
    evalt_comp τ (list_interp L) n m = Some v → Σ k,
    ∀ x, k < x → evalt_comp τ (list_interp (x::L)) n m = Some v.
  Proof.
    induction n in v |-*.
    - exists 42. intros x Hx.
      unfold evalt_comp in *. by destruct (seval (τ []) m).
    - intros H. destruct (evalt_comp τ (list_interp L) n m) eqn: E; last first.
      admit.
      destruct s; last first.
      (* specialize (evalt_comp_step_mono ). *)
      (* exists 42. intros H. 
      destruct v as [i|].
      exists (S (max i k)). intros Hi x Hx.
  *)
  Abort.

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

  Variable P: nat → Prop.
  Hypothesis Hf_: Σ f_, semi_decider f_ P.

  Definition f := projT1 (semi_decider_to_stable (projT2 Hf_)).
  Fact S_P: stable_semi_decider P f.
  Proof. unfold f. by destruct (semi_decider_to_stable (projT2 Hf_)). Qed.

  Definition Φ_ (f: nat → nat → bool) (e x n: nat): option () :=
    match evalt_comp (ξ () e x) (f n) n n with
    | Some (inr ()) => Some ()
    | _ => None 
    end.

  Lemma Φ_spec_1 e x:
    Ξ e (char_rel P) x → (∞∀ n, Φ_ f e x n = Some ()).
  Proof.
    unfold Ξ, rel. intros (qs & ans & Ha & Hb).
    specialize (@S_approx_Σ1 _ _ _ S_P () (ξ _ e x) qs ans Ha) as H.
    eapply interrogation_evalt_comp_limit in H; last apply Hb.
    destruct H as [w Hw].
    exists w; intros m Hm. unfold Φ_. specialize (Hw m Hm).
    destruct (evalt_comp (ξ () e x) (f m) m m).
    destruct s. by injection Hw.
    by destruct u. congruence.
  Qed.

  Lemma Φ_spec: 
    Σ Φ_, ∀ e x, Ξ e (char_rel P) x → (∞∀ n, Φ_ f e x n = Some ()).
  Proof. exists Φ_; intros e x; apply Φ_spec_1. Qed.

End Step_Eval_Spec.






