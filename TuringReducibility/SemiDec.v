From SyntheticComputability Require Import TuringReducibility.OracleComputability.
From SyntheticComputability Require Import partial Definitions reductions Dec DecidabilityFacts.
Require Import Lia List.
From stdpp Require Import list.
Import PartialTactics.

Lemma seval_hasvalue' {partiality : partial.partiality} [A : Type] (x : part A) (a : A) n :
    seval x n = Some a -> x =! a.
Proof.
  intros. eapply seval_hasvalue. eauto.
Qed.

Section PT.

Context  {Part : partiality} {X : Type} {Y : Type}.
Variable  q : Y → Prop.
Variable  p : X → Prop.
Variable  F1 : Functional Y bool X ().
Variable  tau1 : X → (list bool) ↛ (Y + unit).
Variable  HF1 : ∀ (R : FunRel Y bool) (x : X) (o : ()), F1 R x o ↔ (∃ (qs : list Y) (ans : list bool), noqinterrogation (tau1 x) R qs ans ∧ tau1 x ans =! inr o).
Variable  H1 : ∀ x : X, p x ↔ F1 (char_rel q) x ().
Variable  F2 : Functional Y bool X ().
Variable  tau2 : X → (list bool) ↛ (Y + unit).
Variable  HF2 : ∀ (R : FunRel Y bool) (x : X) (o : ()), F2 R x o ↔ (∃ (qs : list Y) (ans : list bool), noqinterrogation (tau2 x) R qs ans ∧ tau2 x ans =! inr o).
Variable  H2 : ∀ x : X, ¬ p x ↔ F2 (char_rel q) x ().

Definition get_ans B (tqs : list (bool * Y)) (ans : list bool) := (map snd (filter (fun '((b, q), a) => b = B) (zip_with pair tqs ans))).
Definition get_ans1 := get_ans true.
Definition get_ans2 := get_ans false.
Definition get_qs B (tqs : list (bool * Y)) := (map snd (filter (fun '((b, q)) => b = B) tqs)).
Definition get_qs1 := get_qs true.
Definition get_qs2 := get_qs false.

Lemma get_ans_app B t1 t2 a1 a2 :
  length t1 = length a1 ->
  get_ans B (t1 ++ t2) (a1 ++ a2) =  get_ans B t1 a1 ++ get_ans B t2 a2.
Proof.
  intros Hlen.
  induction t1 in a1, Hlen |- *; destruct a1; cbn in *; try lia.
  - reflexivity.
  - destruct a. destruct decide.
    + cbn. f_equal.  eapply IHt1. lia.
    + eapply IHt1. lia.
Qed.

Lemma get_qs_app B t1 t2 :
  get_qs B (t1 ++ t2) =  get_qs B t1 ++ get_qs B t2.
Proof.
  induction t1.
  - reflexivity.
  - cbn. destruct a. destruct decide.
    + cbn. f_equal.  eapply IHt1. 
    + eapply IHt1. 
Qed.

Definition τ := fun x '(old, n, tqs) ans =>
                  match old with Some q => ret (inl (None, n, tqs ++ [(false, q)], Some q))
                            | None =>
                                match seval (tau1 x (get_ans1 tqs ans)) n, seval (tau2 x (get_ans2 tqs ans)) n with
                                | Some (inr o), _ => ret (inr true)
                                | _ , Some (inr o) => ret (inr false)
                                | Some (inl q), Some (inl q') => ret (inl (Some q' , S n, tqs ++ [(true,  q)], Some q))
                                | Some (inl q), _ => ret (inl (None, S n, tqs ++ [(true,  q)], Some q))
                                | _, Some (inl q) => ret (inl (None, S n, tqs ++ [(false, q)], Some q))
                                | _, _ => ret (inl (None, S n, tqs, None))
                                end end.

Definition qs_from_tqs (tqs : list (bool * Y)) := map snd tqs.

Definition subtree (tau : list bool ↛ (Y + ())) ans l := tau (ans ++ l).
Definition subtree' {E Q A O} (tau : stree E Q A O) ans e l := tau e (ans ++ l).

Variable q_dec : forall y, q y \/ ~ q y.

Lemma q_reflect y : exists b, char_rel q y b.
Proof.
  destruct (q_dec y).
  exists true; eauto.
  exists false; eauto.
Qed.

Variable Y_dec : eq_dec Y.

Lemma count_up_1 m tqs x ans v n :
  p x ->
  length tqs = length ans ->
  noqinterrogation (tau2 x) (char_rel q) (get_qs2 tqs) (get_ans2 tqs ans) ->
  seval (tau1 x (get_ans1 tqs ans)) n = Some v ->
  exists tqs' ans' n',
    seval (tau1 x (get_ans1 tqs ans)) n' = Some v /\
    sinterrogation (subtree' (τ x) ans) (char_rel q) tqs' ans' (None,m, tqs) (None, n', tqs ++ map (pair false) tqs') /\
    noqinterrogation (subtree (tau2 x) (get_ans2 tqs ans)) (char_rel q) tqs' ans'.
Proof.
  intros Hx Hlen Hi2 Hend.
  edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun n => seval (tau1 x (get_ans1 tqs ans)) n = Some v).
  { intros. clear - Y_dec. destruct seval as [ [? | []] | ]; try now clear; firstorder congruence.
    all: destruct v as [ | []]; try now clear; firstorder congruence.
    destruct (Y_dec y y0); try firstorder congruence.
  }
  { eauto. }
  clear n Hend. rename x0 into n. destruct H as [ [] ]. rename H into Hend.
  clear H3.
  assert (Hleast : ∀ x' : nat, x' < n -> seval (tau1 x (get_ans1 tqs ans)) x' = None).
  {
    intros x' Hl. destruct (seval (tau1 x (get_ans1 tqs ans)) x') as [ [ | []] | ] eqn:E.
    - assert (v = inl y) as ->. { eapply hasvalue_det; eapply seval_hasvalue'; eauto. }
      eapply H0 in E. lia.
    - assert (v = inr ()) as ->. { eapply hasvalue_det; eapply seval_hasvalue'; eauto. }
      eapply H0 in E. lia.
    - reflexivity.
  }
  clear H0.
  destruct (nat_le_dec m n).
  - revert Hi2 Hend Hlen Hleast. revert ans tqs. pattern m, n. revert m l.
    eapply Nat.left_induction.
    + exact _.
    + intros. exists [], [], n. repeat eapply conj.
      * eauto.
      * cbn. rewrite app_nil_r. econstructor.
      * econstructor.
    + intros m Hlt IH ? ? ? ? ? ?.
      destruct (seval (tau2 x (get_ans2 tqs ans)) m) as [ [ | []] | ] eqn:E.
      * destruct (q_reflect y) as [b Hb].
        specialize (IH (ans ++ [b]) (tqs ++ [(false, y)])).
        edestruct IH as (tqs' & ans' & n' & IH1 & IH2 & IH3).
        {
          unfold get_qs2. rewrite !get_qs_app.
          unfold get_ans2. rewrite !get_ans_app; eauto.
          cbn. destruct decide; try congruence.
          cbn. econstructor. eauto. 2: eapply Hb.
          eapply seval_hasvalue'; eassumption.
        }
        {
          unfold get_ans1. rewrite get_ans_app. cbn.
          destruct decide; try congruence. cbn. rewrite app_nil_r.
          all: eauto.
        }
        { rewrite !app_length. cbn. lia. }
        {
          unfold get_ans1. rewrite get_ans_app. cbn.
          destruct decide; try congruence. cbn. rewrite app_nil_r.
          all: eauto.
        }
        exists (y :: tqs'), (b :: ans'), n'. repeat eapply conj.
        -- unfold get_ans1 in IH1.
           rewrite get_ans_app in IH1. 2: eauto.
           cbn in IH1. destruct decide; try congruence.
           cbn in *. rewrite app_nil_r in IH1. eauto.
        -- eapply sinterrogation_cons.
           2: eauto. cbn.
           rewrite app_nil_r.
           assert (seval (tau1 x (get_ans1 tqs ans)) m = None) as ->.
           { eapply Hleast. lia. }
           rewrite E. psimpl.
           cbn. unfold subtree in *.
           rewrite <- !app_assoc in IH2. cbn in *.
           eapply sinterrogation_ext. 2: eassumption.
           intros. unfold subtree'. cbn. now rewrite <- app_assoc.
        -- eapply noqinterrogation_cons. eapply seval_hasvalue'; eauto.
           unfold subtree. rewrite app_nil_r. eassumption. eauto.
           eapply noqinterrogation_ext. 3: eauto. 2: reflexivity.
           intros. unfold subtree.
           unfold get_ans2. rewrite get_ans_app. cbn.
           destruct decide; try congruence. cbn. now rewrite <- app_assoc.
           eauto.
      * edestruct IH as (tqs' & ans' & n' & IH1 & IH2 & IH3); eauto.
        assert (~ p x). {
          eapply H2, HF2. repeat eexists. 2: eapply seval_hasvalue'; eauto.
          eauto.
        }
        tauto.
      * specialize (IH ans tqs).
        edestruct IH as (tqs' & ans' & n' & IH1 & IH2 & IH3); eauto.
        exists tqs', ans', n'. repeat eapply conj.
        -- eauto.
        -- eapply sinterrogation_scons.
           2: eauto. cbn.
           rewrite app_nil_r.
           assert (seval (tau1 x (get_ans1 tqs ans)) m = None) as ->.
           { eapply Hleast. lia. }
           rewrite E. psimpl.
        -- eauto.
  - exists [], [], m. repeat eapply conj.
    + eapply seval_mono; eauto. lia.
    + cbn. rewrite app_nil_r. econstructor.
    + cbn. econstructor.
Qed.

Lemma count_up_2 m tqs x ans v n :
  ~ p x ->
  length tqs = length ans ->
  noqinterrogation (tau1 x) (char_rel q) (get_qs1 tqs) (get_ans1 tqs ans) ->
  seval (tau2 x (get_ans2 tqs ans)) n = Some v ->
  exists tqs' ans' n',
    seval (tau2 x (get_ans2 tqs ans)) n' = Some v /\
    sinterrogation (subtree' (τ x) ans) (char_rel q) tqs' ans' (None,m, tqs) (None, n', tqs ++ map (pair true) tqs') /\
    noqinterrogation (subtree (tau1 x) (get_ans1 tqs ans)) (char_rel q) tqs' ans'.
Proof.
  intros Hx Hlen Hi2 Hend.
  edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun n => seval (tau2 x (get_ans2 tqs ans)) n = Some v).
  { intros. clear - Y_dec. destruct seval as [ [? | []] | ]; try now clear; firstorder congruence.
    all: destruct v as [ | []]; try now clear; firstorder congruence.
    destruct (Y_dec y y0); try firstorder congruence.
  }
  { eauto. }
  clear n Hend. rename x0 into n. destruct H as [ [] ]. rename H into Hend.
  clear H3.
  assert (Hleast : ∀ x' : nat, x' < n -> seval (tau2 x (get_ans2 tqs ans)) x' = None).
  {
    intros x' Hl. destruct (seval (tau2 x (get_ans2 tqs ans)) x') as [ [ | []] | ] eqn:E.
    - assert (v = inl y) as ->. { eapply hasvalue_det; eapply seval_hasvalue'; eauto. }
      eapply H0 in E. lia.
    - assert (v = inr ()) as ->. { eapply hasvalue_det; eapply seval_hasvalue'; eauto. }
      eapply H0 in E. lia.
    - reflexivity.
  }
  clear H0.
  destruct (nat_le_dec m n).
  - revert Hi2 Hend Hlen Hleast. revert ans tqs. pattern m, n. revert m l.
    eapply Nat.left_induction.
    + exact _.
    + intros. exists [], [], n. repeat eapply conj.
      * eauto.
      * cbn. rewrite app_nil_r. econstructor.
      * econstructor.
    + intros m Hlt IH ? ? ? ? ? ?.
      destruct (seval (tau1 x (get_ans1 tqs ans)) m) as [ [ | []] | ] eqn:E.
      * destruct (q_reflect y) as [b Hb].
        specialize (IH (ans ++ [b]) (tqs ++ [(true, y)])).
        edestruct IH as (tqs' & ans' & n' & IH1 & IH2 & IH3).
        {
          unfold get_qs1. rewrite !get_qs_app.
          unfold get_ans1. rewrite !get_ans_app; eauto.
          cbn. destruct decide; try congruence.
          cbn. econstructor. eauto.
          eapply seval_hasvalue'; eauto.
          eauto.
        }
        {
          unfold get_ans2. rewrite get_ans_app. cbn.
          destruct decide; try congruence. cbn.
          rewrite app_nil_r; eassumption.
          all: eauto.
        }
        { rewrite !app_length. cbn. lia. }
        {
          unfold get_ans2. rewrite get_ans_app. cbn.
          destruct decide; try congruence. cbn. rewrite app_nil_r.
          all: eauto.
        }
        exists (y :: tqs'), (b :: ans'), n'. repeat eapply conj.
        -- unfold get_ans2 in IH1.
           rewrite get_ans_app in IH1. 2: eauto.
           cbn in IH1. destruct decide; try congruence.
           cbn in *. rewrite app_nil_r in IH1. eauto.
        -- eapply sinterrogation_cons.
           2: eauto. cbn.
           rewrite app_nil_r.
           rewrite E.
           rewrite Hleast. 2: lia.
           psimpl.
           cbn. unfold subtree in *.
           rewrite <- !app_assoc in IH2. cbn in *.
           eapply sinterrogation_ext. 2: eassumption.
           intros. unfold subtree'. cbn. now rewrite <- app_assoc.
        -- eapply noqinterrogation_cons. eapply seval_hasvalue'; eauto.
           unfold subtree. rewrite app_nil_r. eassumption. eauto.
           eapply noqinterrogation_ext. 3: eauto. 2: reflexivity.
           intros. unfold subtree.
           unfold get_ans1. rewrite get_ans_app. cbn.
           destruct decide; try congruence. cbn. now rewrite <- app_assoc.
           eauto.
      * edestruct IH as (tqs' & ans' & n' & IH1 & IH2 & IH3); eauto.
        assert (p x). {
          eapply H1, HF1. repeat eexists. 2: eapply seval_hasvalue'; eauto.
          eauto.
        }
        tauto.
      * specialize (IH ans tqs).
        edestruct IH as (tqs' & ans' & n' & IH1 & IH2 & IH3); eauto.
        exists tqs', ans', n'. repeat eapply conj.
        -- eauto.
        -- eapply sinterrogation_scons.
           2: eauto. cbn.
           rewrite app_nil_r.
           rewrite E.
           rewrite Hleast. 2: lia. psimpl.
        -- eauto.
  - exists [], [], m. repeat eapply conj.
    + eapply seval_mono; eauto. lia.
    + cbn. rewrite app_nil_r. econstructor.
    + cbn. econstructor.
Qed.

Lemma back:
  ∀ (x : X) (qs : list Y) (ans : list bool) (n : nat) (tqs : list (bool * Y)) o,
    sinterrogation (τ x) (char_rel q) qs ans (None, 0, []) (o, n, tqs)
    → qs = map snd tqs
      /\ length ans = length tqs 
      /\ match o with Some q => tau2 x (get_ans2 tqs ans) =! inl q | None => True end 
      ∧ noqinterrogation (tau1 x) (λ (x0 : Y) (b : bool), if b then q x0 else ¬ q x0) (get_qs1 tqs) (get_ans1 tqs ans)
      ∧ noqinterrogation (tau2 x) (λ (x0 : Y) (b : bool), if b then q x0 else ¬ q x0) (get_qs2 tqs) (get_ans2 tqs ans).
Proof.
  intros x qs ans n tqs o Hint.
  remember (None, 0, []) as begin.
  remember (o, n, tqs) as theend.
  induction Hint in Heqbegin, Heqtheend, tqs, n, o |- *.
  - subst. inversion Heqtheend; subst. cbn. repeat eapply conj; econstructor.
  - subst. destruct e1' as [[o' n'] tqs'].
    cbn in H. destruct o'; cbn in *; psimpl.
    edestruct IHHint as (-> & Hlen & IH3 & IH1 & IH2); try reflexivity.
    destruct seval as [ [? | []] | ] eqn:E1.
    + destruct (seval (tau2 x (get_ans2 tqs' ans)) n') as [ [? | []] | ] eqn:E2; psimpl.
    + psimpl.
    + destruct (seval (tau2 x (get_ans2 tqs' ans)) n') as [ [? | []] | ] eqn:E2; psimpl.
  - subst. destruct e1' as [[o' n'] tqs'].
    edestruct IHHint as (-> & Hlen & IH3 & IH1 & IH2); try reflexivity.
    cbn in H. destruct o'; psimpl.
    {
      assert ((get_qs2 (tqs' ++ [(false, q0)])) = get_qs2 tqs' ++ [q0]) as Eqn1.
      { unfold get_qs2. rewrite get_qs_app. cbn. destruct decide; try congruence. reflexivity. }
      assert ((get_qs1 (tqs' ++ [(false, q0)])) = get_qs1 tqs') as Eqn2.
      { unfold get_qs1. rewrite get_qs_app. cbn. destruct decide; try congruence. cbn. now rewrite app_nil_r. }
      assert ((get_ans2 (tqs' ++ [(false, q0)]) (ans ++ [a])) = get_ans2 tqs' ans ++ [a]) as Eqn1'.
      { unfold get_ans2. rewrite get_ans_app. 2: lia.
        cbn. now destruct decide; try congruence; cbn.
      }
      assert ((get_ans1 (tqs' ++ [(false, q0)]) (ans ++ [a])) = get_ans1 tqs' ans) as Eqn2'.
      { unfold get_ans1. rewrite get_ans_app. 2: lia.
        cbn. destruct decide; try congruence; cbn. now rewrite app_nil_r.
      }
      repeat eapply conj.
      + now rewrite map_app; cbn.
      + rewrite !app_length; cbn. lia.
      + eauto.
      + rewrite Eqn2, Eqn2'. eauto.
      + rewrite Eqn1, Eqn1'. econstructor. eauto. 2: eapply H0.
        eauto.
    }
    destruct seval as [ [? | []] | ] eqn:E1.
    + assert ((get_qs1 (tqs' ++ [(true, q0)])) = get_qs1 tqs' ++ [q0]) as Eqn1.
      { unfold get_qs1. rewrite get_qs_app. cbn. destruct decide; try congruence. reflexivity. }
      assert ((get_qs2 (tqs' ++ [(true, q0)])) = get_qs2 tqs') as Eqn2.
      { unfold get_qs2. rewrite get_qs_app. cbn. destruct decide; try congruence. cbn. now rewrite app_nil_r. }
      assert ((get_ans1 (tqs' ++ [(true, q0)]) (ans ++ [a])) = get_ans1 tqs' ans ++ [a]) as Eqn1'.
      { unfold get_ans1. rewrite get_ans_app. 2: lia.
        cbn. now destruct decide; try congruence; cbn.
      }
      assert ((get_ans2 (tqs' ++ [(true, q0)]) (ans ++ [a])) = get_ans2 tqs' ans) as Eqn2'.
      { unfold get_ans2. rewrite get_ans_app. 2: lia.
        cbn. destruct decide; try congruence; cbn. now rewrite app_nil_r.
      }
      destruct (seval (tau2 x (get_ans2 tqs' ans)) n') as [ [? | []] | ] eqn:E2; psimpl.
      * repeat eapply conj.
        -- now rewrite map_app.
        -- rewrite !app_length; cbn. lia.
        -- rewrite Eqn2'. eapply seval_hasvalue'; eauto.
        -- rewrite Eqn1, Eqn1'. econstructor. eauto. 2: eapply H0.
           eapply seval_hasvalue'; eauto.
        -- rewrite Eqn2, Eqn2'. eauto.
      * repeat eapply conj.
        -- now rewrite map_app.
        -- rewrite !app_length; cbn. lia.
        -- eauto.
        -- rewrite Eqn1, Eqn1'. econstructor. eauto. 2: eapply H0.
           eapply seval_hasvalue'; eauto.
        -- rewrite Eqn2, Eqn2'. eauto.
    + psimpl.
    + destruct (seval (tau2 x (get_ans2 tqs' ans)) n') as [ [? | []] | ] eqn:E2; psimpl.
      assert ((get_qs2 (tqs' ++ [(false, q0)])) = get_qs2 tqs' ++ [q0]) as Eqn1.
      { unfold get_qs2. rewrite get_qs_app. cbn. destruct decide; try congruence. reflexivity. }
      assert ((get_qs1 (tqs' ++ [(false, q0)])) = get_qs1 tqs') as Eqn2.
      { unfold get_qs1. rewrite get_qs_app. cbn. destruct decide; try congruence. cbn. now rewrite app_nil_r. }
      assert ((get_ans2 (tqs' ++ [(false, q0)]) (ans ++ [a])) = get_ans2 tqs' ans ++ [a]) as Eqn1'.
      { unfold get_ans2. rewrite get_ans_app. 2: lia.
        cbn. now destruct decide; try congruence; cbn.
      }
      assert ((get_ans1 (tqs' ++ [(false, q0)]) (ans ++ [a])) = get_ans1 tqs' ans) as Eqn2'.
      { unfold get_ans1. rewrite get_ans_app. 2: lia.
        cbn. destruct decide; try congruence; cbn. now rewrite app_nil_r.
      }
      repeat eapply conj.
        -- now rewrite map_app.
        -- rewrite !app_length; cbn. lia.
        -- eauto.
        -- rewrite Eqn2, Eqn2'. eauto. 
        -- rewrite Eqn1, Eqn1'. econstructor. eauto. 2: eapply H0.
           eapply seval_hasvalue'; eauto.
Qed.

Lemma get_ans_map_no b tqs ans :
  get_ans b (map (pair (negb b)) tqs) ans = [].
Proof.
  induction tqs in ans |- *; cbn. 1: reflexivity.
  destruct ans; try reflexivity. cbn.
  destruct decide. { destruct b; cbn in*; congruence. }
  eauto.
Qed.

Lemma get_qs_map_no b tqs :
  get_qs b (map (pair (negb b)) tqs) = [].
Proof.
  induction tqs; cbn. 1: reflexivity.
  destruct decide. { destruct b; cbn in*; congruence. }
  eauto.
Qed.

Lemma get_qs_map_yes b tqs :
  get_qs b (map (pair (b)) tqs) = tqs.
Proof.
  induction tqs; cbn. 1: reflexivity.
  destruct decide; try congruence. cbn. f_equal. eauto.
Qed.

Lemma get_ans_map_yes b tqs ans :
  length tqs = length ans ->
  get_ans b (map (pair b) tqs) ans = ans.
Proof.
  induction tqs in ans |- *; cbn.
  all: destruct ans; cbn in *; try lia.
  1: reflexivity. intros.
  destruct decide; try congruence.
  cbn. f_equal.
  eauto.
Qed.

Lemma main :
    ∀ (x : X) (b : bool), char_rel p x b ↔ (∃ (qs : list Y) (ans : list bool) e, sinterrogation (τ x) (char_rel q) qs ans (None, 0, nil) e ∧ τ x e ans =! inr b).
Proof.
  intros. split. destruct b; cbn.
  - intros Hx.
    eapply H1 in Hx as Hx'. eapply HF1 in Hx' as (qs & ans & Hint & Hend).
    eapply seval_hasvalue in Hend as [n Hn].
    (* edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun n => seval (tau1 x ans) n = Some (inr ())). *)
    (* { intros. clear. destruct seval as [ [? | []] | ]; firstorder congruence. } *)
    (* { eauto. } *)
    (* clear n Hn. rename x0 into n. destruct H as [ [] ]. rename H into Hn. *)
    (* rename H0 into Hleast. clear H3. *)

    enough (∃ (ans0 : list bool) m (qs0 : list (bool * Y)),
               qs = get_qs1 qs0 /\
               ans = get_ans1 qs0 ans0 /\
               noqinterrogation (tau2 x) (char_rel q) (get_qs2 qs0) (get_ans2 qs0 ans0) /\
               sinterrogation (τ x) (char_rel q) (map snd qs0) ans0 (None, 0, []) (None, m, qs0)).
    { cbn in *. decompose [ex and] H. subst.
      eapply count_up_1 in Hn as lem; eauto.
      2:{ eapply sinterrogation_length in H6. rewrite map_length in H6. lia. }

      destruct lem as (tqs' & ans' & n' & Hn' & IH1 & IH2).
      eexists (_ ++ tqs').
      eexists (_ ++ ans').
      eexists (None, n', _ ++ map (pair false) tqs').
      split.
      eapply sinterrogation_app.
      eauto. eassumption.
      cbn.
      unfold get_ans1. rewrite get_ans_app.
      rewrite get_ans_map_no. rewrite app_nil_r.
      unfold get_ans1 in *.
      rewrite Hn'. psimpl.
      eapply sinterrogation_length in H6.
      rewrite map_length in H6. lia.
    } 
    clear Hn n. induction Hint.
    + exists []. exists 0. exists []. repeat econstructor. 
    + cbn in IHHint. destruct IHHint as (ans_ & m & qs_ & -> & -> & IH1 & IH2).
      eapply seval_hasvalue in H as [n Hn].
      
      eapply count_up_1 in Hn as lem; eauto.
      2:{ eapply sinterrogation_length in IH2. rewrite map_length in IH2. lia. }
      destruct lem as (tqs' & ans' & n' & Hn' & HH1 & HH2).
      rename q0 into y.

      destruct (seval (tau2 x (get_ans false qs_ ans_ ++ ans')) n') as [ [ | []] | ] eqn:E2.
      {
        destruct (q_reflect y0) as [b Hb].
        eexists (ans_ ++ ans' ++ [a;b] ).
        exists (S n').
        eexists (qs_ ++ map (pair false) tqs' ++ [(true, y); (false, y0)] ).
        cbn. repeat eapply conj.
        * unfold get_qs1. rewrite !get_qs_app.
          cbn. destruct decide; try congruence.
          now rewrite get_qs_map_no.
        * unfold get_ans1. rewrite !get_ans_app.
          2:{ rewrite map_length. eapply noqinterrogation_length; eauto. }
          2:{ eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
          cbn. destruct decide; try congruence.

          now rewrite get_ans_map_no.
        * unfold get_qs2, get_ans2.
          rewrite !get_qs_app.
          rewrite !get_ans_app.
          rewrite get_qs_map_yes, get_ans_map_yes.
          eapply noqinterrogation_app; eauto.
          eapply noqinterrogation_app; eauto.
          cbn. destruct decide; try congruence. destruct decide; try congruence. cbn.
          eapply noqinterrogate with (qs := []) (ans := []); eauto. econstructor.
          rewrite app_nil_r. eapply seval_hasvalue'; eauto.
          eapply noqinterrogation_length; eauto.
          rewrite map_length. eapply noqinterrogation_length; eauto.
          eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. 
        * rewrite !map_app. eapply sinterrogation_app.
          eauto.
          eapply sinterrogation_app.
          rewrite map_map, map_id.
          eauto.
          cbn.
          eapply sinterrogation_cons.
          rewrite app_nil_r. cbn.
          unfold get_ans1 in *. rewrite !get_ans_app.
          rewrite get_ans_map_no. rewrite app_nil_r.
          2:{  eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
          rewrite Hn'.
          unfold get_ans2. rewrite get_ans_app.
          2:{  eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
          rewrite get_ans_map_yes. 2: eapply noqinterrogation_length; eauto.
          rewrite E2. rewrite <- app_assoc. psimpl.
          eapply H0.
          eapply sinterrogation_cons.
          cbn. psimpl. eapply Hb.
          rewrite <- !app_assoc. cbn. econstructor.
      }
      {
        enough (~ p x) by tauto.
        eapply H2, HF2. repeat eexists.
        2: eapply seval_hasvalue'; eauto.
        eapply noqinterrogation_app; eauto.
      }

      eexists (ans_ ++ ans' ++ [a] ).
      exists (S n').
      eexists (qs_ ++ map (pair false) tqs' ++ [(true, y)]).
      cbn. repeat eapply conj.
      * unfold get_qs1. rewrite !get_qs_app.
        cbn. destruct decide; try congruence.
        now rewrite get_qs_map_no.
      * unfold get_ans1. rewrite !get_ans_app.
        2:{ rewrite map_length. eapply noqinterrogation_length; eauto. }
        2:{ eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
        cbn. destruct decide; try congruence.
        now rewrite get_ans_map_no.
      * unfold get_qs2, get_ans2.
        rewrite !get_qs_app.
        rewrite !get_ans_app.
        rewrite get_qs_map_yes, get_ans_map_yes.
        eapply noqinterrogation_app; eauto.
        eapply noqinterrogation_app; eauto.
        cbn. destruct decide; try congruence. econstructor.
        eapply noqinterrogation_length; eauto.
        rewrite map_length. eapply noqinterrogation_length; eauto.
        eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. 
      * rewrite !map_app. eapply sinterrogation_app.
        eauto.
        eapply sinterrogation_app.
        rewrite map_map, map_id.
        eauto.
        cbn.
        eapply sinterrogate with (qs := []) (ans := []).
        econstructor. 2: eapply H0.
        cbn.
        rewrite app_nil_r.
        unfold get_ans1 in *. rewrite !get_ans_app.
        rewrite get_ans_map_no. rewrite app_nil_r.
        2:{  eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
        rewrite Hn'.
        unfold get_ans2. rewrite get_ans_app.
        2:{  eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
        rewrite get_ans_map_yes. 2: eapply noqinterrogation_length; eauto.
        rewrite E2. rewrite <- app_assoc. psimpl.
  - intros Hx.
    eapply H2 in Hx as Hx'. eapply HF2 in Hx' as (qs & ans & Hint & Hend).
    eapply seval_hasvalue in Hend as [n Hn].

    enough (∃ (ans0 : list bool) m (qs0 : list (bool * Y)),
               qs = get_qs2 qs0 /\
               ans = get_ans2 qs0 ans0 /\
               noqinterrogation (tau1 x) (char_rel q) (get_qs1 qs0) (get_ans1 qs0 ans0) /\
               sinterrogation (τ x) (char_rel q) (map snd qs0) ans0 (None, 0, []) (None, m, qs0)).
    { cbn in *. decompose [ex and] H. subst.
      eapply count_up_2 in Hn as lem; eauto.
      2:{ eapply sinterrogation_length in H6. rewrite map_length in H6. lia. }

      destruct lem as (tqs' & ans' & n' & Hn' & IH1 & IH2).
      eexists (_ ++ tqs').
      eexists (_ ++ ans').
      eexists (None, n', _ ++ map (pair true) tqs').
      split.
      eapply sinterrogation_app.
      eauto. eassumption.
      cbn.
      unfold get_ans2. rewrite get_ans_app.
      rewrite get_ans_map_no. rewrite app_nil_r.
      unfold get_ans2 in *.
      rewrite Hn'.
      destruct (seval (tau1 x (get_ans1 (x2 ++ map (pair true) tqs') (x0 ++ ans'))) n') as [ [ | []] | ] eqn:EE; psimpl.
      2:{ eapply sinterrogation_length in H6.
          rewrite map_length in H6. lia. }
      enough (p x) by tauto.
      eapply H1, HF1. repeat eexists. 2: eapply seval_hasvalue'; eauto.
      unfold get_ans1. rewrite get_ans_app.
      2:{ eapply sinterrogation_length in H6.
          rewrite map_length in H6. lia. }
      eapply noqinterrogation_app; eauto.
      rewrite get_ans_map_yes.
      2: eapply noqinterrogation_length; eauto.
      eauto.
    }
    clear Hn n. induction Hint.
    + exists []. exists 0. exists []. repeat econstructor. 
    + cbn in IHHint. destruct IHHint as (ans_ & m & qs_ & -> & -> & IH1 & IH2).
      eapply seval_hasvalue in H as [n Hn].
      edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun n => seval (tau2 x (get_ans2 qs_ ans_)) n = Some (inl q0)).
      { intros. clear - Y_dec. destruct seval as [ [? | []] | ]; try now clear; firstorder congruence.
        destruct (Y_dec y q0); try firstorder congruence.
      }
      { eauto. }
      clear n Hn. rename x0 into n. destruct H as [ []]. rename H into Hn.
      rename H3 into Hleast. clear H4.

      eapply count_up_2 in Hn as lem; eauto.
      2:{ eapply sinterrogation_length in IH2. rewrite map_length in IH2. lia. }
      destruct lem as (tqs' & ans' & n' & Hn' & HH1 & HH2).
      rename q0 into y.

      destruct (seval (tau1 x (get_ans1 qs_ ans_ ++ ans')) n') as [ [ | []] | ] eqn:E2.
      {
        destruct (q_reflect y0) as [b Hb].
        eexists (ans_ ++ ans' ++ [b;a] ).
        exists (S n').
        eexists (qs_ ++ map (pair true) tqs' ++ [(true, y0); (false, y)] ).
        cbn. repeat eapply conj.
        * unfold get_qs2. rewrite !get_qs_app.
          cbn. destruct decide; try congruence.
          destruct decide; try congruence.
          now rewrite get_qs_map_no. 
        * unfold get_ans2. rewrite !get_ans_app.
          2:{ rewrite map_length. eapply noqinterrogation_length; eauto. }
          2:{ eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
          cbn. destruct decide; try congruence.
          destruct decide; try congruence.

          now rewrite get_ans_map_no.
        * unfold get_qs1, get_ans1.
          rewrite !get_qs_app.
          rewrite !get_ans_app.
          rewrite get_qs_map_yes, get_ans_map_yes.
          eapply noqinterrogation_app; eauto.
          eapply noqinterrogation_app; eauto.
          cbn. destruct decide; try congruence. destruct decide; try congruence. cbn.
          eapply noqinterrogate with (qs := []) (ans := []); eauto. econstructor.
          rewrite app_nil_r. eapply seval_hasvalue'; eauto.
          eapply noqinterrogation_length; eauto.
          rewrite map_length. eapply noqinterrogation_length; eauto.
          eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. 
        * rewrite !map_app. eapply sinterrogation_app.
          eauto.
          eapply sinterrogation_app.
          rewrite map_map, map_id.
          eauto.
          cbn.
          eapply sinterrogation_cons.
          rewrite app_nil_r. cbn.
          unfold get_ans1 in *. rewrite !get_ans_app.
          rewrite get_ans_map_yes. rewrite E2.
          2:{  eapply sinterrogation_length in HH1. eauto. }
          2:{  eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
          2: eapply Hb.
          unfold get_ans2. rewrite get_ans_app.
          2:{  eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
          rewrite get_ans_map_no. rewrite app_nil_r.
          unfold get_ans2 in *.
          rewrite Hn'. psimpl.
          eapply sinterrogation_cons.
          cbn. psimpl. eapply H0.
          rewrite <- !app_assoc. cbn. econstructor.
      }
      {
        enough (p x) by tauto.
        eapply H1, HF1. repeat eexists.
        2: eapply seval_hasvalue'; eauto.
        eapply noqinterrogation_app; eauto.
      }

      eexists (ans_ ++ ans' ++ [a] ).
      exists (S n').
      eexists (qs_ ++ map (pair true) tqs' ++ [(false, y)]).
      cbn. repeat eapply conj.
      * unfold get_qs2. rewrite !get_qs_app.
        cbn. destruct decide; try congruence.
        now rewrite get_qs_map_no.
      * unfold get_ans2. rewrite !get_ans_app.
        2:{ rewrite map_length. eapply noqinterrogation_length; eauto. }
        2:{ eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
        cbn. destruct decide; try congruence.
        now rewrite get_ans_map_no.
      * unfold get_qs1, get_ans1.
        rewrite !get_qs_app.
        rewrite !get_ans_app.
        rewrite get_qs_map_yes, get_ans_map_yes.
        eapply noqinterrogation_app; eauto.
        eapply noqinterrogation_app; eauto.
        cbn. destruct decide; try congruence. econstructor.
        eapply noqinterrogation_length; eauto.
        rewrite map_length. eapply noqinterrogation_length; eauto.
        eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. 
      * rewrite !map_app. eapply sinterrogation_app.
        eauto.
        eapply sinterrogation_app.
        rewrite map_map, map_id.
        eauto.
        cbn.
        eapply sinterrogate with (qs := []) (ans := []).
        econstructor. 2: eapply H0.
        cbn.
        rewrite app_nil_r.
        unfold get_ans1 in *. rewrite !get_ans_app.
        rewrite get_ans_map_yes. rewrite E2.
        unfold get_ans2. rewrite get_ans_app.
        2:{  eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
        rewrite get_ans_map_no. 
        rewrite app_nil_r. unfold get_ans2 in *. rewrite Hn'.
        rewrite <- app_assoc. cbn. psimpl.
        2:{ eapply sinterrogation_length in IH2. rewrite map_length in IH2. eauto. }
        eapply sinterrogation_length; eauto.
  - intros (qs & ans & [[o n] tqs] & Hint & Hend).
    assert (
        qs = map snd tqs /\
          noqinterrogation (tau1 x) (λ (x0 : Y) (b : bool), if b then q x0 else ¬ q x0) (get_qs1 tqs) (get_ans1 tqs ans) /\
          noqinterrogation (tau2 x) (λ (x0 : Y) (b : bool), if b then q x0 else ¬ q x0) (get_qs2 tqs) (get_ans2 tqs ans)
      ) as [-> [Hi1 Hi2]].
    { eapply back in Hint; firstorder. }

    cbn in Hend.
    destruct o.
    { psimpl. }

    destruct seval as [ [|[]] | ] eqn:E1.
    * destruct (seval (tau2 x (get_ans2 tqs ans)) n) as [ [|[]] | ] eqn:E2; try psimpl.
      eapply H2, HF2. eexists. eexists. split. eassumption. eapply seval_hasvalue'; eauto.
    * psimpl. eapply H1, HF1. repeat eexists. eauto. eapply seval_hasvalue'; eauto.
    * destruct (seval (tau2 x (get_ans2 tqs ans)) n) as [ [|[]] | ] eqn:E2; try psimpl.
      eapply H2, HF2. eexists. eexists. split. eassumption. eapply seval_hasvalue'; eauto.
Qed.

End PT.

Print Assumptions main.

Lemma needed {Part : partiality} {E Q A I O} (τ0 : I -> stree E Q A O) (f : FunRel Q A) e0 :
  ∃ τ1 : I → tree Q A O,
  ∀ (x : I) (b : O),
    (∃ (qs : list Q) (ans : list A) (e : E), sinterrogation (τ0 x) f qs ans e0 e ∧ τ0 x e ans =! inr b)
      ↔ (∃ (qs : list Q) (ans : list A), interrogation (τ1 x) f qs ans ∧ τ1 x (zip qs ans) =! inr b).
Proof.
  destruct (sinterrogation_equiv _ _ _ _ _ e0 τ0) as [τ1 H].
  destruct (einterrogation_equiv _ _ _ _ _ e0 τ1) as [τ2 HH].
  exists (λ x l, τ2 x (map snd l)).
  intros. rewrite H. rewrite HH.
  rewrite noqinterrogation_equiv. reflexivity.
Qed.

Definition OracleSemiDecidable {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :=
  exists R : Functional Y bool X unit,
    OracleComputable R /\
      forall x, p x <-> R (char_rel q) x tt.

Lemma PT {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :
  (∀ y : Y, q y ∨ ¬ q y) ->
  eq_dec Y ->
  OracleSemiDecidable q p ->
  OracleSemiDecidable q (fun x => ~ p x) ->
  red_Turing p q.
Proof.
  intros Hq HY [F1 [[tau1 HF1] % noqOracleComputable_equiv H1]] [F2 [[tau2 HF2] % noqOracleComputable_equiv H2]].
  eapply Turing_reducible_without_rel.
  enough
    (  ∃ τ : X → stree (option Y * nat * (list (bool * Y))) Y bool bool,
    ∀ (x : X) (b : bool), char_rel p x b ↔ (∃ (qs : list Y) (ans : list bool) e, sinterrogation (τ x) (char_rel q) qs ans (None, 0, nil) e ∧ τ x e ans =! inr b)).
  { destruct H as (τ & H). setoid_rewrite H. eapply needed.
  }
  eexists. eapply main.
  exact HF1. exact H1. exact HF2. exact H2.
  all: eauto.
Qed.

Lemma semi_decidable_OracleSemiDecidable {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :
  semi_decidable p -> OracleSemiDecidable q p.
Proof.
  intros (T & g & Hg) % SemiDecidabilityFacts.semi_decidable_part_iff.
  unshelve eexists.
  intros ?. eexists. shelve. split.
  eapply (computable_partial_function (fun x => bind (g x) (fun _ => ret tt))).
  Unshelve.
  2:{ intros ? * ? ?. psimpl. }
  all: cbn. intros. rewrite Hg. split.
  intros []. psimpl.
  intros. psimpl.
Qed.

Lemma OracleSemiDecidable_semi_decidable {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :
  decidable q -> OracleSemiDecidable q p -> semi_decidable p.
Proof.
  intros [f Hf] (F & Hc & HF).
  eapply SemiDecidabilityFacts.semi_decidable_part_iff.
  exists unit.
  setoid_rewrite HF.
  clear HF p.
  eapply Turing_transports_computable in Hc as [F' Hc].
  specialize (Hc (fun y => ret (f y)) (char_rel q)).
  unshelve epose proof (Hc _).
  + red. split; intros.
    * psimpl. eapply reflects_iff, Hf.
    * eapply ret_hasvalue_iff. cbn in H. eapply reflects_iff in H. specialize (Hf x).
      unfold reflects in *. destruct (f x), y; firstorder congruence.
  + clear Hc. unfold pcomputes in H.
    exists (fun x => F' (fun y : Y => ret (f y)) x).
    intros. rewrite <- H. firstorder. destruct x0; eauto.
Qed.

Lemma red_m_transports_sdec {Part : partiality} {X Y Z} (q : Y -> Prop) (p1 : Z -> Prop) (p2 : X -> Prop) :
  OracleSemiDecidable q p2 ->
  red_m p1 p2 ->
  OracleSemiDecidable q p1.
Proof.
  intros [G [HG H1]] [f Hf].
  unshelve eexists. intros R. econstructor. shelve. cbn. split.
  eapply computable_bind.
  eapply (computable_function f).
  eapply computable_precompose with (g := snd). eapply HG.
  cbn. split. Unshelve.
  - intros ? % Hf % H1. eauto.
  - red in Hf. intros. rewrite Hf, H1.
    destruct H as (? & ? & ?). subst. eauto.
  - intros ? ? ?. firstorder subst. eapply G; eauto.
Qed.

Lemma Turing_transports_sdec {Part : partiality} {X Y Z} (q1 : Y -> Prop) (q2 : Z -> Prop) (p : X -> Prop) :
  OracleSemiDecidable q1 p ->
  red_Turing q1 q2 ->
  OracleSemiDecidable q2 p.
Proof.
  intros [G [HG H1]] [F [HF H2]].
  unshelve eexists. intros R. econstructor. 
  2:{ split.
      all: cbn.
      eapply computable_comp.
      eapply HF. eapply HG. cbn.
      intros. rewrite H1.
      eapply OracleComputable_extensional in HG. eapply HG.
      eauto.
  }
  intros ? ? ? ? ?. eapply G; eauto.
Qed.
