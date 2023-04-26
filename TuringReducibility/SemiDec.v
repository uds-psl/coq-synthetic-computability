From SyntheticComputability Require Import TuringReducibility.OracleComputability.
From SyntheticComputability Require Import partial Definitions reductions Dec.
Require Import Lia List.
From stdpp Require Import list.

Definition OracleSemiDecidable_N {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :=
  exists R : Functional Y bool X unit,
    OracleComputable R /\
      forall x, p x <-> R (char_rel q) x tt.

Lemma seval_hasvalue' {partiality : partial.partiality} [A : Type] (x : part A) (a : A) n :
    seval x n = Some a -> x =! a.
Proof.
  intros. eapply seval_hasvalue. eauto.
Qed.

Section PT_N.

Context  {Part : partiality} {X : Type} {Y : Type}.
Variable  q : Y → Prop.
Variable  p : X → Prop.
Variable  F1 : Functional Y bool X ().
Variable  tau1 : X → (list bool) ↛ (Y + ()).
Variable  HF1 : ∀ (R : FunRel Y bool) (x : X) (o : ()), F1 R x o ↔ (∃ (qs : list Y) (ans : list bool), noqinterrogation (tau1 x) R qs ans ∧ tau1 x ans =! inr o).
Variable  H1 : ∀ x : X, p x ↔ F1 (char_rel q) x ().
Variable  F2 : Functional Y bool X ().
Variable  tau2 : X → (list bool) ↛ (Y + ()).
Variable  HF2 : ∀ (R : FunRel Y bool) (x : X) (o : ()), F2 R x o ↔ (∃ (qs : list Y) (ans : list bool), noqinterrogation (tau2 x) R qs ans ∧ tau2 x ans =! inr o).
Variable  H2 : ∀ x : X, ¬ p x ↔ F2 (char_rel q) x ().

Definition get_ans B (tqs : list (bool * Y)) (ans : list bool) := (map snd (filter (fun '((b, q), a) => b = B) (zip_with pair tqs ans))).
Definition get_ans1 := get_ans true.
Definition get_ans2 := get_ans false.
Definition get_qs B (tqs : list (bool * Y)) := (map snd (filter (fun '((b, q)) => b = B) tqs)).
Definition get_qs1 := get_qs true.
Definition get_qs2 := get_qs false.

Definition τ := fun x '(n, tqs) ans =>
                match seval (tau1 x (get_ans1 tqs ans)) n, seval (tau2 x (get_ans2 tqs ans)) n with
                | Some (inr o), _ => ret (inr true)
                | _ , Some (inr o) => ret (inr false)
                | Some (inl q), _ => ret (inl (S n, tqs ++ [(true,  q)], Some q))
                | _, Some (inl q) => ret (inl (S n, tqs ++ [(false, q)], Some q))
                | _, _ => ret (inl (S n, tqs, None))
                end.

Definition qs_from_tqs (tqs : list (bool * Y)) := map snd tqs.

Definition subtree (tau : list bool ↛ (Y + ())) ans l := tau (ans ++ l).
Definition subtree' {E Q A O} (tau : stree E Q A O) ans e l := tau e (ans ++ l).

Lemma count_up_1 m tqs x ans v n :
  sinterrogation (τ x) (char_rel q) (qs_from_tqs tqs) ans (0, []) (m, tqs) ->
  seval (tau1 x (get_ans1 tqs ans)) n = Some v ->
  exists tqs' ans' n',
    seval (tau1 x (get_ans1 tqs ans)) n' = Some v /\
    sinterrogation (subtree' (τ x) ans) (char_rel q) tqs' ans' (m, tqs) (n', tqs ++ map (pair false) tqs') /\
    noqinterrogation (subtree (tau2 x) (get_ans1 tqs ans)) (char_rel q) tqs' ans'.
Proof.
  intros Hint Hend.
  destruct (nat_le_dec m n).
  - admit.
  - exists [], []. 


  (* remember (0, []) as begin. *)
  (* remember (m, tqs) as theend. *)
  (* induction Hint in Heqbegin, Heqtheend, m |- *; subst. *)
  (* -  *)
Admitted.

Lemma back:
  ∀ (x : X) (qs : list Y) (ans : list bool) (n : nat) (tqs : list (bool * Y)),
    sinterrogation (τ x) (char_rel q) qs ans (0, []) (n, tqs)
    → qs = map snd tqs
      ∧ noqinterrogation (tau1 x) (λ (x0 : Y) (b : bool), if b then q x0 else ¬ q x0) (get_qs1 tqs) (get_ans1 tqs ans)
      ∧ noqinterrogation (tau2 x) (λ (x0 : Y) (b : bool), if b then q x0 else ¬ q x0) (get_qs2 tqs) (get_ans2 tqs ans).
Proof.
  intros x qs ans n tqs Hint.
  remember (0, []) as begin.
  remember (n, tqs) as theend.
  induction Hint in Heqbegin, Heqtheend, tqs, n |- *.
  - subst. inversion Heqtheend; subst. cbn. repeat eapply conj; econstructor.
  - subst. destruct e1' as (n', tqs'). edestruct IHHint as (IH1 & IH2); try reflexivity.
    cbn in H.
    destruct seval as [ [? | []] | ] eqn:E1.
    + destruct (seval (tau2 x (get_ans2 tqs' ans)) n') as [ [? | []] | ] eqn:E2; psimpl.
    + psimpl.
    + destruct (seval (tau2 x (get_ans2 tqs' ans)) n') as [ [? | []] | ] eqn:E2; psimpl.
  - subst. destruct e1' as (n', tqs'). edestruct IHHint as (-> & IH1 & IH2); try reflexivity.
    cbn in H.
    destruct seval as [ [? | []] | ] eqn:E1.
    + assert ((get_qs1 (tqs' ++ [(true, q0)])) = get_qs1 tqs' ++ [q0]) as Eqn1 by admit.
      assert ((get_qs2 (tqs' ++ [(true, q0)])) = get_qs2 tqs') as Eqn2 by admit.
      assert ((get_ans1 (tqs' ++ [(true, q0)]) (ans ++ [a])) = get_ans1 tqs' ans ++ [a]) as Eqn1' by admit.
      assert ((get_ans2 (tqs' ++ [(true, q0)]) (ans ++ [a])) = get_ans2 tqs' ans) as Eqn2' by admit.

      destruct (seval (tau2 x (get_ans2 tqs' ans)) n') as [ [? | []] | ] eqn:E2; psimpl.
      * repeat eapply conj.
        -- now rewrite map_app.
        -- rewrite Eqn1, Eqn1'. econstructor. eauto. 2: eapply H0.
           eapply seval_hasvalue'; eauto.
        -- rewrite Eqn2, Eqn2'. eauto.
      * repeat eapply conj.
        -- now rewrite map_app.
        -- rewrite Eqn1, Eqn1'. econstructor. eauto. 2: eapply H0.
           eapply seval_hasvalue'; eauto.
        -- rewrite Eqn2, Eqn2'. eauto.
    + psimpl.
    + destruct (seval (tau2 x (get_ans2 tqs' ans)) n') as [ [? | []] | ] eqn:E2; psimpl.
      assert ((get_qs2 (tqs' ++ [(false, q0)])) = get_qs2 tqs' ++ [q0]) as Eqn1 by admit.
      assert ((get_qs1 (tqs' ++ [(false, q0)])) = get_qs1 tqs') as Eqn2 by admit.
      assert ((get_ans2 (tqs' ++ [(false, q0)]) (ans ++ [a])) = get_ans2 tqs' ans ++ [a]) as Eqn1' by admit.
      assert ((get_ans1 (tqs' ++ [(false, q0)]) (ans ++ [a])) = get_ans1 tqs' ans) as Eqn2' by admit.
      repeat eapply conj.
        -- now rewrite map_app.
        -- rewrite Eqn2, Eqn2'. eauto. 
        -- rewrite Eqn1, Eqn1'. econstructor. eauto. 2: eapply H0.
           eapply seval_hasvalue'; eauto.
Admitted.

Lemma main :
    ∀ (x : X) (b : bool), char_rel p x b ↔ (∃ (qs : list Y) (ans : list bool) e, sinterrogation (τ x) (char_rel q) qs ans (0, nil) e ∧ τ x e ans =! inr b).
Proof.
  intros. split. destruct b; cbn.
  - intros Hx.
    eapply H1 in Hx as Hx'. eapply HF1 in Hx' as (qs & ans & Hint & Hend).
    eapply seval_hasvalue in Hend as [n Hn].
    edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun n => seval (tau1 x ans) n = Some (inr ())).
    { intros. clear. destruct seval as [ [? | []] | ]; firstorder congruence. }
    { eauto. }
    clear n Hn. rename x0 into n. destruct H as [ [] ]. rename H into Hn.
    rename H0 into Hleast. clear H3.

    enough (∃ (ans0 : list bool) m (qs0 : list (bool * Y)),
               let qs_ans := map (fun '((b,q), a) => (q,a)) (filter (fun '((b, q), a) => b = true) (zip_with pair qs0 ans0)) in
               let qs_ans_false := map (fun '((b,q), a) => (q,a)) (filter (fun '((b, q), a) => b = false) (zip_with pair qs0 ans0)) in
               qs = map fst qs_ans /\
               ans = map snd qs_ans /\
               noqinterrogation (tau2 x) (char_rel q) (map fst qs_ans_false) (map snd qs_ans_false) /\
               sinterrogation (τ x) (char_rel q) (map snd qs0) ans0 (0, []) (m, qs0)).
    { cbn in *. decompose [ex and] H. subst.
      rewrite map_map in Hn. erewrite map_ext in Hn.
      eapply count_up_1 in Hn as lem.
      3: now intros [[]]. 2: eauto.
      destruct lem as (tqs' & ans' & n' & Hn' & IH1 & IH2).
      eexists (_ ++ tqs').
      eexists (_ ++ ans').
      eexists (n', _ ++ map (pair false) tqs').
      split.
      eapply sinterrogation_app.
      eauto. eassumption.
      cbn.
      admit.
    } 
    clear Hleast Hn n. induction Hint.
    + exists []. exists 0. exists []. repeat econstructor. 
    + cbn in IHHint. destruct IHHint as (ans_ & m & qs_ & -> & -> & IH1 & IH2).
      eapply seval_hasvalue in H as [n Hn].
      edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun n => seval (tau1 x (map snd (map (λ '(_, q, a), (q, a)) (filter (λ '(b, _, _), b = true) (zip qs_ ans_))))) n = Some (inl q0)).
      { intros. clear. admit. }
      { eauto. }
      clear n Hn. rename x0 into n. destruct H as [ []]. rename H into Hn.
      rename H3 into Hleast. clear H4.

      rewrite map_map in Hn. erewrite map_ext in Hn.
      eapply count_up_1 in Hn as lem. 3: now intros [[]].
      2: eauto.
      destruct lem as (tqs' & ans' & n' & Hn' & HH1 & HH2).
      rename q0 into y.
      eexists (ans_ ++ ans' ++ [a] ).
      exists n'.
      eexists (qs_ ++ map (pair false) tqs' ++ [(true, y)]).
      cbn. repeat eapply conj.
      * admit.
      * admit.
      * admit.
      * rewrite !map_app. eapply sinterrogation_app.
        eauto.
        eapply sinterrogation_app.
        rewrite map_map, map_id.
        eauto.
        cbn.
        eapply sinterrogate with (qs := []) (ans := []).
        econstructor. 2: eapply H0.
        cbn.
        rewrite app_nil_r. admit.
  - admit.
  - intros (qs & ans & [n tqs] & Hint & Hend).
    assert (
        qs = map snd tqs /\
          noqinterrogation (tau1 x) (λ (x0 : Y) (b : bool), if b then q x0 else ¬ q x0) (get_qs1 tqs) (get_ans1 tqs ans) /\
          noqinterrogation (tau2 x) (λ (x0 : Y) (b : bool), if b then q x0 else ¬ q x0) (get_qs2 tqs) (get_ans2 tqs ans)
      ) as [-> [Hi1 Hi2]].
    { eapply back; eauto. }
 
    cbn in Hend.

    destruct seval as [ [|[]] | ] eqn:E1.
    * destruct (seval (tau2 x (get_ans2 tqs ans)) n) as [ [|[]] | ] eqn:E2; try psimpl.
      eapply H2, HF2. eexists. eexists. split. eassumption. eapply seval_hasvalue'; eauto.
    * psimpl. eapply H1, HF1. repeat eexists. eauto. eapply seval_hasvalue'; eauto.
    * destruct (seval (tau2 x (get_ans2 tqs ans)) n) as [ [|[]] | ] eqn:E2; try psimpl.
      eapply H2, HF2. eexists. eexists. split. eassumption. eapply seval_hasvalue'; eauto.
Admitted.

End PT_N.

Lemma PT_N {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :
  OracleSemiDecidable_N q p ->
  OracleSemiDecidable_N q (fun x => ~ p x) ->
  red_Turing p q.
Proof.
  intros [F1 [[tau1 HF1] % noqOracleComputable_equiv H1]] [F2 [[tau2 HF2] % noqOracleComputable_equiv H2]].
  eapply Turing_reducible_without_rel.
  enough
    (  ∃ τ : X → stree (nat * (list (bool * Y))) Y bool bool,
    ∀ (x : X) (b : bool), char_rel p x b ↔ (∃ (qs : list Y) (ans : list bool) e, sinterrogation (τ x) (char_rel q) qs ans (0, nil) e ∧ τ x e ans =! inr b)) by admit.
  eexists. eapply main.
  exact HF1. exact H1. exact HF2. exact H2.
Admitted.

Definition OracleSemiDecidable {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :=
  exists R : Functional Y bool (X * nat) bool,
    OracleComputable R /\
      (forall x n, exists b, R (char_rel q) (x, n) b) /\
      forall x, p x <-> exists n, R (char_rel q) (x, n) true.

Lemma computable_function {Part : partiality} {Q A I O} f :
  @OracleComputable _ Q A I O (fun R i o => f i = o).
Proof.
  exists (fun i _ => ret (inr (f i))). intros.
  split.
  - intros ->. exists nil, nil. split. econstructor. psimpl.
  - intros (qs & ans & H1 & H2). psimpl.
Qed.

Lemma OracleSemiDecidable_comp {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :
  decidable q ->
  OracleSemiDecidable q p <->
  semi_decidable p.
Proof.
  intros [f Hf]. split.
  - intros (F & Hc & Htot & HF).
    unfold semi_decidable, semi_decider.
    setoid_rewrite HF.
    clear HF p.
    eapply Turing_transports_computable in Hc as [F' Hc].
    specialize (Hc (fun y => ret (f y)) (char_rel q)).
    unshelve epose proof (Hc _).
    + red. split; intros.
      * psimpl. eapply reflects_iff, Hf.
      * eapply ret_hasvalue_iff. cbn in H. eapply reflects_iff in H. specialize (Hf x).
        unfold reflects in *. destruct (f x), y; firstorder congruence.
    + clear Hc. unfold pcomputes in H. setoid_rewrite <- H in Htot.
      unshelve epose proof (partial_total (X * nat) bool (fun '(x, n) => F' (fun y : Y => ret (f y)) (x, n)) _) as [g Hg].
      { intros [x n]; destruct (Htot x n) as [b Hb]. exists b. eauto. }
      exists (fun x n => g (x, n)). intros x.
      split.
      * intros [n Hn]. specialize (Hg (x, n)). cbn in *.
        eapply H in Hn. exists n. eapply hasvalue_det; eauto.
      * intros [n Hn]. specialize (Hg (x, n)). cbn in *.
        eapply H in Hg. exists n. rewrite Hn in Hg. eauto.
  - intros [g Hg].
    unshelve eexists.
    intros ?. eexists. shelve. split.
    eapply (computable_function (fun '(x, n) => g x n)).
    Unshelve.
    2: abstract (intros []; congruence).
    all: cbn. split; eauto.
Qed.

Lemma red_m_transports_sdec {Part : partiality} {X Y Z} (q : Y -> Prop) (p1 : Z -> Prop) (p2 : X -> Prop) :
  OracleSemiDecidable q p2 ->
  red_m p1 p2 ->
  OracleSemiDecidable q p1.
Proof.
  intros [G [HG [Htot H1]]] [f Hf].
  unshelve eexists. intros R. econstructor. shelve. split.
  eapply computable_bind.
  eapply (computable_function (fun '(z,n) => f z)).
  eapply computable_precompose with (g := fun '((z,n), b) => (b, n)). eapply HG.
  cbn. split. Unshelve.
  - intros z n. destruct (Htot (f z) n) as [b Hb]. eauto.
  - red in Hf. intros. rewrite Hf, H1.
    split.
    firstorder congruence.
    firstorder subst. eauto.
  - intros [] ? ?. firstorder subst. eapply G; eauto.
Qed.

Lemma Turing_transports_sdec {Part : partiality} {X Y Z} (q1 : Y -> Prop) (q2 : Z -> Prop) (p : X -> Prop) :
  OracleSemiDecidable q1 p ->
  red_Turing q1 q2 ->
  OracleSemiDecidable q2 p.
Proof.
  intros [G [HG [Htot H1]]] [F [HF H2]].
  unshelve eexists. intros R. econstructor. shelve. split.
  all: cbn.
  eapply computable_comp.
  eapply HF. eapply HG. cbn. split.
  - intros. destruct (Htot x n) as [b Hb]. exists b.
    eapply OracleComputable_extensional in HG. eapply HG. exact Hb.
    firstorder.
  - intros. rewrite H1. split;
      (intros [n Hn]; exists n; eapply OracleComputable_extensional in HG; [ eapply HG | ]).
    exact Hn. firstorder. exact Hn. firstorder.
    Unshelve. eapply G.
Qed.

Lemma PT {Part : partiality} {X Y} (q : Y -> Prop) (p : X -> Prop) :
  OracleSemiDecidable q p ->
  OracleSemiDecidable q (fun x => ~ p x) ->
  red_Turing p q.
Proof.
  intros [F1 [HF1 H1]] [F2 [HF2 H2]].
  unshelve eexists. intros R. econstructor. shelve. split.
  eapply computable_bind. 
  eapply computable_comp.
  Unshelve. 11: intros; econstructor. all: shelve_unifiable.
  2: eapply computable_search. cbn.
  eapply computable_bind. 
  eapply HF1.
  eapply computable_if. all:cbn.
  eapply computable_ret with (v := true). all: cbn.
  eapply computable_bind. all: cbn.
  eapply computable_precompose.
  eapply HF2.
  eapply computable_precompose.
  eapply computable_ident. all: cbn.
  eapply computable_bind. all: cbn.
  exact HF1.
  eapply computable_if. all: cbn.
  eapply computable_ret with (v := true).
  eapply computable_bind.
  eapply computable_precompose.
  eapply HF2.
  eapply computable_if.
  eapply computable_ret with (v := false).
  eapply computable_ret with (v := true).
  cbn. intros.
  Unshelve.
  6:{ intros [ [ []]]. exact b0. }
  8:{ intros [ [ []]]. exact b0. }
  4-7: clear; tauto.
  all: cbn. 
  - split. destruct b; intros H.
    + eapply H1 in H as [n Hn].
      edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun m => m <= n /\ (F1 (char_rel q) (x, m) true \/ F1 (char_rel q) (x, m) false /\ F2 (char_rel q) (x, m) true)) as (m & [[Hle Hm1] Hm2] & HHH).
      * intros n0. assert (n0 <= n \/ n0 > n) as [|] by lia.
        -- destruct H1 as [H1 ?]. destruct (H1 x n0) as [[] Hb].
           eauto.
           destruct H2 as [H2 ?]. destruct (H2 x n0) as [[] Hb'].
           eauto.
           right. intros [? [|]]. enough (false = true) by congruence. eapply F1; eauto.
           enough (false = true) by congruence. eapply F2. eauto. eapply H5.
        -- right. intros []. lia.
      * eauto.
      * exists m. repeat split.
        -- destruct Hm1. exists true. split; eauto.
           exists false; eauto. firstorder.
        -- intros. destruct H1 as [H1 ?]. destruct (H1 x m0) as [b Hb].
           exists b. split; eauto. destruct b.
           ++ unshelve epose proof (Hm2 m0 _). split. lia.
              eauto. lia.
           ++ destruct H2 as [H2 ?]. destruct (H2 x m0) as [b Hb'].
              exists b. split. eauto. destruct b; try reflexivity.
              unshelve epose proof (Hm2 m0 _). split. lia.
              eauto. lia.
        -- destruct Hm1. exists true. split; eauto.
           exfalso. enough (p x /\ ~ p x) by tauto.
           split. eapply H1. eauto. eapply H2. destruct H. eauto.
    + eapply H2 in H as [n Hn].
      edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun m => m <= n /\ (F1 (char_rel q) (x, m) true \/ F1 (char_rel q) (x, m) false /\ F2 (char_rel q) (x, m) true)) as (m & [[Hle Hm1] Hm2] & HHH).
      * intros n0. assert (n0 <= n \/ n0 > n) as [|] by lia.
        -- destruct H1 as [H1 ?]. destruct (H1 x n0) as [[] Hb].
           eauto.
           destruct H2 as [H2 ?]. destruct (H2 x n0) as [[] Hb'].
           eauto.
           right. intros [? [|]]. enough (false = true) by congruence. eapply F1; eauto.
           enough (false = true) by congruence. eapply F2. eauto. eapply H5.
        -- right. intros []. lia.
      * exists n. split; eauto.
        destruct H1 as [H1]. destruct (H1 x n) as [[]]; eauto.
      * exists m. repeat split.
        -- destruct Hm1. exists true. split; eauto.
           exists false; eauto. firstorder.
        -- intros. destruct H1 as [H1 ?]. destruct (H1 x m0) as [b Hb].
           exists b. split; eauto. destruct b.
           ++ unshelve epose proof (Hm2 m0 _). split. lia.
              eauto. lia.
           ++ destruct H2 as [H2 ?]. destruct (H2 x m0) as [b Hb'].
              exists b. split. eauto. destruct b; try reflexivity.
              unshelve epose proof (Hm2 m0 _). split. lia.
              eauto. lia.
        -- destruct Hm1. enough (p x /\ ~ p x) by tauto.
           split. eapply H1. eauto. eapply H2. eauto.
           exists false. split; eauto. eapply H.
           cbn
    + intros ?. decompose [ex and] H.
      exists true. split; eauto.
    + intros ?. decompose [ex and] H.
      destruct x2; cbn in *; subst.
      eapply H1. eauto.
      decompose [ex and] H7.
      destruct x2; cbn in *; subst.
      eapply H2 ; eauto.
      destruct x1. enough (false = true) by congruence. eapply F1; eauto.
      decompose [ex and] H6; subst.
      enough (false = true) by congruence. eapply F2; eauto.
  - intros ? * ? ?.
    Ltac help := repeat match goal with
    | H : ex _ |- _ => decompose [ex and] H; subst; clear H
    end.
    help.
    destruct x2, x5; cbn in *; subst; try congruence.
    + help.
      destruct x2; cbn in *; subst; try congruence.
      destruct x4; cbn in *; subst; try congruence.
      eapply F1; eauto.
      help. 
      enough (x0 = x3) as ->. eapply F1; eauto.
      assert (x0 < x3 \/ x0 = x3 \/ x3 < x0) as [  | [] ] by lia; try tauto.
      * eapply H10 in H. help.
        destruct x2; cbn in *; try congruence.
        help. enough (true = false) by congruence.
        eapply F1. exact H5. eauto.
      * eapply H6 in H. help.
        destruct x2; cbn in *; try congruence.
        help. enough (true = false) by congruence.
        eapply F2. exact H4. eauto.
    + help. destruct x2; cbn in *; subst; try congruence.
      destruct x4; cbn in *; subst; try congruence.
      2: eapply F1; eauto.
      help.
      destruct x1; cbn in *; subst; try congruence.
      eapply F1. exact H3. eauto. help.
      enough (x0 = x3) as ->. eapply F1; eauto.
      assert (x0 < x3 \/ x0 = x3 \/ x3 < x0) as [  | [] ] by lia; try tauto.
      * eapply H10 in H. help.
        destruct x1; cbn in *; try congruence.
        help. enough (true = false) by congruence.
        eapply F2. exact H4. eauto.
      * eapply H6 in H. help.
        destruct x1; cbn in *; try congruence.
        help. enough (true = false) by congruence.
        eapply F1. exact H9. eauto.
    + help. destruct x2; cbn in *; subst; try congruence.
      destruct x5; cbn in *; subst; try congruence.
      destruct x4; cbn in *; subst; try congruence.
      eapply F1; eauto.
      help.
      destruct x1; cbn in *; subst; try congruence.
      eapply F1. exact H5. eauto. help.
      eapply F2; eauto.
      destruct x5; cbn in *; subst; try congruence.
      destruct x4; cbn in *; subst; try congruence.
      eapply F1; eauto. help.
      destruct x1; cbn in *; subst; try congruence.
      eapply F1. 2: exact H5. eauto. help.
      eapply F2. exact H8. eauto.
  - intros ? * ? ?. decompose [ex and] H. decompose [ex and] H0.
    destruct x; cbn in *. destruct x0, x1; subst; try reflexivity.
    * enough (true = false) by congruence. eapply F1; eauto.
    * enough (true = false) by congruence. eapply F1; eauto.
    * decompose [ex and] H5; subst. decompose [ex and] H7; subst.
      eapply F2; eauto.
Qed.

Context {Part : partiality}.

Definition OracleComputableT {Q A I O} (r : FunRel Q A -> I -> O -> Prop) :=
  { τ : I -> tree Q A O | forall R x o, r R x o <-> exists qs ans, interrogation (τ x) R qs ans /\ τ x (base.zip_with pair qs ans) =! (inr o)}.

Axiom Ξ : nat -> {F : FunRel nat bool -> FunRel (nat * nat) bool & OracleComputableT F }.
Axiom Ξ_surj : forall F, exists n, Ξ n = F.

Definition jumpat R n m := (projT1 (Ξ n) R (n, m) true) /\
               forall m', m' < m -> projT1 (Ξ n) R (n, m') false.

Definition jump p := fun n => exists m, jumpat (char_rel p) n m.

Instance dec_le n m : dec (n <= m).
Admitted.

Lemma computable_nothing {P} {Q A I O} :
  @OracleComputable P Q A I O (fun R i o => False).
Proof.
  exists (fun _ _ => undef). intros R.
  firstorder. psimpl.
Qed.

Lemma jump_sdec p :
  (forall n, jump p n \/ ~ jump p n) ->
  OracleSemiDecidable p (jump p).
Proof.
  unshelve eexists. intros R. unshelve eexists. 3: split.
  - intros (n, index) res. apply (if res then jumpat R n index else (exists m, m < index /\ jumpat R n m) \/ forall m, m <= index -> projT1 (Ξ n) R (n, m) false).
  - cbn. intros [] ? ?.
    destruct y1, y2; try firstorder congruence.
    intros. destruct H1.
    decompose [ex and] H1.
    eapply (projT1 (Ξ n)). eapply H4. eapply H0. lia.
    eapply (projT1 (Ξ n)). eapply H0. eapply H1. lia.
    intros. destruct H0. decompose [ex and] H0.
    symmetry.
    eapply (projT1 (Ξ n)). eapply H4. eapply H1. lia.
    eapply (projT1 (Ξ n)). 2: eapply H1. eapply H0. lia.
  - cbn.
    eapply OracleComputable_ext.
    eapply computable_bind.
    eapply computable_comp.
    2: eapply computable_search.
    Unshelve. 5: intros R; econstructor.
    all: shelve_unifiable.
    unshelve eapply computable_if.
    { intros [[n1 n2] n3]. destruct (Dec (n3 > n2)). exact true. exact false. } all:cbn.
    all: shelve_unifiable.
    unshelve eapply computable_function.
    { intros. exact true. }
    2: unshelve eapply computable_if.
    2:{ intros [[n1 n2] n3]. destruct (Dec (n3 < n2)). exact true. exact false. }
    all: shelve_unifiable.
    2:{ unshelve eapply computable_function. intros. exact false. }
    2: unshelve eapply computable_if.
    2:{ intros [[n1 n2] n3]. destruct (Dec (n2 = n3)). exact true. exact false. }
    all: shelve_unifiable.
    2:{ unshelve eapply computable_function. intros. exact true. }
    2:{ unshelve eapply computable_function. intros. exact false. }

    2: cbn.
    Unshelve.
    4:{ intros R. intros [[n index] m] b. exact (projT1 (Ξ n) R (n, m) b). }
    3:{ cbn. intros [[]] ? ? ? ?. destruct Dec; try congruence.
        eapply (projT1 (Ξ n)); eauto. }

    unshelve econstructor.
    intros [[x m] n]. destruct (projT2 (Ξ x)) as [τ Ht].
    apply (τ (x, n)). cbn. intros.
    destruct x as [[x m] n]. destruct (Ξ x) as [F [τ HF]] eqn:E; cbn.
    now rewrite <- HF.
    cbn. intros R [n index] o. split.
    + intros H0. decompose [ex and] H0; clear H0.
      destruct Dec; subst.
      * intros.
        destruct Dec; subst.
        right. intros. specialize (H4 m ltac:(lia)).
        destruct Dec; subst; eauto.
        left. exists x. split. lia. split. eauto.
        intros. eapply H4 in H0. destruct Dec; try lia. eauto.
      * destruct Dec; subst.
        destruct Dec; try lia.
        firstorder.
        specialize (H4 m' ltac:(lia)).
        destruct Dec; subst; eauto.
        destruct Dec; try lia.
        right. intros.  specialize (H4 m ltac:(lia)).
        destruct Dec; try lia. eauto.
    + intros. destruct o; cbn.
      * exists index. firstorder. destruct Dec; try lia.
        eauto.
        destruct Dec; try lia. eapply H1. lia.
        destruct Dec; try lia. destruct Dec; try lia. 
      * destruct H0.
        -- decompose [ex and] H0.
           exists x. split. destruct Dec; try lia. split.
           firstorder. intros. destruct Dec; try lia.
           eapply H3; lia.
           destruct Dec; try lia.
        -- exists (S index). destruct Dec; try lia. 
           split. split. all: try reflexivity.
           intros. destruct Dec; try lia. 
           eapply H0. lia.
           destruct Dec; try lia.
           destruct Dec; try lia. 
  - cbn. split. 2: firstorder.
    intros x n. destruct (H x).
    + destruct H0 as [m [Hm1 Hm2]].
      assert (n < m \/ n >= m) as [Hn | Hn] by lia.
      * exists false. intros. right. intros. eapply Hm2. lia.
      * assert (n = m \/ n > m) as [-> | ] by lia.
        -- exists true. firstorder.
        -- exists false. left. exists m. split. lia.
           firstorder.
    + exists false. right. intros.
      assert (forall P, ~~ P -> P) as dne by admit.
      eapply dne.
      admit.
      (*  unfold jump, jumpat in *. eapply reflects_false. *)
      (* intros ?. eapply H0. exists n; eauto. *)
Admitted.

Lemma jump_neg_sdec p :
  ~ OracleSemiDecidable p (fun x => ~ jump p x).
Proof.
  intros [F [Hc [Htot HF]]].
  (* destruct (Ξ_surj (existT F Hc)) as [c Hcode]. *)
  (* specialize (HF c). *)
  (* enough ((exists n : nat, F (char_rel p) (c, n) true) <-> jump p c) by tauto. clear HF. *)
  (* split. *)
  (* - intros [n Hn]. unfold jump, jumpat. *)
  (*   rewrite Hcode. cbn. admit. *)
  (* - firstorder. rewrite Hcode in *. exists x. eapply H. *)
  (*   lia. *)
Admitted.
 
