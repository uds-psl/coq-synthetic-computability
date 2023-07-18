From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.SemiDecidabilityFacts reductions partial embed_nat Dec.
Require Import Setoid Program Lia.

From SyntheticComputability.Axioms Require Export CT SCT EA EPF.

Tactic Notation "intros" "⟨" ident(x) "," ident(n) "⟩" :=
let xn := fresh "xn" in
intros xn; destruct (unembed xn) as [x n]; try setoid_rewrite (@embedP (x,n)).

Lemma CT_SMN_to_SCT :
  (∑ ϕ, CT_for ϕ /\ SMN_for ϕ) ->
  SCT.
Proof.
  intros (ϕ & H).
  exists ϕ.
  destruct H as ([Hϕ CT] & [S SMN]).
  split.
  - eapply Hϕ.
  - intros f.
    destruct (CT (fun! ⟨x,y⟩ => f x y)) as [c0 Hc0].
    exists (S c0). intros.
    eapply SMN. edestruct (Hc0 ⟨x,y⟩). rewrite embedP in H.
    eauto.
Qed.

Lemma SCT_to_CT :
  SCT ->
  ∑ ϕ, CT_for ϕ.
Proof.
  intros (ϕ & Hϕ & SCT).
  exists ϕ. repeat eapply conj.
  - eapply Hϕ.
  - intros f. specialize (SCT (fun _ => f)) as [γ H].
    exists (γ 0). intros. eapply H.
Qed.

Definition e `{partiality} (ϕ : nat -> nat -> nat -> option nat) :=
  (fun c x => mkpart (fun! ⟨n,m⟩ =>
                     if ϕ c ⟨ x, n ⟩ m is Some (S x) then Some x else None)).

Lemma SCT_to_EPF {Part : partiality} :
  SCT -> EPF.
Proof.
  intros (ϕ & Hϕ & SCT).
  exists (e ϕ). intros f. 
  destruct (SCT (fun x => proj1_sig (partial_to_total (f x)))) as [γ H].
  exists γ. intros x y v.
  transitivity (exists n m, ϕ (γ x) ⟨ y, n ⟩ m = Some (S v)). {
    unfold e.
    rewrite mkpart_hasvalue.
    split.
    - intros [n Hn]. destruct (unembed n) as [n' m] eqn:E.
      exists n', m.
      destruct ϕ as [ [] | ]; try congruence.
    - intros [n [m HT]]. exists ⟨ n, m ⟩. now rewrite embedP, HT.
    - intros n1' n2' x1 x2 H1 H2.
      destruct (unembed n1') as [n1 m1], (unembed n2') as [n2 m2].
      destruct (H x ⟨y,n1⟩) as [m3 H3], (H x ⟨y,n2⟩) as [m4 H4].
      destruct (ϕ (γ x) ⟨ y, n1 ⟩ m1) eqn:E1; try congruence.
      destruct (ϕ (γ x) ⟨ y, n2 ⟩ m2) eqn:E2; try congruence.
      eapply monotonic_agnostic in E1; eauto. eapply E1 in H3. subst n.
      eapply monotonic_agnostic in E2; eauto. eapply E2 in H4. subst n0.
      destruct (proj1_sig (partial_to_total (f x)) ⟨ y, n1 ⟩) eqn:E1'; try congruence.
      destruct (proj1_sig (partial_to_total (f x)) ⟨ y, n2 ⟩) eqn:E2'; try congruence.
      inv H1. inv H2.
      assert (f x y =! x1) by (eapply (proj2_sig (partial_to_total (f x))); eauto).
      assert (f x y =! x2) by (eapply (proj2_sig (partial_to_total (f x))); eauto).
      eapply hasvalue_det; eauto.
  }
  
  pose proof (proj2_sig (partial_to_total (f x))) as Eq. cbn in Eq.
  rewrite Eq.

  split.
  - intros [n [m HT]].
    destruct (H x ⟨ y, n ⟩).
    eapply monotonic_agnostic in HT; eauto. eapply HT in H0. eauto.
  - intros [n Hn].
    destruct (H x ⟨ y, n ⟩).
    rewrite Hn in H0. eauto.
Qed.

Lemma EPF_to_SCT {Part : partiality} :
  EPF -> SCT.
Proof.
  intros (θ & EPF).
  exists (fun c x n => seval (θ c x) n). split.
  - intros. eapply seval_mono.
  - intros f.
    specialize (EPF (fun x y => ret (f x y))) as [γ H].
    exists γ. intros x y. specialize (H x y).
    eapply seval_hasvalue, H, ret_hasvalue.
Qed.

Lemma EPF_to_CT_SMN {Part : partiality} :
  EPF -> ∑ ϕ, CT_for ϕ /\ SMN_for ϕ.
Proof.
  intros (θ & EPF).
  exists (fun c x n => seval (θ c x) n). split. split.
  - intros. eapply seval_mono.
  - intros f.
    specialize (EPF (fun x y => ret (f y))) as [γ H].
    exists (γ 0). intros y. specialize (H 0 y).
    eapply seval_hasvalue, H, ret_hasvalue.
  - specialize (EPF (fun! ⟨c,x⟩ => fun y => θ c ⟨x,y⟩)) as [γ H].
    eexists (fun c x => γ ⟨c,x⟩).
    intros c x y v. rewrite <- !seval_hasvalue.
    specialize (H ⟨c,x⟩ y). cbn in H. 
    rewrite embedP in H. symmetry. eapply H.
Qed.


Definition ψ (ϕ : nat -> nat -> nat -> option nat) c := fun! ⟨ n, m ⟩ => match ϕ c n m with Some (S x) => Some x | _ => None end.

Lemma SCTS_to_EAS :
  SCT -> EA.
Proof.
  intros (ϕ & Hϕ & SCT). eapply EA_iff_enumerable.
  unshelve eexists (ψ ϕ). 
  intros p [f Hf]. unfold ψ. cbn.
  specialize (SCT (fun x n => if f n is Some (x',y) then if Nat.eqb x' x then S y else 0 else 0)) as [c Hc].
  exists c. intros x y. split.
  + intros H. eapply (Hf (x,y)) in H as [n H].
    destruct (Hc x n) as [m Hm].
    exists ⟨n,m⟩. now rewrite embedP, Hm, H, PeanoNat.Nat.eqb_refl.
  + intros [nm H]. destruct (unembed nm) as [n m].
    destruct ϕ eqn:E; try congruence.
    destruct n0; inv H.
    specialize (Hc x n) as [m' H'].
    unshelve epose proof (monotonic_agnostic _ E H'). eauto.
    destruct (f n) as [[x' y']| ] eqn:E'; try congruence.
    destruct (PeanoNat.Nat.eqb_spec x' x); inv H.
    eapply (Hf (x,y')). eauto.
Qed.

Require Import SyntheticComputability.Synthetic.ReducibilityFacts.

Fixpoint mk_mono {X} (f : nat -> option X) (n : nat) : option X :=
  match n with
  | 0 => None
  | S n => if mk_mono f n is Some x then Some x else f n
  end.

Lemma monotonic_mk_mono {X} (f : nat -> option X) :
  monotonic (mk_mono f).
Proof.
  intros n1 v H1 n2 H2.
  induction H2; cbn; eauto.
  now rewrite IHle.
Qed.

Lemma mk_mono_spec {X} (f : nat -> option X) n x :
  mk_mono f n = Some x <-> exists m, m < n /\ f m = Some x /\ forall m', f m' <> None -> m <= m'.
Proof.
  revert x. pattern n. eapply Wf_nat.lt_wf_ind.
  clear. intros n IH x. destruct n; cbn.
  - clear IH. split.
    + firstorder. exists 0. firstorder congruence.
    + intros (m & H1 & H2 & H3). assert (m = 0) as -> by lia. lia.
  - destruct mk_mono eqn:E.
    + eapply IH in E as (m & H1 & H2 & H3); try lia.
      split.
      * intros [= ->]. exists m. split. lia. eauto.
      * intros (m' & H1' & H2' & H3').
        enough (m = m') by congruence.
        enough (m <= m' /\ m' <= m) by lia.
        split; [ eapply H3 | eapply H3']; congruence.
    + split.
      * intros H. exists n. repeat split; eauto.
        intros. enough (~ m' < n) by lia. intros ?.
        assert (exists m', f m' <> None). { eauto. }
        eapply mu_nat_dep_least in H2 as (l & _ & H4 & H5). 2: { intros k; destruct (f k); firstorder congruence. }
        destruct (f l) as [x' | ] eqn:E'; try congruence.
        enough (None = Some x') by congruence. rewrite <- E.
        eapply IH. lia. exists l. repeat eapply conj.
        -- enough (l <= m') by lia. eapply H5. lia. eauto.
        -- eauto.
        -- intros. eapply H5. lia. eauto.
      * intros (m & H1 & H2 & H3).
        assert (m = n \/ m < n) as [-> | ] by lia; eauto.
        enough (None = Some x) by congruence.
        rewrite <- E. eapply IH. lia.
        exists m. split. lia. eauto.
Qed.

Lemma EA_to_SCT :
  EA -> SCT.
Proof.
  intros [e EA] % EA_iff_enumerable.
  exists (fun c x => mk_mono (fun n => if e c n is Some xy then (fun! ⟨x',y⟩ => if Nat.eqb x x' then Some y else None) xy else None)).
  split. 1: intros; eapply monotonic_mk_mono.
  intros f.
  destruct (EA (fun x => fun! ⟨n, m⟩ => f x n = m)) as [c Hc].
  { eapply enumerable_red. 4:eapply enumerable_graph with (f := (fun '(x,n) => f x n)).
    - exists (fun '(x,nm) => (fun! ⟨n,m⟩ => ((x,n),m)) nm).
      intros [x nm]. cbn. 
      destruct (unembed nm) as [n m].
      split.
      + intros H. exists (x,n). f_equal. symmetry. exact H.
      + now intros [[] [= -> -> ->]].
    - eauto.
    - eapply discrete_iff. eauto.
    - eauto.
  }
  exists c. intros x y.
  pose proof (Hc x ⟨y,f x y⟩) as Hc'. cbn in Hc'. rewrite embedP in Hc'.
  destruct Hc' as [H _]. specialize (H eq_refl).
  eapply mu_nat_dep_least in H as (n & _ & H & Hl).
  2:{ intros n. clear. destruct (e (c x) n); try firstorder congruence.
      destruct (Dec.nat_eq_dec n0 ⟨y,f x y⟩); firstorder congruence. }

  exists (S n). eapply mk_mono_spec. exists n. repeat eapply conj.
  + lia.
  + now rewrite H, embedP, PeanoNat.Nat.eqb_refl.
  + intros. specialize (Hl m' ltac:(lia)). destruct (e (c x) m') as [x'y | ] eqn:E; try congruence.
    destruct (unembed x'y) as [x' y'] eqn:E'.
    eapply (f_equal embed) in E'. rewrite unembedP in E'. subst.
    assert (f x x' = y'). {
      specialize (Hc x ⟨x', y'⟩). cbn in Hc. rewrite embedP in Hc. eapply Hc.
      eauto.
    } 
    destruct (PeanoNat.Nat.eqb_spec y x'); try congruence.
    subst. eauto.
Qed.


Module R_spec.

Require Import List.
Import ListNotations.
Import implementation.
Local Existing Instance monotonic_functions.

Definition I (f : nat -> nat) (n : nat) : bool :=
  nth n (flat_map (fun n => List.repeat false n ++ [true]) (map f (seq 0 (1 + n)))) false.

Fixpoint R (f : nat -> part bool) (x : nat) : part nat :=
  match x with
  | 0 => mu f
  | S x => bind (mu f) (fun n => R (fun m => f (m + S n)) x)
  end.

Lemma R_spec0 :
  forall (g : nat ↛ bool) (f : nat -> nat),
    (forall x : nat, g x =! I f x) -> hasvalue (mu g) (f 0).
Proof.
  intros g f H.
  eapply mu_hasvalue_imp. split.
  - enough (I f (f 0) = true) as <- by eapply H.
    unfold I.
    rewrite seq_app, map_app. cbn.
    rewrite app_nth1. 2: rewrite app_length, repeat_length; cbn; lia.
    rewrite app_nth2. 2: rewrite repeat_length; cbn; lia.
    now rewrite repeat_length, PeanoNat.Nat.sub_diag.
  - intros.
    enough (I f m = false) as <- by eapply H.
    unfold I.
    rewrite seq_app, map_app. cbn.
    rewrite app_nth1. 2: rewrite app_length, repeat_length; cbn; lia.
    rewrite app_nth1. 2: rewrite repeat_length; cbn; lia.
    destruct nth eqn:E; try reflexivity.
    enough (In true (repeat false (f 0))) by (eapply repeat_spec; eassumption).
    rewrite <- E. eapply nth_In. rewrite repeat_length. lia.
Qed.

Lemma flat_map_length_ge {X Y} (f : X -> list Y) l n :
  length l >= n ->
  (forall x, length (f x) > 0) ->
  length (flat_map f l) >= n.
Proof.
  intros Hl Hf. induction l in n, Hl |- *; cbn in *.
  - lia.
  - rewrite app_length. 
    destruct n; try lia.
    specialize (IHl n ltac:(lia)).
    specialize (Hf a). lia.
Qed.

Lemma R_spec g f :
  (forall x, g x =! I f x) ->
  forall x, R g x =! f x.
Proof.
  intros H x. revert g f H.
  induction x; intros; cbn.
  - now eapply R_spec0.
  - eapply bind_hasvalue_imp. exists (f 0).
    split. now eapply R_spec0.
    eapply (IHx (fun m : nat => g (m + S (f 0))) (fun y => f (S y))).
    clear - H. intros x.
    specialize (H (x + S (f 0))).
    enough (I (fun y => f (S y)) x = I f (x + S (f 0))) as -> by eassumption. clear H.
    unfold I.
    rewrite <- map_map, seq_shift. cbn.
    symmetry.
    rewrite app_nth2. all: rewrite app_length, repeat_length. 2: cbn; lia.
    cbn.
    replace (x + S (f 0) - (f 0 + 1)) with x by lia.
    replace (x + S (f 0)) with (S (x + f 0)) by lia.
    cbn. rewrite seq_app, map_app, flat_map_app.
    rewrite app_assoc, app_nth1. reflexivity.
    rewrite !app_length, repeat_length; cbn.
    enough (length (flat_map (fun n : nat => repeat false n ++ [true]) (map f (seq 2 x)))
            >= x) by lia.
    eapply flat_map_length_ge. 
    + rewrite map_length, seq_length. lia.
    + intros. rewrite app_length, repeat_length. cbn. lia.
Qed.

Lemma SCT_to_SCT_bool :
  SCT -> SCT_bool.
Proof.
  intros (ϕ & Hϕ & SCT).
  exists (fun c x n => if ϕ c x n is Some x then Some (Nat.eqb x 0) else None). split.
  - intros c x n v H n2 H2. specialize (Hϕ c x n).
    destruct (ϕ c x n); inv H.
    eapply Hϕ in H2 as ->; eauto. 
  - intros f.
    specialize (SCT (fun x y => if f x y then 0 else 1)) as [γ H].
    exists γ. intros x y.
    destruct (H x y) as [n Hn]. exists n. rewrite Hn.
    destruct (f x y); reflexivity.
Qed.

Lemma SCT_bool_to_SCT :
  SCT_bool -> SCT.
Proof.
  intros (ϕ & Hϕ & SCT).
  exists (fun c x => the_fun (R (fun x => @Build_part _ (ϕ c x) (Hϕ c x)) x)). split.
  - intros c x. eapply spec_fun.
  - intros f. specialize (SCT (fun x => I (f x))) as [γ H].
    exists γ. intros x y.
    enough (R (fun x0 : nat => {| the_fun := ϕ (γ x) x0; spec_fun := Hϕ (γ x) x0 |}) y
              =! f x y) as [n Hn] by firstorder.
    eapply R_spec. eapply H.
Qed.

End R_spec.

Lemma EPF_bool_to_SCT_bool {Part : partiality} :
  EPF_bool -> SCT_bool.
Proof.
    intros (θ & EPF).
  exists (fun c x n => seval (θ c x) n). split.
  - intros. eapply seval_mono.
  - intros f.
    specialize (EPF (fun x y => ret (f x y))) as [γ H].
    exists γ. intros x y. specialize (H x y).
    eapply seval_hasvalue, H, ret_hasvalue.
Qed.

Lemma EPF_to_EPF_bool {Part : partiality} :
  EPF -> EPF_bool.
Proof.
  intros (θ & EPF).
  exists (fun x y => bind (θ x y) (fun v => ret (Nat.eqb v 0))).
  intros f.
  specialize (EPF (fun x y => bind (f x y) (fun b => ret (if b then 0 else 1)))) as [γ Hγ].
  exists γ. intros x y. specialize (Hγ x y).
  intros v.
  rewrite bind_hasvalue.
  cbn in Hγ. red in Hγ. setoid_rewrite Hγ.
  setoid_rewrite bind_hasvalue.
  split.
  - intros (a & (a0 & H1 & <- % ret_hasvalue_iff) & <- % ret_hasvalue_iff).
    now destruct a0; cbn.
  - intros H. eexists. split. 1:eexists; split. 1: eassumption.
    eapply ret_hasvalue. destruct v; eapply ret_hasvalue.
Qed.

Lemma EPF_nonparam_to_CT { Part : partiality} :
  EPF_nonparam -> ∑ ϕ, CT_for ϕ.
Proof.
  intros [e EPF].
  unshelve eexists; [ | split].
  - exact (fun c x n => Part.(seval) (e c x) n).
  - cbn. intros c x y n1 Hn1 n2 len.
    eapply seval_mono; eauto.
  - intros f.
    destruct (EPF (fun n => ret (f n))) as [c Hc].
    exists c. intros x.
    cbn. specialize (Hc x (f x)).
    eapply seval_hasvalue, Hc, ret_hasvalue.
Qed. 

Lemma CT_to_EPF_nonparam `{partiality} :
  (∑ ϕ, CT_for ϕ) -> EPF_nonparam.
Proof.
  intros [ϕ [Hmono CT]].
  exists (fun c x => mkpart (fun arg => let (n, m) := unembed arg in match ϕ c ⟨ x, n ⟩ m with Some (S x) => Some x | _ => None end)).
  intros f. destruct (partial_to_total f) as [f' Hf'].
  destruct (CT f') as [c Hc].
  exists c. intros x y.

  transitivity (exists n m, ϕ c ⟨ x, n ⟩ m = Some (S y)). {
    rewrite mkpart_hasvalue.
    split.
    - intros [n Hn]. destruct (unembed n) as [n' m] eqn:E.
      exists n', m.
      destruct ϕ as [ [] | ]; try congruence.
    - intros [n [m HT]]. exists ⟨ n, m ⟩. now rewrite embedP, HT.
    - intros n1' n2' x1 x2 H1 H2.
      destruct (unembed n1') as [n1 m1], (unembed n2') as [n2 m2].
      destruct (Hc ⟨x,n1⟩) as [m3 H3], (Hc ⟨x,n2⟩) as [m4 H4].
      destruct (ϕ c ⟨ x, n1 ⟩ m1) eqn:E1; try congruence.
      destruct (ϕ c ⟨ x, n2 ⟩ m2) eqn:E2; try congruence.
      eapply (monotonic_agnostic (Hmono _ _) H3) in E1; eauto. subst n.
      eapply (monotonic_agnostic (Hmono _ _) H4) in E2; eauto. subst n0.
      destruct (f' ⟨ x, n1 ⟩) eqn:E1; try congruence.
      destruct (f' ⟨ x, n2 ⟩) eqn:E2; try congruence.
      inv H1. inv H2.
      assert (f x =! x1) by (eapply Hf'; eauto).
      assert (f x =! x2) by (eapply Hf'; eauto).
      eapply hasvalue_det; eauto.
  }
  
  rewrite Hf'. 

  split.
  - intros [n [m HT]].
    destruct (Hc ⟨ x, n ⟩).
    eapply (monotonic_agnostic (Hmono _ _) H0) in HT; eauto.
  - intros [n Hn].
    destruct (Hc ⟨ x, n ⟩).
    rewrite Hn in H0. eauto.
Qed.

Theorem equivalence `{partiality} : 
  ((∑ ϕ, CT_for ϕ /\ SMN_for ϕ) -> SCT) *
  (SCT -> EPF) *
  (EPF -> EA) *
  (EA -> EPF_bool) *
  (EPF_bool -> SCT_bool) *
  (SCT_bool -> EPF_nonparam) *
  (EPF_nonparam -> (∑ ϕ, CT_for ϕ)) *
  ((∑ ϕ, CT_for ϕ) -> (∑ ϕ, CT_for ϕ /\ SMN_for ϕ)).
Proof.
  repeat split.
  - now eapply CT_SMN_to_SCT.
  - now eapply SCT_to_EPF.
  - now intros ? % EPF_to_SCT % SCTS_to_EAS.
  - now intros ? % EA_to_SCT % SCT_to_EPF % EPF_to_EPF_bool.
  - now intros ? % EPF_bool_to_SCT_bool.
  - now intros ? % R_spec.SCT_bool_to_SCT % SCT_to_EPF % EPF_iff_nonparametric.
  - now eapply EPF_nonparam_to_CT.
  - now intros ? % CT_to_EPF_nonparam % EPF_iff_nonparametric % EPF_to_CT_SMN.
Qed.
