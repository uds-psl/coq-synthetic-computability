From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.SemiDecidabilityFacts reductions partial embed_nat.
Require Import Setoid Program Lia.

(** * Axioms for synthetic computability *)

Definition CT (ϕ : nat -> nat -> nat -> option nat) :=
  (forall c x, monotonic (ϕ c x)) /\
  forall f, exists c, forall x, exists n, ϕ c x n = Some (f x).

Section halting_CT.

  Variable ϕ : nat -> nat -> nat -> option nat.

  Variable ct : CT ϕ.

  Definition K' c := exists n m, ϕ c ⟨c, n⟩ m = Some 0.
  
  Lemma semidecidable_K' : semi_decidable K'.
  Proof.
    exists (fun c => fun! ⟨n, m⟩ => if (ϕ c ⟨c,n⟩ m) is Some 0 then true else false).
    intros c; unfold K'. split.
    - intros (n & m & H).
      exists ⟨n, m⟩. now rewrite embedP, H.
    - intros (nm & H). destruct (unembed nm) as [n m].
      destruct ϕ as [[] | ] eqn:E; inv H.
      eauto.
  Qed. 

  Lemma not_semidecidable_compl_K' : ~ semi_decidable (compl K').
  Proof.
    intros (f & Hf). destruct ct as [Hm ct'].
    destruct (ct' (fun! ⟨x, n⟩ => if f x n then 0 else 1)) as [c Hc].
    enough(compl K' c <-> K' c) by (unfold compl in *; tauto).
    red in Hf.
    rewrite Hf. unfold K'.
    split.
    - intros [n Hn].
      specialize (Hc ⟨c, n⟩) as [m H].
      rewrite embedP in H. 
      exists n, m. rewrite Hn in H. eauto.
    - intros (n & m & H). exists n.
      specialize (Hc (⟨c, n⟩)) as [m' H'].
      rewrite embedP in H'.
      destruct (f c n); try congruence.
      enough (1 = 0) by congruence.
      eapply monotonic_agnostic; eauto.
  Qed.

End halting_CT.

Lemma CT_halting {ϕ} : CT ϕ ->
  exists K : nat -> Prop, semi_decidable K /\ ~ semi_decidable (compl K) /\ ~ decidable K /\ ~ decidable (compl K).
Proof.
  intros [Hm H]. exists (K' ϕ).
  repeat split.
  - now eapply semidecidable_K'.
  - now eapply not_semidecidable_compl_K'.
  - intros ? % decidable_complement % decidable_semi_decidable.
    now eapply not_semidecidable_compl_K'.
  - intros ? % decidable_semi_decidable.
    now eapply not_semidecidable_compl_K'.
Qed.

(** ** Synthetic Church's thesis *)

Definition SCT :=
  ∑ T : nat -> nat -> nat -> option nat,
    (forall c x, monotonic (T c x)) /\
    forall f : nat -> nat -> nat, exists γ, forall x y, exists n, T (γ x) y n = Some (f x y).

Tactic Notation "intros" "⟨" ident(x) "," ident(n) "⟩" :=
  let xn := fresh "xn" in
  intros xn; destruct (unembed xn) as [x n]; try setoid_rewrite (@embedP (x,n)).

Definition SMN_for (T : nat -> nat -> nat -> option nat) :=
  (exists S : nat -> nat -> nat, forall c x y v, (exists n, T c ⟨x,y⟩ n = Some v) <-> (exists n, T (S c x) y n = Some v)).

Lemma CT_SMN_to_SCT :
  (∑ ϕ, CT ϕ /\ SMN_for ϕ) ->
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
  ∑ ϕ, CT ϕ.
Proof.
  intros (ϕ & Hϕ & SCT).
  exists ϕ. repeat eapply conj.
  - eapply Hϕ.
  - intros f. specialize (SCT (fun _ => f)) as [γ H].
    exists (γ 0). intros. eapply H.
Qed.

Section Cantor.

  Variable A : Type.
  Variable g : A -> (A -> bool).

  Lemma Cantor : surjection_wrt ext_equiv g -> False.
  Proof.
    intros g_surj.
    pose (h x1 := negb (g x1 x1)).
    destruct (g_surj h) as [n H].
    specialize (H n). cbn in H. unfold h in H.
    destruct (g n n); inv H.
  Qed.

End Cantor.

Instance equiv_part `{partiality} {A} : equiv_on (part A) := {| equiv_rel := @partial.equiv _ A |}.

Definition EPF `{partiality} :=
  ∑ θ : nat -> (nat ↛ nat), forall f : nat -> nat ↛ nat,
      exists γ, forall x, θ (γ x) ≡{nat ↛ nat} f x.

Notation "A ↔ B" := ((A -> B) * (B -> A))%type (at level 95).

Lemma EPF_iff `{Part : partiality} :
  EPF ↔ ∑ θ : nat -> (nat ↛ nat), forall R : nat -> FunRel nat nat, 
            (exists f, (forall i, pcomputes (f i) (R i))) -> exists γ, forall i, pcomputes (θ (γ i)) (R i).
Proof.
  split.
  - intros [θ H]. exists θ. intros R [f Hf].
    destruct (H f) as [γ Hγ]. exists γ. intros i x y.
    unfold pcomputes in *. specialize (Hγ i x). cbn in Hγ. red in Hγ.
    rewrite Hγ. eapply Hf.
  - intros [θ H]. exists θ. intros f.
    unshelve epose (R := fun i => @Build_FunRel nat nat (fun x y => hasvalue (f i x) y) _).
    { intros ? ? ? ? ?. eapply hasvalue_det; eauto. }
    destruct (H R) as [γ Hγ].
    + exists f. firstorder.
    + exists γ. intros i x y. eapply Hγ.
Qed.    

Lemma partial_to_total `{Part : partiality} (f : nat ↛ nat) :
  {f' : nat -> nat | forall x a, f x =! a <-> exists n, f' ⟨x, n⟩ = S a }.
Proof.
  exists (fun arg => let (x,n) := unembed arg in match seval (f x) n with Some a => S a | None => 0 end).
  intros x a. split.
  - intros [n H] % seval_hasvalue. 
    exists n. now rewrite embedP, H.
  - intros [n H]. rewrite embedP in H.
    eapply seval_hasvalue. exists n.
    destruct seval; congruence.
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
  EPF -> exists ϕ, CT ϕ /\ SMN_for ϕ.
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

Definition EA := ∑ ψ : nat -> (nat -> option nat),
    forall p : nat -> nat -> Prop, penumerable p -> exists γ, parametric_enumerator (fun x => ψ (γ x)) p.

From SyntheticComputability Require Import reductions ReducibilityFacts EnumerabilityFacts ListEnumerabilityFacts.

Lemma EA_iff_enumerable :
  EA ↔ ∑ ψ : nat -> (nat -> option nat),
  forall p : nat -> nat -> Prop, enumerable (uncurry p) -> exists γ, parametric_enumerator (fun x => ψ (γ x)) p.
Proof.
  split; intros [ψ H]; exists ψ; intros p Hp % penumerable_iff; eauto.
  all: eapply discrete_nat.
Qed.

Lemma EA_iff_ran :
  EA ↔ ∑ ψ : nat -> (nat -> option nat),
  forall f : nat -> nat -> option nat,
  exists γ, forall x, ψ (γ x) ≡{ran} f x.
Proof.
  split; intros [ψ H]; exists ψ.
  - intros f.
    specialize (H (fun x y => exists n, f x n = Some y)) as [γ H].
    + exists f. red. reflexivity.
    + exists γ. intros x. cbn. intros y. symmetry. eapply H.
  - intros p [f Hf].
    specialize (H f) as [γ H].
    exists γ. intros x y.
    red in Hf. cbn in H. now rewrite Hf, H.
Qed.

Lemma EA_halting : EA -> exists K : nat -> Prop, enumerable K /\ ~ enumerable (compl K) /\ ~ decidable K.
Proof.
  intros [φ EA].
  exists (fun c => exists n, φ c n = Some c).
  assert (He : ~ enumerable (compl (fun c => exists n, φ c n = Some c))). { 
    intros [f Hf].
    specialize (EA (fun _ => compl (fun c => exists n, φ c n = Some c))) as [γ H].
    { exists (fun _ => f). firstorder. }
    specialize (H 0 (γ 0)). cbn in H. unfold compl in *. tauto.
  }
  repeat split.
  - exists (fun! ⟨c, m⟩ => if φ c m is Some x then if Nat.eqb x c then Some c else None else None).
    unfold enumerator. intros c. split.
    + intros [n H]. exists ⟨c, n⟩. now rewrite embedP, H, PeanoNat.Nat.eqb_refl.
    + intros [cn H]. destruct (unembed cn) as [c' n]. exists n.
      destruct φ eqn:E; inv H.
      now destruct (PeanoNat.Nat.eqb_spec n0 c'); inv H1.
  - eassumption.
  - intros ? % decidable_complement % decidable_enumerable; eauto.
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

Lemma EA_to_EA_star :
  EA -> ∑ φ : nat -> (nat -> option nat),
    (forall p, enumerable p -> exists c, enumerator (φ c) p) /\
    let W c x := exists n, φ c n = Some x in                     
    exists s, forall c x y, W (s c x) y <-> W c ⟨x,y⟩.
Proof.
  intros (φ & H) % EA_iff_enumerable.
  assert (lem : forall p : nat -> Prop, enumerable p -> exists c : nat, enumerator (φ c) p). { 
    intros p [f Hf].
    destruct (H (fun _ => p)) as [c0 Hc0].
    + exists (fun! ⟨x,n⟩ => if f n is Some y then Some (x,y) else None).
      intros [x y]. 
      rewrite (Hf y). 
      split.
      * intros [n Hn]. exists ⟨x,n⟩. now rewrite embedP, Hn. 
      * intros [xn Hn]. destruct (unembed xn) as [x' n].
        destruct f eqn:E'; inv Hn. eauto. 
    + exists (c0 0). intros x. eapply Hc0.
  }
  exists φ. split.
  - eapply lem.
  - cbn. destruct (H (fun! ⟨c,x⟩ => fun y => exists n, φ c n = Some ⟨x,y⟩)) as [γ Hγ].
    + eexists (fun! ⟨c,n⟩ => if φ c n is Some xy then (fun! ⟨x,y⟩ => Some (⟨c,x⟩, y)) xy else @None _). intros [cx y].
      destruct (unembed cx) as [c x] eqn:E'.
      eapply (f_equal embed) in E'. rewrite unembedP in E'.
      subst. split.
      * cbn. rewrite embedP. intros [n Hn]. exists ⟨c,n⟩.
        now rewrite embedP, Hn, embedP.
      * intros [n Hn]. destruct (unembed n) as [c' n'].
        destruct φ eqn:E; try congruence.
        destruct (unembed n0) as [x' y'] eqn:E'. inv Hn.
        eapply (f_equal unembed) in H1. rewrite !embedP in H1.
        inv H1.
        eapply (f_equal embed) in E'. rewrite !unembedP in E'. subst.
        cbn. rewrite embedP. eauto.
    + exists (fun c x => γ ⟨c,x⟩). unfold enumerator in Hγ.
      intros. specialize (Hγ ⟨c,x⟩ y). cbn in Hγ. rewrite embedP in Hγ.
      symmetry. eassumption.
Qed.

Lemma enumerable_pair_red:
  forall p : nat -> nat -> Prop, enumerable (uncurry p) -> enumerable (fun! ⟨ x, y ⟩ => p x y).
Proof.
  intros p Hp.
  eapply enumerable_red; eauto. 2: eapply discrete_iff; eauto.
  exists unembed. intros xy.
  destruct (unembed xy) as [x y]. reflexivity.
Qed.

Lemma EA_star_to_EA :
  (∑ φ : nat -> (nat -> option nat),
    (forall p, enumerable p -> exists c, enumerator (φ c) p) /\
    let W c x := exists n, φ c n = Some x in                     
    exists s, forall c x y, W (s c x) y <-> W c ⟨x,y⟩) -> EA.
Proof.
  intros (φ & H). eapply EA_iff_enumerable.
  exists φ. destruct H as (Hφ & S & HS).
  intros p Hp % enumerable_pair_red.

  destruct (Hφ _ Hp) as [c Hc].
  exists (fun x => S c x). intros x y. red in Hc.
  now rewrite HS, <- Hc, embedP.
Qed.

Definition EA' := ∑ W : nat -> (nat -> Prop), forall p : nat -> Prop, enumerable p <-> exists c, W c ≡{nat -> Prop} p.

Lemma EA_to_EA'  : 
  EA -> EA'.
Proof.
  intros [φ H].
  exists (fun c x => exists n, φ c n = Some x). intros p.
  split.
  - intros [f Hf]. specialize (H (fun _ => p)) as [γ H].
    + exists (fun _ => f). intros _. eapply Hf.
    + exists (γ 0). intros x. cbn. firstorder.
  - intros [c Hc]. exists (φ c). firstorder.
Qed.

Definition SCT_bool :=
  ∑ ϕ : nat -> nat -> nat -> option bool,
    (forall c x, monotonic (ϕ c x)) /\
    forall f : nat -> nat -> bool, exists γ, forall x y,exists n,  ϕ (γ x) y n = Some (f x y).

Module R_spec.

Require Import List.
Import ListNotations.
Import implementation.

Definition I (f : nat -> nat) (n : nat) : bool :=
  nth n (flat_map (fun n => List.repeat false n ++ [true]) (map f (seq 0 (1 + n)))) false.

Fixpoint R (f : nat -> part bool) (x : nat) : part nat :=
  match x with
  | 0 => mu f
  | S x => bind (mu f) (fun n => R (fun m => f (m + S n)) x)
  end.

Lemma R_spec0:
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

Definition EPF_bool `{partiality} :=
  ∑ θ : nat -> (nat ↛ bool), forall f : nat -> nat ↛ bool,
      exists γ, forall x, θ (γ x) ≡{nat ↛ bool} f x.

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

Section halting.

  Variable Part : partiality.
  Variable θ : nat -> nat ↛ bool.

  Variable EPF : forall f : nat -> nat ↛ bool,
     exists γ : nat -> nat, forall x : nat, θ (γ x) ≡{ nat ↛ bool} f x.

  Definition K c := exists v, θ c c =! v.

  Lemma semidecidable_K : semi_decidable K.
  Proof.
    exists (fun c n => if seval (θ c c) n is Some v then true else false).
    intros c; unfold K. split.
    - intros [v [n H] % seval_hasvalue]. exists n. now rewrite H.
    - intros [n H]. destruct (seval) as [v | ] eqn:E; inv H.
      exists v. eapply seval_hasvalue. eauto.
  Qed.

  Lemma not_semidecidable_compl_K : ~ semi_decidable (compl K).
  Proof.
    intros (Y & f & Hf) % semi_decidable_part_iff.
    destruct (EPF (fun _ n => bind (f n) (fun _ => ret true))) as [γ H].
    specialize (H 0). 
    enough(compl K (γ 0) <-> K (γ 0)) by (unfold compl in *; tauto).
    rewrite Hf. unfold K.
    specialize (H (γ 0)). cbn in H. red in H.
    setoid_rewrite H. setoid_rewrite bind_hasvalue.
    setoid_rewrite <- ret_hasvalue_iff. 
    split; intros [v Hv]; eauto; firstorder.
  Qed.

End halting.

Lemma EPF_halting {Part : partiality} : EPF_bool -> 
  exists K : nat -> Prop, semi_decidable K /\ ~ semi_decidable (compl K) /\ ~ decidable K /\ ~ decidable (compl K).
Proof.
  intros [θ H]. exists (K _ θ).
  repeat split.
  - now eapply semidecidable_K.
  - now eapply not_semidecidable_compl_K.
  - intros ? % decidable_complement % decidable_semi_decidable.
    now eapply not_semidecidable_compl_K.
  - intros ? % decidable_semi_decidable.
    now eapply not_semidecidable_compl_K.
Qed.