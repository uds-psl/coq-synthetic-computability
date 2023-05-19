From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.MoreEnumerabilityFacts Synthetic.SemiDecidabilityFacts reductions embed_nat Dec.
Require Import Setoid Program Lia.

Definition EA := ∑ ψ : nat -> (nat -> option nat),
    forall p : nat -> nat -> Prop, penumerable p -> exists γ, parametric_enumerator (fun x => ψ (γ x)) p.

From SyntheticComputability Require Import reductions ReducibilityFacts EnumerabilityFacts ListEnumerabilityFacts.

Require Import SyntheticComputability.Synthetic.ReducibilityFacts.

Local Notation "A ↔ B" := ((A -> B) * (B -> A))%type (at level 95).

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

Lemma enum_iff (p : nat -> Prop) : enumerable p <-> semi_decidable p.
Proof.
  split.
  - intros H. eapply enumerable_semi_decidable. eapply discrete_nat. eassumption.
  - intros H. eapply semi_decidable_enumerable. eauto. eauto.
Qed.

Module Assume_EA.

From SyntheticComputability Require Import reductions.

Axiom EA : EA.

Notation φ := (proj1_sig EA).
Notation EAP := (proj2_sig EA).

Lemma EAS : forall p : nat -> nat -> Prop, enumerable (uncurry p) -> exists γ, forall x, enumerator (φ (γ x)) (p x).
Proof.
  intros p [γ H] % penumerable_iff % EAP; firstorder; eauto.
  eapply discrete_nat.
Qed.

Definition W c x := exists n, φ c n = Some x.

Lemma W_spec : forall p, enumerable p <-> exists c, forall x, p x <-> W c x.
Proof.
  intros p.
  split.
  - intros [f Hf].
    destruct (EAP (fun _ => p)) as [γ H].
    + exists (fun _ => f). firstorder.
    + exists (γ 0). firstorder.
  - intros [c H]. exists (φ c). firstorder.
Qed.

Lemma do_EA p : enumerable p -> exists c, forall x, p x <-> W c x.
Proof.
  eapply W_spec.
Qed.

Global Hint Resolve discrete_nat : core.

Lemma EAS' :
  forall p : nat -> nat -> Prop, enumerable (fun! ⟨x,y⟩ => p x y) ->
                                        exists c : nat -> nat, forall x y, p x y <-> W (c x) y.
Proof.
  intros p Hp.
  eapply EAS, enumerable_red; eauto.
  exists embed. red. intros [x y]. now rewrite embedP.
Qed.

Lemma EAS_datatype X (p : X -> nat -> Prop) (x0 : X) :
  datatype X ->
  enumerable (uncurry p) ->
  exists c : X -> nat, forall x y, p x y <-> W (c x) y.
Proof.
  intros (I & R & HIR) Ep.
  destruct (EAS (fun x y => if R x is Some l then p l y else p x0 y)) as [c Hc].
  - eapply enumerable_red.
    4: eapply Ep.
    + exists (fun '(x, y) => if R x is Some l then (l,y) else (x0, y)).
      intros [x y]. cbn.
      destruct (R x); reflexivity.
    + eauto. 
    + eapply discrete_prod. eapply datatype_discrete. now exists I, R.
      eapply discrete_nat.
  - exists (fun l => c (I l)). intros. 
    now rewrite <- (Hc (I x) y), HIR.
Qed.

Lemma EAS_list (p : list nat -> nat -> Prop) : enumerable (uncurry p) ->
                                      exists c : list nat -> nat, forall x y, W (c x) y <-> p x y.
Proof.
  intros.
  edestruct EAS_datatype with (p := p) as [c Hc]; eauto.
  - exact nil.
  - eapply enumerable_discrete_datatype.
    eapply discrete_list, discrete_nat.
    red; eexists; exact _.
  - exists c. firstorder.
Qed.

Lemma List_id : exists c_l, forall (l : list nat), forall x, W (c_l l) x <-> List.In x l.
Proof.
  eapply EAS_list. 
  eapply decidable_enumerable. 2:eauto.
  eapply decidable_iff. econstructor.
  intros [x y]. cbn. eapply ListAutomation.list_in_dec. intros. eapply nat_eq_dec.
Qed.

Notation π1 := (fun! ⟨x, y⟩ => x).
Notation π2 := (fun! ⟨x, y⟩ => y).

Lemma enumerable_W : enumerable (fun '(x, y) => W x y).
Proof.
  exists (fun p => let (n,m) := unembed p in if φ n m is Some m then Some (n, m) else None).
  intros [n m].
  split.
  - intros H. destruct H as [n' H].
    exists (embed (n, n')). rewrite embedP. cbn. now rewrite H.
  - unfold W.
    intros [p H].
    destruct (unembed p) as [n' m'].
    exists m'.
    destruct (φ n' m') eqn:E; inversion H; now subst.
Qed.

Lemma W_maximal (p : nat -> Prop) :
  enumerable p -> p ⪯ₘ uncurry W.
Proof.
  intros Hp.
  destruct (do_EA p Hp) as [c Hc].
  exists (fun x => (c, x)). exact Hc.
Qed.

Lemma SMN' : forall f, exists k, forall c x, W c (f x) <-> W (k c) x.
Proof.
  intros f.
  eapply EAS.
  eapply enumerable_red with (q := uncurry W).
  - exists (fun '(x,y) => (x, f y)). now intros [x y].
  - eauto.
  - eapply discrete_prod; now eapply discrete_nat.
  - eapply enumerable_W.
Qed.

From SyntheticComputability Require Import truthtables.

Lemma TT : 
  forall f : nat -> { Q : list nat & truthtable}, 
    exists c : list nat -> nat, forall l x, W (c l) x <-> eval_tt (projT2 (f x)) (List.map (fun x => negb (inb (uncurry Nat.eqb) x l)) (projT1 (f x))) = false.
Proof.
  intros f.
  eapply EAS_list.
  eapply decidable_enumerable. 2:eauto.
  eapply decidable_iff. econstructor.
  intros [x y]. cbn. exact _. 
Qed.

Tactic Notation "intros" "⟨" ident(n) "," ident(m) "⟩" :=
  let nm := fresh "nm" in
  let E := fresh "E" in
  intros nm; destruct (unembed nm) as [n m] eqn:E.

Definition K0 c := W c c.

Lemma K0_not_enumerable : ~ enumerable (compl K0).
Proof.
  intros [c Hc] % do_EA. specialize (Hc c).
  unfold K0, compl in Hc. tauto.
Qed.

Lemma K0_undecidable : ~ decidable (compl K0).
Proof.
  intros Hf % decidable_enumerable; eauto.
  now eapply K0_not_enumerable.
Qed.

Lemma W_uncurry_red:
  (fun! ⟨ n, m ⟩ => W n m) ⪯ₘ uncurry W.
Proof.
  exists (fun! ⟨n,m⟩ => (n,m)). intros nm. destruct (unembed nm) as [n m]. reflexivity.
Qed.

Lemma K0_red:
  K0 ⪯ₘ uncurry W.
Proof.
  exists (fun n => (n,n)). intros n. reflexivity.
Qed.

Lemma W_uncurry_red':
  uncurry W ⪯ₘ (fun! ⟨ n, m ⟩ => W n m).
Proof.
  exists (fun '(n,m) => ⟨n,m⟩). intros [n m]. now rewrite embedP.
Qed.

Global Hint Resolve discrete_prod discrete_nat : core.

Lemma W_not_enumerable : ~ enumerable (compl (uncurry W)).
Proof.
  eapply not_coenumerable; eauto.
  - eapply K0_red.
  - eapply K0_not_enumerable. 
Qed.

Lemma K0_enum : enumerable K0.
Proof.
  eapply enumerable_red with (q := uncurry W).
  eapply K0_red. all:eauto.
  eapply enumerable_W.
Qed.

Lemma red_tt_not_red_m :
  compl K0 ⪯ₜₜ K0 /\ ~ compl K0 ⪯ₘ K0.
Proof.
  split.
  - eapply red_tt_complement.
  - intros H % enumerable_red.
    + now eapply K0_not_enumerable.
    + eauto.
    + eapply discrete_nat.
    + eapply K0_enum.
Qed.

Notation "m-complete p" := (forall q : nat -> Prop, enumerable q -> q ⪯ₘ p) (at level 10).

Lemma m_complete_W :
  m-complete (fun! ⟨n,m⟩ =>  W n m).
Proof.
  intros q [c Hc] % do_EA.
  exists (fun x => ⟨c,x⟩). intros x.
  now rewrite embedP.
Qed.

Lemma W_red_K0 : (fun! ⟨n,m⟩ =>  W n m) ⪯ₘ K0.
Proof.
  edestruct EAS with (p := fun! ⟨x,y⟩ => fun (z : nat) => W x y) as [c Hc].
  - eapply ReducibilityFacts.enumerable_red with (q := uncurry W); eauto.
    2: eapply enumerable_W. all:eauto.
    exists (fun '(xy,z) => (fun! ⟨x,y⟩ => (x,y)) xy). intros [xy z].
    cbn. now destruct (unembed xy) as [x y]. 
  - exists c. intros xy. unfold K0. rewrite <- (Hc xy (c xy)).
    now destruct (unembed xy) as [x y].
Qed.

Lemma m_complete_K0 : m-complete K0.
Proof.
  intros q Hq % m_complete_W.
  eapply red_m_transitive. exact Hq. exact W_red_K0.
Qed.


Require Import List.

Lemma generative_W :   generative (fun! ⟨ n, m ⟩ => W n m).
Proof.
  eapply unbounded_generative. 
  intros x y; destruct (Dec.nat_eq_dec x y); eauto.
  destruct (do_EA (fun _ => True)) as [c_top H_top]. {
    eapply decidable_enumerable. 2:eauto. exists (fun _ => true). firstorder.
  }
  intros n. exists (List.map (fun m => ⟨c_top,m⟩) (List.seq 0 n)). split.
  now rewrite map_length, seq_length. split.
  eapply NoDup_map. intros ? ? E % (f_equal unembed). rewrite !embedP in E. congruence. eapply seq_NoDup.
  intros ? (? & <- & ?) % in_map_iff. rewrite embedP. firstorder.
Qed.

End Assume_EA.
