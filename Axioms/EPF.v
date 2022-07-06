From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.SemiDecidabilityFacts reductions partial embed_nat.
Require Import Setoid Program Lia.

Global Instance equiv_part `{partiality} {A} : equiv_on (part A) := {| equiv_rel := @partial.equiv _ A |}.

Definition EPF `{partiality} :=
  ∑ θ : nat -> (nat ↛ nat), forall f : nat -> nat ↛ nat,
      exists γ, forall x, θ (γ x) ≡{nat ↛ nat} f x.

Local Notation "A ↔ B" := ((A -> B) * (B -> A))%type (at level 95).

Lemma EPF_iff_pcomputes_relations `{Part : partiality} :
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

Definition EPF_nonparam `{partiality} := 
    ∑ θ : nat -> (nat ↛ nat), forall f : nat ↛ nat, exists c, θ c ≡{nat ↛ nat} f.

Lemma EPF_iff_nonparametric :
  EPF ↔ EPF_nonparam.    
Proof.
  split.
  - intros [θ H]. exists θ. intros f. destruct (H (fun _ => f)) as [c Hc].
    exists (c 0). eapply Hc.
  - intros [θ EPF]. exists (fun ic x => let (i, c) := unembed ic in θ c (embed (i, x))). intros f.
    destruct (EPF (fun x => let (k, l) := unembed x in f k l)) as [c Hc].
    exists (fun i => embed (i, c)). intros i x. rewrite embedP.
    rewrite (Hc ⟨i,x⟩). rewrite embedP. reflexivity.
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

Definition EPF_bool `{partiality} :=
  ∑ θ : nat -> (nat ↛ bool), forall f : nat -> nat ↛ bool,
      exists γ, forall x, θ (γ x) ≡{nat ↛ bool} f x.      

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