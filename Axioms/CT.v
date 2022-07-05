From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.SemiDecidabilityFacts reductions partial embed_nat.
Require Import Setoid Program Lia.

(** * Axioms for synthetic computability *)

Definition CT_for (ϕ : nat -> nat -> nat -> option nat) :=
  (forall c x, monotonic (ϕ c x)) /\
  forall f, exists c, forall x, exists n, ϕ c x n = Some (f x).

Definition SMN_for (T : nat -> nat -> nat -> option nat) :=
  (exists S : nat -> nat -> nat, forall c x y v, (exists n, T c ⟨x,y⟩ n = Some v) <-> (exists n, T (S c x) y n = Some v)).
  

Section halting_CT.

  Variable ϕ : nat -> nat -> nat -> option nat.

  Variable ct : CT_for ϕ.

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

Lemma CT_halting {ϕ} : CT_for ϕ ->
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