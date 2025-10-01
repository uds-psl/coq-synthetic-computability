From SyntheticComputability Require Import DecidabilityFacts EnumerabilityFacts SemiDecidabilityFacts ListEnumerabilityFacts Axioms.Equivalence embed_nat reductions partial Dec.

Require Import SyntheticComputability.Synthetic.EnumerabilityFacts.

(** * Halting problems  *)

Section assm.

Lemma semi_decidable_enumerable_iff_nat (p : nat -> Prop) : semi_decidable p <-> enumerable p.
Proof.
  split.
  - intros. eapply semi_decidable_enumerable; eauto.
  - intros. eapply enumerable_semi_decidable; eauto.
Qed.

Lemma EPF_SCT_halting {Part : partiality} :
  EPF_bool + SCT -> exists K : nat -> Prop, semi_decidable K /\ ~ semi_decidable (compl K) /\ ~ decidable K /\ ~ decidable (compl K).
Proof.
  intros [H | H].
  - now eapply EPF_halting.
  - eapply SCT_to_CT in H as [ϕ]. eapply CT_halting; eauto.
Qed.

Definition K_nat_bool (f : nat -> bool) := exists n, f n = true.
Definition K_nat_nat  (f : nat -> nat) := exists n, f n <> 0.

Lemma K_nat_bool_complete {X} (p : X -> Prop) :
  semi_decidable p <-> p ⪯ₘ K_nat_bool.
Proof.
  reflexivity.
Qed.

Lemma K_nat_bool_equiv :
  K_nat_bool ≡ₘ K_nat_nat.
Proof.
  split.
  - exists (fun (f : nat -> bool) x => if f x then 1 else 0).
    intros f. unfold K_nat_nat, K_nat_bool.
    split.
    + intros [n Hn]. exists n.
      rewrite Hn. eauto.
    + intros [n Hn]. exists n.
      destruct (f n); congruence.
  - exists (fun f x => negb (Nat.eqb (f x) 0)).
    intros f. unfold K_nat_nat, K_nat_bool.
    setoid_rewrite Bool.negb_true_iff.
    now setoid_rewrite PeanoNat.Nat.eqb_neq.
Qed.

Lemma K_nat_equiv :
  compl K_nat_nat ≡{_} (fun f => forall n : nat, f n = 0).
Proof.
  intros f.
  split; intros H.
  - intros n. destruct (f n) eqn:E. reflexivity.
    destruct H. exists n. now rewrite E.
  - firstorder.
Qed.


Lemma K_nat_bool_undec {Part : partiality}  :
  EPF_bool + SCT -> ~ decidable (compl K_nat_bool).
Proof.
  intros [K (SK & _ & _ & HK)] % EPF_SCT_halting Hd.
  eapply HK, red_m_transports.
  - eapply red_m_complement.
    now eapply K_nat_bool_complete.
  - eauto.
Qed.  

Lemma K_nat_undec {Part : partiality} :
  EPF_bool + SCT -> ~ decidable (fun f => forall n : nat, f n = 0).
Proof.
  intros [K (SK & _ & _ & HK)] % EPF_SCT_halting Hd.
  eapply Proper_decidable in Hd.
  2:{ intros ?. eapply K_nat_equiv. }
  eapply HK, red_m_transports.
  - eapply red_m_complement.
    eapply red_m_transitive. 
    + now eapply K_nat_bool_complete.
    + eapply K_nat_bool_equiv.
  - eauto.
Qed.  

Lemma K_nat_nored {p : nat -> Prop} :
   (forall g g' : nat -> nat, (forall x, g x = g' x) -> g = g') ->
  (fun f => forall n : nat, f n = 0) ⪯ₘ p -> decidable (fun f => forall n : nat, f n = 0).
Proof.
  intros Funext [F HF].
  exists (fun f => Nat.eqb (F f) (F (fun _ => 0))).
  intros f.
  red. rewrite PeanoNat.Nat.eqb_eq.
  split.
  - intros H. f_equal. now eapply Funext.
  - intros H. eapply HF. rewrite H. now eapply HF.
Qed.

End assm.
