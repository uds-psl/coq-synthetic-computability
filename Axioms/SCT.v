From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.SemiDecidabilityFacts reductions partial embed_nat.
Require Import Setoid Program Lia.

(** ** Synthetic Church's thesis *)

Definition SCT :=
  ∑ T : nat -> nat -> nat -> option nat,
    (forall c x, monotonic (T c x)) /\
    forall f : nat -> nat -> nat, exists γ, forall x y, exists n, T (γ x) y n = Some (f x y).

Definition SCT_bool :=
  ∑ ϕ : nat -> nat -> nat -> option bool,
    (forall c x, monotonic (ϕ c x)) /\
    forall f : nat -> nat -> bool, exists γ, forall x y,exists n,  ϕ (γ x) y n = Some (f x y).

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