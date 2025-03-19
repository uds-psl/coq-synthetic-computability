Require Import PeanoNat.

(* bijection from nat * nat to nat *)
Definition embed '(x, y) : nat := 
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(* bijection from nat to nat * nat *)
Definition unembed (n : nat) : nat * nat := 
  nat_rec _ (0, 0) (fun _ '(x, y) => match x with S x => (x, S y) | _ => (S y, 0) end) n.

Lemma embedP {xy: nat * nat} : unembed (embed xy) = xy.
Proof.
  assert (forall n, embed xy = n -> unembed n = xy).
    intro n. revert xy. induction n as [|n IH].
      intros [[|?] [|?]]; intro H; inversion H; reflexivity.
    intros [x [|y]]; simpl.
      case x as [|x]; simpl; intro H.
        inversion H.
      rewrite (IH (0, x)); [reflexivity|].
      inversion H; simpl. rewrite Nat.add_0_r. reflexivity.
    intro H. rewrite (IH (S x, y)); [reflexivity|]. 
    inversion H. simpl. rewrite Nat.add_succ_r. reflexivity.
  apply H. reflexivity.
Qed.

Lemma unembedP {n: nat} : embed (unembed n) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. revert IH. case (unembed n). intros x y.
  case x as [|x]; intro Hx; rewrite <- Hx; simpl.
    rewrite Nat.add_0_r. reflexivity.
  rewrite ?Nat.add_succ_r. simpl. rewrite ?Nat.add_succ_r. reflexivity. 
Qed.
Arguments embed : simpl never.


Module EmbedNatNotations.
  Notation "⟨ a , b ⟩" := (embed (a, b)) (at level 0).
  Notation "'fun!' '⟨' x ',' y '⟩' '=>' b" := (fun p => let (x,y) := unembed p in b) (at level 30, b at level 200).
End EmbedNatNotations.

Module VectorEmbedding.

Require Import Vector.

Fixpoint vec_to_nat {k : nat} (v : Vector.t nat k) {struct v} : nat.
Proof.
  destruct v.
  - exact 0.
  - exact (S (embed (h, (vec_to_nat _ v)))).
Defined.

Fixpoint nat_to_vec (k : nat) (v : nat) : Vector.t nat k.
Proof.
  destruct k.
  - apply Vector.nil.
  - destruct v.
    + apply Vector.cons. exact 0. apply nat_to_vec. exact 0.
    + destruct (unembed v) as [h v'].
      apply Vector.cons. exact h. apply nat_to_vec. exact v'.
Defined.

Lemma vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat v) = v.
Proof.
  induction v.
  - cbn. reflexivity.
  - cbn. now rewrite embedP, IHv.
Qed.

End VectorEmbedding.
