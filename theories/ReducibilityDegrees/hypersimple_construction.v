From SyntheticComputability Require Import simple_construction hypersimple Axioms.EA.

Lemma list_max_cns L:
  list_max L = 0 \/ In (list_max L) L.
Proof.
  induction L.
  - now left.
  - destruct IHL.
    + right. cbn. fold (list_max L). rewrite H. left. lia.
    + right. cbn. fold (list_max L). destruct (le_gt_dec (list_max L) a). lia.
      right. now replace (Nat.max a (list_max L)) with (list_max L) by lia. 
Qed.

Lemma list_max_NoDup L n:  
  NoDup L -> length L = 1 + n -> list_max L >= n.
Proof.
  intros ND H. eapply pigeonhole in ND.
  instantiate (1 := seq 0 n) in ND.
  - destruct ND as [x [H1 % list_max_in H2]]. rewrite in_seq in H2.
    lia. 
  - intros x1 x2; decide (x1 = x2); eauto.
  - rewrite H, seq_length. lia.  
Qed. 

Lemma list_max_length_succ L:
  length L > 0 -> In (list_max L) L.
Proof.
  induction L; cbn. 
  - lia. 
  - intros H. fold (list_max L). destruct (le_gt_dec (list_max L) a). lia.
    right. replace (Nat.max a (list_max L)) with (list_max L) by lia.
    eapply IHL.
    destruct L; cbn in *; lia. 
Qed.

Definition injective {X Y : Type} (f : X -> Y) := forall x1 x2 : X, f x1 = f x2 -> x1 = x2.

Section HS. 
  Import  Coq.Init.Nat. 

  Variable I : nat -> Prop. 

  Variable E_I: nat -> nat.

  Variable E_I_injective: injective E_I.
  
  Variable E_I_enum: strong_enumerator E_I I.

  Variable I_undec: ~ decidable I.

  Lemma in_map_sig {X Y} (f: X -> Y) L:
    eq_dec Y -> forall y, In y (map f L) -> {x | f x = y /\ In x L}.
  Proof. 
    intros DY y H. 
    induction L.
    - cbn; firstorder.
    - cbn in *. decide (In y (map f L)).
      + apply IHL in i as [x IHL1]. exists x. intuition.
      + destruct (DY (f a) y). 
        * exists a. intuition.
        * exfalso. destruct H; firstorder.
  Qed.

  Lemma E_I_first_n bound start: 
    {x | E_I x > bound /\ x >= start}.
  Proof.
    assert (length (map E_I (seq start (bound + 2))) > length (seq 0 (bound + 1))).
    - rewrite map_length, seq_length, seq_length. lia. 
    - apply pigeonhole_Sigma in H.  
      + destruct H as [y [H1 H2]]. rewrite in_seq in H2. apply in_map_sig in H1 as [x [E H1]].        
        exists x. rewrite E. apply in_seq in H1. lia. exact _.
      + exact _.
      + apply NoDup_map.
        * exact E_I_injective. 
        * apply seq_NoDup. 
  Qed.

  Definition HS x := exists y, x < y /\ E_I y < E_I x.
  
  (* Proving HS to be undecidable via decidable HS -> decidable W *)

  Definition boundable n: Type
    := {x | E_I x >= n /\ compl HS x}.

  Lemma greater_el n x':
    {x | x >= x' /\ E_I x > n}.
  Proof.
    assert (NoDup (map E_I (seq x' (2+n)))).
    { apply map_NoDup; try assumption. apply seq_NoDup. }
    eapply pigeonhole_Sigma in H. 
    - instantiate (1:= seq 0 (1 + n)) in H.
      destruct H as (Ex & H1 & H2).
      apply in_map_sig in H1 as [x [H1 H1']].
      + exists x. rewrite in_seq in H1', H2. split; try lia.
      + exact _.
    - exact _.
    - rewrite map_length. repeat rewrite seq_length. lia.
  Qed.
  
  Lemma bound_dec:
    (forall n, boundable n) -> decidable I.
  Proof.
    intros H. 
    assert (forall n, {x | E_I x >= n /\ forall x0, x0 > x -> E_I x0 > E_I x}).
    { intros n. destruct (H n). 
      exists x. intuition. enough (~ E_I x0 <= E_I x) by lia.
      intros E. apply H1. exists x0. intuition. 
      assert (E_I x0 < E_I x \/ E_I x0 = E_I x) as [E1 | E1 % E_I_injective] by lia; lia.
    }
    assert (forall n, {x | forall x0, x0 > x -> E_I x0 > n}).
    { intros n. destruct (H0 n).
      exists x. intros x0 E; try lia. 
      destruct a. specialize (H2 x0 E). lia.
    }
    apply decidable_iff. constructor. 
    intros n. destruct (H1 n). decide (In n (map E_I (seq 0 (x + 1)))).
    - left. apply in_map_iff in i as [x0 H2]. 
      apply E_I_enum. now exists x0.
    - right. intros [n1 H2] % E_I_enum. apply n0. 
      apply in_map_iff. exists n1; intuition.
      apply in_seq. enough (~ n1 > x) by lia.
      intros E % g. lia. 
  Qed.

  Lemma sizerecursion {X: Type} (s: X -> nat) (p: X -> Type):
    (forall x, (forall y, s y < s x -> p y) -> p x) -> forall x, p x.
  Proof.
    intros H. 
    enough (forall n x, s x < n -> p x).
    - intros x. eapply X0. eauto.
    - induction n. 
      + intros x H1. lia. 
      + intros x E. apply H. 
        intros y E1. apply IHn. lia. 
  Qed.  

  Lemma wo_HS {x}:
    (exists y, x < y /\ E_I y < E_I x) -> {y | x < y /\ E_I y < E_I x}.
  Proof.
    intros H. apply mu_nat_dep in H as [y h]. 
    - now exists y.
    - intros y.
      destruct (lt_dec x y); destruct (lt_dec (E_I y) (E_I x)); try (left; lia); try (right; lia).
  Qed.  

  Lemma inner_loop:
    (forall x, dec (HS x)) -> forall n x', boundable n + {x | x > x' /\ E_I x <= n}.
  Proof.
    intros H n x'. destruct (greater_el n x').
    revert x a. 
    apply (@sizerecursion _ E_I (fun x => x >= x' /\ E_I x > n -> boundable n + {x0 : nat | x0 > x' /\ E_I x0 <= n})). 
    intros x IH x0. 
    destruct (H x). 
    - apply wo_HS in h as [y h].
      + specialize (IH y (proj2 h)). destruct (le_dec (E_I y) n).
        * right. exists y; lia.
        * apply IH. lia.  
    - left. exists x. intuition. lia.
  Qed. 

  Lemma outer_loop step:
    (forall x, dec (HS x)) -> forall n, boundable n + {L | NoDup L /\ length L = step
                                                      /\ forall x, In x L -> E_I x <= n}.
  Proof. 
    intros H n. induction step. 
    - right. exists nil; firstorder. constructor. 
    - destruct IHstep; try now left.
      destruct s as (L & H1 & H2 & H3). 
      destruct (inner_loop H n (list_max L)); try now left.
      destruct s as (x & H4 & H5). 
      right. exists (x::L); intuition.
      + eapply NoDupBoundH. 
        * exact H1. 
        * intros x0 E % list_max_in. now instantiate (1:= list_max L).
        * exact H4.
      + firstorder.
      + destruct H0 as [<- | E]; firstorder.
  Qed.

  Lemma all_boundable:
    (forall x, dec (HS x)) -> forall n, boundable n.
  Proof.
    intros H n.
    destruct (outer_loop (2 + n) H n).
    - exact b. 
    - exfalso. destruct s as (L & H0 & H1 & H2).
      assert (incl (map E_I L) (seq 0 (n + 1))).
      { intros x [x0 [<- H4]] % in_map_iff. apply H2 in H4.
        apply in_seq. lia. }
      apply pigeonhole_length in H3.
      + rewrite seq_length, map_length in H3. lia.
      + intros x1 x2; decide(x1 = x2); firstorder.
      + now apply map_NoDup.
  Qed.

  Lemma HS_red:
    decidable HS -> decidable I.
  Proof.
    intros [H] % decidable_iff.
    apply bound_dec, all_boundable, H.
  Qed.

  Corollary HS_undec:
    ~ decidable HS.
  Proof.
    intros H % HS_red.
    now apply I_undec.
  Qed. 

  (* Proving HS to be hypersimple *)

  Lemma HS_enumerable:
    enumerable HS.
  Proof.
    unfold HS.
    eapply enumerable_projection1 with (p := fun xy => (fst xy) < (snd xy) /\ E_I (snd xy) < E_I (fst xy)).
    eapply decidable_enumerable. 2: eauto.
    eapply decidable_conj.
    all: eapply decidable_iff; eauto.
  Qed.

  Lemma HS_no_majorize:
    ~ exists f, majorizes f (compl HS).
  Proof.
    intros [g H].
    assert (forall x, I x <-> In x (map E_I (seq 0 (g (1 + x) + 1)))).
    - intros x. split.
      + intros [n H1] % E_I_enum. 
        apply in_map_iff. exists n. intuition.
        unfold majorizes in H. apply in_seq.
        specialize (H (1 + x)). enough (~ n > g (1 + x)) by lia.
        intros E. apply H. intros [L HL]. assert (list_max (map E_I L) >= x). 
        { apply list_max_NoDup.
          - apply NoDup_map; intuition.
          - now rewrite map_length.
        }  
        assert (length (map E_I L) > 0) by (rewrite map_length; lia). 
        apply list_max_length_succ in H2. apply in_map_iff in H2 as [n0 E1]. intuition. apply H7 in H5 as [H5 H5'].
        apply H5'. exists n. split; try lia. 
        assert (E_I n0 > E_I n \/ E_I n0 = E_I n) as [E1 | E1] by lia.
        * lia. 
        * apply E_I_injective in E1. lia.
      + intros [n [H1 _]] % in_map_iff. apply E_I_enum. now exists n.
    - apply I_undec, decidable_iff. constructor. 
      intros x. decide (In (x) (map E_I (seq 0 (g (1 + x) + 1)))); [left|right];firstorder.
  Qed.

  Lemma inf_help n x:
    E_I x <= n -> ~ ~ exists y, y >= x /\ compl HS y.
  Proof.
    revert x. induction n. 
    - intros x H. intros H1; apply H1. exists x. split. 
      + lia.
      + intros [y H2]. lia.
    - intros x E. intros H. ccase (HS x) as [H0 | H0].
      + destruct H0 as [x0 H2]. apply (IHn x0).
        * lia.
        * intros [y H1]. apply H. exists y. intuition. lia.
      + apply H. exists x. firstorder. 
  Qed.
 
  Lemma HS_co_infinite:
    ~ exhaustible (compl HS).
  Proof.
    apply non_finite_nat.
    intros x H. apply (@inf_help (E_I x) x). 
    - lia. 
    - exact H. 
  Qed.  

  Lemma HS_hypersimple:
    hypersimple HS.
  Proof.
    repeat split.
    - apply HS_enumerable.
    - apply HS_co_infinite.
    - apply HS_no_majorize. 
  Qed.
     
End HS.
