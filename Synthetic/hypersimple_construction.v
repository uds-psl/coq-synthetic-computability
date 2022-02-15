From Undecidability Require Import Synthetic.simple_construction Synthetic.hypersimple Axioms.EA.

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

Definition hyper_simple (p: nat -> Prop) : Prop
  := enumerable p /\ ~ exhaustible (compl p) /\
      ~ exists f, majorizes f (compl p).

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
  
  (* Prooving HS to be undecidable via decidable HS -> decidable W *)

  Lemma HS_undec_help0 n start step:
    (forall x, dec (HS x)) -> E_I start > n -> {x | ~ exists y, x < y /\ E_I y <= n} 
                      + {x | x > start /\ E_I x <= n}
                        + {L | length L = step /\ NoDup L 
                                  /\ forall x, In x L -> n < E_I x <= E_I start}.
  Proof.
    intros D E. induction step. 
    - right.  exists nil; intuition; try constructor; firstorder.
    - destruct IHstep. 
      + destruct s.
        * left. now left.
        * left. now right.
      + destruct s as [L H]. destruct (D (Nat.max start (list_max L) )).
        * apply mu_nat_dep in h as [y h]. destruct (le_gt_dec (E_I y) n).
          ** left. right. exists y. intuition. 
          ** right. exists (y::L). cbn; intuition.
             *** constructor; intuition. apply list_max_in in H1; lia.
             *** rewrite <- H5. destruct (list_max_cns L). 
                **** rewrite H1, Nat.max_0_r in H2. lia. 
                **** apply H4 in H1. 
                     destruct (Nat.max_spec start (list_max L)) as [[_ E3]|[_ E3]]; rewrite E3 in *; lia.
             (* *** apply H4, H5. *)
             (* *** apply H4, H5. *)
          ** intros y. destruct (le_gt_dec y (Nat.max start (list_max L) )); 
                       destruct (le_gt_dec (E_I (Nat.max start (list_max L) )) (E_I y) ); try (right; lia). 
             left. firstorder.
        * left. left. exists (Nat.max (list_max L) start). intros [y [H1 H2]]. apply n0.
          exists y. intuition. destruct (Max.max_spec start (list_max L)) as [[E1 ->]|[E1 ->]].
          ** destruct (list_max_cns L). 
            *** lia.   
            *** apply H4 in H3. lia.     
          ** lia. 
  Qed.


  Lemma HS_undec_help1 n start:
    (forall x, dec (HS x)) -> E_I start > n -> {x | ~ exists y, x < y /\ E_I y <= n} 
                      + {x | x > start /\ E_I x <= n}. 
  Proof.
    intros D E.
    apply (@HS_undec_help0 n start (E_I start + 1)) in D. destruct D. 
    - destruct s.
      + now left.
      + now right.
    - destruct s as (L & H1 & H2 & H3). 
      assert (incl (map E_I L) (seq (n+1) (E_I start))). 
      + intros y [x [I1 I2]] % in_map_iff. apply H3 in I2. 
        rewrite <- I1. apply in_seq. lia.
      + apply (pigeonhole_length _) in H. 
        * rewrite map_length, seq_length, H1 in H. lia.
        * intros x1 x2; decide (x1 = x2); eauto.
        * apply NoDup_map, H2. apply E_I_injective. 
    - exact E. 
  Qed.

  Lemma HS_undec_help2 n step:
    (forall x, dec (HS x)) -> {x | ~ exists y, x < y /\ E_I y <= n} 
                      + {L | length L = step /\ NoDup L /\ forall x, In x L -> E_I x <= n }.
  Proof.
    intros D. induction step. 
    - right. exists nil; intuition.
      + constructor.
    - destruct IHstep. 
      + now left.
      + destruct s as [L H]. destruct (E_I_first_n n (list_max L)). 
        destruct (@HS_undec_help1 n x D). 
        * apply a.
        * now left. 
        * destruct s as [x0 H1]. right. exists (x0::L). cbn; intuition. 
          constructor; intuition. apply list_max_in in H2. lia. 
  Qed.
     
  Lemma HS_undec_help n:
    (forall x, dec (HS x)) -> {x | ~ exists y, x < y /\ E_I y <= n}.
  Proof.
    intros D % (HS_undec_help2 n (n+2)).
    destruct D. 
    - exact s. 
    - destruct s as (L & H1 & H2 & H3). 
      assert (incl (map E_I L) (seq 0 (n+1))). 
      + intros y [x [I1 I2]] % in_map_iff. apply H3 in I2. 
        rewrite <- I1. apply in_seq. lia.
      + apply (pigeonhole_length _) in H. 
        * rewrite map_length, seq_length, H1 in H. lia.
        * intros x1 x2; decide (x1 = x2); eauto.
        * apply NoDup_map, H2. apply E_I_injective.    
  Qed.
 
  Lemma HS_red:
    decidable HS -> decidable I.
  Proof.
    intros [H] % decidable_iff.
    apply decidable_iff.
    constructor.
    intros n. destruct (HS_undec_help n H) as [x H1].
    decide (In n (map E_I (seq 0 (x+1)))) as [HI | HI].
    - apply in_map_iff in HI. left.
      apply E_I_enum. firstorder. 
    - right. intros [n0 E] % E_I_enum. destruct (le_gt_dec n0 x).
      + apply HI. apply in_map_iff. exists n0. intuition.
        apply in_seq. lia.
      + apply H1. exists n0. lia. 
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
        * intros [y H1]. apply H. exists y. intuition. 
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
    hyper_simple HS.
  Proof.
    repeat split.
    - apply HS_enumerable.
    - apply HS_co_infinite.
    - apply HS_no_majorize. 
  Qed.
     
End HS.
