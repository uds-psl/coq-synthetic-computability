Require Export SyntheticComputability.Axioms.EA.
Require Export SyntheticComputability.Shared.Pigeonhole.
Require Export SyntheticComputability.Shared.FinitenessFacts.
Require Export SyntheticComputability.Synthetic.reductions SyntheticComputability.Synthetic.truthtables.
Require Export SyntheticComputability.Synthetic.DecidabilityFacts SyntheticComputability.Synthetic.EnumerabilityFacts SyntheticComputability.Synthetic.SemiDecidabilityFacts.
Require Export SyntheticComputability.Shared.ListAutomation.
Require Export SyntheticComputability.ReducibilityDegrees.simple.
Require Export SyntheticComputability.Shared.embed_nat.
Require Export List Arith.

Import Assume_EA.

Export EmbedNatNotations.

Local Notation "q << p" := (forall x, q x -> p x) (at level 50).
 
Lemma proof_computation {X} (p : X -> Prop) f:
 enumerator f p -> (exists y, p y) 
  -> exists n y, f n = Some y.
Proof.
  intros E [y [n py] % E].
  eauto. 
Qed.

Definition mu_enum_NN_sig {X} (p : X -> Prop) f:
  enumerator f p -> ex p -> 
    {n | (exists x, f n = Some x) /\ 
      (forall n1, (exists x1, (f n1) = Some x1) -> n <= n1) }.
Proof.
  intros E H.
  assert (exists n x, f n = Some x) by exact (proof_computation p f E H).
  eapply mu_nat_dep_least in H0 as (? & ?).
  - exists x. firstorder. eapply H2. lia. eauto.
  - intros n. destruct (f n). 
    + left. eauto.
    + right. intros []. inversion H1.
Defined.

Definition mu_enum_NN {X} (p: X -> Prop) f E H : nat
:= proj1_sig (mu_enum_NN_sig p f E H).

Definition mu_enum_NN_spec {X} (p: X -> Prop) f E H 
:= proj2_sig (mu_enum_NN_sig p f E H).

Definition mu_enum_sig {X} (p : X -> Prop) f :
forall E H, {x | p x /\ Some x = f (mu_enum_NN p f E H)}.
Proof.
intros E H.
- destruct (f (mu_enum_NN p f E H)) eqn: H2.
  + exists x. 
    intuition. apply E. eauto.
  + exfalso. remember (mu_enum_NN_spec p f E H). destruct a as [[x a1] a2].
    unfold mu_enum_NN in H2. rewrite a1 in H2. discriminate.
Defined.

Definition mu_enum {X} (p: X -> Prop) f E H : X
:= proj1_sig (mu_enum_sig p f E H).

Definition mu_enum_spec {X} (p: X -> Prop) f E H 
:= proj2_sig (mu_enum_sig p f E H).

Definition wo_enum_sig {X} (p : X -> Prop) f:
  enumerator f p -> (exists x, p x) -> {x | p x}.
Proof.
  intros E H. destruct (mu_enum_sig p f E H).
  exists x. intuition.
Defined.

Lemma constant_mu_enum_NN {X} (p : X -> Prop) f E:
  forall H1 H2, mu_enum_NN p f E H1 = mu_enum_NN p f E H2.
Proof.
  intros H1 H2.
  set (W1:= mu_enum_NN_spec p f E H1). 
  set (W2:= mu_enum_NN_spec p f E H2).
  destruct W1 as [p1 L1], W2 as [p2 L2].
  specialize (L2 (mu_enum_NN p f E H1)).
  specialize (L1 (mu_enum_NN p f E H2)).
  apply L2 in p1. apply L1 in p2. 
  unfold mu_enum_NN in *. lia.
Qed.

Lemma mu_enum_agree {X} (p : X -> Prop) f E H:
  f (mu_enum_NN p f E H) = Some (mu_enum p f E H).
Proof.
  remember (mu_enum_spec p f E H). cbn in a. destruct a as [a1 a2].
  unfold mu_enum. rewrite a2. trivial.
Qed.

Lemma constant_mu_enum {X} (p : X -> Prop) f E:
  forall H1 H2, mu_enum p f E H1 = mu_enum p f E H2.
Proof.  
  intros H1 H2.
  assert 
    (Some (mu_enum p f E H1) = Some (mu_enum p f E H2)).
  - rewrite <- (mu_enum_agree p f E H1).
    rewrite <- (mu_enum_agree p f E H2).
    rewrite (constant_mu_enum_NN p f E H1 H2). 
    trivial.
  - inversion H. trivial. 
Qed. 

Section ComplToBound.

  Definition complToBound L b : list nat 
    := filter (fun x => Dec (~ In x L)) (seq 0 (S b)).

  Lemma complToBound_Bound L b :
    forall x, In x (complToBound L b) -> x <= b.
  Proof.
    intros x [H % in_seq ?] % in_filter_iff. lia.
  Qed.

  Lemma filter_length {X} f (l : list X) :
    length l = length (filter f l) + length (filter (fun x => (negb (f x))) l).
  Proof.
    induction l; cbn.
    - reflexivity.
    - destruct f; cbn; lia.
  Qed.      

  Lemma filter_NoDup {X} f (l : list X) :
    NoDup l -> NoDup (filter f l).
  Proof.
    induction 1; cbn.
    - econstructor.
    - destruct f; eauto. econstructor; auto.
      intros ? % in_filter_iff. firstorder.
  Qed.

  Lemma complToBound_length L b:
    length (complToBound L b) + length L >= S b.   
  Proof.
    rewrite <- (seq_length (S b) 0).
    erewrite filter_length with (l := seq 0 (S b)). 
    unfold complToBound.
    eapply plus_le_compat_l.
    generalize (seq_NoDup (S b) 0).
    generalize (seq 0 (S b)). clear.
    intros. erewrite filter_ext with (g := fun x => Dec (In x L)).
    2:{ intros a. destruct Dec; cbn; destruct Dec; firstorder congruence. }
    eapply NoDup_incl_length. now eapply filter_NoDup.
    clear. induction l; cbn.
    - firstorder.
    - destruct Dec; cbn. 2: eauto.
      intros ? [-> | ]; eauto.
  Qed.

  Lemma complToBound_NoDup L b:
    NoDup (complToBound L b).
  Proof.
    eapply filter_NoDup, seq_NoDup.
  Qed.

  Lemma firstn_In {X} (l : list X) n x : In x (firstn n l) -> In x l.
  Proof.
    induction n in x, l |- *; destruct l; cbn; firstorder.
  Qed.

  Lemma firstn_NoDup {X} (l : list X) n : NoDup l -> NoDup (firstn n l).
  Proof.
    induction 1 in n |- *; destruct n; cbn; try now econstructor.
    econstructor; eauto.
    now intros ? % firstn_In.
  Qed.

End ComplToBound. 

Section fix_ct.

  (* Assuming enumerator of semidecidable predicates W and its semidecidability *)

  (* Variable W : nat -> nat -> Prop.  *)
  Lemma es : forall p : nat -> Prop, semi_decidable p <-> exists c, forall x, W c x <-> p x.
  Proof.
    intros p. rewrite <- enum_iff, W_spec. firstorder.
  Qed.

  Variable W_SDec: nat * nat -> nat -> bool.
  Variable W_semidecider: semi_decider W_SDec (fun '(c,x) => W c x).

  Variable c_top : nat.
  Variable c_top_spec: forall x, W c_top x.

  (* Auxiliary Predicate C *)

  Definition C : (nat*nat) -> Prop
    := fun '(c,x) => W c x /\ x > 2*c.

  Lemma C_nonempty: 
    C (c_top, 1 + 2 * c_top).
  Proof.
    split.
    - apply c_top_spec.
    - lia.
  Qed.

  Definition C_SDec: (nat*nat) -> nat -> bool
    := fun '(c,x) n => andb (W_SDec (c,x) n) (2*c <? x).

  Lemma C_semidecider:
    semi_decider C_SDec C.
  Proof.
    intros [c x].
    split.
    - intros [Wcx E]. 
      apply (W_semidecider(c,x)) in Wcx as [n Wcx].
      exists n. 
      apply leb_correct_conv in E. unfold C_SDec. rewrite Nat.ltb_antisym, Wcx, E. firstorder.
    - intros [n Ccx]. 
      apply RelationClasses.eq_Symmetric, Bool.andb_true_eq in Ccx as [H1 H2].
      split.
      + apply (W_semidecider (c,x)). exists n. firstorder.
      + apply leb_complete_conv. 
        rewrite Nat.leb_antisym. 
        rewrite <- H2. firstorder.
  Qed.

  Definition iso_three_nat_func : nat -> (nat * nat) * nat
    := fun! ⟨n1, n2⟩ => (unembed n1, n2).
    
  Definition surjective {X} {Y} (f : X -> Y) := forall y, exists x, f x = y.

  Lemma iso_three_nat_func_spec:
    surjective iso_three_nat_func.
  Proof.
    intros [[n1 n2] n3].
    exists ⟨ ⟨n1,n2⟩, n3⟩.
    unfold iso_three_nat_func.
    now rewrite !embedP.
  Qed.  
(* 
  Definition C_Enum: nat -> nat * nat
    := enum_To_StrongenumF (semidec_To_enumF C_SDec iso_three_nat_func) (c_top, 1 + 2 * c_top).
 *)

  Lemma C_strong_enumerator:
    ∑ C_Enum, strong_enumerator C_Enum C.
  Proof.
    eexists.
    eapply enumerator_strong_enumerator with (x0 := (c_top, 1 + 2 * c_top)).
    - exact C_nonempty.
    - eapply semi_decider_enumerator. exact _. exact C_semidecider.
  Qed.

  Definition C_Enum := proj1_sig C_strong_enumerator.
  Definition C_enumerator : strong_enumerator C_Enum C := proj2_sig C_strong_enumerator.

  Definition DomC : nat -> Prop
    := fun c => exists x, C (c,x).

  Lemma DomC_nonempty: DomC c_top.
  Proof.
    exists (1+2*c_top).
    exact C_nonempty.
  Qed.

  Definition DomC_Enum : nat -> nat
    := fun n => fst (C_Enum n).

  Lemma DomC_enumerator:
    strong_enumerator DomC_Enum DomC.
  Proof.
    intros c; split; unfold DomC_Enum.
    - intros [x H]. apply C_enumerator in H as [n H]. 
      exists n. rewrite H. trivial.
    - intros [n H]. exists (snd (C_Enum n)). rewrite <- H.
      apply C_enumerator. exists n. apply surjective_pairing.   
  Qed.   
    
  Definition RangeC c : nat -> Prop
    := fun x => C(c,x).

  Definition RangeC_Enum c : nat -> option nat
    := fun n => match C_Enum n with (c1,x) => if c =? c1 then Some x else None end.

  Lemma RangeC_Enum_spec c:
    enumerator (RangeC_Enum c) (RangeC c).
  Proof.
    intros x. split.
    - intros Ccx. unfold RangeC in Ccx. apply C_enumerator in Ccx as [n Ccx].
      exists n. unfold RangeC_Enum. rewrite Ccx. 
      now rewrite Nat.eqb_refl.
    - intros [n H]. apply C_enumerator.
      exists n. unfold RangeC_Enum in H.
      destruct (C_Enum n) as [c1 x1]. 
      destruct (Nat.eqb_spec c c1).
      + rewrite e. now inversion H.
      + discriminate. 
  Qed.

  (* Definition of psi via recursive mu-operator for enumerable predicates *)

  Definition psi: forall c, DomC c -> nat .
  Proof.
    intros c H. 
    apply (mu_enum (fun x => C (c,x)) (RangeC_Enum c)).
    - apply RangeC_Enum_spec.
    - exact H.
  Defined.

  Lemma psi_spec c H:
     C (c,psi c H).
  Proof. 
    eapply (mu_enum_spec (fun x => C (c,x))).
  Qed.

  Lemma psi_spec1 c H:
    psi c H > 2*c.
  Proof.
    exact (proj2 (psi_spec c H)).
  Qed.

  Lemma psi_PI c H1 H2:
    psi c H1 = psi c H2.
  Proof.
    apply (constant_mu_enum (fun x => C (c, x)) (RangeC_Enum c)
    (RangeC_Enum_spec c) H1 H2).
  Qed.

  (* Definition of the simple predicate S as the range of psi *)

  Definition S : nat -> Prop 
    := fun x => exists c H, psi c H = x.

  (* S is semidecidable *)

  Definition DomC_proof n: DomC (DomC_Enum n).
  Proof.
    apply DomC_enumerator.
    eauto.
  Qed.

  Definition S_Enum : nat -> nat
    := fun n => let c := DomC_Enum n in 
                  let H := DomC_proof n in 
                     psi c H.

  Lemma S_enumerator:
    strong_enumerator S_Enum S.
  Proof.
    intros x.
    split.
    - intros [c [H E]].
      assert (exists n, DomC_Enum n = c) as [n H1]. 
      apply DomC_enumerator. exact H.
      exists n. unfold S_Enum. 
      revert E. revert H. rewrite <- H1. intros H E.
      rewrite <- E.
      exact (psi_PI (DomC_Enum n) (DomC_proof n) H).
    - intros [n H]. 
      unfold S_Enum in H.
      exists (DomC_Enum n).
      exists (DomC_proof n).
      exact H.
  Qed.  

  Corollary S_SemiDec:
    semi_decidable S.
  Proof.
    eapply enumerable_semi_decidable. eapply discrete_iff. econstructor. exact _.
    enough (strongly_enumerable S) as ? %  enumerable_strongly_enumerable_iff by tauto.
    exists S_Enum. exact S_enumerator.
  Qed.

  (* Complement of S contains no semidecidable, infinite subset *)

  Lemma S_No_S_Inf_Subset:
    forall (q: nat -> Prop), ~ exhaustible q -> semi_decidable q -> ~ (q << (compl S)).
  Proof.
    intros q Inf [c Se] % es H.
    apply Inf.
    exists (seq 0 (1+2*c)).
    intros x qx.
    assert (x <= 2*c). 
    - destruct (Nat.le_gt_cases x (2*c)). 
      + exact H0. 
      + exfalso. 
        assert (exists x, C (c,x)). 
        * exists x. split. apply Se, qx. exact H0.
        * assert (exists x0, q x0 /\ S x0) as [x0 [qx0 Sx0]].
          { exists (psi c H1). split.
            - apply Se. apply psi_spec.
            - exists c. exists H1. trivial.
          }
          apply (H x0 qx0), Sx0. 
    - apply in_seq. lia.
  Qed.


  (* Co-Infinity Proof of S *)

  Lemma DomC_pullback n L:
    (forall x, In x L -> S x /\ x <= 2 * n) -> forall x, In x L
      -> exists c H, psi c H = x /\ c < n.
  Proof. 
    intros H1 x [[c [H Sx]] E] % H1.
    exists c. exists H. intuition. rewrite <- Sx in E. 
    assert (psi c H > 2 * c) by apply psi_spec1.
    lia.
  Qed.

  Lemma DomC_pullback_list n L:
    NoDup L -> (forall x, In x L -> S x /\ x <= 2 * n) -> 
      exists (LC: list nat), NoDup LC /\ length LC = length L /\
        forall c, In c LC -> exists H, In (psi c H) L /\ c < n.
  Proof.
    intros ND Sub.
    induction L.
    - exists nil.
      intuition.
    - remember (DomC_pullback n (a::L) Sub a).
      assert (In a (a::L)) as H0 by intuition .
      apply e in H0 as [c0 [H0 [E1 E2]]].
      assert (NoDup L) by (inversion ND; intuition).
      apply IHL in H as [LC H].
      exists (c0::LC).
      intuition.
      + constructor. intros In. apply H3 in In as [H0' E]. 
        assert (a = psi c0 H0') by (rewrite <- E1; exact (psi_PI c0 H0 H0')).
        rewrite <- H2 in E. inversion ND. intuition. exact H1.
      + cbn. rewrite H. trivial.
      + destruct H2.
        * rewrite <- H2.  exists H0. rewrite E1. intuition.
        * apply H3 in H2 as [H4 E]. exists H4. intuition.
      + intros y In1. assert (In y (a::L)) by intuition.
        apply Sub in H1. exact H1.    
  Qed. 

  Lemma S_List_Bound n L:
    NoDup L -> (forall x, In x L -> S x /\ x <= 2 * n) 
      -> length L <= n.
  Proof.
    intros ND [LC H] % DomC_pullback_list; intuition.
    rewrite <- H.
    assert (incl LC (seq 0 n)).
    - intros c [_ [_ H3]] % H2. apply in_seq. lia.
    - apply pigeonhole_length in H1.
      + now rewrite seq_length in H1.
      + intros. decide (x1 = x2); tauto.
      + exact H0.
  Qed.  

  (* Listing of predicates up to a bound b *)

  Definition PredListTo p : list nat -> nat -> Prop
    := fun L b => forall x, In x L <-> p x /\ x <= b.

  Lemma PredListTo_spec {p L b}:
    PredListTo p L b -> forall x, In x L -> p x /\ x <= b.
  Proof.
    intros H x I % H.
    apply I.
  Qed.

  Lemma PredListTo_Bound {p L b}:
    PredListTo p L b -> forall x, In x L -> x <= b.
  Proof.
    intros H x I % H.
    apply I.
  Qed.

  Lemma NoDupBoundH {L} b:
    NoDup L -> (forall x, In x L -> x <= b) -> forall x, x > b -> NoDup (x::L).
  Proof.
    intros ND H x E.
    constructor.
    - intros H1 % H. lia.
    - exact ND.
  Qed. 

  Lemma PredNoDupListTo_NNExist p:
    forall b, ~~ exists L, PredListTo p L b /\ NoDup L.
  Proof.
    induction b; intros H.
    - ccase (p 0) as [H0 | H0]; apply H.
      + exists [0]. split; try split.
        * intros [E | E]; (try contradiction E).
          rewrite <- E. intuition.
        * intros E. assert (x = 0) by lia. 
          rewrite H1. intuition.
        * constructor; intuition; constructor. 
      + exists nil. split; try split.
        * contradiction.
        * intros E. assert (x = 0) by lia. 
          rewrite H1 in E. firstorder.
        * constructor.
    - apply IHb. intros [L H1].
      ccase (p (1 + b)) as [H0 | H0]; apply H.
      + exists ((1+ b) :: L). split; try split.
        * intros [E | E]; try (rewrite <- E; intuition). 
          apply H1 in E. intuition.
        * intros [E1 E2]. assert (x <= b \/ x = 1 + b) as [E | E] by lia. 
          ** right. apply H1. intuition.
          ** left. lia.
        * apply (NoDupBoundH b). 
          ** apply H1.
          ** intros x H3 % H1. lia.
          ** lia.
      + exists L. split; try split.
        * intros E % H1. intuition.
        * intros [E1 E2]. assert (x <= b \/ x = 1 + b) as [E | E] by lia. 
          ** apply H1. intuition.
          ** rewrite E in E1. firstorder.
        * apply H1. 
  Qed. 

  Lemma complToBound_compl p L b:
    PredListTo p L b -> PredListTo (compl p) (complToBound L b) b.
  Proof.
    intros H x. split. 
    - intros [H1 H1'] % in_filter_iff.
      destruct Dec; cbn in H1'; try congruence.
      enough (x <= b). 
      + intuition. intros npx. firstorder.
      + apply in_seq in H1. lia.
    - intros [H1 H2]. eapply in_filter_iff. split.
      + apply in_seq; lia.
      + destruct Dec; cbn; try tauto. exfalso. firstorder.
  Qed.

  (* Length of listings of S up to 2*n is bounded by n *)

  Lemma S_Listing:
    forall n, ~~ exists L, NoDup L /\ length L <= n /\ PredListTo S L (2*n).
  Proof.
    intros n H. apply (PredNoDupListTo_NNExist S (2*n)). 
    intros [L H1]. apply H. exists L; intuition.
    apply S_List_Bound. 
    - exact H2. 
    - apply H0. 
  Qed. 

  (* Weak Existence Infinite Criterion *)

  Lemma ComplS_Listing:
  forall (n: nat) ,~~ exists L, length L >= n /\ NoDup L  
                                /\ forall x, In x L -> ~ S x.
  Proof.
    intros n H.
    apply (S_Listing n). intros [L H1]. 
    apply H. exists (complToBound L (2*n)). repeat split.
    - remember (complToBound_length L (2*n)). lia. 
    - apply complToBound_NoDup.
    - intros x I % (complToBound_compl S); intuition.
  Qed. 

  Lemma S_coInfinite:
    ~ exhaustible (compl S).
  Proof.
    eapply weakly_unbounded_non_finite.
    intros n H. eapply ComplS_Listing with (n := n).
    intros (l & ? & ? & H2).
    eapply H.
    exists (firstn n l).
    repeat split.
    - rewrite firstn_length. lia.
    - now eapply firstn_NoDup.
    - intros ? ? % firstn_In. now eapply H2.
  Qed.

  (* S is a simple predicate *)

  Corollary S_simple:
    simple S.
  Proof.
    split.
    - eapply semi_decidable_enumerable; eauto. exact S_SemiDec.
    - split. 
      + exact S_coInfinite.
      + intros (? & ? % enumerable_semi_decidable & ? & ?); eauto.
        eapply S_No_S_Inf_Subset; eauto. 
  Qed.


End fix_ct.

Section S_Star.
  Import  Coq.Init.Nat. 


  Variable W_SDec: nat * nat -> nat -> bool.
  Variable W_semidecider: semi_decider W_SDec (fun '(c,x) => W c x).

  Variable c_top : nat.
  Variable c_top_spec: forall x, W c_top x.

  Definition S' : nat -> Prop 
    := S W_SDec W_semidecider c_top c_top_spec.

  (* Auxiliary List *)

  Definition S_Pow n : list nat 
    := seq (2^n - 1) (2^n).

  Lemma pow_pos n:
    2^n > n.
  Proof. 
    induction n; cbn; lia.
  Qed.

  Lemma pow_sum n:
    2 ^ n - 1 + 2 ^ n = 2 ^ (1 + n) - 1.
  Proof.
    induction n; cbn in *; lia.
  Qed.

  Lemma S_Pow_injective x n1 n2:
    In x (S_Pow n1) /\ In x (S_Pow n2) -> n1 = n2.
  Proof.
    intros [H1 H2]. 
    apply in_seq in H1. apply in_seq in H2. 
    assert (n1 = n2 \/ 1 + n1 <= n2 \/ 1 + n2 <= n1) by lia.
    destruct H as [H | [H | H]].
    - exact H.
    - assert (2 ^ (1 + n1) - 1 <= x).
      + enough (2 ^ (1 + n1) <= 2 ^ n2) by lia.
        apply Nat.pow_le_mono_r; lia. 
      + assert (2 ^ n1 - 1 + 2 ^ n1 = 2 ^ (1 + n1) - 1) by apply pow_sum.
        lia.
    - assert (2 ^ (1 + n2) - 1 <= x).
      + enough (2 ^ (1 + n2) <= 2 ^ n1) by lia.
        apply Nat.pow_le_mono_r; lia. 
      + assert (2 ^ n2 - 1 + 2 ^ n2 = 2 ^ (1 + n2) - 1) by apply pow_sum.
        lia.
  Qed.

  (* Definition S* *)

  Definition S_Star : nat -> Prop
    := fun x => S' x 
                  \/ exists n, (fun '(c,x0) => W c x0) (unembed n) 
                                /\ In x (S_Pow n).

  Definition S_Star_compl : nat -> Prop 
    := fun x => (compl S') x /\ ~ exists n, ((fun '(c,x0) => W c x0) (unembed n) 
                                              /\ In x (S_Pow n )).

  Lemma S_Star_comp_agree:
    forall x, (compl S_Star) x <-> S_Star_compl x.
  Proof. 
    intros x. unfold S_Star_compl,  S_Star, compl, not. now rewrite Decidable.not_or_iff.  
  Qed.


  (* S* is semidecidable *)

  Lemma S_Star_semidec:
    semi_decidable S_Star.
  Proof.   
    apply semi_decidable_or.
    - apply S_SemiDec.
    - eapply semi_decidable_ex.
      eapply semi_decidable_and.
      + exists (fun pa n => W_SDec (unembed (fst pa)) n). 
        intros [n0 x0]; specialize (W_semidecider (unembed n0)); firstorder.
      + apply decidable_semi_decidable. eapply dec_decidable.
        intros pa. exact _.
  Qed.

  (* Complement of S* contains no semidecidable, infinite subset *)

  Lemma S_Star_No_S_Inf_Subset:
    forall (q: nat -> Prop), ~ exhaustible q -> semi_decidable q -> ~ (q << (compl (S_Star))).
  Proof.
    intros q H1 H2 H3.
    eapply (S_No_S_Inf_Subset).
    - exact H1.
    - exact H2.
    - intros x qx % H3.  
      intros nSx. apply qx. left. exact nSx. 
  Qed. 

  (* Co-Infinite Proof of S* *)

  Lemma W_empty: exists c_bot, forall x, ~ W c_bot x.
  Proof.
    destruct (es (fun _ => False)) as [[c_bot]_].
    - exists (fun _ _ => false). red. firstorder congruence. congruence.
    - exists c_bot. firstorder.
  Qed.

  Lemma W_CoInfinite:
    ~ exhaustible (compl (fun '(c,x) => W c x)).
  Proof.   
    destruct W_empty as [c_bot H].
    eapply unbounded_non_finite.
    intros n.
    exists (map (fun x => (c_bot, x)) (seq 0 n)).
    repeat split.
    - now rewrite map_length, seq_length.
    - eapply NoDup_map. now intros ? ? [= ->]. eapply seq_NoDup.
    - intros [? ?] (? & [= <- <-] & ? % in_seq) % in_map_iff. eapply H.
  Qed.

  Lemma WNat_CoInfinite:
    ~ exhaustible (compl (fun n => (fun '(c,x) => W c x) (unembed n))).
  Proof.  
    destruct W_empty as [c_bot H].
    eapply unbounded_non_finite.
    intros n.
    exists (map (fun x => ⟨c_bot, x⟩) (seq 0 n)).
    repeat split.
    - now rewrite map_length, seq_length.
    - eapply NoDup_map. 2: eapply seq_NoDup. intros ? ? ? % (f_equal unembed).
      rewrite !embedP in H0. congruence.
    - intros x (? & <- & ? % in_seq) % in_map_iff. red. now rewrite embedP.
  Qed. 

  Lemma S_Pow_NotInS n:
    ~ Forall S' (S_Pow n). 
  Proof.
    intros H.
    assert (length (S_Pow n) <= 2^n - 1).
    - eapply S_List_Bound. 
      + apply seq_NoDup. 
      + intros x. split. 
        * revert H0. apply Forall_forall. exact H.
        * apply in_seq in H0. lia. 
    - unfold S_Pow in H0. rewrite seq_length in H0. clear H. 
      induction n; cbn in H0; lia.
  Qed.

  Lemma Not_Forall_2_WeakEx {X} (p: X -> Prop) L:
    (~ Forall p L) -> ~~ exists x, In x L /\ ~ p x.
  Proof.
    intros H1 H2.
    induction L. 
    - now apply H1.
    - ccase (p a) as [H | H].
      + apply IHL. 
        * contradict H1. now constructor.
        * contradict H2. destruct H2. exists x; firstorder.
      + apply H2. exists a. firstorder.
  Qed. 
   
  Lemma S_Pow_WeakEx_NotS n:
    ~~ exists x, In x (S_Pow n) /\ (compl S') x.
  Proof.
    apply Not_Forall_2_WeakEx, S_Pow_NotInS.
  Qed.

  Lemma S_Star_coInfinite:
    ~ exhaustible (compl S_Star).
  Proof.
    eapply non_finite_nat.
    intros n0. 
    assert (~ ~ (exists n : nat, n >= n0 + 1/\ compl (fun n : nat => let '(c, x) := unembed n in W c x) n)).
    - eapply non_finite_nat. apply WNat_CoInfinite. 
    - contradict H. intros [n H2].
      apply (S_Pow_WeakEx_NotS n). 
      intros [x [H3 H4]]. apply H.  
      exists x; split. 
      + apply in_seq in H3. enough (2 ^ n > n) by lia. apply pow_pos.
      + apply S_Star_comp_agree. 
        unfold S_Star_compl. split.
        * exact H4.
        * intros [n1 [H5 H6]].
          assert (n = n1) by now apply (S_Pow_injective x). 
          apply H2. now rewrite H0.
  Qed.

  (* S* is simple *)

  Corollary S_Star_simple:
    simple S_Star.
  Proof.
    split.
    - eapply semi_decidable_enumerable; eauto. exact S_Star_semidec.
    - split.
      + exact S_Star_coInfinite.
      + intros (? & ? % enumerable_semi_decidable & ? & ?); eauto.
        eapply S_Star_No_S_Inf_Subset; eauto.
  Qed.

  (* W truth-table reduces to S* *) 

  Lemma S_Star_split L:
    Forall S_Star L 
      -> Forall S' L \/ exists n, (fun '(c,x) => W c x) (unembed n) /\ exists x, In x L /\ In x (S_Pow n).
  Proof.
    induction 1.
    - left; constructor.
    - destruct IHForall.
      + destruct H. 
        * left; now constructor.
        * right. destruct H. 
          exists x0. intuition. 
          exists x; intuition.
      + right. destruct H1. 
        exists x0. intuition. destruct H3.   
        exists x1; intuition.
  Qed.

  Lemma Forall2_equiv {X} {Y} {p : X -> Prop} {q : Y -> Prop} l1 l2: 
    Forall2 (fun x y => q y <-> p x) l1 l2 ->
    Forall p l1 <-> Forall q l2.
  Proof.
    induction 1.
    - split; now econstructor.
    - split; intros H1; inv H1; econstructor; firstorder.
  Qed.

  Lemma Forall_map {X} {p : X -> Prop} l : 
    Forall (fun P => P) (map p l) <-> Forall p l.
  Proof.
    induction l; cbn.
    - split; econstructor.
    - split; intros H1; inv H1; econstructor; firstorder.
  Qed.

  Lemma tt_red_W_S_Star:
    (fun '(c,x) => W c x) ⪯ₜₜ S_Star. 
  Proof.
    unshelve eexists (fun '(c, x) => existT (let n := embed (c,x) in S_Pow n) (mk_tt (fun L => if (Forall_dec (fun b => b = true) _ L) then true else false))).
    1:{ intros b. cbn. decide (b = true); tauto. }
    1:{ refine (length (S_Pow ⟨c, x⟩)). }
    intros [c x] L. cbn.
    unfold reflects. intros H1. 
    rewrite eval_tt_mk_tt'.
    2:{ eapply list.Forall2_length in H1.
        now rewrite H1, map_length. }
    unshelve edestruct (Forall_dec (fun b => b = true)) as [H0 | H0].
    - intuition. 
      assert (Forall S_Star (S_Pow ⟨c,x⟩)). {
       eapply Forall2_equiv in H1.
       rewrite Forall_map in H1. now eapply H1. }
      clear H0. rename H2 into H0. 
      apply S_Star_split in H0 as [H0 | H0]. 
      + apply S_Pow_NotInS in H0. contradict H0. 
      + destruct H0 as [n [H0 [x0 H3]]]. 
        apply S_Pow_injective in H3.
        subst. now rewrite embedP in H0.
    - split; intros; try congruence.
      contradict H0.
      assert (Forall S_Star (S_Pow (embed (c,x)))). 
      * apply Forall_forall.
        intros x0 H3. right. 
        exists (embed (c, x)). rewrite embedP. intuition.
      * eapply Forall2_equiv. exact H1.
        now eapply Forall_map.
  Qed.  

End S_Star.

