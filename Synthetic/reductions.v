From stdpp Require Import prelude.
Require Import ssreflect.

From SyntheticComputability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts MoreEnumerabilityFacts.
From SyntheticComputability.Synthetic Require Import truthtables.
From SyntheticComputability.Shared Require Import Dec FinitenessFacts.

Ltac inv H := inversion H; subst; clear H.
Definition LEM := forall P, P \/ ~ P.

(** * Reducibility *)

Definition reduces_m {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) :=
  forall x, P x <-> Q (f x).
Definition red_m {X Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists f : X -> Y, reduces_m f P Q.
Notation "P ⪯ₘ Q" := (red_m P Q) (at level 50).
Notation "p ≡ₘ q" := (p ⪯ₘ q /\ q ⪯ₘ p) (at level 50).

Definition reduces_o {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) :=
  Inj (=) (=) f /\ reduces_m f P Q. 
Definition red_o {X} {Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists f : X -> Y, reduces_o f P Q.
Notation "P ⪯₁ Q" := (red_o P Q) (at level 50).
Notation "p ≡₁ q" := (p ⪯₁ q /\ q ⪯₁ p) (at level 50).

Definition reduces_tt {X} {Y} (f : X -> {qs : list Y & truthtable}) (P : X -> Prop) (Q : Y -> Prop) := 
  forall x, forall L, Forall2 reflects L (map Q (projT1 (f x))) -> reflects (eval_tt (projT2 (f x)) L) (P x).

Definition red_tt {X} {Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists f, 
    reduces_tt f P Q.
Notation "P ⪯ₜₜ Q" := (red_tt P Q) (at level 50).

Definition reduces_tTuring {X} {Y} (f : (Y -> bool) -> (X -> bool)) (P : X -> Prop) (Q : Y -> Prop) :=
  forall d, decider d Q -> decider (f d) P.
Definition red_tTuring {X} {Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists f : (Y -> bool) -> (X -> bool),
    reduces_tTuring f P Q.
Notation "P ⪯ₜᴛ Q" := (red_tTuring P Q) (at level 50).

(** ** Many-one reducibility *)

Instance red_m_reflexive {X} : Reflexive (@red_m X X).
Proof.
  exists (fun x => x). firstorder.
Qed.

Lemma red_m_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ₘ q -> q ⪯ₘ r -> p ⪯ₘ r.
Proof.
  move => [f Hf] [g Hg].
  exists (g ∘ f). firstorder.
Qed.

Lemma red_m_transports {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₘ q -> decidable q -> decidable p.
Proof.
  move => [f Hf] [d Hd].
  exists (d ∘ f). firstorder.
Qed.

Definition compl {X} (p : X -> Prop) := fun x => ~ p x.

Lemma red_m_complement {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₘ q -> compl p ⪯ₘ compl q.
Proof.
  firstorder.
Qed.

Lemma red_m_compl_compl_LEM :
  (forall X (p : X -> Prop), p ⪯ₘ compl (compl p)) <-> LEM.
Proof.
  split.
  - move => H P.
    assert (forall P : Prop, ~~ P -> P). {
      move => Q.
      destruct (H unit (fun _ => Q)) as [f Hf % (fun Hf => Hf tt)].
      eapply Hf.
    }
    eapply H0. tauto.
  - intros H X p.
    exists (fun x => x). intros x. specialize (H (p x)). cbv. tauto.
Qed.

Lemma red_m_compl_compl_LEM_2 :
  (forall X (p : X -> Prop), compl (compl p) ⪯ₘ p) <-> LEM.
Proof.
  split.
  - move => H P.
    assert (forall P : Prop, ~~ P -> P). {
      move => Q.
      destruct (H unit (fun _ => Q)) as [f Hf % (fun Hf => Hf tt)].
      eapply Hf.
    }
    eapply H0. tauto.
  - intros H X p.
    exists (fun x => x). intros x. specialize (H (p x)). cbv. tauto.
Qed.

Lemma red_m_compl_compl_LEM_3 :
  (forall X Y (p : X -> Prop) (q : Y -> Prop), compl p ⪯ₘ compl q -> p ⪯ₘ q) <-> LEM.
Proof.
  split.
  - move => H.
    rewrite - red_m_compl_compl_LEM.
    move => *.
    eapply H. 
    exists (fun x => x). firstorder.
  - intros H X Y p q [f Hf]. exists f.
    intros x. specialize (Hf x).
    split.
    + intros Hx. destruct (H (q (f x))) as [H0 | H0]; firstorder.
    + intros Hx. destruct (H (p x)) as [H0 | H0]; firstorder. 
Qed.

Lemma red_m_inverse {X Y} p q (f : X -> Y) g :
  reduces_m f p q -> (forall y, f (g y) = y) -> reduces_m g q p.
Proof.
  intros Hf Hfg y.
  now rewrite Hf Hfg.
Qed.

Section upper_semi_lattice.

  Context {X Y : Prop}.
  Variables (p : X -> Prop) (q : Y -> Prop).

  Definition join : X + Y -> Prop := fun z => match z with inl x => p x | inr y => q y end.

  Lemma red_m_join_p :
    p ⪯ₘ join.
  Proof.
    exists inl. firstorder.
  Qed.

  Lemma red_m_join_q :
    q ⪯ₘ join.
  Proof.
    exists inr. firstorder.
  Qed.

  Lemma red_m_join_least {Z} (r : Z -> Prop) :
    p ⪯ₘ r -> q ⪯ₘ r -> join ⪯ₘ r.
  Proof.
    move => [f Hf] [g Hg].
    exists (fun z => match z with inl x => f x | inr y => g y end).
    move => []; firstorder.
  Qed.

End upper_semi_lattice.

Lemma red_m_decidable_nontriv {X Y} {p : X -> Prop} {q : Y -> Prop} :
  decidable p -> (exists y1, q y1) -> (exists y2, ~ q y2) -> p ⪯ₘ q.
Proof.
  intros [f H] [y1 H1] [y2 H2].
  exists (fun x => if f x then y1 else y2).
  move => x. specialize (H x). destruct (f x); firstorder congruence.
Qed.

Definition stable {X} (p : X -> Prop) := forall x, ~~ p x -> p x.

Lemma red_m_transports_stable {X Y} {p : X -> Prop} {q : Y -> Prop} :
  stable q -> p ⪯ₘ q -> stable p.
Proof.
  move => Hp [f Hf] y Hy.
  eapply Hf, Hp.
  now rewrite <- (Hf y).
Qed.

Definition K (f : nat -> bool) := exists n, f n = true.

Lemma semi_decidable_red_K_iff {X} {p : X -> Prop} :
  semi_decidable p <-> p ⪯ₘ K.
Proof.
  reflexivity.
Qed.

(** ** One-one reducibility *)

Instance red_1_reflexive {X} : Reflexive (@red_o X X).
Proof.
  exists (fun x => x). firstorder.
Qed.

Lemma red_1_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯₁ q -> q ⪯₁ r -> p ⪯₁ r.
Proof.
  move => [f [inj_f Hf]] [g [inj_g Hg]].
  exists (g ∘ f). firstorder.
Qed.

Lemma red_1_transports {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯₁ q -> decidable q -> decidable p.
Proof.
  move => [f [inj_f Hf]] [d Hd].
  exists (d ∘ f). firstorder.
Qed.

Lemma red_oo_mm {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯₁ q -> p ⪯ₘ q.
Proof.
  firstorder.
Qed.

Lemma red_m_nat_0 :
  (fun x => x <> 0) ⪯ₘ (fun x => x = 0).
Proof.
  exists (fun x => if x is 0 then 1 else 0). move => x.
  destruct x; cbn; firstorder congruence.
Qed.

Lemma not_red_o_nat_0 :
  ~ (fun x => x <> 0) ⪯₁ (fun x => x = 0).
Proof.
  intros [f [inj Hf]].
  pose proof (Hf 1) as H1.
  pose proof (Hf 2) as H2. 
  assert (f 1 = f 2); firstorder congruence.
Qed.

Tactic Notation "red_transitivity" open_constr(P) :=
  match goal with
  | [ |- ?p ⪯₁ ?q ] => eapply (red_1_transitive P)
  | [ |- ?p ⪯ₘ ?q ] => eapply (red_m_transitive P)
  end.

Section characterisation_mm_in_oo.

  Definition full (X : Type) := fun x : X => True.

  Notation "p × q" := (fun '(x,y) => p x /\ q y) (at level 45).
  
  Lemma char_1 {X} {Y} {y0 : Y} {p : X -> Prop} :
    p ⪯₁ p × full Y.
  Proof.
    exists (fun x => (x,y0)). firstorder congruence.
  Qed.

  Lemma char_2 {X} {p : X -> Prop} {Y} :
    p × full Y ⪯ₘ p.
  Proof.
    exists fst. move => []. firstorder.
  Qed.

  Lemma char_3 {X Y Z} {embed : Y -> Z} {q : Y -> Prop} {p : X -> Prop} :
    Inj (=) (=) embed ->
    q ⪯ₘ p × full Z -> q ⪯₁ p × full Z.
  Proof.
    move => Hembed [f Hf].
    exists (fun y => (fst (f y), embed y)).
    split.
    - now move => y1 y2 [] H1 / Hembed.
    - move => y. rewrite Hf. destruct (f y); intuition.
  Qed.

  Lemma red_o_max {X} {Y} {Z} {p : X -> Prop} {q : Y -> Prop} {z0 : Z}  (embed : Y -> Z)  :
    Inj (=) (=) embed ->
    q ⪯ₘ p -> p ⪯₁ q -> q ⪯₁ p × full Z.
  Proof.
    move => Hinj Hmo Hoo.
    eapply (char_3 Hinj).
    red_transitivity p. eassumption.
    eapply red_oo_mm.
    eapply (char_1 (y0 := z0)).
  Qed.

  Lemma char_mm_oo {X Y Z} {embed : Y * Z -> Z} {q : Y -> Prop} {p : X -> Prop} {z0 : Z} :
    Inj (=) (=) embed ->
    q ⪯ₘ p <-> q × full Z ⪯₁ p × full Z.
  Proof.
    move => Hpair.
    split.
    - move => H.
      eapply (char_3 Hpair).
      red_transitivity q. eapply char_2.
      red_transitivity p. eassumption.
      eapply red_oo_mm. eapply (char_1 (y0 := z0)).
    - move => ?.
      red_transitivity (q × full Z). eapply red_oo_mm, (char_1 (y0 := z0)).
      red_transitivity (p × full Z). now eapply red_oo_mm.
      eapply char_2.
  Qed.

End characterisation_mm_in_oo.

(** ** Truth-table reducibility  *)

Local Notation "( a ,, b )" := (existT a b).
Local Notation "( a ).1" := (projT1 a).
Local Notation "( a ).2" := (projT2 a).

Instance red_tt_reflexive {X} : Reflexive (@red_tt X X).
Proof.
  move => p.
  eexists (fun x => ([x],, @mk_tt (fun L => match L with [b] => b | _ => true end ) _)).
  move => x L H. cbn in *. 
  inv H. inv H4. rewrite eval_tt_mk_tt'. cbn. reflexivity.
  eassumption.
Qed.

Lemma red_tt_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ₜₜ q -> q ⪯ₜₜ r -> p ⪯ₜₜ r.
Proof.
  move => [f Hf] [g Hg].
  eexists (fun x => (flat_map (fun y => (g y).1) (f x).1,,
                  mk_tt (fun L =>
                  eval_tt (f x).2 ((fix rec L1 L2 :=
                             match L1 with
                             | [] => []
                             | y :: L1  => let l := (length ((g y).1)) in eval_tt (g y).2 (take l L2) :: rec L1 (skipn l L2)
                           end) (f x).1 L)
          ) _)). cbn in *.
  move => x L H. cbn.
  setoid_rewrite eval_tt_mk_tt'. 
  2:{
    cbn in *. eapply Forall2_length in H.
    now rewrite H map_length.
  }
  eapply Hf.
  destruct (f x) as [fx tt]. cbn in *.
  induction fx in H, L |- *; cbn in *.
  - econstructor.
  - econstructor.
    + eapply Hg. eapply Forall2_take with (n := length (g a).1) in H.
      rewrite map_app in H.
      erewrite <- map_length with (f := r) in H at 2.
      now rewrite take_app in H.
    + eapply IHfx. eapply Forall2_drop with (n := length (g a).1) in H.
      erewrite <- map_length with (f := r) in H at 2.
      rewrite map_app in H.
      now rewrite drop_app in H.
Qed.

Lemma red_tt_transports {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₜₜ q -> decidable q -> decidable p.
Proof.
  move => [f Hf] [d Hd].
  exists (fun x => eval_tt (f x).2 (map d (f x).1)).
  move => x. eapply Hf.
  induction ((f x).1). econstructor.
  econstructor; eauto.
Qed.

Lemma red_mo_tt {X Y} (p : X -> Prop) (q : Y -> Prop) : p ⪯ₘ q -> p ⪯ₜₜ q.
Proof.
  intros [f Hf].
  exists (fun x => ([f x],, mk_tt (fun L => if L is [b] then b else true) 1)).
  intros ? ? H. inversion H. subst.
  destruct l; inv H4. rewrite eval_tt_mk_tt'; cbn in *.
  lia. firstorder.
Qed.

Lemma red_tt_complement {X} {p : X -> Prop} : compl p ⪯ₜₜ p. 
Proof.
  eexists (fun x => ([x],, mk_tt (fun L => match L with b :: _ => negb b | _ => true end) _ )).
  cbn. move => ? ? H. cbn in H. inv H. inv H4.
  rewrite eval_tt_mk_tt'; cbn; try reflexivity.
  destruct x; cbn; firstorder congruence.
Qed.

Lemma red_tt_not_m :
  (fun _ : unit => True) ⪯ₜₜ (fun _ : unit => False) /\
  ~ (fun _ : unit => True) ⪯ₘ (fun _ : unit => False).
Proof.
  split.
  - eexists (fun _ => ([],, @mk_tt (fun _ => true) _)). red. firstorder.
    inv H. now rewrite eval_tt_mk_tt'. 
  - move => [f] / (fun Hf => Hf tt). tauto.
Qed.

Section upper_semi_lattice.

  Context {X Y : Prop}.
  Variables (p : X -> Prop) (q : Y -> Prop).

  Lemma red_tt_join_p :
    p ⪯ₜₜ join p q.
  Proof.
    eexists (fun x => ([inl x],, @mk_tt (fun L => if L is [b] then b else true) _)).
    move => x L H. cbn in *.
    inv H. inv H4. now rewrite eval_tt_mk_tt'; cbn.
  Qed.

  Lemma red_tt_join_q :
    q ⪯ₜₜ join p q.
  Proof.
    eexists (fun y => ([inr y],, mk_tt (fun L => if L is [b] then b else true) _)).
    move => x L H. cbn in *.
    inv H. inv H4. now rewrite eval_tt_mk_tt'; cbn.
  Qed.

  Lemma red_tt_join_least {Z} (r : Z -> Prop) :
    p ⪯ₜₜ r -> q ⪯ₜₜ r -> join p q ⪯ₜₜ r.
  Proof.
    move => [f Hf] [g Hg].
    exists (fun z => match z with inl x => f x | inr y => g y end).
    move => []; firstorder.
  Qed.

End upper_semi_lattice.

Lemma red_tt_decidable {X Y} {p : X -> Prop} {q : Y -> Prop} :
  decidable p -> p ⪯ₜₜ q.
Proof.
  intros [f H].
  eexists (fun x => ([],, mk_tt (fun _ => f x) _)).
  move => x L HL. inv HL.
  rewrite eval_tt_mk_tt'. reflexivity. firstorder. 
Qed.

Definition tt_conds {X} (p : X -> Prop) := fun '(qus,,tb) => forall asw, Forall2 reflects asw (map p qus) -> eval_tt tb asw = true.
Notation "q 'ᵗᵗ'" := (tt_conds q) (at level 10).

Lemma tt_char_1 {X} {p : X -> Prop} :
  compl (compl p) ⪯₁ p ᵗᵗ.
Proof.
  eexists (fun x => ([x],, @mk_tt (fun L => if L is [b] then b else false) _)).
  split. now firstorder congruence.
  cbn. move => x. split.
  - move => H L HF. inv HF. inv H4.
    rewrite eval_tt_mk_tt'.
    + cbn. reflexivity.
    + destruct x0; firstorder congruence.
  - move => H H1. specialize (H [false]). cbn in H.
    enough (false = true) by congruence. apply H.
    econstructor. firstorder congruence. econstructor.
Qed.

Lemma p_tt_conds {X} {p : X -> Prop} :
  stable p ->
  p ⪯₁ tt_conds p.
Proof.
  move => Hs.
  eexists (fun x => ([x],, mk_tt (fun L => if L is [b] then b else true) _)). split. 
  now firstorder congruence.
  move => x. split.
  - move => H asw Hasw. inv Hasw. inv H4.
    rewrite eval_tt_mk_tt'; cbn; firstorder.
  - move => H. cbn in H. eapply Hs. move => Hp.
    specialize (H [false]). cbn in H.
    enough (false = true) by congruence.
    eapply H. econstructor. 1:firstorder congruence. econstructor.
Qed.

Lemma Forall2_inj_left {X Y} (P : X -> Y -> Prop) L1 L2 L3 :
  (forall x1 x2 y, P x1 y -> P x2 y -> x1 = x2) ->
  Forall2 P L1 L3 -> Forall2 P L2 L3 -> L1 = L2.
Proof.
  move => H HL1 HL2.
  induction HL1 in L2, HL2 |- *.
  - now inv HL2. 
  - inv HL2. f_equal; eauto.
Qed.

Lemma conds_tt_p {X} {p : X -> Prop} {x0 : X} :
  tt_conds p ⪯ₜₜ p.
Proof.
  exists (fun x => x). move => [] qus tb L HL. cbn in *.
  split.
  - firstorder.
  - move => H asw /Forall2_inj_left E.
    erewrite E; try eassumption.
    move => b1 b2 P Hb1 Hb2.
    destruct b1, b2; firstorder.
Qed.

Lemma not_not_Forall2_total {X} {Y} (P : X -> Y -> Prop) :
  (forall y, ~~ exists x, P x y) ->
  forall L2, ~~ exists L1, Forall2 P L1 L2.
Proof.
  move => HP L2. induction L2.
  - move => H1. apply H1. exists []. econstructor.
  - move => H1. apply (HP a). move => [x Hx].
    apply IHL2. move => [L1 IH].
    apply H1. exists (x :: L1). eauto.
Qed.

Lemma tt_make_inj {X} {Y} (q : Y -> Prop) (p : X -> Prop) (g : X -> Y) :
  Inj (=) (=) g ->
  p ⪯ₜₜ q -> exists f, reduces_tt f p q  /\ Inj (=) (=) f.
Proof.
  intros Hg [f Hf].
  eexists (fun n => (g n :: (f n).1,, mk_tt (fun l => if l is x :: l then eval_tt (f n).2 l else false) _)).
  split.
  - intros n L H. cbn in *.
    inv H. rewrite eval_tt_mk_tt'.
    + cbn. f_equal. eapply Forall2_length in H4.
      rewrite map_length in H4. exact H4.
    + eapply Hf. eassumption.
  - intros x y. intros [=].
    now eapply Hg.
Qed.

Lemma tt_conds_1 {X} {p : X -> Prop} {Y} {q : Y -> Prop} {x0 : X} (g : Y -> X) :
  stable q -> Inj (=) (=) g ->
  q ⪯ₜₜ p -> q ⪯₁ tt_conds p.
Proof.
  move => Hsq Hg H1.
  eapply tt_make_inj in H1 as [f [H1 Hinj]]. exists f.
  split. eassumption.
  move => x. specialize (H1 x).
  destruct (f x) as (qus, tb); cbn.
  split.
  - move => Hx asw Hasw. cbn in *.
    specialize (H1 _ Hasw). firstorder.
  - move => Hasw. cbn in *.
    eapply Hsq. move => Hq.
    eapply not_not_Forall2_total with (L2 := map p qus) (P := reflects).
    + move => P H2. assert (H0 : ~~ (P \/ ~P)) by tauto. apply H0. move => [] H3.
      apply H2. exists true. firstorder. apply H2. exists false. firstorder congruence.
    + move => [L HL]. specialize (Hasw _ HL). specialize (H1 _ HL). firstorder.
  - eassumption.
Qed.

Lemma red_m_stable {X} {p : X -> Prop} {Y} {q : Y -> Prop} :
  p ⪯ₘ q -> stable q -> stable p.
Proof.
  move => [f Hf] Hq x Hx.
  apply Hf, Hq. firstorder.
Qed.

Lemma redtt_char_as_redo {X} {p : X -> Prop} {Y} {q : Y -> Prop} {x0 : X} {y0 : Y} (g : {qus : list X & truthtables.truthtable } → Y) :
  Inj (=) (=) g ->
  stable p ->
  p ⪯ₜₜ q <-> tt_conds p ⪯₁ tt_conds q.
Proof.
  move => Hg Hsp.
  split.
  - move => H.
    eapply (tt_conds_1 (x0 := y0)). {
      clear.
      move => [qus tb] H L HL. destruct (eval_tt tb L) eqn:E. reflexivity. exfalso.
      contradiction H. move => H1. eapply H1 in HL.
      congruence.
    }
    {
      exact Hg.
    }
    apply (red_tt_transitive p); try eassumption.
    eapply (conds_tt_p (x0 := x0)).
  - move => H.
    apply (red_tt_transitive (tt_conds p)). now eapply red_mo_tt, red_oo_mm, p_tt_conds. 
    apply (red_tt_transitive (tt_conds q)). now eapply red_mo_tt, red_oo_mm.
    eapply (conds_tt_p (x0 := y0)).
Qed.

Lemma enumerable_truthtable :
  enumerableᵗ {qus : list nat & truthtables.truthtable}.
Proof.
  eapply enumerator_enumerable.
  eapply enumeratorᵗ_dep_prod. exact _.
  intros. unfold truthtables.truthtable. exact _.
Qed.

Lemma eq_dec_truthtable :
  eq_dec {qus : list nat & truthtables.truthtable}.
Proof.
  clear. intros [l1 t1] [l2 t2]. red.
  decide (l1 = l2).
  * decide (t1 = t2).
    -- left. subst. f_equal.
    -- right. inversion 1. eauto.
  * right. inversion 1. eauto.
Qed.

Lemma generative_truthtable : generative (fun _ : {_ : list nat & truthtables.truthtable} => True).
Proof.
  eapply unbounded_generative. 
  - intros x1 x2; destruct (eq_dec_truthtable x1 x2); firstorder congruence.
  - eapply dedekind_infinite_unbounded. unshelve eexists.
    + intros n. exists (repeat 0 n). exact [].
    + intros. split; eauto. intros ? [= H0 % (f_equal length)].
      now rewrite !repeat_length in H0.
Qed.

Lemma redtt_char_as_redo_nat {p q : nat -> Prop} :
  stable p -> 
  p ⪯ₜₜ q <-> tt_conds p ⪯₁ tt_conds q.
Proof.
  destruct enumerable_truthtable as [f Hf].
  unshelve eapply redtt_char_as_redo.
  - exact 0.
  - exact 0.
  - intros x. eapply (G (X := {qus : list nat & truthtables.truthtable}) (p := fun _ => True)).
    + split. intros. eapply Hf. eauto.
    + eapply eq_dec_truthtable.
    + eapply generative_truthtable.
    + exact x.
    + econstructor.
  - intros x1 x2 H.
    erewrite <- FG with (x := x1).
    setoid_rewrite H. eapply FG.
Qed.

(** ** Total Turing reducibility  *)

Instance red_tT_reflexive {X} : Reflexive (@red_tTuring X X).
Proof.
  move => p.
  exists (fun d => d). firstorder.
Qed.

Lemma red_tT_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ₜᴛ q -> q ⪯ₜᴛ r -> p ⪯ₜᴛ r.
Proof.
  move => [f Hf] [g Hg].
  exists (fun h x => f (g h) x).
  firstorder.
Qed.

Lemma red_tT_transports {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₜᴛ q -> decidable q -> decidable p.
Proof.
  move => [f Hf] [d Hd].
  exists (f d). firstorder.
Qed.

Lemma red_tt_tTuring {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₜₜ q -> p ⪯ₜᴛ q.
Proof.
  move => [r H].
  pose (o x := projT1 (r x)).  pose (f x := eval_tt (projT2 (r x))).
  exists (fun g x => f x (map g (o x))).
  move => ? ? x. eapply H. subst o f. cbn.
  induction (r x).1; econstructor; eauto.
Qed.

Section upper_semi_lattice.

  Context {X Y : Prop}.
  Variables (p : X -> Prop) (q : Y -> Prop).

  Lemma red_tT_join_p :
    p ⪯ₜᴛ join p q.
  Proof.
    exists (fun d x => d (inl x)). firstorder.
  Qed.

  Lemma red_tT_join_q :
    q ⪯ₜᴛ join p q.
  Proof.
    exists (fun d y => d (inr y)). firstorder.
  Qed.

  Lemma red_tT_join_least {Z} (r : Z -> Prop) :
    p ⪯ₜᴛ r -> q ⪯ₜᴛ r -> join p q ⪯ₜᴛ r.
  Proof.
    move => [f Hf] [g Hg].
    exists (fun d z => match z with inl x => f d x | inr y => g d y end).
    move => d Hd []; firstorder.
  Qed.

End upper_semi_lattice.
