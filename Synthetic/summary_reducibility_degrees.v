From Undecidability Require Import simple simple_construction hypersimple hypersimple_construction myhill MoreEnumerabilityFacts ReducibilityFacts.

Theorem Myhill_Isomorphism_Theorem :
  forall X : Set, discrete X -> enumerableᵗ X ->
  forall Y : Set, discrete Y -> enumerableᵗ Y ->
  forall p : X -> Prop, forall q : Y -> Prop,
      p ⪯₁ q -> q ⪯₁ p -> exists f g, reduces_m f p q /\ reduces_m g q p /\ forall x y, f (g y) = y /\ g (f x) = x.
Proof.
  intros X [dX HdX] [eX HeX] Y [dY HdY] [eY HeY] p q [f [f_inj Hf]] [g [g_inj Hg]].
  assert (inhabited (eq_dec X)) as [eq_dec_X]  by (eapply discrete_iff; firstorder).
  assert (inhabited (eq_dec Y)) as [eq_dec_Y]  by (eapply discrete_iff; firstorder).
  destruct (enumerator_retraction _ _ _ HdX HeX) as [IX HIX].
  destruct (enumerator_retraction _ _ _ HdY HeY) as [IY HIY].
  eexists _, _. repeat eapply conj.
  - unshelve eapply f'_red; eauto; firstorder. 
  - unshelve eapply g'_red; eauto; firstorder.
  - intros. split.
    + eapply f'_g'.
    + eapply g'_f'.
Qed.

Corollary Computational_Cantor_Bernstein :
  forall X : Set, discrete X -> enumerableᵗ X ->
  forall Y : Set, discrete Y -> enumerableᵗ Y ->
  forall f : X -> Y, (forall x1 x2, f x1 = f x2 -> x1 = x2) ->
  forall g : Y -> X, (forall y1 y2, g y1 = g y2 -> y1 = y2) ->
  exists (f' : X -> Y) (g' : Y -> X), forall x y, f' (g' y) = y /\ g' (f' x) = x.
Proof.
  intros X HX1 HX2 Y HY1 HY2 f Hf g Hg.
  destruct (@Myhill_Isomorphism_Theorem X HX1 HX2 Y HY1 HY2 (fun _ => True) (fun _ => True)) as (f' & g' & Hf' & Hg' & H).
  - exists f. firstorder.
  - exists g. firstorder.
  - exists f', g'. eapply H.
Qed.

Theorem Posts_problem_many_one :
  exists p : nat -> Prop, simple p /\ enumerable p /\ ~ decidable p /\ ~ uncurry W ⪯ₘ p.
Proof.
  assert (semi_decidable (uncurry W)) as [W_sdec H_sdec]. {
    eapply enumerable_semi_decidable. eapply discrete_prod; eapply discrete_nat.
    eapply enumerable_W.
  }
  destruct (do_EA (fun _ => True)) as [c_top H_top]. {
    eapply decidable_enumerable. 2:eauto. exists (fun _ => true). firstorder.
  } 
  eexists.
  split; [ | repeat eapply conj].
  - eapply S_simple; eauto. 
  - eapply S_simple; eauto.
  - eapply simple_undecidable. eapply S_simple; eauto.
  - intros H. eapply simple_m_incomplete. eapply S_simple; eauto. 
    intros q Hq.
    eapply red_m_transitive. eapply m_complete_W. eauto.
    eapply red_m_transitive with (q0 := uncurry W). eapply W_uncurry_red.
    exact H.
    Unshelve. all:eauto. firstorder.
Qed.

Corollary one_one_and_many_one_differ :
  exists p : nat * nat -> Prop, exists q : nat -> Prop, enumerable p /\ ~ decidable p /\ enumerable q /\ ~ decidable q /\ p ⪯ₘ q /\ ~ p ⪯₁ q.
Proof.
  assert (semi_decidable (uncurry W)) as [W_sdec H_sdec]. {
    eapply enumerable_semi_decidable. eapply discrete_prod; eapply discrete_nat.
    eapply enumerable_W.
  }
  destruct (do_EA (fun _ => True)) as [c_top H_top]. {
    eapply decidable_enumerable. 2:eauto. exists (fun _ => true). firstorder.
  } 
  epose (S := S W_sdec H_sdec c_top ltac:(abstract firstorder)).
  assert (H1 : enumerable S). { eapply S_simple; eauto. }
  assert (H2 : ~ decidable S). { eapply simple_undecidable. eapply S_simple; eauto. }
  assert (H3 : ((fun '(x,_) => S x) : nat * nat -> Prop) ⪯ₘ S). { exists (fun '(x,_) => x). now intros (x, _). }
  exists (fun '(x,_) => S x). exists S. repeat eapply conj.
  - eapply enumerable_red; eauto. 
  - intros ?. eapply red_m_transports in H.
    eapply H2. eassumption. exists (fun x => (x,0)). now intros x.
  - eauto.
  - eauto.
  - eauto.
  - intros ? % simple_no_cylinder. eapply H0. eapply S_simple; eauto. 
Qed.

Theorem Posts_problem_truth_table :
  exists p : nat -> Prop, hyper_simple p /\ enumerable p /\ ~ decidable p /\ ~ uncurry W ⪯ₜₜ p.
Proof.
  destruct (@generative_enumerable_strong _ (fun! ⟨n,m⟩ => W n m)) as [f Hf].
  - eapply discrete_nat.
  - eapply enumerable_red. eapply W_uncurry_red. eauto. eauto.
    eapply enumerable_W.
  - eapply generative_W.
  - unshelve epose proof (HS_hypersimple (I := (fun! ⟨n,m⟩ => W n m)) (E_I := f) _ _ _).
    + firstorder.
    + firstorder.
    + intros ? % decidable_complement % decidable_enumerable.
      eapply not_coenumerable. 5: eapply H0. eapply W_uncurry_red'. all: eauto.
      eapply W_not_enumerable.
    + eexists. split. eapply H. repeat eapply conj.
      * eapply H.
      * eapply (HS_undec (I := (fun! ⟨n,m⟩ => W n m)) (E_I := f)). firstorder. firstorder.
        intros ? % decidable_complement % decidable_enumerable.
        eapply not_coenumerable. 5: eapply H1. eapply W_uncurry_red'. all: eauto.
        eapply W_not_enumerable.
      * intros Htt. eapply H.
        edestruct tt_complete_exceeds as [g Hg % exceeds_majorizes]. 2:eauto.
        eapply red_tt_transitive. 2: eauto.
        eapply red_mo_tt, K0_red.
Qed.

Corollary many_one_truth_table_differ :
  exists p q : nat -> Prop, enumerable p /\ ~ decidable p /\ enumerable q /\ ~ decidable q /\ p ⪯ₜₜ q /\ ~ p ⪯ₘ q.
Proof.
  assert (semi_decidable (uncurry W)) as [W_sdec H_sdec]. {
    eapply enumerable_semi_decidable. eapply discrete_prod; eapply discrete_nat.
    eapply enumerable_W.
  }
  destruct (do_EA (fun _ => True)) as [c_top H_top]. {
    eapply decidable_enumerable. 2:eauto. exists (fun _ => true). firstorder.
  } 
  epose (S_Star := S_Star W_sdec H_sdec c_top ltac:(abstract firstorder)).
  assert (H1 : enumerable S_Star). { eapply S_Star_simple; eauto. }
  assert (H2 : ~ decidable S_Star). { eapply simple_undecidable. eapply S_Star_simple; eauto. }
  exists (fun! ⟨n,m⟩ => W n m), S_Star. repeat eapply conj.
  - eapply enumerable_red. eapply W_uncurry_red. eauto. eauto.
    eapply enumerable_W.
  - intros H. eapply red_m_transports in H. eapply H2; eassumption.
    eapply m_complete_W. eauto.
  - eauto.
  - eauto.
  - eapply red_tt_transitive. 2: eapply tt_red_W_S_Star.
    eapply red_mo_tt, W_uncurry_red.
  - intros H. eapply simple_m_incomplete.
    eapply S_Star_simple; eauto.
    intros ? ?. eapply red_m_transitive. 2: eapply H.
    eapply m_complete_W. eauto.
Qed.

Print Assumptions Myhill_Isomorphism_Theorem.
Print Assumptions Posts_problem_many_one.
Print Assumptions Posts_problem_truth_table.
