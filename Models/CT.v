Require Import Undecidability.L.Datatypes.LNat.
Require Import Undecidability.L.Datatypes.List.List_in Undecidability.L.Datatypes.List.List_basics.
From SyntheticComputability Require Import Unenc.
Require Import SyntheticComputability.Shared.ListAutomation.
Require Import SyntheticComputability.Shared.embed_nat.

Require Import Undecidability.L.Datatypes.List.List_extra Undecidability.L.Datatypes.LProd.
Require Import Undecidability.L.Datatypes.LTerm Undecidability.L.Functions.Eval.

Import ListNotations ListAutomationNotations EmbedNatNotations.

Definition L_nat := (fix f n := match n with 0 => [0] | S n0 => f n0 ++ [S n0] end).

Instance L_T_nat_computable : computable L_nat.
Proof.
  unfold L_nat. cbn.
  extract.
Qed.

Fixpoint list_enumerator_term (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => list_enumerator_term n ++ [var m | m ∈ L_nat n] ++ [ lam s | s ∈ list_enumerator_term n ] ++ [ L.app s t | (s,t) ∈ (list_enumerator_term n × list_enumerator_term n) ]
  end.

Definition app' '(s,t) := L.app s t.

Instance app'_computable : computable app'.
Proof.
  extract.
Qed.  

Instance list_enumerator_term_computable : computable list_enumerator_term.
Proof.
  change (computable (fix FFF (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => FFF n
           ++ map var (L_nat n) 
           ++ map lam (FFF n) 
           ++ map app' (list_prod (FFF n) (FFF n))
  end)). extract.
Qed.

Definition unembed' := (fix F (k : nat) := 
  match k with 0 => (0,0) | S n => match fst (F n) with 0 => (S (snd (F n)), 0) | S x => (x, S (snd (F n))) end end).

Instance unembed_computable : computable unembed.
Proof.
  eapply computableExt with (x := unembed'). 2:extract.
  intros n. cbn. induction n; cbn.
  - reflexivity.
  - fold (unembed n). rewrite IHn. now destruct (unembed n).
Qed.

(* Definition unembed' := (fix F (k : nat) :=  *)
(*                           match k with 0 => (0,0) | S n => match fst (F n) with 0 => (S (snd (F n)), 0) | S x => (x, S (snd (F n))) end end). *)

Fixpoint sum n : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + sum n'
  end.

Definition encode '(x, y) : nat :=
  y + sum (y + x).

Instance sum_computable : computable sum.
Proof.
  extract.
Qed.

Instance embed_computable : computable embed.
Proof.
  change (computable encode). extract.
Qed.

Definition enum_term := (fun! ⟨n,m⟩ => nth_error (list_enumerator_term n) m).

(* Instance enum_term_computable : computable enum_term. *)
(* Proof. *)
(*   extract. *)
(* Qed.     *)

Definition enum_closed n :=
  match enum_term n with Some t =>
                         if bound_dec 0 t then Some t else None | _ => None end.

Lemma enum_closed_proc n t :
  enum_closed n = Some t -> closed t.
Proof.
  unfold enum_closed. destruct enum_term as [|]; try congruence.
  destruct bound_dec; try congruence.
  intros [= <-]. eapply closed_dcl in b. firstorder.
Qed.

Definition T_L (c : nat) (x : nat) (n : nat) :=
   match enum_closed c with
   | Some t => match eva n (L.app t (enc x)) with
               | Some t => nat_unenc t
               | None => None
               end
   | None => None
   end.

(* Instance T_L_computable : computable T_L. *)
(* Proof. *)
(*   extract. *)
(* Qed. *)

Require Import SyntheticComputability.Axioms.Equivalence.
Require Import Undecidability.L.Util.L_facts SyntheticComputability.Models.Seval.
Require Import SyntheticComputability.Synthetic.ListEnumerabilityFacts SyntheticComputability.Synthetic.EnumerabilityFacts SyntheticComputability.Synthetic.DecidabilityFacts.
Require Import SyntheticComputability.Shared.ListAutomation Undecidability.Shared.Dec.

Lemma list_enumerator_term_correct : list_enumeratorᵗ list_enumerator_term term.
Proof with (try eapply cum_ge'; eauto; lia).
  intros t. induction t as [m | t1 [n1 IH1] t2 [n2 IH2] | t [n IH]].
  - destruct (el_T m) as [n Hn]. exists (S n). cbn. in_app 2. eauto.
  - exists (1 + n1 + n2). cbn. in_app 4.
    in_collect (t1, t2)...  
  - exists (1 + n). cbn. in_app 3. eauto.
Qed.

Lemma datatype_term : {I | retraction I enum_term term nat}.
  eapply enumerator_retraction.
  2: abstract eapply list_enumeratorᵗ_enumeratorᵗ, list_enumerator_term_correct.
  unshelve eapply DecidabilityFacts.dec_decider; intros [t1 t2]; eapply term_eq_dec.
Defined.

Definition I_term := proj1_sig datatype_term.

Lemma I_term_correct s : enum_term (I_term s) = Some s.
Proof.
  unfold I_term. destruct datatype_term as [? H]. eapply H.
Qed.

Lemma I_term_correct'' s : closed s -> enum_closed (I_term s) = Some s.
Proof.
  intros H1 % closed_dcl.
  unfold enum_closed.
  rewrite I_term_correct.
  destruct bound_dec. reflexivity. tauto.
Qed.

Lemma I_term_correct' s : proc s -> enum_closed (I_term s) = Some s.
Proof.
  intros [H1 % closed_dcl [s' ->]].
  unfold enum_closed.
  rewrite I_term_correct.
  destruct bound_dec. reflexivity. tauto.
Qed.


Lemma step_beta s t u :
  t = subst s 0 u ->
  lambda u ->
  L.app (lam s) u ≻ t.
Proof.
  intros -> [? ->]. econstructor.
Qed.

Theorem SMN : SMN_for T_L.
Proof.
  red.
  unfold T_L.
  exists (fun c x => match enum_closed c with
               Some t => I_term (lam (L.app (lam (L.app t (var 0))) (L.app (ext embed) (L.app (L.app (ext (@pair nat nat)) (enc x)) (var 0)))))
             | _ => c
             end).
  intros c x y v.
  destruct enum_closed eqn:E1. 2: rewrite E1; firstorder congruence.
  pose proof (Ht := enum_closed_proc E1).
  remember ((lam (L.app t (var 0)))) as s.
  assert (Hs : proc s). { subst s. Lproc. }
  assert (Es : L.app s (enc ⟨ x, y ⟩) == L.app t (enc ⟨ x, y ⟩)). {
    rewrite Heqs. etransitivity. econstructor. eapply step_beta. cbn. 
    rewrite Ht. reflexivity. Lproc. auto. }
  setoid_rewrite I_term_correct'.
  split.
  - intros [n H].
    destruct eva eqn:E; inversion H; clear H.
    eapply unenc_correct2 in H1. subst t0.
    eapply eva_equiv in E.
    assert (Eq : (L.app
             (lam
                (L.app s (L.app (ext embed) (L.app (L.app (ext (@pair nat nat)) (enc x)) # 0))))
             (enc y)) == L.app s (enc ⟨ x, y ⟩)). { symmetry in E. now Lsimpl. }
    rewrite Es, E in Eq.
    eapply equiv_eva in Eq as [m H].
    exists m. cbn in *.
    now rewrite H. eapply nat_enc_proc.
  - intros [n H].
    destruct eva eqn:E; inversion H.
    eapply unenc_correct2 in H1. subst t0.
    eapply eva_equiv in E.
    assert (H' : L.app t (enc (embed (x, y))) == nat_enc v). {
      rewrite <- E, <- Es.
      symmetry. now Lsimpl. }
    eapply equiv_eva in H' as [m H'].
    exists m. cbn in *.
    now rewrite H'. eapply nat_enc_proc.
  - Lproc.
Qed.

Definition CT_L := CT_for T_L.

Import partial.implementation.
Existing Instance  monotonic_functions.

Lemma monotonic_T_L c x : monotonic (T_L c x).
Proof.
  intros n1 v H n2 Hle.
  unfold T_L in *.
  destruct (enum_closed); try congruence.
  destruct (eva n1) eqn:E; try congruence.
  erewrite eva_le; eauto.
Qed.

Definition θ_L : nat -> (nat ↛ nat) := fun c x : nat => Build_part (@monotonic_T_L c x).

Definition EPF_L := EPF_nonparam_for θ_L.

From SyntheticComputability Require Import Synthetic.

Definition CT_L_elem :=
  forall f : nat -> nat, exists t : term, closed t /\ forall n, L.eval (L.app t (enc n)) (enc (f n)).

Definition CT_L_elem_bool :=
  forall f : nat -> bool, exists t : term, closed t /\ forall n, L.eval (L.app t (enc n)) (enc (f n)).

Definition CT_L_semidecidable :=
  forall p : nat -> Prop, semi_decidable p -> L_recognisable p.

Definition CT_L_enumerable :=
  forall p : nat -> Prop, enumerable p -> L_enumerable p.

Definition CT_L_decidable :=
  forall p : nat -> Prop, decidable p -> L_decidable p.

Lemma enumerable_graph_part (f : nat -> part nat) :
  enumerable (fun! ⟨x, y⟩ => hasvalue (f x) y).
Proof.
  exists (fun! ⟨n, m⟩ => if seval (f n) m is Some y then Some ⟨n, y⟩ else None).
  intros xy. destruct (unembed xy) as [x y] eqn:E. split; cbn.
  - intros [m Hm] % (@seval_hasvalue monotonic_functions).
    exists ⟨x, m⟩. rewrite embedP. unfold seval. rewrite Hm. f_equal.
    eapply (f_equal embed) in E. now rewrite unembedP in E.
  - intros [mn H]. destruct (unembed mn) as [m n].
    destruct (seval (f m) n) as [x' | ] eqn:E2; try congruence.
    inv H.
    rewrite embedP in E. inv E.
    eapply (seval_hasvalue (partiality := monotonic_functions)).
    eexists. eapply E2.
Qed.

Import L_Notations.

From SyntheticComputability Require Import partial.

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

Lemma T_L_iff t x v : proc t ->
  (exists n, T_L (I_term t) x n = Some v) <-> t (enc x) == enc v.
Proof.
  intros Ht. split.
  - intros [n Hn]. unfold T_L in *.
    rewrite I_term_correct' in Hn; eauto.
    destruct (eva n) eqn:E; try congruence.
    eapply eva_equiv. rewrite E.
    eapply unenc_correct2 in Hn. subst. reflexivity.
  - intros He.
    eapply equiv_eva in He as [n Hn]. 2:Lproc.
    exists n. unfold T_L. rewrite I_term_correct'; eauto. rewrite Hn.
    now rewrite unenc_correct.
Qed.

Lemma closed_subst s n t : closed s -> subst s n t = s.
Proof.
  intros H. eapply H.
Qed.

Lemma closed_converges_proc s :
  closed s -> exists t, proc t /\ forall n : nat, s (enc n) == t (enc n).
Proof.
  intros Hs.
  exists (lam (s 0)). split. Lproc.
  intros n. now rewrite Eta; try Lproc.
Qed.

Lemma CT_L_to_EPF_L : CT_L -> EPF_L.
Proof.
  intros [_ ct] f.
  pose proof (partial_to_total f) as [f' H].
  destruct (ct f') as [c Hc].
  unfold T_L in Hc.
  destruct (enum_closed c) as [t | ] eqn:E.
  2: now destruct (Hc 0) as (? & [=]).
  rename t into t'.
  destruct (@closed_converges_proc t') as [t [Hproc Hequiv]].
  now eapply enum_closed_proc.
  exists (I_term (lam (t (ext embed (ext (@pair nat nat) 0
                                    (LMuRecursion.mu (lam ((t (ext embed (ext (@pair nat nat) 1 0))) (enc false) (lam (enc true))))))) (lam Omega) (lam (lam 1 )) I))).
  unfold θ_L. intros x.
  cbn. unfold equiv. cbn. unfold implementation.hasvalue at 1. cbn.
  intros v. rewrite T_L_iff, H. 2:{ eapply enum_closed_proc in E. Lproc. }
  assert (lam
    (t
       (ext embed
          (ext (@pair nat nat) # 0
             (LMuRecursion.mu
                (lam
                   (t (ext embed (ext (@pair nat nat) # 1 # 0)) (enc false) (lam (enc true)))))))
       (lam Omega) (lam (lam 1)) I) (enc x) ==
    (t
       (ext embed
          (ext (@pair nat nat) (enc x)
             (LMuRecursion.mu
                (lam
                   (t (ext embed (ext (@pair nat nat) (enc x) # 0)) (enc false) (lam (enc true)))))))
       (lam Omega) (lam (lam 1)) I)) as ->.
  { eapply enum_closed_proc in E.
    econstructor.
    eapply CT.step_beta. 2: Lproc.
    cbn. rewrite !closed_subst; try Lproc.
    reflexivity. }
  assert (Ht : forall xv : nat, t (enc xv) == enc (f' xv)). {
    intros xv. specialize (Hc xv) as [n Hn].
    destruct (eva n) as [v' | ] eqn:E' ; try congruence.
    eapply eva_equiv in E'.
    eapply unenc_correct2 in Hn. subst. rewrite <- Hequiv. exact E'.
  }
  clear E Hc t' Hequiv.
  assert (Hfun : forall n0 : nat,
  exists b : bool,
    lam (t (ext embed (ext (@pair nat nat) (enc x) # 0)) (enc false) (lam (enc true)))
      (ext n0) == ext b). {
    intros m.
    destruct (f' ⟨ x, m ⟩) eqn:E_.
    - exists false. Lsimpl. rewrite Ht, E_. now Lsimpl.
    - exists true. Lsimpl. rewrite Ht, E_. now Lsimpl.
  }
  split.
  - intros He.
    match type of He with (L_facts.equiv ?L ?R) => assert (Hcon : converges L) end.
    { eexists. split; eauto. Lproc. }
    do 3 eapply app_converges in Hcon as [Hcon _].
    eapply app_converges in Hcon as [_ Hcon].
    eapply app_converges in Hcon as [_ Hcon].
    eapply app_converges in Hcon as [_ Hcon].
    eapply LMuRecursion.mu_spec in Hcon as [n Hn].
    + edestruct LMuRecursion.mu_complete as [n' Hn'].
      4: rewrite Hn' in He.
      Lproc. 2: eauto. eauto. 
      exists n'. destruct (f' ⟨x, n'⟩) eqn:Ef.
      * assert (lambda (enc v)) as [s Hs] by Lproc.
        edestruct Omega_diverges.
        rewrite <- Hs, <- He. symmetry.
        Lsimpl. rewrite Ht, Ef. Lsimpl.
        repeat econstructor.
      * f_equal. eapply enc_extinj.
        rewrite <- He. symmetry.
        Lsimpl. rewrite Ht, Ef. now Lsimpl.
    + Lproc.
    + eauto.
  - intros [n Hn].
    specialize (Ht ⟨x, n⟩) as Ht'.
    edestruct LMuRecursion.mu_complete as [n' Hn'].
    4: rewrite Hn'. 1:Lproc. eauto.
    Lsimpl. 
    instantiate (1 := n). Lsimpl.
    rewrite Ht, Hn. now Lsimpl.
    Lsimpl. eapply LMuRecursion.mu_sound in Hn' as Hn_.
    2:Lproc. 2:eauto.
    destruct Hn_ as (n_ & E_ & He & Hmin).
    eapply inj_enc in E_ as <-.
    rewrite Ht.
    destruct (f' ⟨x, n'⟩) eqn:Ef.
    + enough (true = false) by congruence.
      eapply enc_extinj. rewrite <- He.
      Lsimpl.
      rewrite Ht, Ef. now Lsimpl.
    + enough (n0 = v) as -> by now Lsimpl.
      eapply hasvalue_det; eapply H; eauto.
    + Lproc.
Qed.

Lemma EPF_L_to_CT_L : EPF_L -> CT_L.
Proof.
  intros epf. split. 1:eapply monotonic_T_L.
  intros f. destruct (epf (fun x => ret (f x))) as [c Hc].
  exists c. intros x. specialize (Hc x (f x)). cbn in Hc.
  destruct Hc as [_ Hc].
  unfold θ_L in *.  eapply Hc. 
  eapply (ret_hasvalue (partiality := monotonic_functions)).
Qed.

Lemma CT_L_iff_CT_L_elem : CT_L <-> CT_L_elem.
Proof.
  split. 2:intros ct; split.
  - intros [H ct] f.
    specialize (ct f) as [c Hc].
    pose proof (Hc 0) as [c0 Hc0].
    unfold T_L in Hc0.
    destruct enum_closed as [t | ] eqn:Ht; try congruence.
    assert (Hcl : closed t) by now eapply enum_closed_proc. clear Hc0.
    exists t. split. eapply Hcl.
    intros x.
    specialize (Hc x) as [n Hc]. eapply eval_iff. split. 2: Lproc.
    unfold T_L in Hc. rewrite Ht in Hc.
    destruct eva as [v | ] eqn:E; try congruence.
    eapply unenc_correct2 in Hc. subst.
    eapply seval_eval, eva_seval, E.
  - intros c x n1 v H1 n2 Hle.
    unfold T_L in *.
    destruct (enum_closed c) as [t | ]; try congruence.
    destruct (eva n1) as [? | ] eqn:E ; try congruence.
    eapply eva_le with (n2 := n2) in E. 2: lia.
    now rewrite E.
  - intros f. destruct (ct f) as (t & Hcl & H).
    exists (I_term (lam (L.app t (L.var 0)))).
    intros x. specialize (H x).
    eapply eval_iff in H.
    assert (L.app (lam (L.app t # 0)) (enc x) ⇓ enc (f x)).
    { split. 2: eapply H.
      econstructor. eapply step_beta. 3: eapply H.
      2: Lproc. cbn. now rewrite Hcl. }
    eapply eval_seval in H0 as [n Hn % seval_eva].
    exists n. unfold T_L.
    rewrite I_term_correct'. 2: Lproc.
    rewrite Hn. now rewrite unenc_correct.
Qed.

Import L_Notations.

Lemma subst_closed s n u : closed s -> subst s n u = s.
Proof.
  firstorder.
Qed.

Lemma CT_L_iff_CT_L_computable :
  CT_L <-> forall f : nat -> nat, is_computable f.
Proof.
  rewrite CT_L_iff_CT_L_elem.
  split.
  - intros ctl f. destruct (ctl f) as (t & H1 & H2).
    econstructor. exists (lam (t 0)).
    cbn. split. Lproc. intros x ? ->.
    exists (enc (f x)). split. 2:reflexivity.
    econstructor 2. eapply step_beta.
    cbn. rewrite subst_closed. reflexivity. Lproc.
    Lproc. specialize (H2 x). eapply eval_iff in H2.
    now rewrite H2.
  - intros H f. destruct (H f) as [Hf].
    exists (ext f). split. Lproc.
    intros n. eapply eval_iff. Lsimpl.
    eapply eval_refl. Lproc.
Qed.

Lemma CT_L_elem_bool_iff_CT_L_decidable :
  CT_L_elem_bool <-> CT_L_decidable.
Proof.
  split.
  - intros ct p [f Hf].
    specialize (ct f) as (t & Ht1 & Ht2).
    exists f. split. 2:exact Hf.
    econstructor. exists (lam (t 0)).
    cbn. split. Lproc. intros n ? ->.
    eexists. split. 2:reflexivity.
    specialize (Ht2 n) as ? % eval_iff.
    econstructor 2.
    eapply step_beta. cbn. rewrite Ht1. reflexivity. Lproc.
    now Lsimpl.
  - intros ct f.
    specialize (ct (fun x => f x = true)) as (g & [Ht1] & Ht2). firstorder.
    exists (ext g). split. Lproc.
    intros. eapply eval_iff. Lsimpl.
    specialize (Ht2 n). destruct (g n), (f n).
    1, 4: split; try reflexivity; Lproc.
    all: try (enough (false = true) by congruence; tauto).
Qed.

Lemma CT_L_elem_to_CT_L_elem_bool :
  CT_L_elem -> CT_L_elem_bool.
Proof.
  intros ct f.
  specialize (ct (fun x => if f x then 0 else 1)) as (t & H1 & H2).
  exists (lam (t 0 (enc true) (lam (enc false)))). split. 1:Lproc.
  intros n. specialize (H2 n).
  eapply eval_iff in H2 as [H2 H2']. eapply eval_iff.
  split. 2:Lproc.
  econstructor.
  eapply step_beta with (t := t (enc n) (enc true) (lam (enc false))). 2:Lproc.
  1:{ cbn. rewrite !subst_closed; try Lproc. reflexivity. }
  Lsimpl. destruct (f n); now try Lsimpl.
Qed.

Lemma CT_L_elem_bool_to_CT_L_semidecidable :
  CT_L_elem_bool -> CT_L_semidecidable.
Proof.
  intros ct p [f Hf].
  specialize (ct (fun! ⟨x,n⟩ => f x n)) as (t & H1 & H2).
  exists f. split. 2: eapply Hf.
  econstructor. exists (lam (lam (t ((ext embed) ((ext (@pair nat nat) 1 0)))))). cbn.
  split. Lproc.
  intros. subst.
  eexists. split. 
  econstructor 2. eapply step_beta.
  cbn. rewrite !subst_closed; try Lproc. reflexivity.
  2:reflexivity. Lproc.
  split. Lproc.
  intros. subst. eexists.
  split. 2:reflexivity.
  specialize (H2 ⟨a, a0⟩).
  rewrite embedP in H2.
  etransitivity.
  econstructor 2. eapply step_beta.
  cbn. rewrite !subst_closed. all: try Lproc. reflexivity.
  reflexivity. eapply eval_iff in H2. now Lsimpl. 
Qed.

Lemma CT_L_semidecidable_to_CT_L_enumerable :
  CT_L_semidecidable -> CT_L_enumerable.
Proof.
  intros ct p Hp.
  destruct (ct p) as (f & [Hf1] & Hf2). eapply SemiDecidabilityFacts.enumerable_semi_decidable.
  eapply discrete_nat. eauto.
  eexists. split.
  2:eapply SemiDecidabilityFacts.semi_decider_enumerator.
  2: eauto. 2: exact Hf2.
  unfold nat_enum. econstructor.
  extract.
Qed.

Lemma enumerable_graph (f : nat -> nat) :
  enumerable (fun p => exists x, p = ⟨x, f x ⟩).
Proof.
  exists (fun n => Some ⟨n, f n⟩).
  split.
  - intros [? ->]. eauto.
  - intros [n [= <-]]. eauto.
Qed.

Require Import SyntheticComputability.Models.LMuRecursion.

Lemma CT_L_enumerable_to_CT_L_elem :
  CT_L_enumerable -> CT_L_elem.
Proof.
  intros ct f.
  pose proof (enumerable_graph f); eauto.
  eapply ct in H as (g & [Hg1] & Hg2).
  pose (h := (fun x n => match g n with Some xfx =>
                                             match unembed xfx with
                                               (x', fx) => Nat.eqb x x'
                                             end
                                | _ => false end)).
  pose (h2 := (fun n => match g n with Some xfx =>
                                             match unembed xfx with
                                               (x', fx) => fx
                                             end
                                 | _ => 0 end)).
  assert (Hh : computable h) by (unfold h; extract).
  assert (Hh2 : computable h2) by (unfold h2; extract).
  exists (lam (ext h2 (mu (lam (ext h 1 0))))).
  split. Lproc.
  intros x. eapply eval_iff.
  destruct (Hg2 ⟨x,f x⟩) as [[n H] _].
  eauto.
  Lsimpl.
  edestruct (mu_complete).
  4: rewrite H0.
  - Lproc. 
  - intros n0. eexists. Lsimpl. reflexivity.
  - instantiate (1 := n). Lsimpl.
    unfold h. now rewrite H, embedP, Nat.eqb_refl. 
  - Lsimpl.
    eapply mu_sound in H0 as (m & -> % inj_enc & H2 & H3); try Lproc.
    2: intros; eexists; now Lsimpl.
    assert (Heq : h x m = true). { 
      eapply enc_extinj. rewrite <- H2. symmetry. now Lsimpl.
    }
    unfold h in Heq.
    destruct (g m) eqn:E1; try congruence.
    destruct (unembed n0) eqn:E2.
    eapply beq_nat_true in Heq as ->.
    unfold h2. rewrite E1, E2.
    enough (n2 = f n1) as ->. split. reflexivity. Lproc.
    eapply (f_equal embed) in E2. rewrite unembedP in E2.
    subst.
    specialize (Hg2 ⟨n1,n2⟩) as [_ [x HH]]. eauto.
    eapply (f_equal unembed) in HH. rewrite !embedP in HH.
    congruence.
Qed.

Set Default Goal Selector "!".


(** # <a id="decidable_Ldecidable_iff" /> #*)
Lemma CT_L_decidable_equiv :
  CT_L -> forall p : nat -> Prop, decidable p <-> exists t, closed t /\ forall n, (p n /\ L.eval (t (enc n)) (enc true)) \/ (~ p n /\ L.eval (t (enc n)) (enc false)).
Proof.
  intros ct % CT_L_iff_CT_L_elem % CT_L_elem_to_CT_L_elem_bool % CT_L_elem_bool_iff_CT_L_decidable.
  intros p. split.
  - intros (f & [H1] & H2) % ct. exists (ext f).
    split. 1:Lproc. intros n. specialize (H2 n).
    destruct (f n) eqn:E.
    + left. split. 1:tauto.
      eapply eval_iff. Lsimpl. rewrite E. split; [ reflexivity | Lproc].
    + right. split. 1: intros ? % H2; congruence.
      eapply eval_iff. Lsimpl. rewrite E. split; [ reflexivity | Lproc].
  - intros (t & H1 & H2).
    unshelve eexists.
    + intros n.
      destruct (@informative_eval2 (t (enc n))) as [b Hb].
      1: destruct (H2 n) as [[_ H % eval_iff] | [_  H % eval_iff]]; eauto.
      destruct (term_eq_dec b (enc true)) as [-> | N1].
      1: exact true.
      destruct (term_eq_dec b (enc false)) as [-> | N2].
      1: exact false.
      exfalso.
      destruct (H2 n) as [[_ H % eval_iff] | [_ H % eval_iff]]; eauto.
      * eapply N1. eapply unique_normal_forms. 1:eapply Hb.
        1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
        destruct H as [H _]. now Lsimpl.
      * eapply N2. eapply unique_normal_forms. 1:eapply Hb.
        1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
        destruct H as [H _]. now Lsimpl.
    + intros n.
      destruct (@informative_eval2 (t (enc n))) as [b Hb]. cbn.
      destruct term_eq_dec as [-> | N1]; cbn.
      * split; intros _; try tauto.
        destruct (H2 n) as [[? H % eval_iff] | [_ H % eval_iff]]; eauto.
        enough (He : enc true = enc false) by (cbv in He; congruence).
        eapply unique_normal_forms. 1:eapply Hb.
        1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
        destruct H as [H _]. now Lsimpl.
      * destruct term_eq_dec as [-> | N2]; cbn.
        -- split; intros ?; try congruence.
           exfalso; revert H.
           destruct (H2 n) as [[_ H % eval_iff] | [? H % eval_iff]]; eauto.
           enough (He : enc true = enc false) by (cbv in He; congruence).
           eapply unique_normal_forms. 1:Lproc. 1:eapply Hb.
           destruct Hb as [Hb _]. rewrite <- Hb.
           destruct H as [H _]. now Lsimpl.
        -- exfalso.
           destruct (H2 n) as [[_ H % eval_iff] | [_ H % eval_iff]].
           ++ eapply N1. eapply unique_normal_forms. 1:eapply Hb.
              1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
              destruct H as [H _]. now Lsimpl.
           ++ eapply N2. eapply unique_normal_forms. 1:eapply Hb.
              1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
              destruct H as [H _]. now Lsimpl.
Qed.

Lemma HaltL_semidecidable :
  semi_decidable HaltL.
Proof.
  exists (fun t n => if eva n t is Some x then true else false).
  intros t. split.
  - intros [v [n H % seval_eva] % eval_iff % eval_seval].
    exists n. now rewrite H.
  - intros [n H]. destruct eva as [v | ] eqn:E; try congruence.
    exists v. eapply eval_iff, seval_eval, eva_seval, E.
Qed.

Lemma CT_L_semidecidable_equiv :
  CT_L ->
  forall p : nat -> Prop, semi_decidable p <-> exists t, closed t /\ forall n, p n <-> HaltL (t (enc n)).
Proof.
  intros ct % CT_L_iff_CT_L_elem % CT_L_elem_to_CT_L_elem_bool % CT_L_elem_bool_to_CT_L_semidecidable. split.
  - intros (f & [H1] & H2) % ct.
    exists (lam (mu (lam (ext f 1 0)))). split. 1:Lproc. intros x. rewrite H2.
    split.
    + intros [n Hn].
      edestruct (@mu_complete (lam (ext f (enc x) 0))) as [v Hv].
      * Lproc.
      * intros n'. exists (f x n'). now Lsimpl.
      * instantiate (1 := n). Lsimpl. now rewrite Hn.
      * exists (ext v). eapply eval_iff.
        Lsimpl. rewrite Hv.  split; [ reflexivity | Lproc].
    + intros [v Hv % eval_iff].
      assert (lam (mu (lam (ext f 1 0))) (enc x) == mu (lam (ext f (enc x) 0))) by (clear Hv; now Lsimpl).
      rewrite H in Hv. edestruct (@mu_sound (lam (ext f (enc x) 0))) as [n [H3 [H4 _]]].
      3: eapply Hv.
      * Lproc.
      * intros n'. exists (f x n'). now Lsimpl.
      * now Lsimpl.
      * exists n. subst.
        eapply enc_extinj. rewrite <- H4. symmetry. now Lsimpl.
  - intros (t & H1 & H2).
    destruct (HaltL_semidecidable) as [g Hg].
    exists (fun x n => g (t (enc x)) n). red in Hg. intros x.
    now rewrite H2, Hg.
Qed.

From SyntheticComputability Require Import principles.

Lemma CT_L_MP_equiv :
  CT_L ->
  MP <-> forall t,  ~~ (HaltL t) -> HaltL t.
Proof.
  intros ct. split.
  - intros H % MP_to_MP_semidecidable. apply H, HaltL_semidecidable.
  - intros He.
    intros f Hf.
    eapply CT_L_semidecidable_equiv with (p := fun _ => exists n, f n = true) in ct as [(t & H1 & H2) _].
    + exists (fun _ n => f n). firstorder.
    + eapply (H2 0). eapply He. now rewrite <- H2.
Qed.

From SyntheticComputability Require Import reductions.

Lemma CT_L_enumerable_equiv :
  CT_L -> forall p : nat -> Prop, enumerable p <-> p ⪯ₘ HaltL.
Proof.
  intros ct p. rewrite <- halting.semi_decidable_enumerable_iff_nat. split.
  - intros (t & H1 & H2) % CT_L_semidecidable_equiv; eauto.
    eexists. exact H2.
  - intros [f Hf].
    destruct (HaltL_semidecidable) as [g Hg].
    exists (fun x n => g (f x) n). red in Hg. intros x. red in Hf.
    now rewrite Hf, Hg.
Qed.
