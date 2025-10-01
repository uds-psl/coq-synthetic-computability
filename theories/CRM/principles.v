From Coq.Logic Require Import ConstructiveEpsilon.
Require Import Lia Nat.
From stdpp Require Import numbers list list_numbers.
From SyntheticComputability Require Import SemiDecidabilityFacts DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts reductions Axioms.Equivalence halting FinChoice Dec.

(** * CT in relation to other axioms  *)

(** ** Provable choice axioms  *)

Lemma decidable_AC X :
  forall R : X -> nat -> Prop, decidable (uncurry R) -> (forall x, exists n, R x n) -> exists f, forall x, R x (f x).
Proof.
  intros R [f Hf] Htot.
  destruct (decider_AC _ f R) as [g Hg]; eauto.
Qed.

Lemma semi_decidable_AC X :
  forall R : X -> nat -> Prop, semi_decidable (uncurry R) -> (forall x, exists n, R x n) -> exists f, forall x, R x (f x).
Proof.
  intros R [f Hf] Htot.
  destruct (semi_decider_AC _ f R) as [g Hg]; eauto.
Qed.

Lemma sdec_compute_lor {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> (forall x, p x \/ q x) -> exists f : X -> bool, forall x, if f x then p x else q x.
Proof.
  intros Hp Hq Hpq.
  edestruct (semi_decidable_AC X (fun x n => if n is 0 then p x else q x)) as [f Hf].
  - destruct Hp as [f1 H1], Hq as [f2 H2]. red in H1, H2.
    exists (fun '(x,n) m => if n is 0 then f1 x m else f2 x m).
    now intros (x,[]); cbn; rewrite ?H1, ?H2.
  - intros x. destruct (Hpq x). now exists 0. now exists 1.
  - exists (fun x => if f x is 0 then true else false). intros x.
    specialize (Hf x). destruct (f x); firstorder.
Qed.

Lemma inspect_opt {X} (o : option X) :
  {x | o = Some x} + {o = None}.
Proof.
  destruct o; eauto.
Qed.

Lemma enumerable_AC :
  forall X, discrete X -> forall Y, forall R : X -> Y -> Prop, enumerable (uncurry R) -> (forall x, exists n, R x n) -> exists f, forall x, R x (f x).
Proof.
  intros X [d Hd] Y R [f Hf] Htot.
  destruct (enumerator_AC _ _ f d _ Hd Hf Htot) as [g Hg].
  now exists g.
Qed.

Lemma finite_AC :
  forall X, discrete X -> finiteᵗ X -> forall Y,
    forall R : X -> Y -> Prop, (forall x, exists y, R x y) -> exists f : X -> Y, forall x, R x (f x).
Proof.
  intros X [D] % discrete_iff Hfin Y R Htot.
  eapply finite_choice; auto.
Qed.

(** ** Extensionality axioms  *)

Definition Fext := forall X Y (f g : X -> Y), (forall x, f x = g x) -> f = g.
Definition Pext := forall P Q : Prop, P <-> Q -> P = Q.
Definition hProp (P : Prop) := forall x1 x2 : P, x1 = x2.
Definition PI := forall P : Prop, hProp P.

Lemma Pext_to_PI :
  Pext -> PI.
Proof.
  intros pext P x1 x2.
  assert (P = True) as -> by firstorder.
  now destruct x1, x2.
Qed.

Lemma hProp_disj P Q :
  hProp P -> hProp Q -> ~ (P /\ Q) -> hProp (P \/ Q).
Proof.
  unfold hProp.
  intros hP hQ H [H1 | H1] [H2 | H2]; f_equal; firstorder; exfalso; tauto.
Qed.

Lemma Fext_hProp_neg P :
  Fext -> hProp (~ P).
Proof.
  intros fext H1 H2.
  eapply fext. intros x. exfalso. tauto.
Qed.

Lemma Fext_hProp_disj P :
  Fext -> hProp P -> hProp (P \/ ~ P).
Proof.
  intros. now eapply hProp_disj; [ | eapply Fext_hProp_neg | ].
Qed.

Lemma Fext_hProp_wdisj P :
  Fext -> hProp (~ P \/ ~~ P).
Proof.
  intros. now eapply Fext_hProp_disj; [ | eapply Fext_hProp_neg].
Qed.

Section CT_wrong.

  Context {Part : partiality}.

  Variable ϕ : nat -> nat -> nat -> option nat.
  Variable Hϕ : forall c x, monotonic (ϕ c x).

  Definition CT_Sigma := forall f : nat -> nat, {c : nat | forall x, exists n, ϕ c x n = Some (f x) }.

  Lemma CT_Sigma_wrong : CT_Sigma -> Fext -> False.
  Proof.
    intros CT fext.
    eapply K_nat_undec. { 
      right. exists ϕ. split; try eassumption.
      intros f. unshelve eexists.
      + intros x. destruct (CT (f x)) as [c]. exact c.
      + intros x y. cbn. destruct (CT (f x)) as [c Hc]; eauto.
    }
    exists (fun f => Nat.eqb (proj1_sig (CT f)) (proj1_sig (CT (fun _ => 0)))).
    intros f.
    destruct (PeanoNat.Nat.eqb_spec (` (CT f)) (` (CT (fun _ : nat => 0)))).
    - unfold reflects. intuition.
      destruct (CT f) as [cf Hf].
      destruct (CT (fun _ => 0)) as [cc Hc]. cbn in *. subst.
      destruct (Hf n), (Hc n).
      eapply monotonic_agnostic; eauto.
    - unfold reflects. intuition try congruence.
      assert (f = fun x => 0) as -> by now apply fext.
      congruence.
  Qed.

End CT_wrong.

(** ** Classical logical axioms  *)

Definition LEM := forall P, P \/ ~ P.
Definition DNE := forall P, ~~P -> P.
Definition DGP := forall P Q : Prop, (P -> Q) \/ (Q -> P).
Definition WLEM := forall P, ~~P \/ ~ P.

Definition IP := forall (P : Prop), forall p : nat -> Prop, (P -> exists n, p n) -> exists n, P -> p n.

Lemma LEM_to_DGP :
  LEM -> DGP.
Proof.
  intros H P Q.
  destruct (H P), (H Q); tauto.
Qed.

Lemma DGP_to_WLEM :
  DGP -> WLEM.
Proof.
  intros H P.
  destruct (H P (~ P)); tauto.
Qed.

Lemma LEM_to_IP : LEM -> IP.
Proof.
  intros H P p.
  destruct (H P) as [H0 | H0].
  - intros [n H1] % (fun H1 => H1 H0). eauto.
  - exists 0. tauto.
Qed.

(*

    LEM --> DGP --> WLEM  
     |               |
     |               |
     v               v
    LPO     -->    WLPO   -->   LLPO
     ^               ^
     |               |
     v               v
  MP /\ WLPO     PFP /\ LLPO

     ^
     |
     
  MP /\ IP

 *)

Definition LPO := forall f : nat -> bool, (exists n, f n = true) \/ ~ (exists n, f n = true).
Definition WLPO := forall f : nat -> bool, (forall n, f n = false) \/ ~ (forall n, f n = false).

Lemma forall_neg_exists_iff (f : nat -> bool) :
  (forall n, f n = false) <-> ~ exists n, f n = true.
Proof.
  split.
  - intros H [n Hn]. rewrite H in Hn. congruence.
  - intros H n. destruct (f n) eqn:E; try reflexivity.
    destruct H. eauto.
Qed.

Lemma LEM_to_LPO : LEM -> LPO.
Proof.
  cbv. intuition.
Qed.

Lemma WLEM_to_WLPO : WLEM -> WLPO.
Proof.
  intros H f. rewrite forall_neg_exists_iff.
  edestruct H; eauto.
Qed.

Lemma LPO_to_WLPO : LPO -> WLPO.
Proof.
  intros H f. rewrite forall_neg_exists_iff.
  edestruct H; eauto.
Qed.

Definition LPO_semidecidable := forall X (p : X -> Prop), semi_decidable p -> forall x, p x \/ ~ p x.

Lemma LPO_semidecidable_iff :
  LPO <-> LPO_semidecidable.
Proof.
  split.
  - intros H X p [f Hf] x. red in Hf.
    rewrite Hf. eapply H.
  - intros H f.
    eapply (H unit (fun _ => exists n, f n = true)).
    exists (fun _ => f). cbv. intuition. econstructor.
Qed.

Definition WLPO_semidecidable := forall X (p : X -> Prop), semi_decidable p -> forall x, ~ p x \/ ~~ p x.

Lemma WLPO_semidecidable_iff :
  WLPO <-> WLPO_semidecidable.
Proof.
  split.
  - intros H X p [f Hf] x. red in Hf.
    rewrite Hf. rewrite <- forall_neg_exists_iff.
    eapply H.
  - intros H f.
    rewrite forall_neg_exists_iff.
    eapply (H unit (fun _ => exists n, f n = true)).
    exists (fun _ => f). cbv. intuition. econstructor.
Qed.

Definition WLPO_cosemidecidable := forall X (p : X -> Prop), co_semi_decidable p -> forall x, p x \/ ~ p x.

Lemma WLPO_cosemidecidable_iff :
  WLPO_cosemidecidable <-> WLPO_semidecidable.
Proof.
  split.
  - intros H X p [f Hf] x. red in Hf.
    rewrite Hf. rewrite <- forall_neg_exists_iff.
    eapply (H _ (fun x => forall n, f x n = false)).
    exists f. red. reflexivity.
  - intros H X p [f Hf] x. red in Hf.
    rewrite Hf. rewrite forall_neg_exists_iff.
    eapply (H _ (fun x => exists n, f x n = true)).
    exists f. intros x'. reflexivity.
Qed.

Definition CODING :=
  exists F : (nat -> bool) -> nat, forall f, F f = F (fun _ => false) <-> forall n, f n = false.

Lemma no_CODING :
  CODING -> decidable (compl K_nat_bool).
Proof.
  intros [F HF].
  exists (fun f => Nat.eqb (F f) (F (fun _ => false))).
  intros f. unfold compl, K_nat_bool. red. rewrite <- forall_neg_exists_iff.
  destruct (Nat.eqb_spec (F f) (F (fun _ => false))); rewrite <- HF.
  all: firstorder congruence.
Qed.

Definition LLPO := forall f g : nat -> bool, ((exists n, f n = true) -> (exists n, g n = true)) \/ ((exists n, g n = true) -> (exists n, f n = true)).
Definition DM_Sigma_0_1 := forall f g : nat -> bool, ~ ((exists n, f n = true) /\ (exists n, g n = true)) -> ~ (exists n, f n = true) \/ ~ (exists n, g n = true).
Definition DGP_sdec := forall X (p : X -> Prop), semi_decidable p -> forall x y, (p x -> p y) \/ (p y -> p x).
Definition DM_sdec := forall X (p q : X -> Prop), semi_decidable p -> semi_decidable q -> forall x, ~ (p x /\ q x) -> ~ p x \/ ~ q x.
Definition LLPO_split := forall f : nat -> bool, (forall n m, f n = true -> f m = true -> n = m) -> (forall n, f (2 * n) = false) \/ (forall n, f (1 + 2 * n) = false).

Lemma LLPO_to_DM_Sigma_0_1 :
  LLPO -> DM_Sigma_0_1.
Proof.
  intros H f g Hfg.
  destruct (H f g); tauto.
Qed.

Lemma LLPO_iff_DGP_sdec :
  LLPO <-> DGP_sdec.
Proof.
  split.
  - intros H X p [f Hf] x y.
    unfold semi_decider in *.
    rewrite !Hf. eapply H.
  - intros H f g.
    unshelve eapply (H bool (fun b => if b then exists n, f n = true else exists n, g n = true) _ true false).
    + exists (fun b : bool => if b then f else g). red. intros []; reflexivity.
Qed.

Lemma DM_Sigma_0_1_iff_DM_sdec :
  DM_Sigma_0_1 <-> DM_sdec.
Proof.
  split.
  - intros H X p q [f Hf] [g Hg] x.
    unfold semi_decider in *.
    rewrite Hf, Hg. eapply H.
  - intros H f g Hfg.
    eapply (H unit (fun _ => exists n, f n = true) (fun _ => exists n, g n = true)).
    + exists (fun _ => f). red. reflexivity.
    + exists (fun _ => g). red. reflexivity.
    + econstructor.
    + eassumption.
Qed.

Lemma neg_neg_XM P :
  ~~ (P \/ ~ P).
Proof.
  tauto.
Qed.

Lemma DM_Sigma_0_1_iff_totality :
  DM_Sigma_0_1 <-> (forall X (R : X -> bool -> Prop), co_semi_decidable (uncurry R) -> forall n, ~~ (exists b, R n b) -> exists b, R n b).
Proof.
  split.
  - intros H X R [f Hf'] n.
    assert (Hf : forall n b, R n b <-> forall m, f (n, b) m = false) by (intros; eapply (Hf' (_, b))).
    setoid_rewrite Hf. clear - H. intros Hb.
    destruct (H (f (n, true)) (f (n, false))) as [H1 | H1].
    + intros [ [n1 ?] [n2 ?]]. eapply Hb. intros [[] ?]; congruence.
    + exists true. now eapply forall_neg_exists_iff.
    + exists false. now eapply forall_neg_exists_iff.
  - intros H f g Hfg.
    edestruct (H nat (fun _ b => if b then forall n, f n = false else forall n, g n = false)) with (n := 0) as [[] H1].
    + exists (fun '(n,b) => if b : bool then f else g). now intros (n, []).
    + intros H0. eapply (neg_neg_XM (exists n, f n = true)). intros [H1 | H1].
      * eapply (neg_neg_XM (exists n, g n = true)). intros [H2 | H2].
        -- eauto.
        -- eapply H0. exists false. now eapply forall_neg_exists_iff.
      * eapply H0. exists true. now eapply forall_neg_exists_iff.
    + left. now eapply forall_neg_exists_iff.
    + right. now eapply forall_neg_exists_iff.
Qed.

Lemma DM_Sigma_0_1_to_LLPO_split :
  DM_Sigma_0_1 -> LLPO_split.
Proof.
  intros H f Huni.
  destruct (H (fun n => f (2 * n)) (fun n => (f (1 + 2 * n)))).
  - intros [[n Hn] [m Hm]].
    eapply Huni in Hn; eauto. lia.
  - left. now rewrite forall_neg_exists_iff.
  - right. now rewrite forall_neg_exists_iff.
Qed.

Lemma dec_bounded_quant P n :
  (forall m, m <= n -> P m \/ ~ P m) -> (forall m, m <= n -> ~ P m) \/ exists m, m <= n /\ P m.
Proof.
  intros H.
  induction n.
  - destruct (H 0 (Nat.le_refl 0)).
    + right. exists 0. split. lia. eauto.
    + left. intros m Hm. enough (m = 0) by now subst. lia.
  - destruct IHn as [H1 | [m [Hle Hm]]].
    + intros. eapply H. lia.
    + destruct (H (S n) (Nat.le_refl _)).
      * right. eauto.
      * left. intros m [Hle |  ->] % Nat.lt_eq_cases; eauto.
        eapply H1. lia.
    + right. exists m. split. lia. eassumption.
Qed.

Lemma least_ex (P : nat -> Prop) n : P n -> (forall m, m < n -> P m \/~ P m) -> exists n, P n /\ forall m, P m -> m >= n.
Proof.
  induction n using lt_wf_rec.
  intros Hn Hlt.
  destruct n.
  - exists 0. split. eauto. intros. lia.
  - edestruct dec_bounded_quant with (n := n).
    + intros. eapply (Hlt m). lia.
    + exists (S n). split. eauto. intros.
      destruct (le_lt_dec (S n) m); eauto. eapply H0 in H1; lia. 
    + destruct H0 as (m & Hle & Hm).
      eapply (H m).
      * lia.
      * eassumption.
      * intros. eapply Hlt. lia.
Qed.

Lemma LLPO_split_to_LLPO :
  LLPO_split -> LLPO.
Proof.
  intros H f g.
  pose (alpha := (fun n => if n `mod` 2 =? 0 then f (n `div` 2) else g (n `div` 2))).
  pose (alpha' n := alpha n && forallb negb (map alpha (seq 0 n))).
  destruct (H alpha') as [H0 | H0].
  - intros n m [Ha1 Ha2] % andb_true_iff [Ha3 Ha4] % andb_true_iff.
    destruct (lt_eq_lt_dec n m) as [ [Hl | ] | Hl]; eauto.
    + rewrite forallb_forall in Ha4.
      setoid_rewrite in_map_iff in Ha4.
      setoid_rewrite in_seq in Ha4.
      enough (false = true) by congruence.
      eapply (Ha4 true). cbn. exists n. repeat split; eauto with arith. 
    + rewrite forallb_forall in Ha2.
      setoid_rewrite in_map_iff in Ha2.
      setoid_rewrite in_seq in Ha2.
      enough (false = true) by congruence.
      eapply (Ha2 true). cbn. exists m. repeat split; eauto with arith. 
  - left. intros [m Hm].
    destruct (least_ex (fun n => f n = true) _ Hm) as [n [Hn Hle]].
    { intros x. destruct (f x); firstorder congruence. }
    clear m Hm.
    assert (alpha (n * 2) = true). {
      unfold alpha. rewrite Nat.mod_mul. rewrite Nat.eqb_refl.
      rewrite Nat.div_mul. eauto. lia. lia.
    }
    destruct (dec_bounded_quant (fun n => g n = true) n).
    + intros m ?; destruct (g m); firstorder congruence.
    + exfalso. enough (alpha' (2 * n) = true). rewrite H0 in H3. congruence.
      rewrite Nat.mul_comm. unfold alpha'.
      eapply andb_true_iff. split. eauto.
      eapply forallb_forall.
      intros b. rewrite in_map_iff. setoid_rewrite in_seq.
      intros [k [H3 [_ H4] ]]. destruct b; try reflexivity.
      unfold alpha in H3.
      exfalso. destruct (k `mod` 2) eqn:Em.
      * cbn [Nat.eqb] in H3. eapply Hle in H3. cbn in H4.
        pose proof (Nat.div_lt_upper_bound k 2 n).
        lia.
      * cbn [Nat.eqb] in H3. eapply H2 in H3. lia. 
        eapply Nat.div_le_upper_bound. lia. lia.
    + firstorder.
  - right. intros [m Hm].
    destruct (least_ex (fun n => g n = true) _ Hm) as [n [Hn Hle]].
    { intros x. destruct (g x); firstorder congruence. }
    clear m Hm.
    assert (alpha (1 + n * 2) = true). {
      unfold alpha. rewrite Nat.mod_add; try lia.
      change (1 `mod` 2 =? 0) with false. hnf.
      rewrite Nat.div_add. cbn. eauto. lia.
    }
    destruct (dec_bounded_quant (fun n => f n = true) (S n)).
    + intros m ?; destruct (f m); firstorder congruence.
    + exfalso. enough (H3 : alpha' (1 + 2 * n) = true). rewrite H0 in H3. congruence.
      rewrite Nat.mul_comm. unfold alpha'.
      eapply andb_true_iff. split. eauto.
      eapply forallb_forall.
      intros b. rewrite in_map_iff. setoid_rewrite in_seq.
      intros [k [H3 [_ H4] ]]. destruct b; try reflexivity.
      unfold alpha in H3.
      exfalso. destruct (k `mod` 2) eqn:Em.
      * cbn [Nat.eqb] in H3. eapply H2 in H3. cbn in H4. eauto.
        eapply Nat.div_le_upper_bound. lia. lia.
      * cbn [Nat.eqb] in H3. eapply Hle in H3. cbn in H4.
        rewrite Nat.mod_eq in Em; lia.
    + firstorder.
Qed.

Definition PFP := forall f : nat -> bool, exists g : nat -> bool, (forall n, f n = false) <-> exists n, g n = true.

Lemma WLPO_PFP_LLPO_iff :
  WLPO <-> PFP /\ LLPO.
Proof.
  split.
  - intros H. split.
    + intros f. destruct (H f).
      * exists (fun _ => true).
        split.
        -- now exists 0.
        -- eauto.
      * exists (fun _ => false).
        split.
        -- tauto.
        -- intros [? [=]].
    + eapply LLPO_split_to_LLPO, DM_Sigma_0_1_to_LLPO_split. 
      intros f g Hfg. 
      destruct (H f).
      * left. firstorder congruence.
      * destruct (H g).
        -- right. firstorder congruence.
        -- left. intros Hf.
           assert (H2 : ~~ ((exists n, g n = true) \/ ~ (exists n, g n = true))) by tauto.
           eapply H2. intros [Hg | Hg].
           now eapply Hfg. now rewrite <- forall_neg_exists_iff in Hg.
  - intros [PFP LLPO % LLPO_to_DM_Sigma_0_1] f.
    destruct (PFP f) as [g Hg].
    destruct (LLPO f g).
    + rewrite <- Hg. intros [[n Hn] H]. rewrite H in Hn. congruence.
    + left. now rewrite forall_neg_exists_iff.
    + right. now rewrite <- Hg in H.
Qed.

Definition KS := forall P, exists f : nat -> bool, P <-> exists n, f n = true.

Lemma LEM_to_KS :
  LEM -> KS.
Proof.
  intros xm P.
  destruct (xm P) as [H | H].
  - exists (fun _ => true). firstorder. econstructor.
  - exists (fun _ => false). firstorder congruence.
Qed.

Lemma KS_LPO_to_LEM :
  KS -> LPO -> LEM.
Proof.
  intros ks lpo P.
  destruct (ks P) as [f ->].
  eapply lpo.
Qed.

Lemma KS_WLPO_to_WLEM :
  KS -> LPO -> LEM.
Proof.
  intros ks lpo P.
  destruct (ks P) as [f ->].
  eapply lpo.
Qed.  

Lemma KS_LLPO_to_DGP :
  KS -> LLPO -> DGP.
Proof.
  intros ks lpo P Q.
  destruct (ks P) as [f ->].
  destruct (ks Q) as [g ->].
  eapply lpo.
Qed.

(** ** Axioms of russian constructivism  *)

Definition MP := forall f : nat -> bool, ~~ (exists n, f n = true) -> exists n, f n = true.

Definition MP_semidecidable := forall X (p : X -> Prop), semi_decidable p -> forall x, ~~ p x -> p x.
Definition Post_logical := forall X (p : X -> Prop), semi_decidable p -> semi_decidable (compl p) -> forall x, p x \/ ~ p x.
Definition Post := forall X (p : X -> Prop), semi_decidable p -> semi_decidable (compl p) -> decidable p.

Lemma LPO_MP_WLPO_iff :
  LPO <-> MP /\ WLPO.
Proof.
  split.
  - intros H. split.
    + intros f Hf. destruct (H f); tauto.
    + intros f. rewrite forall_neg_exists_iff. destruct (H f); tauto.
  - intros [MP WLPO] f.
    destruct (WLPO f).
    + right. now rewrite <- forall_neg_exists_iff.
    + left. eapply MP. now rewrite <- forall_neg_exists_iff.
Qed.

Lemma MP_IP_LPO : IP -> MP -> LPO.
Proof.
  intros IP MP f.
  assert (exists n, forall k, f k = true -> f n = true) as [n Hn].
  - specialize (MP f). apply IP in MP as [n Hn].
    exists n. intros k H. apply Hn. intros H'. apply H'. now exists k.
  - destruct (f n) eqn:E.
    + eauto.
    + right. intros [m Hm]. 
      specialize (Hn m Hm). congruence.
Qed.

Lemma MP_to_MP_semidecidable :
  MP -> MP_semidecidable.
Proof.
  intros H X p [f Hf] x. red in Hf.
  rewrite Hf. eapply H.
Qed.

Definition MP_semidecidable_ex := forall (p : nat -> Prop), semi_decidable p -> ~~ (exists x, p x) -> exists x, p x.

Lemma MP_semidecidable_to_MP_semidecidable_ex :
  MP_semidecidable -> MP_semidecidable_ex.
Proof.
  intros mp p [f Hf]. red in Hf. setoid_rewrite Hf.
  eapply (mp unit (fun _ => exists x n, f x n = true)).
  exists (fun _ => fun! ⟨x,n⟩ => f x n). intros _.
  split.
  - intros (x & n & Hxn). exists ⟨x,n⟩. now rewrite embedP.
  - intros (xn & Hxn). destruct (unembed xn) as [x n]. eauto.
  - exact tt.
Qed.

Lemma MP_semidecidable_ex_to_MP_semidecidable :
  MP_semidecidable_ex -> MP_semidecidable.
Proof.
  intros mp X p [f Hf] x. red in Hf. setoid_rewrite Hf.
  eapply mp. eapply decidable_semi_decidable.
  exists (fun x0 => f x x0). intros ?. red. reflexivity.
Qed.

Lemma MP_semidecidable_nat_to_MP_semidecidable :
  (forall p : nat -> Prop, semi_decidable p -> forall x, ~~ p x -> p x) -> MP_semidecidable.
Proof.
  intros mp. eapply MP_semidecidable_ex_to_MP_semidecidable.
  intros p [f Hf]. red in Hf. setoid_rewrite Hf.
  eapply (mp (fun _ => exists x n, f x n = true)).
  exists (fun _ => fun! ⟨x,n⟩ => f x n). intros _.
  split.
  - intros (x & n & Hxn). exists ⟨x,n⟩. now rewrite embedP.
  - intros (xn & Hxn). destruct (unembed xn) as [x n]. eauto.
  - exact 0.
Qed.

Lemma MP_semidecidable_to_Post_logical :
  MP_semidecidable -> Post_logical.
Proof.
  intros H X p Hp Hcp x. pattern x.
  eapply H.
  - now eapply semi_decidable_or.
  - tauto.
Qed
.
Definition MP_semidecidable_ex_enumerable := forall X (p : X -> Prop), enumerable p -> ~~ (exists x, p x) -> exists x, p x.

Lemma MP_bla :
  MP_semidecidable_ex -> MP_semidecidable_ex_enumerable.
Proof.
  intros mp X p [f Hf]. red in Hf.
  setoid_rewrite Hf. intros H.
  destruct (mp (fun n => f n <> None)) as [n Hn].
  - eapply decidable_semi_decidable. eapply decidable_iff.
    econstructor. intros n. destruct (f n); firstorder.
  - intros HH. apply H. intros (x & n & HHH). eapply HH. exists n. congruence.
  - destruct (f n) eqn:E; try congruence. now exists x, n.
Qed.

Lemma MP_blub :
  MP_semidecidable_ex_enumerable -> MP_semidecidable_ex.
Proof.
  intros mp p Hp.
  eapply mp. eapply semi_decidable_enumerable; eauto.
Qed.

Lemma Post_logical_to_Post :
  Post_logical -> Post.
Proof.
  intros H X p Hp Hcp.
  destruct (sdec_compute_lor Hp Hcp) as [f Hf].
  - eapply H; eauto.
  - exists f. intros x. red. specialize (Hf x). destruct (f x); firstorder congruence.
Qed.

Lemma Post_nempty_to_MP {X} (x0 : X) :
  (forall (p : X -> Prop), semi_decidable p -> semi_decidable (compl p) -> decidable p) -> MP.
Proof.
  intros H f Hf.
  destruct (H (fun _ => exists n, f n = true)) as [d Hd].
  - exists (fun _ => f). now intros x.
  - exists (fun _ _ => false). firstorder congruence.
  - destruct (decider_decide Hd x0); tauto.
Qed.

Lemma Post_to_MP :
  Post -> MP.
Proof.
  intros H. apply (Post_nempty_to_MP tt). apply H.
Qed.

Lemma semi_decidable_ext {X} (p q : X -> Prop) :
  p ≡{X -> Prop} q -> semi_decidable p -> semi_decidable q.
Proof.
  intros H [f Hf]. exists f. intros x. cbv -[iff] in H.
  rewrite <- H. eapply Hf.
Qed.

Lemma MP_iff_sdec_weak_total :
  MP_semidecidable <-> (forall X (R : X -> bool -> Prop), semi_decidable (uncurry R) -> forall x, ~~ (exists b, R x b) -> exists b, R x b).
Proof.
  split.
  - intros H X R [f Hf] x Hx.
    eapply H with (x := x).
    eapply semi_decidable_ext.
    2: eapply (@semi_decidable_or _ (fun x => R x true) (fun x => R x false)).
    + clear. intros x. split. firstorder. intros [[] ?]; firstorder.
    + exists (fun x n => f (x, true) n). intros x0. red in Hf.
      now rewrite (Hf (x0, true)). 
    + exists (fun x n => f (x, false) n). intros x0. red in Hf.
      now rewrite (Hf (x0, false)).
    + eassumption.
  - intros H X p [f Hf] x Hx.
    edestruct (H X (fun x b => p x)).
    + exists (fun '(x, b) n => f x n). intros (?, b). cbn. eapply Hf.
    + intros Hp. eapply Hx. intros Hpx. eapply Hp. exists true. eassumption.
    + eassumption.
Qed.

Lemma MP_cosdec_to_sdec :
  MP ->
  (forall X (p : X -> Prop), co_semi_decidable p -> semi_decidable (compl p)).
Proof.
  intros mp X p [f Hf]. exists f. unfold semi_decider, compl.
  intros x. red in Hf. rewrite Hf. rewrite forall_neg_exists_iff.
  split; eauto.
Qed.

Lemma MP_partial_to_MP {Part : partiality} X (x0 : X) :
  (forall x : part X, ~~ ter x -> ter x) -> MP.
Proof.
  intros mp f Hf.
  destruct (mp (bind (mu_tot f) (fun _ => ret x0))) as [? H].
  intros H. apply Hf. intros [n [m Hm] % mu_tot_ter].
  apply H. exists x0.
  eapply bind_hasvalue.
  exists m. split; eauto. eapply ret_hasvalue.
  eapply bind_hasvalue in H as (? & [] % mu_tot_hasvalue & ?).
  eauto.
Qed.

Lemma MP_to_MP_partial {Part : partiality} :
  MP -> (forall X, forall x : part X, ~~ ter x -> ter x).
Proof.
  intros MP X x.
  assert (ter x <-> exists n, (if seval x n is Some x then true else false) = true). {
    split.
    - intros [a [n H] % seval_hasvalue]. exists n. now rewrite H.
    - intros [n H]. destruct seval as [ a | ] eqn:E; try congruence.
      exists a. eapply seval_hasvalue. eauto.
  }
  rewrite H.
  eapply MP.
Qed.

Section Assume_EA.

  Context {EA : EA}.

  Notation φ := (proj1_sig EA).
  Notation EAP := (proj2_sig EA).

  Lemma MP_iff_stable_W :
    MP <-> Definitions.stable (uncurry W).
  Proof.
    split.
    - intros mp. eapply MP_to_MP_semidecidable; eauto.
      eapply enumerable_semi_decidable. eauto.
      eapply enumerable_W.
    - intros mp. eapply Post_to_MP, Post_logical_to_Post, MP_semidecidable_to_Post_logical,
        MP_semidecidable_nat_to_MP_semidecidable.
      intros p H % enum_iff % m_complete_W.
      eapply red_m_transports_stable. eauto.
      eapply red_m_transitive; eauto. eapply W_uncurry_red.
  Qed.

  Lemma MP_iff_stable_K :
    MP <-> Definitions.stable K0.
  Proof.
    rewrite MP_iff_stable_W.
    split; intros; eapply red_m_transports_stable; eauto.
    - eapply K0_red.
    - eapply red_m_transitive. eapply W_uncurry_red'. eapply W_red_K0.
  Qed.

  Lemma MP_iff_every_stable_m_complete :
    MP <-> forall p : nat -> Prop, enumerable p -> m-complete p -> Definitions.stable p.
  Proof.
    rewrite MP_iff_stable_K. split.
    - intros H p He Hp. eapply red_m_transports_stable. exact H.
      eapply m_complete_K0; eauto.
    - intros H. eapply H. eapply K0_enum. eapply m_complete_K0.
  Qed.

  Lemma MP_iff_any_stable_m_complete :
    MP <-> exists p : nat -> Prop, enumerable p /\ m-complete p /\ Definitions.stable p.
  Proof.
    rewrite MP_iff_every_stable_m_complete. split.
    - intros H. exists K0. repeat split. 3: eapply H.
      all: eauto using m_complete_K0, K0_enum.
    - intros (p & He & Hm & Hp) q Heq Hmq.
      eapply red_m_transports_stable. exact Hp.
      eapply Hm; eauto.
  Qed.

End Assume_EA.

Lemma DNE_sdec_to_cosdec :
  DNE ->
  (forall X (p : X -> Prop), semi_decidable (compl p) -> co_semi_decidable p).
Proof.
  intros mp X p [f Hf]. exists f. unfold semi_decider, compl in *.
  intros x. rewrite forall_neg_exists_iff. rewrite <- Hf. 
  split; eauto. eapply mp.
Qed.

Require Import SyntheticComputability.Shared.FinitenessFacts.

Require Import SyntheticComputability.Shared.Dec.

Lemma semi_decidable_generative (p : nat -> Prop) :
  MP -> semi_decidable p ->
  ~ exhaustible p -> generative p.
Proof.
  intros mp % MP_to_MP_semidecidable % MP_semidecidable_to_MP_semidecidable_ex Hs Hl l.
  eapply mp.
  - eapply semi_decidable_and. eauto. eapply decidable_semi_decidable, decidable_complement, listable_decidable.
    eapply discrete_nat. exists l. red. reflexivity.
  - apply non_finite_spec; eauto. intros. destruct (Nat.eqb_spec x1 x2); firstorder.
Qed.

Lemma MP_non_finite_generative (p : nat -> Prop) :
  MP -> enumerable p ->
  ~ exhaustible p -> generative p.
Proof.
  intros.
  eapply semi_decidable_generative; eauto.
  eapply enum_iff; eauto.
Qed.

(** ** Choice axioms *)

Definition AC_on X Y :=
  forall R : X -> Y -> Prop, (forall x, exists y, R x y) -> exists f : X -> Y, forall x, R x (f x).

Definition AC := forall X Y, AC_on X Y.

Definition UNIF_on X Y := forall R : X -> Y -> Prop,
  (forall x, exists y, R x y) -> exists R' : X -> Y -> Prop, (forall x y, R' x y -> R x y) /\ (forall x, exists! y, R' x y).

Definition AUC_on X Y :=
  forall R : X -> Y -> Prop, (forall x, exists! y, R x y) -> exists f : X -> Y, forall x, R x (f x).

Definition AC_0_0 :=
  AC_on nat nat.

Definition AC_1_0 :=
  AC_on (nat -> nat) nat.

Definition ADC_on X := forall R : X -> X -> Prop, forall x0, (forall x, exists x', R x x') -> exists f : nat -> X, f 0 = x0 /\ forall n, R (f n) (f (S n)).

Definition ADC := forall X, ADC_on X.
Definition ACC := forall X, AC_on nat X.

Lemma total_list {X Y} {R : X -> Y -> Prop} L :
  (forall x, exists y, R x y) -> exists L', Forall2 R L L'.
Proof.
  intros HTot. induction L as [ | x L [L' IH]].
  - exists []. econstructor.
  - destruct (HTot x) as [y H]. exists (y :: L').
    now econstructor. 
Qed.

Lemma AC_rel_to_ADC : forall X, AC_on X X -> ADC_on X.
Proof.
  intros X C R x0 Htot.
  eapply C in Htot as [f].
  exists (fun n => Nat.iter n f x0).
  split. reflexivity. intros n. eapply H.
Qed.

Lemma AC_on_to_AUC_on : forall X Y, AC_on X Y -> AUC_on X Y.
Proof.
  intros X Y C R H. eapply C. firstorder.
Qed.

Goal AC -> ADC.
Proof.
  intros ? X Inh.
  eapply AC_rel_to_ADC, H.
Qed.

Goal ADC -> ACC.
Proof.
  intros C X R Htot.
  destruct (Htot 0) as [y0 Hy0].
  unshelve epose proof (C (∑ '(n, x), R n x) (fun '(exist _  (n, x) H) '(exist _ (m, y) H2) => m = S n)).
  unshelve edestruct H as [f].
  - eexists (_, _). eauto.
  - intros [(n, x) H']. destruct (Htot (S n)) as [y Hy]. now exists (exist _ (S n, y) Hy). 
  - clear H. destruct H0 as [H0 H].
    pose (N n := fst (proj1_sig (f n))).
    pose (s n := snd (proj1_sig (f n))).
    assert (HN : forall n, N (S n) = S (N n)). {
      intros n. cbv.
      pose proof (H (S n)) as Hsn.
      pose proof (H n) as Hn. 
      destruct (f n) as [(m', y') H'].
      destruct (f (S n)) as [(m, y) Hmy]. eassumption.
    }
    assert (HN0 : forall n, N n = N 0 + n) by (induction n; rewrite ?HN; lia).
    assert (H1 : forall n, R (N n) (s n)). {
      intros n. unfold N, s.
      specialize (H n).
      destruct (f n) as [(m, y) Hmy]. exact Hmy.
    }
    pose proof (total_list (seq 0 (N 0)) Htot) as [L' HL'].
    exists (fun n => if le_lt_dec (N 0) n is left _ then s (n - N 0) else (nth n L' (s 0))). intros n.
    destruct (le_lt_dec (N 0) n) as [Hl | Hl].
    + specialize (H1 (n - N 0)). rewrite HN0 in H1.
      now replace n with (N 0 + (n - N 0)) at 1 by lia.
    + rewrite nth_lookup.
      destruct (L' !! n) as [x|] eqn:E.
      * cbn. 
        edestruct (Forall2_lookup_l R (seq 0 (N 0)) L') as [? []]. eassumption.
        rewrite lookup_seq; eauto.
        rewrite E in H2. inv H2. eassumption.
      * eapply lookup_ge_None in E. erewrite <- Forall2_length in E; eauto.
        rewrite seq_length in E. lia.
Qed.

Goal ACC -> AC_0_0.
Proof.
  unfold ACC, AC_0_0.
  intros H. eapply H. 
Qed.

Lemma AC_1_0_to_AC_0_0 : AC_1_0 -> AC_0_0.
Proof.
  intros C R Htot.
  destruct (C (fun g x => R (g 0) x)) as [f].
  - intros g. eapply Htot.
  - exists (fun x => f (fun _ => x)).
    intros x. eapply (H (fun _ => x)).
Qed.

Lemma AC_0_0_to_AC_nat_bool : AC_0_0 -> AC_on nat bool.
Proof.
  intros C R Htot.
  destruct (C (fun n m => R n (Nat.eqb m 0))) as [f].
  - intros x. destruct (Htot x) as [ [] ].
    + exists 0. firstorder.
    + exists 1. firstorder.
  - eexists. eapply H.
Qed.

Lemma UNIFx_char X Y :
  AC_on X Y <-> AUC_on X Y /\ UNIF_on X Y.
Proof.
  split. 1: intros C; split.
  - intros R Htot. edestruct (C R) as [f Hf]; firstorder.
  - intros R [f Hf] % C. exists (fun x y => f x = y). now firstorder subst.
  - intros [C1 C2] R Htot.
    specialize (C2 _ Htot) as (R' & H1 & H2).
    destruct (C1 _ H2) as [f Hf]. eauto.
Qed.

Lemma Diaconescu :
  (forall X Y, AC_on X Y) -> Fext -> Pext -> LEM.
Proof.
  intros C fext pext P.
  pose (U (x : bool) := x = true \/ P).
  pose (V (x : bool) := x = false \/ P).
  destruct (C ({ p : bool -> Prop | p = U \/ p = V}) bool (fun p b => (proj1_sig p b))) as [f Hf].
  - intros (p & [-> | ->]); cbn.
    + exists true. now left.
    + exists false. now left.
  - pose proof (Hf (exist _ U (or_introl eq_refl))) as H1. 
    pose proof (Hf (exist _ V (or_intror eq_refl))) as H2. cbn in *.
    assert (f (exist _ U (or_introl eq_refl)) <> f (exist _ V (or_intror eq_refl)) \/ P) as [H3 | H3]; eauto.
    {
      destruct H1 as [H1 | H1], H2 as [H2 | H2]; eauto.
      firstorder congruence.
    }
    right. intros H.
    assert (U = V) as ->. {
      eapply fext. intros b. eapply pext.
      unfold U, V. intuition.
    }
    eapply H3. repeat f_equal.
    eapply (Pext_to_PI pext).
Qed.

(* *** Compatibility  *)
(* 
Lemma AC_1_0_Fext :
  AC_1_0 -> Fext -> EA -> decidable (compl K_nat_nat).
Proof.
  intros C Fext EA.
  pose proof (fun f => enumerable_code EA _ (enumerable_graph' f)).
  eapply C in H as [code Hcode].
  exists (fun f => Nat.eqb (code f) (code (fun _ => 0))).
  eapply Proper_decider. intros ?. reflexivity.
  eapply (K_nat_equiv).
  intros f. split; rewrite NPeano.Nat.eqb_eq.
  - intros E.
    eapply f_equal, Fext, E.
  - intros E n.
    generalize (Hcode f), (Hcode (fun _ => 0)).
    rewrite E. clear E.
    intros Hf H.
    pose proof(enumerator_ext Hf H (ltac:(reflexivity)) ⟨ n, f n ⟩) as E.
    destruct E as [[x E%(f_equal unembed)] _]; eauto.
    rewrite !embedP in E. now inv E.
Qed. *)

Lemma AUC_to_dec (p : nat -> Prop) :
  AUC_on nat bool -> (forall n, p n \/ ~ p n) -> decidable p.
Proof.
  intros C Hp.
  destruct (C (fun n b => (p n /\ b = true) \/ (~ p n /\ b = false))) as [f Hf].
  - intros n. destruct (Hp n) as [H | H].
    + exists true.  split. left. eauto. intros [];  firstorder congruence. congruence.
    + exists false. split. right. eauto. intros []; firstorder congruence. congruence.
  - exists f. intros n. destruct (Hf n) as [[H ->] | [H ->]]; firstorder congruence. congruence.
Qed.

Lemma AC_0_0_LPO_incompat' {Part : partiality} :
  AUC_on nat bool -> WLPO -> EPF_bool -> forall p : nat -> Prop,
    semi_decidable p -> decidable (compl p).
Proof.
  intros C LPO % WLPO_semidecidable_iff EPF p Hp. 
  eapply AUC_to_dec; eauto.
Qed.

Lemma AC_0_0_LPO_incompat {Part : partiality} :
  AUC_on nat bool -> WLPO -> EPF_bool -> False.
Proof.
  intros C LPO EPF_bool.
  destruct (EPF_SCT_halting) as (K & H1 & H2 & H3 & H4); [eauto|].
  eapply H4. eapply AC_0_0_LPO_incompat'; eauto.
Qed.

Lemma AC_1_0_Fext_CODING :
  AC_1_0 -> Fext -> SCT -> CODING.
Proof.
  intros C Fext (ϕ & Hmono & Hϕ).
  assert (forall f : nat -> nat, exists c, forall x, exists n, ϕ c x n = Some (f x)) as [F HF] % C. {
    intros f. destruct (Hϕ (fun _ => f)) as [c Hc].
    eexists. eapply (Hc 0).
  } 
  exists (fun (f : nat -> bool) => F (fun x : nat => if f x then 0 else 1)).
  intros f. split.
  + intros H x.
    pose proof (HF (λ _ : nat, 1) x) as [n1 Hn1]. rewrite <- H in Hn1.
    pose proof (HF (λ x : nat, if f x then 0 else 1) x) as [n2 Hn2].
    eapply monotonic_agnostic in Hn1. 2: eapply Hmono.
    eapply Hn1 in Hn2. destruct (f x); congruence.
  + intros H2. f_equal. eapply Fext. intros x. rewrite H2. reflexivity.
Qed.

Lemma AC_1_0_Fext_incompat {Part : partiality} :
  AC_1_0 -> Fext -> SCT -> False.
Proof.
  intros C funext ct.
  eapply K_nat_bool_undec; [ eauto | ].
  now eapply no_CODING, AC_1_0_Fext_CODING.
Qed.

(** ** Brouwer's intuitionism *)

Definition WC_N :=
  forall R : (nat -> nat) -> nat -> Prop,
    (forall α, exists x, R α x) -> forall α, exists L, exists y, forall β, map α L = map β L -> R β y.

Lemma max_list_with_spec' {X} (l : list X) f :
  l <> nil -> In (max_list_with f l) (map f l).
Proof.
  destruct l as [ | x l] using rev_ind; try congruence.
  clear IHl. intros _. induction l; cbn in *.
  - lia.
  - destruct (Nat.max_dec (f a) (max_list_with f (l ++ [x]))) as [H1 | H1].
    + now left.
    + right. rewrite H1 in *. eauto.
Qed.

Lemma max_list_spec' l :
  l <> nil -> In (max_list l) l. 
Proof.
  intros H % (max_list_with_spec' _ id).
  now rewrite map_id in H.
Qed.

Lemma max_list_with_spec {X} (x : X) l f :
  In x l -> f x <= max_list_with f l.
Proof.
  intros H.
  induction l in x, H |- *.
  - inv H.
  - inv H; cbn.
    + lia. 
    + eapply IHl in H0. lia.
Qed.

Lemma max_list_spec x l :
  In x l -> x <= max_list l.
Proof.
  eapply (max_list_with_spec x l id).
Qed.

Lemma WC_N_CT_inc :
  WC_N -> SCT -> False.
Proof.
  intros WC [ϕ [Hm CT]].
  edestruct (WC (fun α c => forall x, exists n, ϕ c x n = Some (α x))) with (α := fun x : nat => 0) as [L [c H]].
  - intros f. destruct (CT (fun _ => f)) as [c]. eexists. eapply (H 0).
  - unshelve epose proof (H (fun x => if ListDec.In_dec Nat.eq_dec x L is left _ then 0 else 1) _).
    + eapply map_ext_in. intros a Ha. now destruct List.In_dec.
    + destruct (H0 (1 + max_list L)).
      destruct (H _ eq_refl (1 + max_list L)).
      enough (1 = 0) by lia.
      eapply monotonic_agnostic.
      * eapply Hm.
      * rewrite H1. destruct ListDec.In_dec as [HH | HH].
        -- eapply max_list_spec in HH. lia.
        -- reflexivity.
      * eauto.
Qed.

Definition Cont := forall F : (nat -> nat) -> nat, forall f, exists L, forall g, map f L = map g L -> F f = F g.

Lemma WC_N_to_Cont :
  WC_N -> Cont.
Proof.
  intros H F f.
  edestruct (H (fun f n => F f = n)) as (L & c & Hc).
  + eauto.
  + exists L. intros g Hg.
    eapply Hc in Hg. rewrite Hg.
    now eapply Hc.
Qed.

Definition ADC_on' X := forall R : list X -> X -> Prop, (forall x, exists x', R x x') -> exists f : nat -> X, forall n, R (map f (seq 0 n)) (f n).

Lemma ADC_on'_iff :
  AC_on nat bool -> ADC_on' bool.
Proof.
  intros C R Htot.
  assert (datatype (list bool)) as (G & F & HFG). {
      eapply enumerable_discrete_datatype; eauto.
      eapply discrete_iff. econstructor. exact _.
  }
  pose (F' n := match F n with Some u => u | _ => [] end).
  destruct (C (fun n b => R (F' n) b)) as [f Hf]; eauto.
  pose (f' := fix f' n := match n with 0 => [] | S n => f' n ++ [f (G (f' n))] end).
  assert (Hlen : forall n, length (f' n) = n) by (induction n; cbn; rewrite ?app_length; cbn; lia).
  exists (fun n => nth n (f' (S n)) false).
  cbn. intros n.
  rewrite app_nth2. 2: rewrite Hlen; lia.
  assert (n - length (f' n) = 0) as -> by (rewrite Hlen; lia). cbn.
  specialize (Hf (G (f' n))).
  enough ((F' (G (f' n))) = map (λ n0 : nat, nth n0 (f' n0 ++ [f (G (f' n0))]) false) (seq 0 n)) by congruence.
  unfold F'. rewrite HFG.
  erewrite map_ext. 2:{
    intros a. rewrite app_nth2. 2: rewrite Hlen; lia.
    assert (a - length (f' a) = 0) as -> by (rewrite Hlen; lia). cbn. reflexivity.
  }
  clear.
  induction n.
  - reflexivity.
  - cbn [f']. replace (S n) with (n + 1) by lia.
    rewrite seq_app, map_app. cbn. congruence.
Qed.
