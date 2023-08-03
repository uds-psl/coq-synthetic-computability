(** * Kleene-Post Theorem *)

From SyntheticComputability Require Import TuringReducibility.OracleComputability partial.
Require Import Lia List.
Import ListNotations.

Section Part.

(* Assumptions *)

Context {Part : partiality}.

Notation "R <<= S" := (forall x y, R x y -> S x y) (at level 30).
Notation "R == S" := (forall x y, R x y <-> S x y) (at level 30).

Variable lenum : list bool -> nat.
Variable lenum' : nat -> list bool.
Hypothesis lenum_lenum' : forall s, lenum' (lenum s) = s.

Variable Xi : nat -> Functional nat bool nat bool.
Hypothesis Xi_comp : forall n, OracleComputable (Xi n).
Hypothesis Xi_enum : forall F, OracleComputable F -> exists c, forall R, Xi c R == F R.

Lemma Xi_func e p :
  functional p -> functional (Xi e p).
Proof.
  apply OracleComputable_functional. apply Xi_comp.
Qed.

Lemma Xi_bound e p n b :
  Xi e p n b -> exists N, forall (q : nat -> bool -> Prop), (forall n b, n < N -> p n b -> q n b) -> Xi e q n b.
Proof.
  intros H. apply cont_to_cont in H as [L HL]; try apply Xi_comp.
  exists (S (list_max L)). intros q Hq. apply HL.
  intros n' b' Hn. apply Hq. apply list_max_spec in Hn. lia.
Qed.

Lemma Xi_mono e (p q : nat -> bool -> Prop) :
  p <<= q -> Xi e p <<= Xi e q.
Proof.
  intros H n b [N HN] % Xi_bound. apply HN. intros n' b' _. apply H.
Qed.

(* Prelims *)

Lemma lenum_inj s t :
  lenum s = lenum t -> s = t.
Proof.
  rewrite <- (lenum_lenum' s) at 2. rewrite <- (lenum_lenum' t) at 2. now intros ->.
Qed.

Definition char_rel' (P : nat -> Prop) : FunRel nat bool.
Proof.
  exists (char_rel P). apply char_rel_functional.
Defined.

Lemma nat_even_odd n :
  { k | n = 2 * k } + { k | n = S (2 * k) }.
Proof.
  induction n.
  - left. exists 0. reflexivity.
  - destruct IHn as [[k Hk]|[k Hk]].
    + right. exists k. lia.
    + left. exists (S k). lia.
Qed.

Definition bools_to_funrel (L : list bool) : FunRel nat bool.
Proof.
  exists (fun n b => nth_error L n = Some b).
  abstract (intros n H1 H2; congruence).
Defined.

Definition prefix (sigma tau : list bool) :=
  exists rho, sigma ++ rho = tau.

Lemma prefix_refl sigma :
  prefix sigma sigma.
Proof.
  exists nil. apply app_nil_r.
Qed.

Lemma prefix_trans s t u :
  prefix s t -> prefix t u -> prefix s u.
Proof.
  intros [t' <-] [u' <-]. exists (t' ++ u'). apply app_assoc.
Qed.

Lemma prefix_dec s t :
  {prefix s t} + {~ prefix s t}.
Proof.
  induction s in t |- *.
  - left. exists t. reflexivity.
  - destruct t as [|[] t].
    + right. intros [t Ht]. cbn in Ht. congruence.
    + destruct a.
      * destruct (IHs t) as [H|H].
        -- left. destruct H as [u Hu]. exists u. cbn. congruence.
        -- right. intros [u Hu]. apply H. exists u. cbn in Hu. congruence.
      * right. intros [u Hu]. cbn in Hu. congruence.
    + destruct a.
      * right. intros [u Hu]. cbn in Hu. congruence.
      * destruct (IHs t) as [H|H].
        -- left. destruct H as [u Hu]. exists u. cbn. congruence.
        -- right. intros [u Hu]. apply H. exists u. cbn in Hu. congruence.
Qed.

Lemma prefix_length s t :
  prefix s t -> length s <= length t.
Proof.
  intros [u <-]. rewrite app_length. lia.
Qed.

Lemma prefix_sub s t :
  prefix s t -> bools_to_funrel s <<= bools_to_funrel t.
Proof.
  intros [u <-] n b Hn. unfold bools_to_funrel. cbn in *. rewrite nth_error_app1; trivial.
  apply nth_error_Some. intros H. rewrite H in Hn. discriminate.
Qed.

(* Degree construction *)

Inductive sigtau : nat -> list bool -> list bool -> Prop :=
| base : sigtau 0 nil nil
| even_step1 e sigma tau rho b : sigtau (2 * e) sigma tau -> prefix sigma rho
                           -> (forall rho' b, prefix sigma rho' -> lenum rho' < lenum rho
                                        -> ~ Xi e (bools_to_funrel rho') (length tau) b)
                           -> Xi e (bools_to_funrel rho) (length tau) b
                           -> sigtau (S (2 * e)) rho (tau ++ [negb b])
| even_step2 e sigma tau : sigtau (2 * e) sigma tau
                       -> (~ exists rho b, prefix sigma rho /\ Xi e (bools_to_funrel rho) (length tau) b)
                       -> sigtau (S (2 * e)) sigma (tau ++ [false])
| odd_step1 e sigma tau rho b : sigtau (S (2 * e)) sigma tau -> prefix tau rho
                          -> (forall rho' b, prefix tau rho' -> lenum rho' < lenum rho
                                        -> ~ Xi e (bools_to_funrel rho') (length sigma) b)
                          -> Xi e (bools_to_funrel rho) (length sigma) b
                          -> sigtau (S (S (2 * e))) (sigma ++ [negb b]) rho
| odd_step2 e sigma tau : sigtau (S (2 * e)) sigma tau
                      -> (~ exists rho b, prefix tau rho /\ Xi e (bools_to_funrel rho) (length sigma) b)
                      -> sigtau (S (S (2 * e))) (sigma ++ [false]) tau.

Definition A n :=
  exists k, forall s t, sigtau k s t -> nth_error s n = Some true.

Definition B n :=
  exists k, forall s t, sigtau k s t -> nth_error t n = Some true.

(* Properties of sigtau: functionality, totality, cumulativity, agreement, unboundedness *)

Lemma sigtau_fun n sigma tau sig' tau' :
  sigtau n sigma tau -> sigtau n sig' tau' -> sigma = sig' /\ tau = tau'.
Proof.
  induction 1 in sig', tau' |- *.
  - inversion 1; auto.
  - inversion 1; subst; try lia; assert (e = e0) as -> by lia.
    + apply IHsigtau in H5 as [-> ->].
      destruct (PeanoNat.Nat.lt_total (lenum rho) (lenum sig')) as [Hr|[Hr|Hr]].
      * exfalso. now apply (H7 rho b).
      * apply lenum_inj in Hr. subst. split; trivial. repeat f_equal.
        eapply Xi_func; eauto. apply the_func_proof.
      * exfalso. now apply (H1 sig' b0).
    + apply IHsigtau in H5 as [-> ->]. contradict H6. eauto.
  - inversion 1; subst; try lia; assert (e = e0) as -> by lia.
    + apply IHsigtau in H3 as [-> ->]. contradict H0. eauto.
    + apply IHsigtau in H3 as [-> ->]. tauto.
  - inversion 1; subst; try lia; assert (e = e0) as -> by lia.
    + apply IHsigtau in H5 as [-> ->].
      destruct (PeanoNat.Nat.lt_total (lenum rho) (lenum tau')) as [Hr|[Hr|Hr]].
      * exfalso. now apply (H7 rho b).
      * apply lenum_inj in Hr. subst. split; trivial. repeat f_equal.
        eapply Xi_func; eauto. apply the_func_proof.
      * exfalso. now apply (H1 tau' b0).
    + apply IHsigtau in H5 as [-> ->]. contradict H6. eauto.
  - inversion 1; subst; try lia; assert (e = e0) as -> by lia.
    + apply IHsigtau in H3 as [-> ->]. contradict H0. eauto.
    + apply IHsigtau in H3 as [-> ->]. tauto.
Qed.

Lemma wf_ind (P : nat -> Prop) :
  (forall n, (forall k, k < n -> P k) -> P n) -> forall n, P n.
Proof.
  intros HI n. apply HI. induction n.
  - lia.
  - intros k H. apply HI. intros k' H'. apply IHn. lia.
Qed.

Definition DNLEM P :
  ~ ~ (P \/ ~ P).
Proof.
  tauto.
Qed.

Lemma least_doubleneg (P : nat -> Prop) :
  (exists n, P n) -> ~ ~ exists n, P n /\ forall k, k < n -> ~ P k.
Proof.
  intros [n Hn]. induction n as [n IH] using wf_ind.
  intros HL. apply (@DNLEM (exists k, k < n /\ P k)). intros [[k Hk]|H].
  - apply (IH k); tauto.
  - apply HL. exists n. split; trivial. intros k H1 H2. apply H. exists k. tauto.
Qed.

Lemma least_termination (f : Functional nat bool nat bool) sigma n :
  (exists rho b, prefix sigma rho /\ f (bools_to_funrel rho) n b) ->
  ~ ~ (exists rho b, prefix sigma rho /\ f (bools_to_funrel rho) n b
            /\ forall rho' b, prefix sigma rho' -> lenum rho' < lenum rho
                        -> ~ f (bools_to_funrel rho') n b).
Proof.
  intros H1 H2.
  apply (@least_doubleneg (fun k => exists rho, k = lenum rho /\ prefix sigma rho /\ exists b, f (bools_to_funrel rho) n b)).
  - destruct H1 as [rho[b H]]. exists (lenum rho), rho. intuition eauto.
  - intros [k [[rho[-> [H[b Hb]]]] H']]. apply H2. exists rho, b. repeat split; trivial.
    intros rho' b'. intros H3 H4 H5. apply (H' (lenum rho')); eauto.
Qed.

Lemma sigtau_tot n :
  ~ ~ exists sigma tau, sigtau n sigma tau.
Proof.
  induction n.
  - intros H. apply H. exists nil, nil. constructor.
  - intros H. apply IHn. intros (sigma & tau & Hn).
    destruct (nat_even_odd n) as [[e He]|[e He]].
    + apply (@DNLEM (exists rho b, prefix sigma rho /\ Xi e (bools_to_funrel rho) (length tau) b)).
      intros [Hr|Hr]; subst n.
      * apply (least_termination Hr). intros [rho[b Hb]]. apply H.
        exists rho, (tau ++ [negb b]). eapply even_step1; intuition eauto.
      * apply H. exists sigma, (tau ++ [false]). apply (even_step2 Hn). firstorder.
    + apply (@DNLEM (exists rho b, prefix tau rho /\ Xi e (bools_to_funrel rho) (length sigma) b)).
      intros [Hr|Hr]; subst n.
      * apply (least_termination Hr). intros [rho[b Hb]]. apply H.
        exists (sigma ++ [negb b]), rho. eapply odd_step1; intuition eauto.
      * apply H. exists (sigma ++ [false]), tau. apply (odd_step2 Hn). firstorder.
Qed.

Lemma sigtau_step n sigma tau sig' tau' :
  sigtau n sigma tau -> sigtau (S n) sig' tau' -> prefix sigma sig' /\ prefix tau tau'.
Proof.
  intros H1 H2. inversion H2; subst.
  - assert (sigma0 = sigma /\ tau0 = tau) as [-> ->] by apply (sigtau_fun H0 H1).
    split; try tauto. now exists [negb b].
  - assert (sig' = sigma /\ tau0 = tau) as [-> ->] by apply (sigtau_fun H0 H1).
    split; try apply prefix_refl. now exists [false].
  - assert (sigma0 = sigma /\ tau0 = tau) as [-> ->] by apply (sigtau_fun H0 H1).
    split; try tauto. now exists [negb b].
  - assert (sigma0 = sigma /\ tau' = tau) as [-> ->] by apply (sigtau_fun H0 H1).
    split; try apply prefix_refl. now exists [false].
Qed.

Lemma sigtau_cum n k sigma tau sig' tau' :
  sigtau n sigma tau -> n <= k -> sigtau k sig' tau' -> prefix sigma sig' /\ prefix tau tau'.
Proof.
  intros Hn H Hk. induction H in sig', tau', Hk |- *.
  - assert (sig' = sigma /\ tau' = tau) as [-> ->] by apply (sigtau_fun Hk Hn). split; apply prefix_refl.
  - destruct (prefix_dec sigma sig') as [Hs|Hs], (prefix_dec tau tau') as [Ht|Ht]; try tauto; exfalso.
    all: apply (@sigtau_tot m); intros (s & t & Hst); eapply sigtau_step in Hk; eauto.
    all: apply IHle in Hst; intuition eauto using prefix_trans.
Qed.

Lemma sigma_agree k s t k' s' t' n b b' :
  sigtau k s t -> sigtau k' s' t' -> bools_to_funrel s n b -> bools_to_funrel s' n b' -> b = b'.
Proof.
  intros Hk Hk' Hb Hb'. assert (k <= k' \/ k' <= k) as [H|H] by lia.
  - apply (prefix_sub (t:=s')) in Hb; try apply (sigtau_cum Hk H Hk'). apply (the_func_proof Hb Hb').
  - apply (prefix_sub (t:=s)) in Hb'; try apply (sigtau_cum Hk' H Hk). apply (the_func_proof Hb Hb').
Qed.

Lemma tau_agree k s t k' s' t' n b b' :
  sigtau k s t -> sigtau k' s' t' -> bools_to_funrel t n b -> bools_to_funrel t' n b' -> b = b'.
Proof.
  intros Hk Hk' Hb Hb'. assert (k <= k' \/ k' <= k) as [H|H] by lia.
  - apply (prefix_sub (t:=t')) in Hb; try apply (sigtau_cum Hk H Hk'). apply (the_func_proof Hb Hb').
  - apply (prefix_sub (t:=t)) in Hb'; try apply (sigtau_cum Hk' H Hk). apply (the_func_proof Hb Hb').
Qed.

Lemma sigtau_length n s t :
  sigtau (2 * n) s t -> n <= length s /\ n <= length t.
Proof.
  induction n in s, t |- *; cbn; try lia.
  assert (S (n + S (n + 0)) = S (S (2 * n))) as -> by lia.
  inversion 1; subst; try lia; inversion H1; subst; try lia; assert (n = e0) as <- by lia.
  - apply IHn in H6. split.
    + rewrite app_length. cbn. apply prefix_length in H7. lia.
    + apply prefix_length in H2. rewrite app_length in H2. cbn in H2. lia.
  - apply IHn in H6. split.
    + rewrite app_length. cbn. lia.
    + apply prefix_length in H2. rewrite app_length in H2. cbn in H2. lia.
  - apply IHn in H4. split.
    + rewrite app_length. cbn. apply prefix_length in H5. lia.
    + rewrite app_length. cbn. lia.
  - apply IHn in H4. split.
    + rewrite app_length. cbn. lia.
    + rewrite app_length. cbn. lia.
Qed.

Lemma sigtau_length' k n s t :
  2 * n <= k -> sigtau k s t -> n <= length s /\ n <= length t.
Proof.
  intros Hk Hst. destruct (Compare_dec.le_dec n (length s)) as [H|H], (Compare_dec.le_dec n (length t)) as [H'|H'].
  all: try tauto. all: exfalso; apply (@sigtau_tot (2 * n)); intros (s' & t' & Hst').
  - apply H'. assert (length t' <= length t) by apply prefix_length, (sigtau_cum Hst' Hk Hst).
    apply sigtau_length in Hst'. lia.
  - apply H. assert (length s' <= length s) by apply prefix_length, (sigtau_cum Hst' Hk Hst).
    apply sigtau_length in Hst'. lia.
  - apply H'. assert (length t' <= length t) by apply prefix_length, (sigtau_cum Hst' Hk Hst).
    apply sigtau_length in Hst'. lia.
Qed.

(* Obtained functional relations *)

Definition sigmas (n : nat) : FunRel nat bool.
Proof.
  exists (fun k b => forall sigma tau, sigtau n sigma tau -> bools_to_funrel sigma k b).
  intros k [] [] H1 H2; trivial; exfalso.
  all: apply (@sigtau_tot n); intros (sigma & tau & H).
  - enough (true = false) by congruence. apply (the_func_proof (H1 sigma tau H) (H2 sigma tau H)).
  - enough (false = true) by congruence. apply (the_func_proof (H1 sigma tau H) (H2 sigma tau H)).
Defined.

Definition taus (n : nat) : FunRel nat bool.
Proof.
  exists (fun k b => forall sigma tau, sigtau n sigma tau -> bools_to_funrel tau k b).
  intros k [] [] H1 H2; trivial; exfalso.
  all: apply (@sigtau_tot n); intros (sigma & tau & H).
  - enough (true = false) by congruence. apply (the_func_proof (H1 sigma tau H) (H2 sigma tau H)).
  - enough (false = true) by congruence. apply (the_func_proof (H1 sigma tau H) (H2 sigma tau H)).
Defined.

Lemma sigtau_sigmas s t n :
  sigtau n s t -> bools_to_funrel s == sigmas n.
Proof.
  intros Hn k b. split; intros H.
  - now intros s' t' [-> ->] % (sigtau_fun Hn).
  - apply (H s t Hn).
Qed.

Lemma sigtau_taus s t n :
  sigtau n s t -> bools_to_funrel t == taus n.
Proof.
  intros Hn k b. split; intros H.
  - now intros s' t' [-> ->] % (sigtau_fun Hn).
  - apply (H s t Hn).
Qed.

(* Simple properties of degrees A and B *)

Lemma A_sigmas n sigma tau :
  sigtau n sigma tau -> bools_to_funrel sigma <<= char_rel A.
Proof.
  intros Hn k b Hk. destruct b; cbn.
  - exists n. now intros s t [<- <-] % (sigtau_fun Hn).
  - intros [l Hl]. apply (@sigtau_tot l). intros (s & t & Hs).
    enough (false = true) by congruence. apply (sigma_agree Hn Hs (n:=k)).
    + apply Hk.
    + eapply Hl, Hs.
Qed.

Lemma B_taus n sigma tau :
  sigtau n sigma tau -> bools_to_funrel tau <<= char_rel B.
Proof.
  intros Hn k b Hk. destruct b; cbn.
  - exists n. now intros s t [<- <-] % (sigtau_fun Hn).
  - intros [l Hl]. apply (@sigtau_tot l). intros (s & t & Hs).
    enough (false = true) by congruence. apply (tau_agree Hn Hs (n:=k)).
    + apply Hk.
    + eapply Hl, Hs.
Qed.

Lemma A_tot n :
  ~ ~ exists b, char_rel A n b.
Proof.
  intros H. apply (@sigtau_tot (2 * (S n))).
  intros (s & t & Hst). destruct (sigtau_length Hst) as [Hs _].
  destruct (nth_error s n) as [|] eqn : Hn.
  - apply H. exists b. destruct b; cbn.
    + exists (2 * (S n)). intros s' t' Hst'. apply (sigtau_fun Hst) in Hst' as [-> ->]. apply Hn.
    + intros [k Hk]. apply (@sigtau_tot k). intros (s' & t' & Hst').
      specialize (Hk s' t' Hst'). enough (true = false) by congruence.
      apply (sigma_agree Hst' Hst (n:=n)); eauto.
  - eapply nth_error_Some; eauto. 
Qed.

Lemma B_tot n :
  ~ ~ exists b, char_rel B n b.
Proof.
  intros H. apply (@sigtau_tot (2 * (S n))).
  intros (s & t & Hst). destruct (sigtau_length Hst) as [_ Ht].
  destruct (nth_error t n) as [|] eqn : Hn.
  - apply H. exists b. destruct b; cbn.
    + exists (2 * (S n)). intros s' t' Hst'. apply (sigtau_fun Hst) in Hst' as [-> ->]. apply Hn.
    + intros [k Hk]. apply (@sigtau_tot k). intros (s' & t' & Hst').
      specialize (Hk s' t' Hst'). enough (true = false) by congruence.
      apply (tau_agree Hst' Hst (n:=n)); eauto.
  - eapply nth_error_Some; eauto. 
Qed.

(* Remaining verification using continuity *)

Lemma A_agree N k n b :
   2 * N <= k -> n < N -> char_rel' A n b <-> sigmas k n b.
Proof.
  intros Hk Hn. split; intros H.
  - intros s t Hst. unfold bools_to_funrel. cbn. destruct nth_error as [|] eqn : Hs'.
    + f_equal. symmetry. now apply (the_func_proof H), (A_sigmas Hst).
    + exfalso. eapply nth_error_Some; eauto. apply (sigtau_length' Hk) in Hst. lia.
  - destruct b; cbn.
    + exists k. now intros s t Hst % H.
    + intros [l Hl]. apply (@sigtau_tot l). intros (s & t & Hst).
      apply (@sigtau_tot k). intros (s' & t' & Hst').
      enough (false = true) by congruence. apply (sigma_agree Hst' Hst (n:=n)).
      * now apply (sigtau_sigmas Hst').
      * eapply Hl, Hst.
Qed.

Lemma A_prefix e n b :
  Xi e (char_rel' A) n b -> exists k, ~ ~ Xi e (sigmas k) n b.
Proof.
  intros He. destruct (Xi_bound He) as [N HN]. exists (2 * N).
  intros Hn. apply (@sigtau_tot (2 * N)). intros (s & t & Hst).
  apply Hn. apply HN. intros k b'. now apply A_agree.
Qed.

Lemma A_mono e k sigma tau n b :
  sigtau k sigma tau -> Xi e (bools_to_funrel sigma) n b -> ~ ~ Xi e (char_rel' A) n b.
Proof.
  intros H1 H2. destruct (Xi_bound H2) as [N HN].
  intros Hr. apply (@sigtau_tot (k + 2 * N)). intros (s & t & Hst).
  apply Hr, HN. intros n' b' _. apply (A_sigmas H1).
Qed.

Lemma B_disc e sigma tau sig' tau' b :
  sigtau (2 * e) sigma tau -> sigtau (S (2 * e)) sig' tau'
  -> char_rel' B (length tau) b -> ~ Xi e (char_rel' A) (length tau) b.
Proof.
  intros H. inversion 1; subst; try lia.
  - intros HB HA. assert (e = e0) as <- by lia.
    assert (sigma = sigma0 /\ tau = tau0) as [<- <-] by apply (sigtau_fun H H2). assert (b = negb b0) as ->.
    { apply (the_func_proof HB), (B_taus H0). cbn. now rewrite nth_error_app2, PeanoNat.Nat.sub_diag. }
    apply (A_mono H0) in H5. apply H5. intros H5'.
    apply (Bool.no_fixpoint_negb b0). eapply Xi_func; eauto. apply the_func_proof.
  - intros _ [k Hk] % A_prefix. apply Hk. intros Hk'. assert (e = e0) as <- by lia.
    assert (sigma = sig' /\ tau = tau0) as [<- <-] by apply (sigtau_fun H H2).
    apply (@sigtau_tot k). intros (s & t & Hst).
    assert (k <= 2 * e \/ 2 * e <= k) as [H'|H'] by lia.
    + apply H3. exists sigma, b. split; try apply prefix_refl. eapply Xi_mono; try apply Hk'.
      intros l b' Hl. apply prefix_sub with s; try apply (sigtau_cum Hst H' H).
      apply (sigtau_sigmas Hst), Hl.
    + apply H3. exists s, b. split; try apply (sigtau_cum H H' Hst).
      eapply Xi_mono; try apply Hk'. intros n' b'. apply (sigtau_sigmas Hst).
Qed.

Lemma Kleene_Post1 e :
  ~ char_rel' B <<= Xi e (char_rel' A).
Proof.
  intros H. apply (@sigtau_tot (2 * e)). intros (sigma & tau & Hst).
  apply (@sigtau_tot (S (2 * e))). intros (sig' & tau' & Hst').
  specialize (H (length tau)). apply (@B_tot (length tau)). intros [b Hb].
  specialize (H b). apply (B_disc Hst Hst' Hb). apply H, Hb.
Qed.

Lemma B_agree N k n b :
   2 * N <= k -> n < N -> char_rel' B n b <-> taus k n b.
Proof.
  intros Hk Hn. split; intros H.
  - intros s t Hst. unfold bools_to_funrel. cbn. destruct nth_error as [|] eqn : Hs'.
    + f_equal. symmetry. now apply (the_func_proof H), (B_taus Hst).
    + exfalso. eapply nth_error_Some; eauto. apply (sigtau_length' Hk) in Hst. lia.
  - destruct b; cbn.
    + exists k. now intros s t Hst % H.
    + intros [l Hl]. apply (@sigtau_tot l). intros (s & t & Hst).
      apply (@sigtau_tot k). intros (s' & t' & Hst').
      enough (false = true) by congruence. apply (tau_agree Hst' Hst (n:=n)).
      * now apply (sigtau_taus Hst').
      * eapply Hl, Hst.
Qed.

Lemma B_prefix e n b :
  Xi e (char_rel' B) n b -> exists k, ~ ~ Xi e (taus k) n b.
Proof.
  intros He. destruct (Xi_bound He) as [N HN]. exists (2 * N).
  intros Hn. apply (@sigtau_tot (2 * N)). intros (s & t & Hst).
  apply Hn. apply HN. intros k b'. now apply B_agree.
Qed.

Lemma B_mono e k sigma tau n b :
  sigtau k sigma tau -> Xi e (bools_to_funrel tau) n b -> ~ ~ Xi e (char_rel' B) n b.
Proof.
  intros H1 H2. destruct (Xi_bound H2) as [N HN].
  intros Hr. apply (@sigtau_tot (k + 2 * N)). intros (s & t & Hst).
  apply Hr, HN. intros n' b' _. apply (B_taus H1).
Qed.

Lemma A_disc e sigma tau sig' tau' b :
  sigtau (S (2 * e)) sigma tau -> sigtau (S (S (2 * e))) sig' tau'
  -> char_rel' A (length sigma) b -> ~ Xi e (char_rel' B) (length sigma) b.
Proof.
  intros H. inversion 1; subst; try lia.
  - intros HB HA. assert (e = e0) as <- by lia.
    assert (sigma = sigma0 /\ tau = tau0) as [<- <-] by apply (sigtau_fun H H2). assert (b = negb b0) as ->.
    { apply (the_func_proof HB), (A_sigmas H0). cbn. now rewrite nth_error_app2, PeanoNat.Nat.sub_diag. }
    apply (B_mono H0) in H5. apply H5. intros H5'.
    apply (Bool.no_fixpoint_negb b0). eapply Xi_func; eauto. apply the_func_proof.
  - intros _ [k Hk] % B_prefix. apply Hk. intros Hk'. assert (e = e0) as <- by lia.
    assert (sigma = sigma0 /\ tau = tau') as [<- <-] by apply (sigtau_fun H H2).
    apply (@sigtau_tot k). intros (s & t & Hst).
    assert (k <= S (2 * e) \/ S (2 * e) <= k) as [H'|H'] by lia.
    + apply H3. exists tau, b. split; try apply prefix_refl. eapply Xi_mono; try apply Hk'.
      intros l b' Hl. apply prefix_sub with t; try apply (sigtau_cum Hst H' H).
      apply (sigtau_taus Hst), Hl.
    + apply H3. exists t, b. split; try apply (sigtau_cum H H' Hst).
      eapply Xi_mono; try apply Hk'. intros n' b'. apply (sigtau_taus Hst).
Qed.

Lemma Kleene_Post2 e :
  ~ char_rel' A <<= Xi e (char_rel' B).
Proof.
  intros H. apply (@sigtau_tot (S (2 * e))). intros (sigma & tau & Hst).
  apply (@sigtau_tot (S (S (2 * e)))). intros (sig' & tau' & Hst').
  specialize (H (length sigma)). apply (@A_tot (length sigma)). intros [b Hb].
  specialize (H b). apply (A_disc Hst Hst' Hb). apply H, Hb.
Qed.

(* Main result *)

Theorem KleenePost :
  exists (A B : nat -> Prop), ~ (A ⪯ᴛ B) /\ ~ (B ⪯ᴛ A).
Proof.
  exists A, B. split.
  - intros [F [HF1 HF2]]. destruct (Xi_enum HF1) as [e He].
    apply (Kleene_Post2 (e:=e)). intros n b. cbn. now rewrite HF2, He.
  - intros [F [HF1 HF2]]. destruct (Xi_enum HF1) as [e He].
    apply (Kleene_Post1 (e:=e)). intros n b. cbn. now rewrite HF2, He.
Qed.

Print Assumptions KleenePost.

Lemma computable_nat_rec (Q A O : Type) (F : Functional Q A (nat * O) O) (o0 : O) :
  OracleComputable F -> OracleComputable (fun R n => @nat_rect (fun _ => O -> Prop) (fun o => o0 = o) (fun n r o => exists o', r o' /\ F R (n, o') o) n).

End Part.

