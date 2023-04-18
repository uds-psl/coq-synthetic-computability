Require Import ssreflect Setoid Lia List.
Require Import SyntheticComputability.Shared.embed_nat SyntheticComputability.Shared.mu_nat.
From Coq.Logic Require Import ConstructiveEpsilon.
Import EmbedNatNotations ListNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Definition monotonic {X} (f : nat -> option X) :=
  forall n1 x, f n1 = Some x -> forall n2, n2 >= n1 -> f n2 = Some x.

Definition agnostic {X} (f : nat -> option X) :=
  forall n1 n2 y1 y2, f n1 = Some y1 -> f n2 = Some y2 -> y1 = y2.

Lemma monotonic_agnostic {X} (f : nat -> option X) :
  monotonic f -> agnostic f.
Proof.
  move => mono n1 n2 y1 y2 H1 H2.
  destruct (Compare_dec.le_ge_dec n1 n2) as [l | g].
  - eapply mono in l; eauto. congruence.
  - eapply mono in g; eauto. congruence.
Qed.

Class partiality :=
  {

    part : Type -> Type ;

    hasvalue : forall A, part A -> A -> Prop ;
    hasvalue_det : forall A x (a1 a2 : A), hasvalue x a1 -> hasvalue x a2 -> a1 = a2 ;

    ret : forall A, A -> part A ;
    ret_hasvalue : forall A (a : A), hasvalue (ret a) a ;

    bind : forall A B, part A -> (A -> part B) -> part B ;
    bind_hasvalue : forall A B x(f : A -> part B) b, hasvalue (bind x f) b <-> exists a, hasvalue x a /\ hasvalue (f a) b;

    undef : forall {A}, part A ;
    undef_hasvalue : forall A (a : A), ~ hasvalue undef a ;

    mu : (nat -> part bool) -> part nat ;
    mu_hasvalue : forall (f : nat -> part bool) n, hasvalue (mu f) n <-> (hasvalue (f n) true /\ forall m, m < n -> hasvalue (f m) false);
  
    seval : forall A, part A -> nat -> option A ;
    seval_mono : forall A x, monotonic (@seval A x) ;
    seval_hasvalue : forall A x (a : A), hasvalue x a <-> exists n, seval x n = Some a ;

  }.

Definition ter {Part : partiality} A (x : part A) := exists a, hasvalue x a.
Definition equiv {Part : partiality} A (x y : part A) := forall a, hasvalue x a <-> hasvalue y a.

Notation "a =! b" := (hasvalue a b) (at level 50).

Notation "A ↛ B" := (A -> part B) (at level 10).

Definition pcomputes {X Y} `{partiality} (f : X ↛ Y) (R : X -> Y -> Prop) :=
  forall x y, f x =! y <-> R x y.

Definition functional {X Y} (R : X -> Y -> Prop) :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

Definition total {X Y} (R : X -> Y -> Prop) :=
  forall x, exists y, R x y.

Record FunRel X Y := {the_rel :> X -> Y -> Prop ; the_func_proof : functional the_rel}.
Arguments the_rel {_ _}.

Instance part_equiv_Equivalence `{partiality} {A} :
  Equivalence (@equiv _ A).
Proof.
  firstorder.
Qed.

Section assume_part.

  Context {impl : partiality}.
  
  Lemma ret_hasvalue_inv {A} (a1 a2 : A) :
    ret a1 =! a2 -> a1 = a2.
  Proof.
    move => H.
    eapply hasvalue_det. eapply ret_hasvalue. eauto.
  Qed.

  Lemma ret_hasvalue' {A} (a1 a2 : A) :
    a1 = a2 -> ret a1 =! a2.
  Proof.
    intros ->. eapply ret_hasvalue.
  Qed.
  
  Lemma ret_hasvalue_iff {A} (a1 a2 : A) :
    a1 = a2 <-> ret a1 =! a2.
  Proof.
    split.
    - apply ret_hasvalue'.
    - apply ret_hasvalue_inv.
  Qed.

  Lemma mu_ter f :
    (exists n, f n =! true /\ forall x, x < n -> ter (f x)) ->
    ter (mu f).
  Proof.
    intros (n & H1 & H2).
    enough (exists n, f n =! true /\ forall x, x < n -> f x =! false) as [m Hm].
    { exists m. eapply mu_hasvalue. eapply Hm. }
    edestruct Wf_nat.dec_inh_nat_subset_has_unique_least_element with (P := fun m => m <= n /\ f m =! true) as (m & [Hm1 Hm2] & HHH).
    - intros n0.
      destruct (Compare_dec.le_dec n0 n); try firstorder congruence.
      assert (n0 = n \/ n0 < n) as [-> | Hl] by lia.
      firstorder.
      eapply H2 in Hl as []. destruct x.
      firstorder congruence.
      right. intros [].
      enough (false = true) by congruence.
      eapply hasvalue_det; eauto.
    - exists n; firstorder.
    - exists m. split. firstorder.
      intros.
      destruct (H2 x). lia.
      destruct x0; eauto.
      enough (m <= x) by lia.
      eapply Hm2. split; eauto. lia.
  Qed.

  Definition mu_tot (f : nat -> bool) := mu (fun n => ret (f n)).

  Lemma mu_tot_hasvalue (f : nat -> bool) n :
    hasvalue (mu_tot f) n <-> (f n = true /\ forall m, m < n -> f m = false).
  Proof.
    unfold mu_tot. rewrite mu_hasvalue. now repeat setoid_rewrite ret_hasvalue_iff.
  Qed.

  Lemma mu_tot_ter (f : nat -> bool) n :
    f n = true ->
    ter (mu_tot f).
  Proof.
    move => H.
    assert (He : exists n, f n = true) by eauto.
    assert (d : forall n, {f n = true} + {~ f n = true}) by (move => n'; destruct (f n'); firstorder congruence).
    destruct (mu_nat_dep _ d He) as [n' Hn'] eqn:E.
    eapply (f_equal (@proj1_sig _ _)) in E.
    exists n'. eapply mu_tot_hasvalue. split.
    - eauto.
    - move => m Hlt. cbn in E. subst.
      eapply mu_nat_dep_min in Hlt. destruct (f m); congruence.
  Qed.

  Definition undef' : forall {A}, A -> part A := fun A a0 => bind (mu_tot (fun _ => false)) (fun n => ret a0).

  Lemma undef'_hasvalue : forall A a0 (a : A), ~ hasvalue (undef' a0) a.
  Proof.
    intros A a0 a [a' [[[=]] % mu_tot_hasvalue H2]] % bind_hasvalue.
  Qed.

  Definition eval' {A} (x : part A) (H : ter x) : {a : A | hasvalue x a}.
  Proof.
    assert (Hx : exists n, seval x n <> None). {
      destruct H as [a [n H] % seval_hasvalue]. exists n. congruence.
    }
    eapply constructive_indefinite_ground_description_nat in Hx as [n Hx].
    - destruct seval eqn:E; try congruence. exists a. eapply seval_hasvalue. firstorder.
    - move => n. destruct seval; firstorder congruence.
  Qed.

  Definition eval {A} (x : part A) (H : ter x) : A := proj1_sig (eval' H).
  Definition eval_hasvalue {A} (x : part A) (H : ter x) : hasvalue x (eval H) := proj2_sig (eval' H).

  Definition mkpart {A} (f : nat -> option A) := 
    bind (mu_tot (fun n => match f n with Some a => true | None => false end)) 
      (fun n => match f n with Some a => ret a | None => undef end).

  Lemma mkpart_hasvalue1 {A} (f : nat -> option A) :
    forall a, mkpart f =! a -> exists n, f n = Some a.
  Proof.
    move => a.
    rewrite /mkpart bind_hasvalue.
    move => [] x [] / mu_hasvalue [] ter_mu Hmu Hf.
    exists x. destruct (f x). eapply (hasvalue_det (ret_hasvalue a0)) in Hf as ->.
    reflexivity. eapply undef_hasvalue in Hf as [].
  Qed.

  Lemma mkpart_ter {A} (f : nat -> option A) n a :
    f n = Some a -> ter (mkpart f).
  Proof.
    move => Hn. unfold ter.
    rewrite /mkpart. setoid_rewrite bind_hasvalue. 
    assert (Hf : exists n, f n <> None). exists n. firstorder congruence.
    assert (d : forall n : nat, {(fun n0 : nat => f n0 <> None) n} + {~ (fun n0 : nat => f n0 <> None) n}). { move => n0. destruct (f n0); firstorder congruence. }
    edestruct (mu_nat_dep _ d Hf) as [m Hm] eqn:E. eapply (f_equal (@proj1_sig _ _)) in E.  cbn in E.
    destruct (f m) as [a0|]eqn:E2; try congruence.
    exists a0, m.
    rewrite mu_tot_hasvalue. repeat split.
    + rewrite E2. reflexivity.
    + subst. move => m' Hle.
      destruct (f m') eqn:E3.
      * eapply mu_nat_dep_min in Hle. firstorder congruence.
      * reflexivity.
    + rewrite E2. eapply ret_hasvalue.
  Qed.

  Lemma mkpart_hasvalue2 {A} (f : nat -> option A) n a :
    agnostic f -> f n = Some a -> mkpart f =! a.
  Proof.
    move => Hagn Hn.
    destruct (mkpart_ter Hn) as [a' H].
    destruct (mkpart_hasvalue1 H) as [n' H'].
    now assert (a' = a) as -> by (eapply Hagn; eauto).
  Qed.

  Lemma mkpart_hasvalue {A} (f : nat -> option A) :
    agnostic f -> forall a, mkpart f =! a <-> exists n, f n = Some a.
  Proof.
    split.
    eapply mkpart_hasvalue1.
    move => [n Hn]. eapply mkpart_hasvalue2; eauto.
  Qed.  

  Definition par : forall A B, part A -> part B -> part (A + B) :=
    fun A B x y => 
    bind (mu_tot (fun n => if seval x n is Some a then true else if seval y n is Some b then true else false))
      (fun n => if seval x n is Some a then ret (inl a) else if seval y n is Some b then ret (inr b) else undef).
  
  Lemma par_hasvalue1 : forall A B (x : part A) (y : part B) a, hasvalue (par x y) (inl a) -> hasvalue x a.
  Proof.  
    intros A B x y a [a' [(H1 & H2) % mu_tot_hasvalue H3]] % bind_hasvalue.
    destruct (seval x a') eqn:E1, (seval y a') eqn:E2; try congruence.
    - eapply ret_hasvalue_iff in H3 as [= ->]. eapply seval_hasvalue. eauto.
    - eapply ret_hasvalue_iff in H3 as [= ->]. eapply seval_hasvalue. eauto.
    - eapply ret_hasvalue_iff in H3 as [= ->].
  Qed.
    
  Lemma par_hasvalue2 : forall A B (x : part A) (y : part B) b, hasvalue (par x y) (inr b) -> hasvalue y b.
  Proof.
    intros A B x y b [a' [(H1 & H2) % mu_tot_hasvalue H3]] % bind_hasvalue.
    destruct (seval x a') eqn:E1, (seval y a') eqn:E2; try congruence.
    - eapply ret_hasvalue_iff in H3 as [= ->].
    - eapply ret_hasvalue_iff in H3 as [= ->].
    - eapply ret_hasvalue_iff in H3 as [= ->].  eapply seval_hasvalue. eauto.
  Qed.
  
  Lemma par_hasvalue3 : forall A B (x : part A) (y : part B), ter x \/ ter y -> ter (par x y).
  Proof.
    intros A B x y [[a H] | [b H]].
    - eapply seval_hasvalue in H as [n Hn].
      destruct (@mu_tot_ter (fun n => if seval x n is Some a then true else if seval y n is Some b then true else false) n) as [m Hm].
      + now rewrite Hn. 
      + pose proof (Hm' := Hm).
        eapply mu_tot_hasvalue in Hm as (H1 & H2).
        destruct (seval x m) eqn:E1, (seval y m) eqn:E2; try congruence.
        * exists (inl a0). eapply bind_hasvalue. eexists. split. eapply Hm'. rewrite E1. eapply ret_hasvalue.
        * exists (inl a0). eapply bind_hasvalue. eexists. split. eapply Hm'. rewrite E1. eapply ret_hasvalue.
        * exists (inr b). eapply bind_hasvalue. eexists. split. eapply Hm'. rewrite E1 E2. eapply ret_hasvalue.
    - eapply seval_hasvalue in H as [n Hn].
      destruct (@mu_tot_ter (fun n => if seval x n is Some a then true else if seval y n is Some b then true else false) n) as [m Hm].
      + rewrite Hn. clear. now destruct seval. 
      + pose proof (Hm' := Hm).
        eapply mu_tot_hasvalue in Hm as (H1 & H2).
        destruct (seval x m) eqn:E1, (seval y m) eqn:E2; try congruence.
        * exists (inl a). eapply bind_hasvalue. eexists. split. eapply Hm'. rewrite E1. eapply ret_hasvalue.
        * exists (inl a). eapply bind_hasvalue. eexists. split. eapply Hm'. rewrite E1. eapply ret_hasvalue.
        * exists (inr b). eapply bind_hasvalue. eexists. split. eapply Hm'. rewrite E1 E2.
          erewrite (monotonic_agnostic (@seval_mono _ _ _) Hn E2). eapply ret_hasvalue.
  Qed.

End assume_part.

Lemma list_max_spec L x :
  In x L -> x <= list_max L.
Proof.
  induction L.
  - firstorder.
  - intros [-> | ]; cbn.
    + lia.
    + eapply IHL in H. unfold list_max in H. lia.
Qed.

Module implementation.

  Record part A := {
    the_fun : nat -> option A ;
    spec_fun : monotonic the_fun
  }.

  Definition hasvalue {A} (x : part A) (a : A) := exists n, the_fun x n = Some a.

  Lemma hasvalue_det : forall A x (a1 a2 : A), hasvalue x a1 -> hasvalue x a2 -> a1 = a2.
  Proof.
    intros A x a1 a2 [n1 H1] [n2 H2].
    refine (monotonic_agnostic _ H1 H2).
    apply spec_fun.
  Qed.

  Definition ter A (x : part A) := exists a, hasvalue x a.
  Definition equiv A (x y : part A) := forall a, hasvalue x a <-> hasvalue y a.

  Definition ret : forall A, A -> part A. 
  Proof.
   intros A a. exists (fun n => Some a).
   abstract now intros n1 n2 [= ->].
  Defined.

  Lemma ret_hasvalue : forall A (a : A), hasvalue (ret a) a.
  Proof.
    intros A a. exists 0. reflexivity.
  Qed.

  Definition bind : forall A B, part A -> (A -> part B) -> part B.
  Proof.
    intros A B f F.
    exists (fun n => if the_fun f n is Some a then the_fun (F a) n else None).
    abstract (destruct f as [f Hf]; intros n1 x H1 n2 Hle; cbn in *;
    destruct (f n1) eqn:E1; cbn in *; try congruence;
    destruct (the_fun) eqn:E2; cbn in *; try congruence; 
    eapply Hf in E1; specialize (E1 _ Hle) as ->;
    eapply spec_fun in E2; now specialize (E2 _ Hle) as ->).
  Defined.    

  Lemma bind_hasvalue_imp : forall A B x (f : A -> part B) b, hasvalue (bind x f) b <-> exists a, hasvalue x a /\ hasvalue (f a) b.
  Proof.
    intros A B x f b.
    split.
    - intros (n & H).
      cbn in H. destruct (the_fun x n) eqn:E1; try congruence; destruct (the_fun (f a) n) eqn:E2; try congruence.
      inversion H; subst; clear H. exists a. split.
      + now exists n.
      + now exists n.
    - intros (a & (n1 & H1) & (n2 & H2)).
      exists (n1 + n2). unfold bind. cbn. erewrite spec_fun; eauto. 2:lia.
      erewrite spec_fun; eauto. lia.
  Qed.

  Definition undef : forall {A}, part A.
  Proof.
   intros A. exists (fun n => None).
   abstract now intros n1 n2 [=].
  Defined.

  Lemma undef_hasvalue : forall A (a : A), ~ hasvalue undef a.
  Proof.
    intros A a [n [=]].
  Qed.

  Definition seval : forall A, part A -> nat -> option A.
  Proof.
    intros A x n. exact (the_fun x n).
  Defined.

  Lemma seval_mono : forall A x, monotonic (@seval A x).
  Proof.
    intros A f. eapply spec_fun.
  Qed.

  Lemma seval_hasvalue_imp : forall A x (a : A), hasvalue x a <-> exists n, seval x n = Some a.
  Proof.
    intros A [f Hf] a. reflexivity.
  Qed.

  Inductive res := Diverged | Allfalse | Trueat (n : nat).

  Fixpoint mu_fun (f : nat -> part bool) (fuel : nat) (bound : nat) : res :=
    match bound with
    | 0 => Allfalse
    | S bound => match mu_fun f fuel bound with
                 | Diverged => Diverged
                 | Trueat n => Trueat n
                 | Allfalse => match the_fun (f bound) fuel with
                               | Some true => Trueat bound
                               | Some false => Allfalse
                               | None => Diverged
                               end
                 end
    end.

  Lemma mu_fun_spec f fuel bound :
    match mu_fun f fuel bound with
    | Diverged => exists m, m < bound /\ the_fun (f m) fuel = None /\ forall k, k < m -> the_fun (f k) fuel <> Some true
    | Allfalse => forall m, m < bound -> the_fun (f m) fuel = Some false
    | Trueat k => k < bound /\ the_fun (f k) fuel = Some true /\ forall m, m < k -> the_fun (f m) fuel = Some false
    end.
  Proof.
    induction bound in fuel |- *; cbn in *.
    - intros. lia.
    - destruct mu_fun eqn:E.
      + specialize (IHbound fuel). rewrite E in IHbound. firstorder.
      + specialize (IHbound fuel). rewrite E in IHbound.
        destruct (the_fun (f bound) fuel) as [[]|] eqn:E1.
        * repeat split; try lia. eauto. firstorder.
        * intros. assert (m < bound \/ m = bound) as [ | -> ] by lia; eauto.
        * exists bound. repeat split; eauto. intros.
          rewrite IHbound. lia. congruence.
      + specialize (IHbound fuel). rewrite E in IHbound.
        destruct IHbound as (IH1 & IH2 & IH3); eauto.
  Qed.

  Definition mu (f : nat -> part bool) : part nat.
  Proof.
    exists (fun n => if mu_fun f n n is Trueat n then Some n else None).
    intros n1 n H1 n2 Hle.
    destruct (mu_fun f n1 n1) as [| | m ] eqn:E; inversion H1; subst; clear H1.
    pose proof (mu_fun_spec f n1 n1) as H. rewrite E in H.
    destruct H as (H1 & H2 & H3).
    pose proof (mu_fun_spec f n2 n2) as H.
    destruct (mu_fun f n2 n2).
    - destruct H as (m & ? & H0 & HH).  
      eapply spec_fun in H2. specialize (H2 _ Hle).
      assert (n < m \/ n = m \/ m < n) as [H5 | [H5 | H5]] by lia.
      + eapply HH in H5. congruence.
      + subst. congruence.
      + eapply H3 in H5.
        eapply spec_fun in H5. specialize (H5 _ Hle). congruence.
    - specialize (H n ltac:(lia)). erewrite spec_fun in H.
      3: eassumption. 2: eassumption. congruence.
    - destruct H as (? & ? & H0).
      assert (n0 < n \/ n0 = n \/ n0 > n) as [H5 | [H5 | H5]] by lia; try congruence.
      + eapply H3 in H5. erewrite spec_fun in H4. 3: exact Hle. 2:eassumption. congruence.
      + eapply H0 in H5. erewrite spec_fun in H5. 3: exact Hle. 2:eassumption. congruence.
  Defined.

  Require Import stdpp.list.

  Lemma lookup_seq k m n : m < n -> (seq k n) !! m = Some (k + m).
  Proof.
    induction m in k, n |- *; cbn; intros H.
    - destruct n; cbn; try f_equal; lia.
    - destruct n; cbn; try lia. erewrite IHm. 1: f_equal; lia. lia.
  Qed.

  Lemma list_max_lookup k n l : l !! k = Some n -> n <= list_max l.
  Proof.
    intros H. eapply list_max_spec, elem_of_list_In, elem_of_list_lookup_2, H.
  Qed.

  Lemma lt_list {X} n (P : X -> nat -> Prop) k :
    (forall m, m < n -> exists x, P x (k + m)) -> exists l, Forall2 P l (seq k n).
  Proof.
    intros H. induction n in k, H |- *; cbn.
    - exists []. econstructor.
    - edestruct (IHn (S k)) as [l IH].
      + intros. destruct (H (S m)) as [x Hx]. lia. exists x. now assert (S k + m = k + S m) as -> by lia. 
      + destruct (H 0 ltac:(lia)) as [x Hx]. exists (x :: l). econstructor. replace k with (k + 0) by lia. eauto. eauto.
  Qed.

  Lemma lt_list' {X} n (P : X -> nat -> Prop) :
    (forall m, m < n -> exists x, P x m) -> exists l, Forall2 P l (seq 0 n).
  Proof.
    intros H. eapply lt_list. exact H.
  Qed.  

  Lemma mu_hasvalue_imp : forall (f : nat -> part bool) n, hasvalue (mu f) n <-> (hasvalue (f n) true /\ forall m, m < n -> hasvalue (f m) false).
  Proof.
    intros f n. split.
    - intros [n1 H]. cbn in H.
      pose proof (mu_fun_spec f n1 n1) as Hmu.
      destruct (mu_fun f n1 n1); inversion H; subst; clear H.
      destruct Hmu as (H1 & H2 & H3).
      split.
      + now exists n1.
      + intros ? ? % H3. exists n1. eauto.
    - intros [[n1 H1] H2]. pose proof (H2' := H2).
      eapply (lt_list') in H2 as [l H2].
      exists (1 + n + n1 + list_max l).
      pose proof (mu_fun_spec f (1 + n + n1 + list_max l) (1 + n + n1 + list_max l)) as H. 
      cbn in *. destruct (mu_fun f).
      + destruct H as (m & H3 & H4 & H5). 
        assert (n < m \/ n = m \/ m < n) as [H6 | [H6 | H6]] by lia.
        * eapply H5 in H6. eapply spec_fun in H1.
          specialize (H1 (1 + n + n1 + list_max l) ltac:(lia)). cbn in *. congruence.
        * subst. eapply spec_fun in H1.
          specialize (H1 (1 + m + n1 + list_max l) ltac:(lia)). cbn in *. congruence.
        * clear - H2 H6 H4. eapply (lookup_seq 0) in H6. cbn in H6.
          eapply Forall2_lookup_r in H2 as (n_m & H2 & H3); eauto.
          eapply spec_fun in H3. unshelve epose proof (H3 (S (n + n1 + list_max l)) _). 2: congruence.
          unfold ge. transitivity (list_max l). 2: lia.
          eapply list_max_lookup. eauto.
      + destruct (the_fun (f (n + n1 + list_max l))) as [ [] | ].
        * destruct H as (H3 & H4 & H5). f_equal.
          pose (m := n + n1 + list_max l).
          assert (n < m \/ n = m \/ m < n) as [H6 | [H6 | H6]] by lia; subst m.
          -- eapply H5 in H6. unshelve epose proof (monotonic_agnostic _ H1 H6). eapply spec_fun. congruence.
          -- congruence.
          -- eapply H2' in H6 as [? H6].                    
             unshelve epose proof (monotonic_agnostic _ H4 H6).
             eapply spec_fun.            
            congruence.
        * specialize (H n ltac:(lia)).
          unshelve epose proof (monotonic_agnostic _ H1 H).
          eapply spec_fun. congruence.
        * destruct H as (m & H3 & H4 & H5).
          assert (m < n \/ m = n \/ m > n) as [H6 | [ H6 | H6 ]] by lia.
          -- eapply (lookup_seq 0) in H6. cbn in H6.
             eapply Forall2_lookup_r in H2 as (n_m & H2 & H7); eauto.
             eapply spec_fun in H7. rewrite H7 in H4.
             unfold ge. transitivity (list_max l). 2: lia.
             eapply list_max_lookup. eauto.
             congruence.
          -- subst. eapply spec_fun in H1. rewrite H1 in H4. lia. congruence.
          -- eapply H5 in H6. eapply spec_fun in H1. rewrite H1 in H6. lia. congruence.
      + destruct H as (H4 & H5 & H6).
        assert (n0 < n \/ n0 = n \/ n0 > n) as [H3 | [H3 | H3]] by lia.
        * eapply H2' in H3 as [? H3].
          unshelve epose proof (monotonic_agnostic _ H3 H5). eapply spec_fun. congruence.
        * congruence.
        * eapply H6 in H3.
          unshelve epose proof (monotonic_agnostic _ H3 H1). eapply spec_fun. congruence.
  Qed.

  Instance monotonic_functions : partiality.
  Proof.
    unshelve econstructor.
    - exact part.
    - exact @hasvalue.
    - exact @ret.
    - exact @bind.
    - exact @undef.
    - exact @mu.
    - exact @seval.
    - exact @hasvalue_det.
    - exact ret_hasvalue.
    - exact bind_hasvalue_imp.
    - exact undef_hasvalue.
    - exact mu_hasvalue_imp.
    - exact seval_mono.
    - exact seval_hasvalue_imp.
  Defined.

End implementation.
