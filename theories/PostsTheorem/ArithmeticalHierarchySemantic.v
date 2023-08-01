(** ** Arithmetical Hierarchy in Type Theory *)

From SyntheticComputability.Shared Require Import embed_nat.
Require Import Lia Vector Fin List.
Import Vector.VectorNotations.
(* From Undecidability.FOL Require Import Syntax. *)
From SyntheticComputability.Synthetic Require Import Definitions.

Require Import PeanoNat (* Nat.eqb *) Bool.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.
Derive Signature for vec.

Lemma eqhd : forall (x:nat) n (v: vec nat n), (VectorDef.hd (x :: v)) = x. Proof. reflexivity. Qed.
Lemma eqtl : forall (x:nat) n (v: vec nat n), (VectorDef.tl (x :: v)) = v. Proof. reflexivity. Qed.

Notation "P ⪯ₘ Q" := (reduces P Q) (at level 50).

Section ArithmeticalHierarchySemantic.

  Inductive isΣsem : nat -> forall (k: nat), ((vec nat k) -> Prop) -> Prop :=
  | isΣsem0_ {k} p (f: vec nat k -> bool) : (forall v, p v <-> f v = true) -> isΣsem 0 p
  | isΣsemS_ {n} {k} p' {p: vec nat (S k) -> Prop} : @isΠsem n (S k) p -> (forall v, p' v <-> exists x, p (x::v)) -> @isΣsem (S n) k p' 
  with isΠsem : nat -> forall (k: nat), ((vec nat k) -> Prop) -> Prop :=
  | isΠsem0_ {k} p (f: vec nat k -> bool) : (forall v, p v <-> f v = true) -> isΠsem 0 p
  | isΠsemS_ {n} {k} p' {p: vec nat (S k) -> Prop} : @isΣsem n (S k) p -> (forall v, p' v <-> forall x, p (x::v)) -> @isΠsem (S n) k p'.

  Lemma isΠsem0 {k} (f: vec nat k -> bool) : isΠsem 0 (fun v => f v = true).
  Proof.
    econstructor. reflexivity.
  Qed.

  Lemma isΣsem0 {k} (f: vec nat k -> bool) : isΣsem 0 (fun v => f v = true).
  Proof.
    econstructor. reflexivity.
  Qed.

  Lemma isΣsemS {n} {k} {p: vec nat (S k) -> Prop} : @isΠsem n (S k) p -> @isΣsem (S n) k (fun v => exists x, p (x::v)).
  Proof.
    econstructor. eauto. reflexivity.
  Qed.

  Lemma isΠsemS {n} {k} {p: vec nat (S k) -> Prop} : @isΣsem n (S k) p -> @isΠsem (S n) k (fun v =>  forall x, p (x::v)).
  Proof.
    econstructor. eauto. reflexivity.
  Qed.

  Derive Signature for isΣsem.
  Derive Signature for isΠsem.
  #[local] Hint Constructors isΣsem : core.
  #[local] Hint Constructors isΠsem : core.

  (* generacte induction scheme *)
  Scheme isΣsem_isΠsem_ind := Induction for isΣsem Sort Prop
  with isΠsem_isΣsem_ind := Induction for isΠsem Sort Prop.
  (* https://coq.inria.fr/refman/proofs/writing-proofs/reasoning-inductives.html#combined-scheme *)
  Combined Scheme isΣsem_isΠsem_mutind from isΣsem_isΠsem_ind,isΠsem_isΣsem_ind.

  Lemma curry {k} t: (nat -> vec nat k -> t) -> vec nat (S k) -> t.
  Proof.
    intros P v.
    inversion v as [|n k' v' eq]. subst.
    exact (P n v').
  Defined.

  Lemma curry0 t : t -> vec nat 0 -> t.
  Proof.
    intros P v. apply P.
  Defined.

  Lemma curry1 t: (nat -> t) -> vec nat 1 -> t.
  Proof.
    intros P. apply curry. intros n. apply curry0. exact (P n).
  Defined.

  Lemma curry2 t: (nat -> nat -> t) -> vec nat 2 -> t.
  Proof.
    intros P. apply curry. intros n. apply curry1. exact (P n).
  Defined.

  Lemma PredExt :
    (forall n k (p: vec nat k -> Prop), isΣsem n p -> forall p', (forall v, p' v <-> p v) -> isΣsem n p')
 /\ (forall n k (p: vec nat k -> Prop), isΠsem n p -> forall p', (forall v, p' v <-> p v) -> isΠsem n p').
  Proof.
    eapply isΣsem_isΠsem_mutind.
    - intros. econstructor. intros. now rewrite H, i.
    - intros. econstructor. eapply H. reflexivity. firstorder.
    - intros. econstructor. intros. now rewrite H, i.
    - intros. econstructor. eapply H. reflexivity. firstorder.
  Qed.

  (** # <a id="semi_dec_iff_Sigma1" /> #*)
  Lemma semi_dec_iff_Σ1 {k} (p : vec nat k -> Prop):
    semi_decidable p <-> isΣsem 1 p.
  Proof.
  unfold semi_decidable, semi_decider.
  split.
  - intros [f Hf].
    eapply PredExt. 2: exact Hf.
    unshelve eapply PredExt. {
      exact (fun v => exists n, (fun v => (fun v => f (Vector.tl v) (Vector.hd v)) v = true) (n::v)).
    } 2: reflexivity. eapply isΣsemS, isΠsem0.
  - intros H. repeat dependent destruction H.
    exists (fun v n => f (n::v)). firstorder.
  Qed.

  Lemma isΣΠsem0 {k} (f: vec nat k -> bool) n :
    isΣsem n (fun v => f v = true) /\ isΠsem n (fun v => f v = true).
  Proof.
    induction n in k, f |-*.
    - split; apply isΣsem0 + apply isΠsem0.
    - split.
      + unshelve eapply PredExt. exact (fun v => exists x, f (Vector.tl (x::v)) = true). 2: firstorder.
        change (isΣsem (S n) (fun v => exists x, (fun v => f (Vector.tl v) = true) (x::v))).
        apply isΣsemS. apply IHn.
      + unshelve eapply PredExt. exact (fun v => forall x, f (Vector.tl (x::v)) = true). 2: firstorder.
        change (isΠsem (S n) (fun v => forall x, (fun v => f (Vector.tl v) = true) (x::v))).
        apply isΠsemS. apply IHn.
  Qed.

  (** # <a id="isSigman_In_SigmaSn" /> #*)
  Lemma isΣΠn_In_ΣΠSn l :
    (forall n k (p: vec nat k -> Prop), isΣsem n p -> isΣsem (l + n) p)
/\  (forall n k (p: vec nat k -> Prop), isΠsem n p -> isΠsem (l + n) p).
  Proof.
    apply isΣsem_isΠsem_mutind; intros.
    1,3: eapply PredExt; [eapply isΣΠsem0 | ]; cbn; eassumption.
    all: replace (l + S n) with (S l + n) by lia.
    all: cbn; econstructor; eauto.
  Qed.

  (** # <a id="isSigmasem_m_red_closed" /> #*)
  Lemma isΣsem_m_red_closed : 
    (forall n k (q: vec nat k -> Prop), isΣsem n q -> forall k' (p : vec nat k' -> Prop), p ⪯ₘ q -> isΣsem n p)
/\  (forall n k (q: vec nat k -> Prop), isΠsem n q -> forall k' (p : vec nat k' -> Prop), p ⪯ₘ q -> isΠsem n p).
  Proof.
    apply isΣsem_isΠsem_mutind.
    - intros ? ? ? ? ? ? [e He]. econstructor. intros v. red in He. rewrite He, i.
      eapply iff_refl. 
    - intros n k p' q Πq IH k' H p [e He].
      rename q into q'.
      rename p' into q.
      econstructor. eapply IH with (p := fun v => q' ((Vector.hd v)::(e (Vector.tl v)))).
      + exists (fun v => (Vector.hd v)::(e (Vector.tl v))).
        intros x. eapply iff_refl.
      + cbn. firstorder.
    - intros k p' f H k' p [e He]. econstructor. intros v. red in He. rewrite He, H.
      eapply iff_refl.
    - intros n k p' q Πq IH k' H p [e He].
      econstructor. eapply IH.
      + exists (fun v => (Vector.hd v)::(e (Vector.tl v))).
        intros x. eapply iff_refl.
      + firstorder.
  Qed.

  (** # <a id="isSigmasemTwoEx" /> #*)
  Lemma isΣsemTwoEx k n (p : vec nat (S (S k)) -> Prop):
    isΠsem n p -> isΣsem (S n) (fun v => exists y x : nat, p (x :: y :: v)).
  Proof.
    intros H.
    unshelve eapply isΣsem_m_red_closed in H.
    2: exact (fun v => let (x, y) := unembed (VectorDef.hd v) in p (x :: y :: VectorDef.tl v)).
    2: {
      exists (fun v => let (x, y) := unembed (VectorDef.hd v) in x :: y :: Vector.tl v).
      intros v. destruct unembed. reflexivity.
    }
    apply isΣsemS in H. eapply PredExt. { apply H. }
    intros v. cbv beta. split.
    - intros [y [x Hp]]. exists (embed (x, y)).
      now rewrite eqhd, eqtl, embedP.
    - intros [m Hp]. destruct (unembed m) as [x y] eqn:eq. exists y, x.
      now rewrite eqhd, eqtl, eq in Hp.
  Qed.

  (** # <a id="isSigmasemE" /> #*)
  Lemma isΣsemE k n (p : vec nat (S k) -> Prop):
    isΣsem (S n) p -> isΣsem (S n) (fun v => exists x : nat, p (x :: v)).
  Proof.
    intros H. dependent destruction H. cbn in *.
    eapply PredExt.
    eapply isΣsemTwoEx; eauto. firstorder. 
  Qed.

  Lemma isΠsemTwoAll k n (p : vec nat (S (S k)) -> Prop):
    isΣsem n p -> isΠsem (S n) (fun v => forall y x : nat, p (x :: y :: v)).
  Proof.
    intros H.
    unshelve eapply isΣsem_m_red_closed in H.
    2: exact (fun v => let (x, y) := unembed (VectorDef.hd v) in p (x :: y :: VectorDef.tl v)).
    2: {
      exists (fun v => let (x, y) := unembed (VectorDef.hd v) in x :: y :: Vector.tl v).
      intros v. destruct unembed. reflexivity.
    }
    apply isΠsemS in H. eapply PredExt. { apply H. }
    intros v. cbv beta. split.
    - intros Hp m. rewrite eqhd, eqtl.
      now destruct (unembed m) as [x y] eqn:eq.
    - intros Hp y x. specialize (Hp (embed (x, y))).
      now rewrite eqhd, eqtl, embedP in Hp.
  Qed.

  Lemma isΠsemA k n (p : vec nat (S k) -> Prop):
    isΠsem (S n) p -> isΠsem (S n) (fun v => forall x : nat, p (x :: v)).
  Proof.
    intros H. dependent destruction H.
    eapply PredExt. eapply isΠsemTwoAll. eauto. firstorder.
  Qed.

  (** # <a id="isSigman_In_PiSn" /> #*)
  Lemma isΣΠn_In_ΠΣSn :
    (forall n k (p: vec nat k -> Prop), isΣsem n p -> isΠsem (S n) p)
/\  (forall n k (p: vec nat k -> Prop), isΠsem n p -> isΣsem (S n) p).
  Proof.
    split; intros n k p H.
    - eapply isΣsem_m_red_closed in H.
      2: { exists (fun v => Vector.tl v). intros v. split; intros pv; apply pv. }
      apply isΠsemS in H. eapply PredExt. 1: apply H. firstorder.
    - eapply isΣsem_m_red_closed in H.
      2: { exists (fun v => Vector.tl v). intros v. split; intros pv; apply pv. }
      apply isΣsemS in H. eapply PredExt. 1: apply H. firstorder.
  Qed.

  (** # <a id="isSigmasem_and_closed" /> #*)
  Lemma isΣsem_and_closed n :
    (forall k (p: vec nat k -> Prop), isΣsem n p -> forall (q : vec nat k -> Prop), isΣsem n q -> isΣsem n (fun v => p v /\ q v))
/\  (forall k (p: vec nat k -> Prop), isΠsem n p -> forall (q : vec nat k -> Prop), isΠsem n q -> isΠsem n (fun v => p v /\ q v)).
  Proof.
    induction n as [|n IH].
    - split.
      + intros k p Hp q Hq. dependent destruction Hp. dependent destruction Hq.
        unshelve eapply PredExt. exact (fun v => f0 v && f v = true). 2: cbn; intros; rewrite andb_true_iff; firstorder.
        apply isΣsem0.
      + intros k p Hp q Hq. dependent destruction Hp. dependent destruction Hq.
        unshelve eapply PredExt. exact (fun v => f0 v && f v = true). 2: cbn; intros; rewrite andb_true_iff; firstorder.
        apply isΠsem0.
    - split; intros k p Hp q Hq; dependent destruction Hp; dependent destruction Hq.
      + cbn in *. rename p0 into p'.
        rename p1 into q'.
        unshelve eapply PredExt.
        exact (fun v => exists y x : nat, (fun v => p' (Vector.hd v:: Vector.tl (Vector.tl v)) /\ q' (Vector.hd (Vector.tl v)::Vector.tl (Vector.tl v))) (x::y::v)).
        2:{ cbn in *. intros. rewrite H0, H2. clear. firstorder. }
        apply isΣsemTwoEx. apply IH.
        * eapply isΣsem_m_red_closed. { apply H. }
          now exists (fun v => (Vector.hd v :: Vector.tl (Vector.tl v))). 
        * eapply isΣsem_m_red_closed. { apply H1. }
          now exists (fun v => Vector.hd (Vector.tl v) :: Vector.tl (Vector.tl v)).
      + unshelve eapply PredExt.
        exact (fun v => forall y x : nat, (fun v => p0 (Vector.hd v:: Vector.tl (Vector.tl v)) /\ p1 (Vector.hd (Vector.tl v)::Vector.tl (Vector.tl v))) (x::y::v)).
        2:{ cbn in *. intros. rewrite H0, H2. clear. firstorder. }
        apply isΠsemTwoAll. apply IH.
        * eapply isΣsem_m_red_closed. { apply H. }
          now exists (fun v => (Vector.hd v :: Vector.tl (Vector.tl v))). 
        * eapply isΣsem_m_red_closed. { apply H1. }
          now exists (fun v => Vector.hd (Vector.tl v) :: Vector.tl (Vector.tl v)).
  Qed.

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat (nat_to_vec k n) = n.

  Variable list_vec_to_nat : forall k, list (vec nat k) -> nat.
  Variable nat_to_list_vec : forall k, nat -> list (vec nat k).
  Variable list_vec_nat_inv : forall k v, nat_to_list_vec k (list_vec_to_nat v) = v.
  Variable nat_list_vec_inv : forall k n, list_vec_to_nat (nat_to_list_vec k n) = n.

  (** # <a id="isSigmasem_if_closed" /> #*)
  Lemma isΣsem_if_closed n :
    (forall k (p: vec nat k -> Prop), isΣsem n p -> forall (q : vec nat k -> Prop) (f : nat -> bool), isΣsem n q -> isΣsem n (fun v => if f (Vector.hd v) then p (Vector.tl v) else q (Vector.tl v)))
/\  (forall k (p: vec nat k -> Prop), isΠsem n p -> forall (q : vec nat k -> Prop) (f : nat -> bool), isΠsem n q -> isΠsem n (fun v => if f (Vector.hd v) then p (Vector.tl v) else q (Vector.tl v))). 
  Proof.
    induction n as [|n IH].
    - split.
      + intros k p Hp q f Hq. dependent destruction Hp. dependent destruction Hq.
        unshelve eapply PredExt. exact (fun v => (if f (Vector.hd v) then f0 (Vector.tl v) else f1 (Vector.tl v)) = true). 
        apply isΣsem0.
        intros v. cbn. destruct f; firstorder.
      + intros k p Hp q f Hq. dependent destruction Hp. dependent destruction Hq.
        unshelve eapply PredExt. exact (fun v => (if f (Vector.hd v) then f0 (Vector.tl v) else f1 (Vector.tl v)) = true). 
        apply isΠsem0.
        intros v. cbn. destruct f; firstorder.
    - split; intros k p Hp q f Hq; dependent destruction Hp; dependent destruction Hq; cbn in *.
      + unshelve eapply PredExt.
        exact (fun v => exists x : nat, (fun v => if f (Vector.hd (Vector.tl v)) then p0 (Vector.hd v :: Vector.tl (Vector.tl v)) else p1 (Vector.hd v :: Vector.tl (Vector.tl v))) (x :: v)). 2: firstorder.
        eapply isΣsemS.
        eapply isΣsem_m_red_closed. eapply IH. exact H. exact H1.
        exists (fun v => (Vector.hd (Vector.tl v)) :: Vector.hd v :: Vector.tl (Vector.tl v)). red. cbn. reflexivity.
        firstorder. cbn. destruct f; firstorder. cbn in *. destruct f; firstorder.
      + unshelve eapply PredExt.
        exact (fun v => forall x : nat, (fun v => if f (Vector.hd (Vector.tl v)) then p0 (Vector.hd v :: Vector.tl (Vector.tl v)) else p1 (Vector.hd v :: Vector.tl (Vector.tl v))) (x :: v)). 2: firstorder.
        eapply isΠsemS.
        eapply isΣsem_m_red_closed. eapply IH. exact H. exact H1.
        exists (fun v => (Vector.hd (Vector.tl v)) :: Vector.hd v :: Vector.tl (Vector.tl v)). red. cbn. reflexivity.
        firstorder. cbn. destruct f; firstorder. cbn in *. destruct f; firstorder.
  Qed.

  (** # <a id="isSigmaPiball" /> #*)
  Lemma isΣΠball n :
    (forall k (p : vec nat (S k) -> Prop), isΣsem n p -> isΣsem n (fun v => forall l, l < (Vector.hd v) -> p (l::(Vector.tl v))))
/\  (forall k (p : vec nat (S k) -> Prop), isΠsem n p -> isΠsem n (fun v => forall l, l < (Vector.hd v) -> p (l::(Vector.tl v)))).
  Proof.
    induction n as [|n [IH1 IH2]]; split; intros k p H; dependent destruction H.
    - unshelve eapply PredExt. cbn in *. exact (fun v => (fix f' n v := match n with 0 => true | S n => f(n::v) && f' n v end)(Vector.hd v)(Vector.tl v) = true). 1: apply isΣsem0.
      intros v. dependent destruction v. setoid_rewrite H. clear.
      rewrite eqhd, eqtl. induction h as [|n IH].
      + split; lia.
      + split.
        * intros H. apply andb_true_iff. firstorder. 
        * intros [H H']%andb_true_iff. intros l le. assert (l = n \/ l < n) as [->|] by lia; [apply H | now apply IH].
    - unshelve eapply PredExt. cbn in *. exact (fun v => (fix f' n v := match n with 0 => true | S n => f(n::v) && f' n v end)(Vector.hd v)(Vector.tl v) = true). 1: apply isΠsem0.
      intros v. dependent destruction v. setoid_rewrite H. clear.
      rewrite eqhd, eqtl. induction h as [|n IH].
      + split; lia.
      + split.
        * intros H. apply andb_true_iff. firstorder. 
        * intros [H H']%andb_true_iff. intros l le. assert (l = n \/ l < n) as [->|] by lia; [apply H | now apply IH].
    - unshelve eapply PredExt.
        1: exact (fun v =>
        exists L : nat,
        (fun v => let L := Vector.hd v in let N := Vector.hd (Vector.tl v) in let v := Vector.tl (Vector.tl v) in
          (fun v =>
            forall (l : nat), l < Vector.hd v ->
              (fun v =>
                let l := Vector.hd v in
                let N := Vector.hd (Vector.tl v) in
                let L := Vector.hd (Vector.tl (Vector.tl v)) in
                let v := Vector.tl (Vector.tl (Vector.tl v)) in
                let L' := nat_to_vec N L in
                let xl := match Compare_dec.lt_dec l N with left lt => Vector.nth L' (of_nat_lt lt) | right _ => 42 end in
                  (fun v => p0 (Vector.tl v))(N::xl::l::v)
              )(l::v)
          )(N::L::v)
        )(L::v)).
      2: { 
        clear n IH1 IH2 H. intros v. cbn. dependent destruction v. rewrite eqhd. rewrite eqtl. setoid_rewrite H0. clear H0.
        induction h as [|n [IH1 IH2]].
        - firstorder lia.
        - split.
          + intros H. specialize (IH1 ltac:(intros l leq; apply H; lia)) as [L Hl].
            remember (nat_to_vec n L) as L'. destruct (H n ltac:(lia)) as [x Hx].
            exists (vec_to_nat(Vector.shiftin x L')). intros l lt. rewrite vec_nat_inv.
            destruct Compare_dec.lt_dec as [lt'|]; [|contradiction].
            assert (l = n \/ l < n) as [->|lt''] by lia.
            * enough ((shiftin x L')[@of_nat_lt lt'] = x) as -> by assumption.
              clear. induction L' as [|y k' L' IH]; [reflexivity|apply IH].
            * enough ((shiftin x L')[@of_nat_lt lt'] = L'[@of_nat_lt lt'']) as ->. { specialize (Hl l lt''). destruct Compare_dec.lt_dec;[|contradiction]. erewrite of_nat_ext. eauto. }
              clear. induction L' in l, lt', lt'' |-*; induction l; try lia + reflexivity + apply IHL'.
          + intros [L H] l lt. eexists. now apply H.
      }
      remember (fun v =>
        let l := Vector.hd v in
        let N := Vector.hd (Vector.tl v) in
        let L := Vector.hd (Vector.tl (Vector.tl v)) in
        let v := Vector.tl (Vector.tl (Vector.tl v)) in
        let L' := nat_to_vec N L in
        let xl := match Compare_dec.lt_dec l N with left lt => Vector.nth L' (of_nat_lt lt) | right _ => 42 end in
          (fun v => p0 (Vector.tl v))(N::xl::l::v)
      ) as p'.
      remember (fun v => forall (l : nat), l < Vector.hd v -> p'(l::v)) as p''.
      apply isΣsemS.
      unshelve eapply isΣsem_m_red_closed. 2: apply p''. 2: {
        exists (fun v => let L := Vector.hd v in
        let N := Vector.hd (Vector.tl v) in
        let v := Vector.tl (Vector.tl v) in (N :: L :: v)).
        intros v. now do 2 dependent destruction v.
      }
      rewrite Heqp''. specialize (IH2 _ p'). cbn in IH2.
      eapply isΣsem_m_red_closed. 1: apply IH2. 2: {
        exists (fun v => (Vector.hd v)::(Vector.hd v)::(Vector.tl v)).
        intros v. now dependent destruction v.
      }
      rewrite Heqp'.
      eapply isΣsem_m_red_closed. apply H.
      exists (fun v : vec nat (S (S (S k))) =>
      let l := Vector.hd v in
      let N := Vector.hd (Vector.tl v) in
      let L := Vector.hd (Vector.tl (Vector.tl v)) in
      let v0 := Vector.tl (Vector.tl (Vector.tl v)) in
      let L' := nat_to_vec N L in
      let xl :=
        match Compare_dec.lt_dec l N with
        | left lt => L'[@of_nat_lt lt]
        | right _ => 42
        end in Vector.tl (N :: xl :: l :: v0)).
      now intros.
  - unshelve eapply PredExt. {
      exact (fun v =>
      forall L : nat,
      (fun v => let L := Vector.hd v in let N := Vector.hd (Vector.tl v) in let v := Vector.tl (Vector.tl v) in
        (fun v =>
          forall (l : nat), l < Vector.hd v ->
            (fun v =>
              let l := Vector.hd v in
              let N := Vector.hd (Vector.tl v) in
              let L := Vector.hd (Vector.tl (Vector.tl v)) in
              let v := Vector.tl (Vector.tl (Vector.tl v)) in
              let L' := nat_to_vec N L in
              let xl := match Compare_dec.lt_dec l N with left lt => Vector.nth L' (of_nat_lt lt) | right _ => 42 end in
                (fun v => p0 (Vector.tl v))(N::xl::l::v)
            )(l::v)
        )(N::L::v)
      )(L::v)).
    } 2: { 
      clear n IH1 IH2 H. intros v. cbn. dependent destruction v. rewrite eqhd, eqtl. setoid_rewrite H0. clear H0.
      induction h as [|n [IH1 IH2]].
      - firstorder lia.
      - split.
        + firstorder.
        + intros H l lt x.
          specialize (H (vec_to_nat (Vector.const x (S n))) l lt).
          rewrite vec_nat_inv in H. destruct Compare_dec.lt_dec; [|lia].
          now rewrite Vector.const_nth in H.
    }
    remember (fun v =>
      let l := Vector.hd v in
      let N := Vector.hd (Vector.tl v) in
      let L := Vector.hd (Vector.tl (Vector.tl v)) in
      let v := Vector.tl (Vector.tl (Vector.tl v)) in
      let L' := nat_to_vec N L in
      let xl := match Compare_dec.lt_dec l N with left lt => Vector.nth L' (of_nat_lt lt) | right _ => 42 end in
        (fun v => p0 (Vector.tl v))(N::xl::l::v)
    ) as p'.
    remember (fun v => forall (l : nat), l < Vector.hd v -> p'(l::v)) as p''.
    apply isΠsemS.
    unshelve eapply isΣsem_m_red_closed. 2: apply p''. 2: {
      exists (fun v => let L := Vector.hd v in
      let N := Vector.hd (Vector.tl v) in
      let v := Vector.tl (Vector.tl v) in (N :: L :: v)).
      intros v. now do 2 dependent destruction v.
    }
    rewrite Heqp''. specialize (IH1 _ p').
    eapply isΣsem_m_red_closed. 1: apply IH1. 2: {
      exists (fun v => (Vector.hd v)::(Vector.hd v)::(Vector.tl v)).
      intros v. now dependent destruction v.
    }
    rewrite Heqp'.
    eapply isΣsem_m_red_closed. apply H.
    exists (fun v : vec nat (S (S (S k))) =>
    let l := Vector.hd v in
    let N := Vector.hd (Vector.tl v) in
    let L := Vector.hd (Vector.tl (Vector.tl v)) in
    let v0 := Vector.tl (Vector.tl (Vector.tl v)) in
    let L' := nat_to_vec N L in
    let xl :=
      match Compare_dec.lt_dec l N with
      | left lt => L'[@of_nat_lt lt]
      | right _ => 42
      end in Vector.tl (N :: xl :: l :: v0)).
    now intros.
  Qed.
  
  Definition DN := forall P, ~~P -> P.

  Definition Markov: Prop :=
    forall f: nat -> bool, ~(forall x, f x = false) -> exists n, f n = true.
  
  Lemma Markov_Forster:
    Markov <-> forall f : nat -> bool, ~~ (exists n, f n = true) -> exists n, f n = true.
  Proof.
    unfold Markov. split.
    - intros MP f nnE. apply MP. intros A. apply nnE. intros [n Hn]. congruence.
    - intros MP f nA. apply MP.
      intros nE. apply nA. intros x. destruct f eqn:eq.
      + exfalso. apply nE. now exists x.
      + reflexivity.
  Qed.

  Lemma DN_Markov : DN -> Markov.
  Proof.
    unfold DN, Markov.
    intros DN. intros f nA.
    assert (~(forall x, ~(f x = true))). {
      intros A. apply nA. intros x. specialize (A x). now destruct f.
    }
    apply DN. firstorder.
  Qed.
  
  Lemma Σ0sem_notΠ0_int :
    (forall k (p : vec nat k -> Prop), isΣsem 0 p -> isΠsem 0 (fun v => ~ (p v)))
 /\ (forall k (p : vec nat k -> Prop), isΠsem 0 p -> isΣsem 0 (fun v => ~ (p v))).
  Proof.
    split.
    all: intros k p H; dependent destruction H; cbn in *.
    all: econstructor; setoid_rewrite H.
    all: instantiate (1 := fun v => negb (f v)); cbn; intros.
    all: destruct (f v); cbn; firstorder congruence.
  Qed.

  Lemma int_notEx_Allnot {X} k (p: vec X (S k) -> Prop):
    forall v, (~(exists x, p (x::v)) <-> (forall x, ~p (x::v))).
  Proof. clear. firstorder. Qed.

  Lemma Σ1sem_notΠ1_int :
    forall k (p : vec nat k -> Prop), isΣsem 1 p -> isΠsem 1 (fun v => ~ (p v)).
  Proof.
    intros k p H.
    dependent destruction H; cbn in *.
    econstructor. eapply Σ0sem_notΠ0_int. eassumption.
    cbn. firstorder.
  Qed.

  Lemma Π1sem_notΣ1_MP :
    Markov -> forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΣsem 1 (fun v => ~ (p v)).
  Proof.
    unfold Markov. intros Markov k p H.
    dependent destruction H.
    dependent destruction H.
    cbn in *.
    eapply PredExt.
    2:{ intros. etransitivity. rewrite H0. setoid_rewrite H. reflexivity. instantiate (1 := fun v => ~ (forall x : nat, f (x :: v) = true)). reflexivity. }
    eapply PredExt.
    - instantiate (1 := fun v : vec nat k => exists x : nat, (fun v => (if f v then false else true) = true)(x :: v)). apply isΣsemS, isΠsem0.
    - intros v. split.
      + intros nA. apply Markov. intros Hx. apply nA. intros x. specialize (Hx x). now destruct f.
      + intros [x Hx] nA. specialize (nA x). rewrite nA in Hx. discriminate.
  Qed.

  Lemma equiv_DN_sdec : 
    (forall k (p : vec nat k -> Prop), semi_decidable p -> semi_decidable (fun v => ~~p v))
    <->
    (forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΣsem 1 (fun v => ~ (p v))).
  Proof.
    split.
    - intros Hsdec k p H. repeat dependent destruction H.
      assert (semi_decidable (fun v => (exists x, f(x::v) = false))) as sdec. {
        unfold semi_decidable, semi_decider.
        exists (fun v x => if f(x::v) then false else true).
        intros v. split.
        - intros [x Hx]. exists x. now destruct f.
        - intros [x Hx]. exists x. now destruct f.
      }
      specialize (Hsdec _ _ sdec) as [f' Hf']. unfold semi_decider in Hf'.
      assert (forall v, ~~(exists x, f (x::v) = false) <-> ~forall x, f(x::v) = true) as eq. {
        enough (forall v, f v = true <-> ~f v = false) as eq by (setoid_rewrite eq; firstorder).
        intros v. now destruct f.
      }
      setoid_rewrite eq in Hf'.
      eapply PredExt. instantiate (1 := (fun v => exists x, (fun v => f' (Vector.tl v) (Vector.hd v) = true) (x::v))).
      apply isΣsemS, isΠsem0. intros. cbn in *.
      rewrite H0. setoid_rewrite H. firstorder.
    - intros H k p [f Hf]. unfold semi_decidable, semi_decider in *.
      assert (isΠsem 1 (fun v => ~p v)) as HΠ. {
        eapply PredExt. instantiate (1 := fun x => forall n, ~f x n = true). 2: firstorder.
        change (isΠsem 1 (fun v => forall x, (fun v => f (Vector.tl v) (Vector.hd v) <> true) (x::v))).
        apply isΠsemS.
        econstructor. instantiate (1 := fun v => if f (Vector.tl v) (Vector.hd v) then false else true).
        firstorder; now destruct f.
      }
      specialize (H _ _ HΠ). repeat dependent destruction H.
      exists (fun v x => f0 (x::v)). intros v.
      change ((fun v : vec nat k => ~ ~ p v) v <-> (fun v : vec nat k => exists x : nat, f0 (x :: v) = true) v).
      cbn in *. firstorder.
  Qed.

  Lemma equiv_sdec_functions :
    (forall k alpha, exists beta, forall (x : vec nat k), ~ (forall (n : nat), alpha x n = false) <-> (exists (n : nat), beta x n = true))
    <->
    (forall k (p : vec nat k -> Prop), semi_decidable p -> semi_decidable (fun v => ~~p v)).
  Proof.
    unfold semi_decidable, semi_decider.
    split.
    - intros H k p [f Hf].
      specialize (H _ f) as [f' Hf'].
      exists f'.
      intros x. rewrite <- Hf'.
      rewrite Hf.
      assert (~ (forall n : nat, f x n <> true) <-> ~ ~ (exists n : nat, f x n = true)) as <- by firstorder.
      split. all: intros nA A; apply nA; intros n; specialize (A n); now destruct f.
    - intros H k f.
      specialize (H k (fun v => exists x, f v x = true) ltac:(firstorder)) as [f' Hf'].
      exists f'. setoid_rewrite <- Hf'.
      intros v. assert (~ (forall n : nat, f v n <> true) <-> ~ ~ (exists n : nat, f v n = true)) as <- by firstorder.
      split. all: intros nA A; apply nA; intros n; specialize (A n); now destruct f.
  Qed.

  Lemma anonymisedMPiff :
    (forall k alpha, exists beta, forall (x : vec nat k), ~ (forall (n : nat), alpha x n = false) <-> (exists (n : nat), beta x n = true))
    <->
      (forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΣsem 1 (fun v => ~ (p v))).
  Proof. rewrite equiv_sdec_functions. apply equiv_DN_sdec. Qed.

  Definition stable {X} (p : X -> Prop) := forall x, ~~ p x -> p x.
  Definition definite {X} (p : X -> Prop) := forall x, p x \/ ~ p x.
  Definition DNE_Π n := forall k (p: vec nat k -> Prop), isΠsem n p -> stable p.
  Definition DNE_Σ n := forall k (p: vec nat k -> Prop), isΣsem n p -> stable p.

  Definition DNE_ΠorΠ n :=
    forall (k : nat) (p1 p2 : vec nat k -> Prop), isΠsem n p1 -> isΠsem n p2 -> stable (fun v => p1 v \/ p2 v).

  Definition LEM_Π n := forall k (p: vec nat k -> Prop), isΠsem n p -> definite p.
  Definition LEM_Σ n := forall k (p: vec nat k -> Prop), isΣsem n p -> definite p.
  Definition LEM_Δ n := forall k (p: vec nat k -> Prop), isΣsem n p -> isΠsem n p -> definite p.

  Lemma LEM_Δ_to_LEM_Σ n :
    LEM_Δ (S n) ->
    LEM_Σ n.
  Proof.
    intros H k p Hp.
    eapply H.
    - eapply isΣΠn_In_ΣΠSn with (l := 1); assumption.
    - now eapply isΣΠn_In_ΠΣSn.
  Qed.

  Lemma LEM_Σ_to_DNE_Σ n :
    LEM_Σ n ->
    DNE_Σ n.
  Proof.
    firstorder.
  Qed.

  Lemma LEM_Π_to_DNE_Π n :
    LEM_Π n ->
    DNE_Π n.
  Proof.
    firstorder.
  Qed.

  Lemma DNE_equiv_S n :
    DNE_Σ n <-> DNE_Π (S n).
  Proof.
    induction n; split; intros dne k p Hp v Hv; depelim Hp; try rename p0 into p; cbn in *.
    - depelim H; cbn in *. apply H0. intros x. destruct (f (x :: v)) eqn:E; try firstorder congruence.
    - destruct (f v) eqn:E; try firstorder congruence.
    - depelim H; cbn in *. eapply H1. intros x. eapply dne. eauto. firstorder.
    - eapply dne with (x := v); eauto.
      eapply isΣΠn_In_ΠΣSn. econstructor; eauto.
  Qed.

  Lemma DNEimpl n :
    DNE_Σ n -> DNE_Π n.
  Proof.
    intros dne % DNE_equiv_S k p H.
    eapply dne.
    1:now eapply isΣΠn_In_ΣΠSn with (l := 1).
  Qed.

  Lemma negΣinΠsem: (forall n k (p: vec nat k -> Prop), isΣsem n p -> DNE_Π n -> isΠsem n (fun v => ~(p v)))
    /\ (forall n k (p: vec nat k -> Prop), isΠsem n p -> DNE_Σ n -> isΣsem n (fun v => ~(p v))).
  Proof.
    apply isΣsem_isΠsem_mutind.
    - intros. apply Σ0sem_notΠ0_int. econstructor. eassumption.
    - intros n k p p' H IH H' DN.
      econstructor. apply IH. 1: now eapply DNE_equiv_S.
      cbn. clear - H'. firstorder.
    - intros. apply Σ0sem_notΠ0_int. econstructor. eassumption.
    - intros n k p p' H IH H' DN.
      econstructor. eapply IH. 1: now eapply DNEimpl, DNE_equiv_S, DNEimpl.
      intros v. split.
      * intros nA. eapply DN with (x := v).
        econstructor. eapply IH.
        1: now eapply DNEimpl, DNE_equiv_S, DNEimpl.
        cbn. reflexivity.
        intros ?. eapply nA. eapply H'. intros x. eapply DN.
        1:now eapply isΣΠn_In_ΣΠSn with (l := 1).
        firstorder. 
      * clear - H'. firstorder.
  Qed.

  Lemma LEM_Σ_to_LEM_Π n :
    LEM_Σ n ->
    LEM_Π n.
  Proof.
    intros lem k p Hp v.
    eapply negΣinΠsem in Hp as H.
    2:{ eapply LEM_Σ_to_DNE_Σ. assumption. }
    eapply lem in H. red in H.
    destruct (H v).
    - tauto.
    - left.
      eapply DNEimpl. 2: exact Hp.
      eapply LEM_Σ_to_DNE_Σ. assumption. 
      assumption.
  Qed.

  Lemma LEM_Π_Sn_to_LEM_Σ_n n :
    LEM_Π (S n) -> LEM_Σ n.
  Proof.
    intros H ? ? ?.
    eapply H. now eapply isΣΠn_In_ΠΣSn.
  Qed.

  From SyntheticComputability Require Import principles.

  Lemma level1 :
    DNE_Σ 0
    /\ (LEM_Σ 1 <-> LPO)
    /\ (DNE_Σ 1 <-> MP)
    /\ (LEM_Π 1 <-> WLPO)
    /\ DNE_Π 1.
  Proof.
    repeat split.
    - intros k p H v. depelim H. cbn in H.
      rewrite H. destruct (f v); firstorder congruence.
    - intros H f. destruct (H 0 (fun _ => exists n, f n = true)) as [ | ];
        firstorder.
      eapply (isΣsemS (p := fun v => f (Vector.hd v) = true)).
      eapply isΠsem0. exact Vector.nil.
    - intros H k p Hp v. depelim Hp. depelim H0.
      cbn in *. rewrite H1. setoid_rewrite H0.
      destruct (H (fun x => f (x :: v))); firstorder.
    - intros H f. eapply (H 0 (fun _ => exists n, f n = true)).
      eapply (isΣsemS (p := fun v => f (Vector.hd v) = true)).
      eapply isΠsem0. exact Vector.nil.
    - intros H k p Hp v. depelim Hp. depelim H0.
      cbn in *. rewrite H1. setoid_rewrite H0.
      eapply (H (fun x => f (x :: v))).
    - intros H f. destruct (H 0 (fun _ => forall n, f n = false)) as [ | ];
        firstorder.
      eapply (isΠsemS (p := fun v => f (Vector.hd v) = false)).
      eapply isΣsem0_ with (f := fun v => negb (f (Vector.hd v))).
      intros. destruct (f (Vector.hd v)); cbn; firstorder congruence.
      exact Vector.nil.
    - intros H k p Hp v. depelim Hp. depelim H0.
      cbn in *. rewrite H1. setoid_rewrite H0.
      red in H. destruct (H (fun x => negb (f (x :: v)))).
      + left. intros. specialize (H2 x).
        destruct (f (x :: v)); cbn in *; congruence.
      + right. intros ?. eapply H2. intros x.
        specialize (H3 x).
        destruct (f (x :: v)); cbn in *; congruence.
    - intros k p H x. depelim H. depelim H.
      cbn in *. rewrite H0. setoid_rewrite H.
      firstorder. destruct (f (x0 :: x)) eqn:E; eauto.
      contradiction H1. intros HE.
      rewrite HE in E. congruence.
  Qed.

  Definition ArithmeticHierarchyNegation n :=
    (forall k (p: vec nat k -> Prop), isΣsem n p -> isΠsem n (fun v => ~(p v)))
    /\ (forall k (p: vec nat k -> Prop), isΠsem n p -> isΣsem n (fun v => ~(p v))).

  Lemma DN_implies_ArithmeticHierarchyNegation n :
    DNE_Σ n -> ArithmeticHierarchyNegation n.
  Proof.
    intros. split; intros; eapply negΣinΠsem; eauto using DNEimpl.
  Qed.

  Definition ArithmeticHierarchyDoubleNegation n :=
    (forall k (p: vec nat k -> Prop), isΣsem n p -> isΣsem n (fun v => ~~(p v)))
    /\ (forall k (p: vec nat k -> Prop), isΠsem n p -> isΠsem n (fun v => ~~(p v))).

  Lemma Negation_to_DoubleNegation n :
    ArithmeticHierarchyNegation n -> ArithmeticHierarchyDoubleNegation n.
  Proof.
    intros H. firstorder.
  Qed.

  Lemma DoubleNegation_to_Negation n :
    (forall m, m <= n -> ArithmeticHierarchyDoubleNegation m) ->
    DNE_Π n ->
    ArithmeticHierarchyNegation n.
  Proof.
    enough ((forall n (k : nat) (p : vec nat k -> Prop), isΣsem n p -> DNE_Π n -> (forall m, m <= n -> ArithmeticHierarchyDoubleNegation m) -> isΠsem n (fun v : vec nat k => ~ p v)) /\
              (forall n (k : nat) (p : vec nat k -> Prop), isΠsem n p -> DNE_Π n -> (forall m, m <= n -> ArithmeticHierarchyDoubleNegation m) ->isΣsem n (fun v : vec nat k => ~ p v))) by firstorder.
    clear n. apply isΣsem_isΠsem_mutind.
    - intros. apply Σ0sem_notΠ0_int. econstructor. eassumption.
    - intros n k p p' H IH H' DN HH.
      econstructor. apply IH.
      + now eapply DNEimpl, DNE_equiv_S.
      + intros. eapply HH. lia.
      + cbn. clear - H'. firstorder.
    - intros. apply Σ0sem_notΠ0_int. econstructor. eassumption.
    - intros n k p p' H IH H' DN HH.
      eapply PredExt with (p := fun v => ~~ exists x, ~p' (x :: v)).
      2:{ intros. rewrite H'. split. 2:firstorder.
          intros ? ?.  eapply H0.
          intros. eapply DNE_equiv_S; eauto.
      }
      eapply HH. lia.
      econstructor. eapply IH.
      + now eapply DNEimpl, DNE_equiv_S.
      + intros. eapply HH. lia.
      + cbn. reflexivity.
  Qed.

  (** # <a id="isSigmasem_or_closed" /> #*)
  Lemma isΣsem_or_closed n :
    (forall k (p: vec nat k -> Prop), isΣsem n p -> forall (q : vec nat k -> Prop), isΣsem n q -> isΣsem n (fun v => p v \/ q v)).
  Proof.
    intros k p Hp q Hq.
    depelim Hp.
    + depelim Hq. cbn in *.
      unshelve eapply PredExt. exact (fun v => f0 v || f v = true). 2: cbn; intros; rewrite orb_true_iff; firstorder.
      apply isΣsem0.
    + depelim Hq. cbn in *.
      rename p' into pp.
      rename p into p'.
      rename p0 into q'.
      rename pp into p.
      unshelve eapply PredExt.
      exact (fun v => exists n, if Nat.eqb n 0 then exists x, p' (x :: v) else exists x, q' (x :: v)).
      2:{ cbn in *. split.
          + intros []. exists 0; firstorder. exists 1; firstorder.
          + intros [[]]; firstorder.
      }
      eapply isΣsemE with (p := fun v => if Vector.hd v =? 0 then exists x : nat, p' (x :: Vector.tl v) else exists x : nat, q' (x :: Vector.tl v)).
      destruct (isΣsem_if_closed (S n)) as [Hs _].
      eapply Hs with (f := fun x => Nat.eqb x 0) (p := fun v => exists x, p' (x :: v)) (q := fun v => exists x, q' (x :: v)).
      eapply isΣsemS. eauto.
      eapply isΣsemS. eauto.
  Qed.

  Lemma DNE_Σ_Sn_to_LEM_Σ_n n :
    DNE_Σ (S n) -> LEM_Σ n.
  Proof.
    intros DNE k p H v.
    eapply DNE with (x := v). 2: firstorder.
    eapply isΣsem_or_closed.
    - now eapply isΣΠn_In_ΣΠSn with (l := 1).
    - eapply DN_implies_ArithmeticHierarchyNegation; eauto.
      now eapply isΣΠn_In_ΠΣSn.
  Qed.

  Definition DNE_Πdisj := fun n : nat => forall (k : nat) (p1 p2 : vec nat k -> Prop), isΠsem n p1 -> isΠsem n p2 -> stable (fun v => p1 v \/ p2 v).

  (** # <a id="isPisem_or_closed" /> #*)
  Lemma isΠsem_or_closed n :
    (forall k (p: vec nat k -> Prop), isΠsem n p -> forall (q : vec nat k -> Prop), isΠsem n q -> DNE_Πdisj n -> isΠsem n (fun v => p v \/ q v)).
  Proof.
    intros. depelim H.
    + depelim H0. cbn in *.
      unshelve eapply PredExt. exact (fun v => f0 v || f v = true). 2: cbn; intros; rewrite orb_true_iff; firstorder.
      apply isΠsem0.
    + depelim H1. cbn in *.
      rename p' into pp.
      rename p into p'.
      rename p0 into q'.
      rename pp into p.
      unshelve eapply PredExt.
      exact (fun v => forall y x : nat, (fun v => p' (Vector.hd v:: Vector.tl (Vector.tl v)) \/ q' (Vector.hd (Vector.tl v)::Vector.tl (Vector.tl v))) (x::y::v)).
      apply isΠsemTwoAll.
      * eapply isΣsem_or_closed.
        -- eapply isΣsem_m_red_closed. { apply H. }
           eexists. red. intros. eapply iff_refl.
        -- eapply isΣsem_m_red_closed. { apply H1. }
           eexists. red. intros. eapply iff_refl.
      * firstorder. edestruct (H3 k p q) with (x := v); eauto. cbn in *.
        rewrite H0 in *. rewrite H2 in *. clear H0 H2 p q.
        intros G.
        assert (~~ ((forall x : nat, p' (x :: v)) \/ ~ (forall x : nat, p' (x :: v)))) by tauto. eapply H0.
        intros []; eauto.
        assert (~~ ((forall x : nat, q' (x :: v)) \/ ~(forall x : nat, q' (x :: v)))) by tauto. eapply H5.
        intros []; eauto. clear H0 H5.
        eapply H2. intros y.
        unshelve edestruct (H3 _ (fun v => p' (y :: v)) (fun _ => False)).
        -- exact v.
        -- eapply isΣΠn_In_ΠΣSn. eapply isΣsem_m_red_closed. { apply H. }
           now eexists. 
        -- replace (S n) with (S n + 0) by lia.
           eapply isΣΠn_In_ΣΠSn with (l := S n).
           unshelve econstructor. exact (fun v => false). firstorder congruence.
        -- firstorder.
        -- auto.
        -- firstorder.
  Qed.

  Lemma LEM_Π_to_DNE_disj n :
    LEM_Π n -> DNE_Πdisj n .
  Proof.
    intros H k p1 p2 H1 H2 v Hv.
    destruct (H _ p1 H1 v); eauto.
    destruct (H _ p2 H2 v); eauto.
    firstorder.
  Qed.
  
End ArithmeticalHierarchySemantic.

 
