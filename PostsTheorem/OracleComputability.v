(** * Synthetic Oracle Computability *)

From SyntheticComputability.Shared Require Import embed_nat.
From SyntheticComputability Require Import Synthetic.Definitions.

From SyntheticComputability Require Import partial.
Require Import ssreflect Setoid.

Require Import Lia Vector List.
Import ListNotations.
Local Notation vec := Vector.t.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Notation "P ⪯ₘ Q" := (reduces P Q) (at level 70).
Lemma red_m_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ₘ q -> q ⪯ₘ r -> p ⪯ₘ r.
Proof.
  intros [f Hf] [g Hg]. exists (fun x => g (f x)). firstorder.
Qed.

Definition compl {X} (p : X -> Prop) := fun x => ~ p x.

Notation "⟨ a , b ⟩" := (embed (a, b)) (at level 0).
  Notation "'fun!' '⟨' x ',' y '⟩' '=>' b" := (fun p => let (x,y) := unembed p in b) (at level 30, b at level 200).

Tactic Notation "intros" "⟨" ident(n) "," ident(m) "⟩" :=
let nm := fresh "nm" in
let E := fresh "E" in
intros nm; destruct (unembed nm) as [n m] eqn:E.

Notation "'∑' x .. y , p" := (sig (fun x => .. (sig (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Lemma R_func {X} {R: FunRel X bool} {x} :
  R x true -> R x false -> False.
Proof.
  intros t f. enough (true = false) by discriminate.
  eapply R; eauto.
Qed.

Definition char_rel {X} (p : X -> Prop) : FunRel X bool. (*** copied from Yannick's PhD ***)
  exists (fun x b => if (b : bool) then p x else ~ p x).
  abstract (intros ? [] [] ? ?; firstorder congruence).
Defined.

Lemma partfun_to_FunRel `{partiality} {X Y} (f : X ↛ Y) :
  exists F : FunRel X Y, forall y b, F y b <-> f y =! b.
Proof.
  unshelve eexists. {
    apply (@Build_FunRel X Y (fun x y => f x =! y)).
    intros x y z. apply hasvalue_det.
  }
  reflexivity.
Qed.

Section Continouity.

    Context {Part : partiality}.

    Definition continuous {X Y Z1 Z2} (r : FunRel Y Z1 -> FunRel X Z2) :=
    forall (R : FunRel Y Z1) (x : X) (b : Z2), r R x b -> exists L, (forall y, In y L -> exists b, R y b) /\ (forall R' : FunRel Y Z1, (forall y b, In y L -> R y b -> R' y b) -> r R' x b).

    Definition continuous_f {X Y Z1 Z2} (r' : (Y ↛ Z1) -> (X ↛ Z2)) :=
    forall f x z, r' f x =! z -> exists L, (forall y, In y L -> exists b, f y =! b) /\ (forall f', (forall y b, In y L -> f y =! b -> f' y =! b) -> r' f' x =! z).

    Definition monotonic {X Y Z1 Z2} (r : FunRel Y Z1 -> FunRel X Z2) :=
    forall (R R' : FunRel Y Z1), (forall x b, R x b -> R' x b) -> forall x b, r R x b -> r R' x b.

    Definition monotonic_f {X Y Z1 Z2} (r' : (Y ↛ Z1) -> (X ↛ Z2)) :=
    forall f f', (forall x b, f x =! b -> f' x =! b) -> forall x b, r' f x =! b -> r' f' x =! b.

    Definition compact {X Y Z1 Z2} (r : FunRel Y Z1 -> FunRel X Z2) :=
    forall (R : FunRel Y Z1) (x : X) b, r R x b -> exists Rfin, (exists L, forall x, In x L <-> exists b, the_rel Rfin x b) /\ (forall x b, Rfin x b -> R x b) /\ r Rfin x b.

    Definition compact_f {X Y Z1 Z2} (r' : (Y ↛ Z1) -> (X ↛ Z2)) :=
    forall f x b, r' f x =! b -> exists Ffin, (exists L, forall x, In x L <-> exists b, Ffin x =! b) /\ (forall x b, Ffin x =! b -> f x =! b) /\ r' Ffin x =! b.

    Lemma cont_is_mon_and_comp {X Y Z1 Z2} (r : FunRel Y Z1 -> FunRel X Z2) :
    continuous r <-> monotonic r /\ compact r.
    Proof.
    unfold continuous, monotonic, compact. split.
    - intros cont. split.
        + firstorder.
        + intros R x b h.
        specialize (cont R x b h) as [L Hl].
        exists (@Build_FunRel _ _ (fun y z => In y L /\ R y z) ltac:(intros y z1 z2 [_ R1] [_ R2]; eapply R; eauto)).
        repeat split; cbn.
        * exists L. firstorder.
        * firstorder.
        * apply Hl. cbn. firstorder.
    - intros [mono comp].
        intros R x b h. specialize (comp R x b h) as [Rfin [[L Hl] [HRfin HRfh]]].
        exists L. split.
        + intros y i. apply Hl in i as [z Hz]. exists z. apply HRfin, Hz.
        + intros R' HRR'. eapply mono. 2: apply HRfh.
        intros y z Hyz. apply HRR'.
        * apply Hl. now exists z.
        * apply HRfin, Hyz.
    Qed.

    Lemma cont_is_mon_and_comp_f {X Y Z1 Z2} (dec : forall (x y : Y), {x = y} + {x <> y}) (r' : (Y ↛ Z1) -> (X ↛ Z2)) :
    continuous_f r' <-> monotonic_f r' /\ compact_f r'.
    Proof.
    unfold continuous_f, monotonic_f, compact_f. split.
    - intros cont. split.
        + intros f f' Hff' x z H. destruct (cont _ _ _ H) as [L HL].
          apply HL. intros. now apply Hff'.
        + intros R x b h.
        specialize (cont R x b h) as [L Hl].
        exists (fun y => match List.find (fun y' => match dec y y' with left _ => true | right _ => false end) L with Some _ => R y | None => undef end).
        assert (forall y z, match List.find (fun y' => match dec y y' with left _ => true | right _ => false end) L with Some _ => R y | None => undef end =! z <-> (In y L /\ R y =! z)) as spec. {
            clear. intros y Hz.
            destruct find eqn:eq.
            - apply find_some in eq as [i eq].
            destruct dec as [<- | neq]. 2: discriminate.
            easy.
            - split; [intros []%undef_hasvalue|].
            intros [H%(find_none _ _ eq y) H']. now destruct dec.
        }
        repeat setoid_rewrite spec.
        repeat split; cbn.
        * exists L. firstorder.
        * firstorder.
        * apply Hl. firstorder.
    - intros [mono comp].
        intros R x b h. specialize (comp R x b h) as [Rfin [[L Hl] [HRfin HRfh]]].
        exists L. split.
        + intros y i. apply Hl in i as [z Hz]. exists z. apply HRfin, Hz.
        + intros R' HRR'. eapply mono. 2: apply HRfh.
        intros y z Hyz. apply HRR'.
        * apply Hl. now exists z.
        * apply HRfin, Hyz.
    Qed.
End Continouity.

(** ** Oracle Machines *)
Section OracleMachines.

  Context {Part : partiality}.

  Record oracle_machine A B X Y :=
    {
    oracle_fun_rel :> FunRel A B -> FunRel X Y ;
    oracle_fun_part : (A ↛ B) -> (X ↛ Y) ;
    oracle_factors : (forall f R, pcomputes f (the_rel R) -> pcomputes (oracle_fun_part f) (oracle_fun_rel R)) ;
    oracle_continuous : continuous oracle_fun_rel
    }.

  Lemma oracle_machine_core_coninous {A B X Y} (om : oracle_machine A B X Y) :
    continuous_f (om.(oracle_fun_part)).
  Proof.
    intros f x b h. destruct om as [r r' Hr cont]. cbn in *.
    apply (Hr f (@Build_FunRel A B (fun a b => f a =! b) ltac:(intros ? ?; apply hasvalue_det)) ltac:(firstorder)) in h.
    destruct (cont _ _ _ h) as [L [Hl Hl']]. exists L. split.
    - intros a i. destruct (Hl a i) as [b' Hb']. now exists b'.
    - intros f' Hf'. apply (Hr f' (@Build_FunRel A B (fun a b => f' a =! b) ltac:(intros ? ?; apply hasvalue_det)) ltac:(firstorder)).
      now apply Hl'.
  Qed.

End OracleMachines.

(** ** Turing Reductions *)
Section TuringReduction.

  Context {Part : partiality}.

  Definition red_Turing {X A} (p : X -> Prop) (q : A -> Prop) :=
    exists r : oracle_machine A bool X bool, forall x b, char_rel p x b <-> r (char_rel q) x b. 

  Notation "P ⪯ᴛ Q" := (red_Turing P Q) (at level 50).

  Definition red_m_impl_red_T {X} (P : X -> Prop) {Y} (Q : Y -> Prop):
    P ⪯ₘ Q -> P ⪯ᴛ Q.
  Proof.
    intros [f Hf].
    unshelve eexists. {
      unshelve econstructor.
      - intros R. apply (@Build_FunRel _ _ (fun x b => R (f x) b)). { intros x b b'. apply R. }
      - intros r x. apply r, f, x.
      - cbn. firstorder.
      - intros R x b H. cbn in *. exists ([f x]). split; [|firstorder].
        intros y [<-|[]]. now exists b.
    }
    cbn. intros x []; cbn; firstorder.
  Qed.

  Lemma weakly_total_Forall2' {X Y} {R : X -> Y -> Prop} (L : list X) :
  (forall x, In x L -> exists y, R x y) -> exists L', Forall2 R L L'.
  Proof.
  intros Htot. induction L.
  - exists []. econstructor.
  - destruct (Htot a ltac:(now left)) as [y Hy].
    destruct (IHL ltac:(firstorder)) as [L' IH].
    exists (y :: L'). now econstructor.
  Qed.

  Lemma Forall2_Forall_l {A B} (P : A -> B -> Prop) (Q : A -> Prop) l k :
    Forall2 P l k -> Forall (fun y => forall x, P x y -> Q x) k -> Forall Q l.
  Proof. induction 1; inversion_clear 1; eauto. Qed.

  Lemma red_T_trans {X} (A : X -> Prop) {Y} (B : Y -> Prop) {Z} (C : Z -> Prop) :
    A ⪯ᴛ B -> B ⪯ᴛ C -> A ⪯ᴛ C.
  Proof.
    intros [om1 Hom1] [om2 Hom2].
    unshelve eexists. {
      unshelve econstructor.
      - intros R. apply (@Build_FunRel _ _ (fun x b => om1 (om2 R) x b)). {
          intros ? [] [] eq eq'; cbn in *; reflexivity + destruct (R_func eq eq') + destruct (R_func eq' eq).
        }
      - intros r. apply om1, om2, r.
      - intros. now apply om1, om2.
      - intros R x H.
        destruct om1 as [or or' oHr oC]. destruct om2 as [rr rr' rHr rC].
        unfold continuous in *. cbn in *.
        intros halt. 
        destruct (oC (rr R) x _ halt) as [L1 [HL1' HL1]].
        assert (forall x, In x L1 ->
          exists L, (forall y : Z, In y L -> exists b : bool, R y b)
          /\ (forall R': FunRel Z bool, (forall y b, In y L -> R y b -> R' y b) -> forall b, rr R x b -> rr R' x b)) as rC'. {
            intros y i.
            destruct (HL1' y i) as [b Hb].
            destruct (rC R y b Hb) as [L Hl].
            exists L. split; [apply Hl|].
            intros R' HR' b' Hb'.
            assert (b = b') as <-. {
              destruct (rr R) as [rrf rrp]. eapply rrp; eauto.
            } now apply Hl.
        }
        eapply (@weakly_total_Forall2' _ _ _ L1) in rC' as [L2 HL2].
        exists (concat L2). split. {
          rewrite <- List.Forall_forall.
          setoid_rewrite Forall_concat.
          rewrite List.Forall_forall.
          intros L' i'.
          clear HL1.
          induction HL2.
          - destruct i'.
          - cbn in *. destruct i' as [-> | i'].
            + rewrite List.Forall_forall. apply H0.
            + apply IHHL2.
              * intros. apply HL1'. now right.
              * apply i'.
          } 
        intros. eapply HL1. intros y b' Hy. revert b'. pattern y. revert y Hy.
        eapply List.Forall_forall.
        eapply Forall2_Forall_l. eassumption.
        eapply List.Forall_forall. intros. eapply H2. 2: eauto.
        intros. apply H0.
        eapply in_concat. eauto. eauto.
    }
    cbn. 
    specialize om1.(oracle_continuous).
    intros [mono _]%cont_is_mon_and_comp x b.
    assert (om1 (om2 (char_rel C)) x b <-> om1 (char_rel B) x b) as -> by (split; eapply mono, Hom2).
    apply Hom1.
  Qed.

  Definition stable {X} (p : X -> Prop) := forall x, ~~ p x -> p x.

  Lemma Turing_red_compl {X} (P : X -> Prop): 
    stable P -> P ⪯ᴛ compl P.
  Proof.
    intros DN.
    unshelve eexists. {
      clear DN.
      unshelve econstructor.
      - intros R. apply (@Build_FunRel _ _ (fun x b => R x (negb b))). { intros ? [] [] eq eq'; cbn in *; try reflexivity; eapply R; eauto. }
      - intros O x. apply (bind (O x) (fun b => ret (negb b))).
      - cbn. intros f R pc x b. rewrite bind_hasvalue. setoid_rewrite <- ret_hasvalue_iff.
        split. { now intros [[] [H%pc <-]]. } { intros H%pc. exists (negb b). now destruct b. }
      - unfold continuous. cbn. intros R x b H. exists [x]. split; [exists (negb b)|]; firstorder congruence.
    } cbn. intros x []; cbn.
    - split; [firstorder|apply DN].
    - reflexivity.
  Qed.

  Lemma compl_Turing_red {X} (P : X -> Prop): 
    stable P -> (compl P) ⪯ᴛ P.
  Proof.
    intros DN.
    unshelve eexists. {
      clear DN.
      unshelve econstructor.
      - intros R. apply (@Build_FunRel _ _ (fun x b => R x (negb b))). { intros ? [] [] eq eq'; cbn in *; try reflexivity; eapply R; eauto. }
      - intros O x. apply (bind (O x) (fun b => ret (negb b))).
      - cbn. intros f R pc x b. rewrite bind_hasvalue. setoid_rewrite <- ret_hasvalue_iff.
        split. { now intros [[] [H%pc <-]]. } { intros H%pc. exists (negb b). now destruct b. }
      - unfold continuous. cbn. intros R x b H. exists [x]. split;[exists (negb b)|]; firstorder congruence.
    } cbn. intros x []; cbn.
    - reflexivity.
    - split; [apply DN|firstorder].
  Qed.

  Lemma partial_total X Y (f : X ↛ Y) :
    (forall x, (ter (f x))) -> ∑ g : X -> Y, forall x, f x =! g x.
  Proof.
    intros H. unshelve eexists.
    - intros x. specialize (H x). exact (eval H).
    - intros x. cbn. eapply eval_hasvalue.
  Qed.

  Lemma partial_decidable {X} (p : X -> Prop) (f : X ↛ bool) :
    (forall x, ter (f x)) -> (forall x, f x =! true <-> p x) -> decidable p.
  Proof.
    intros Hter He.
    destruct (@partial_total _ _ _ Hter) as [g Hg].
    exists g. intros x. red. rewrite <- He. specialize (Hg x).
    destruct (g x); firstorder. eapply hasvalue_det; eauto. congruence.
  Qed.

  Lemma pcomputes_decider {X} f (R : FunRel X bool) :
    pcomputes f R -> (forall x, ter (f x)) -> decidable (fun x => R x true).
  Proof.
    intros Hf HR.
    eapply partial_decidable with (f := f).
    - intros x. eauto. 
    - intros x. split.
      + intros H. now eapply Hf.
      + intros H. destruct (HR x) as [b Hb].
        enough (b = true) by congruence.
        eapply Hf in Hb. eapply R; eauto.
  Qed.

  Require Import Morphisms.

  Instance Proper_decider {X} :
    Proper (pointwise_relation X (@eq bool) ==> pointwise_relation X iff ==> iff ) (@decider X).
  Proof.
    intros f g H1 p q H2. red in H1, H2.
    unfold decider, reflects. 
    split; intros H x.
    - now rewrite <- H2, H, H1.
    - now rewrite H2 H H1.
  Qed.

  Instance Proper_decidable {X} :
    Proper (pointwise_relation X iff ==> iff) (@decidable X).
  Proof.
    intros p q H2.
    split; intros [f H]; exists f.
    - now rewrite <- H2.
    - now rewrite H2.
  Qed.

  Lemma transport_decidable : forall X Y (p : X -> Prop) (q : Y -> Prop),
      (forall x : part bool, ~~ ter x -> ter x) ->
      p ⪯ᴛ q -> decidable q -> decidable p.
  Proof.
    intros X Y p q mp ([r r' Hr' HC] & H) [f Hf].
    pose proof (Hq := Hr' (fun x => ret (f x)) (char_rel q)).
    - cbn in *.
      eapply (@Proper_decidable X) with (y := fun x => r (char_rel q) x true).
      intros x. eapply (H x true).
      unshelve epose proof (Hq _); clear Hq; try rename H0 into Hq.
      + intros x b. rewrite <- ret_hasvalue_iff.
        specialize (Hf x). clear - Hf. destruct b, (f x); firstorder congruence.
      + eapply pcomputes_decider; eauto.
         intros. eapply mp.
         intros Hx. assert (~~ (p x \/ ~ p x)) as HH by tauto. eapply HH. intros [Hp | Hp].
         -- eapply (H x true) in Hp. eapply Hx. eapply Hq in Hp. eexists; eauto.
         -- eapply (H x false) in Hp. eapply Hx. eapply Hq in Hp. eexists; eauto.
  Qed.

  Lemma decidable_compl_stable {X} (P : X -> Prop) :
    (forall P : X -> Prop, decidable (compl P) -> decidable P) -> stable P.
  Proof.
    intros H x Hx.
    destruct (H (fun _ => P x)) as [f Hf].
    - exists (fun _ => false). firstorder congruence.
    - specialize (Hf x). destruct (f x); firstorder congruence.
  Qed.

  Lemma rev {X} (P : X -> Prop) :
    (forall x : part bool, ~~ ter x -> ter x) ->
    (forall P : X -> Prop, P ⪯ᴛ compl P) -> stable P.
  Proof.
    intros mp H.
    eapply decidable_compl_stable.
    intros Q. eapply transport_decidable; eauto.
  Qed.

End TuringReduction.

Notation "P ⪯ᴛ Q" := (red_Turing P Q) (at level 50).

(** ** Oracle Semi-decidability *)
Section OracleSemiDecidability.

  Context {Part : partiality}.

  Lemma semi_decidable_part_iff_True {X} {p : X -> Prop} :
    semi_decidable p <-> exists (f : X -> part True), forall x, p x <-> f x =! I.
  Proof.
    split.
    - intros [f Hf].
      exists (fun x : X => mkpart (fun n : nat => if f x n then Some I else None)).
      intros x.
      rewrite (Hf x). split.
      + intros [n H].
        apply mkpart_hasvalue. {
          intros n1 n2 [] []. destruct (f x n1), (f x n2). all: congruence.
        }
        exists n. now rewrite H.
      + intros [n H]%mkpart_hasvalue1. exists n.
        destruct f; congruence.
    - intros [f Hf]. exists (fun x n => if seval (f x) n is Some _ then true else false).
      intros x. rewrite Hf. split.
      + intros H. eapply seval_hasvalue in H as [n H].
        exists n. now rewrite H.
      + intros [n H]. eapply seval_hasvalue. exists n.
        destruct seval as [[]|]; congruence.
  Qed.

  Definition oracle_semi_decidable `{partiality} {A} (Q : A -> Prop) {X} (P : X -> Prop) : Prop :=
    exists (om : oracle_machine A bool X True), forall x, P x <-> om (char_rel Q) x I.

  Lemma oracle_semi_dec_inhabited_type {A} (Q : A -> Prop) {X} (P : X -> Prop) {Y} (z : Y) :
    oracle_semi_decidable Q P <-> exists (om : oracle_machine A bool X Y), forall x, P x <-> exists z, om (char_rel Q) x z.
  Proof.
    split; intros [[r r' Hr cont] Hom]; cbn in *.
    - unshelve eexists. {
        unshelve econstructor.
        - intros R. eapply (@Build_FunRel X Y (fun x z' => z' = z /\ r R x I)).
          now intros x z1 z2 [-> _] [-> _].
        - intros R x. apply (bind (r' R x)). intros _. apply (ret z).
        - cbn. intros f R Hf x z'. rewrite bind_hasvalue. split.
          + now intros [[] [H%(Hr f R Hf) H'%ret_hasvalue_iff]].
          + intros [-> H%(Hr f R Hf)]. exists I. now rewrite <- ret_hasvalue_iff.
        - unfold continuous. cbn. intros R x ? [-> H].
          specialize (cont R x I H). firstorder.
      } cbn. intros x. rewrite Hom. now split; [exists z|intros [? [-> ?]]].
    - unshelve eexists. {
        unshelve econstructor.
        - intros R. eapply (@Build_FunRel X True (fun x i => exists z, r R x z)). now intros x [] [].
        - intros R x. apply (bind (r' R x)). intros _. apply (ret I).
        - cbn. intros f R Hf x []. rewrite bind_hasvalue. split.
          + intros [z' [H%(Hr f R Hf) H'%ret_hasvalue_iff]]; eauto.
          + intros [z' H%(Hr f R Hf)]. exists z'. now rewrite <- ret_hasvalue_iff.
        - unfold continuous. cbn. intros R x [] [z' H].
          specialize (cont R x z' H). firstorder.
      } cbn. intros x. now rewrite Hom.
  Qed.

  Lemma oracle_semi_dec_inhabited_discrete_type {A} (Q : A -> Prop) {X} (P : X -> Prop) {Y} (z : Y) (dec: forall z', {z = z'} + {z <> z'}) :
    oracle_semi_decidable Q P <-> exists (om : oracle_machine A bool X Y), forall x, P x <-> om (char_rel Q) x z.
  Proof.
    split; intros [[r r' Hr cont] Hom]; cbn in *.
    - unshelve eexists. {
        unshelve econstructor.
        - intros R. eapply (@Build_FunRel X Y (fun x z' => z' = z /\ r R x I)).
          now intros x z1 z2 [-> _] [-> _].
        - intros R x. apply (bind (r' R x)). intros _. apply (ret z).
        - cbn. intros f R Hf x z'. rewrite bind_hasvalue. split.
          + now intros [[] [H%(Hr f R Hf) H'%ret_hasvalue_iff]].
          + intros [-> H%(Hr f R Hf)]. exists I. now rewrite <- ret_hasvalue_iff.
        - unfold continuous. cbn. intros R x ? [-> H].
          specialize (cont R x I H). firstorder.
      } cbn. intros x. now rewrite Hom.
    - unshelve eexists. {
        unshelve econstructor.
        - intros R. eapply (@Build_FunRel X True (fun x i => r R x z)). now intros x [] [].
        - intros R x. apply (bind (r' R x)). intros z'. destruct (dec z'); [apply (ret I) | apply undef].
        - cbn. intros f R Hf x []. rewrite bind_hasvalue. split.
          + intros [z' [H%(Hr f R Hf) H']]. destruct dec as [->|]; [easy|]. now apply undef_hasvalue in H'.
          + intros H%(Hr f R Hf). exists z. destruct (dec z) as [_|neq]; [now rewrite <- ret_hasvalue_iff|now contradict neq].
        - unfold continuous. cbn. intros R x []. apply cont.
      } cbn. intros x. now rewrite Hom.
  Qed.

  Lemma mk𝕄True {X Y} (r : FunRel Y bool -> X -> Prop) (r' : (Y ↛ bool) -> (X ↛ True)) :
    (forall f (R : FunRel Y bool), pcomputes f R -> forall x, r' f x =! I <-> r R x) ->
    (forall R x, r R x -> exists L, (forall y, In y L -> exists b, R y b)
          /\ (forall R' : FunRel Y bool,
              (forall y b, In y L -> R y b -> R' y b) -> r R' x)) ->
    oracle_machine Y bool X True.
  Proof.
    unshelve eexists.
    - intros R. apply (@Build_FunRel _ True (fun x _ => r R x)). now intros ? [] [].
    - apply r'.
    - unfold pcomputes. cbn. intros ? ? ? ? []. auto.
    - unfold continuous. cbn. intros ? ? []. auto.
  Defined.

  Lemma mk_semi_dec {X Y} {Q : Y -> Prop} {P : X -> Prop} (r : FunRel Y bool -> X -> Prop) (r' : (Y ↛ bool) -> (X ↛ True)) :
    (forall f (R : FunRel Y bool), pcomputes f R -> forall x, r' f x =! I <-> r R x) ->
    (forall R x, r R x -> exists L, (forall y, In y L -> exists b, R y b)
          /\ (forall R' : FunRel Y bool,
              (forall y b, In y L -> R y b -> R' y b) -> r R' x)) ->
    (forall x, P x <-> r (char_rel Q) x) -> 
    oracle_semi_decidable Q P.
  Proof.
    intros.
    unshelve eexists.
    eapply mk𝕄True; eauto.
    assumption.
  Qed.

  Lemma no_oracle_semi_decidable {X A} (p : X -> Prop) (q : A -> Prop):
    decidable q -> semi_decidable p <-> oracle_semi_decidable q p.
  Proof. unfold decidable, decider, reflects.
    intros Hdec. split.
    - intros [f Hf]%semi_decidable_part_iff_True.
      unfold oracle_semi_decidable.
      eapply mk_semi_dec with (r := fun _ => p) (r' := fun _ => f); eauto.
      + intros. now rewrite <- Hf.
      + intros. now exists [].
    - intros [[r r' Hr'] H]. cbn in H.
      apply semi_decidable_part_iff_True.
      destruct Hdec as [fd Hdec].
      exists (r' (fun a => ret(fd a))).
      unfold pcomputes in *.
      intros x. rewrite H. rewrite (Hr' _ ). 2: reflexivity. clear x.
      intros x b. unfold char_rel. cbn.
      rewrite <- ret_hasvalue_iff. unfold decider, reflects in Hdec.
      destruct b; rewrite Hdec; destruct fd; split; congruence.
  Qed.

  Lemma semi_dec_turing_red_trans {X} (A : X -> Prop) {Y} (B : Y -> Prop) {Z} (C : Z -> Prop) :
      oracle_semi_decidable B A -> B ⪯ᴛ C -> oracle_semi_decidable C A.
  Proof.
    intros [om Hom] [red Hred].
    unshelve eapply mk_semi_dec with
      (r := fun O x => om (red O) x I)
      (r' := fun O => om.(oracle_fun_part) (red.(oracle_fun_part) O)).
    - intros. now apply om, red.
    - intros R x H.
      destruct om as [or or' oHr oC]. destruct red as [rr rr' rHr rC].
      unfold continuous in *. cbn in *. 
      destruct (oC (rr R) x I H) as [L1 [HL1' HL1]].
      assert (forall x, In x L1 ->
        exists L, (forall y : Z, In y L -> exists b : bool, R y b)
        /\ (forall R': FunRel Z bool, (forall y b, In y L -> R y b -> R' y b) -> forall b, rr R x b -> rr R' x b)) as rC'. {
          intros y i.
          destruct (HL1' y i) as [b Hb].
          destruct (rC R y b Hb) as [L Hl].
          exists L. split; [apply Hl|].
          intros R' HR' b' Hb'.
          assert (b = b') as <-. {
            destruct (rr R) as [rrf rrp]. eapply rrp; eauto.
          } now apply Hl.
      }
      eapply (@weakly_total_Forall2' _ _ _ L1) in rC' as [L2 HL2].
      exists (concat L2). split. {
        rewrite <- List.Forall_forall.
        setoid_rewrite Forall_concat.
        rewrite List.Forall_forall.
        intros L' i'.
        clear HL1.
        induction HL2.
        - destruct i'.
        - cbn in *. destruct i' as [-> | i'].
          + rewrite List.Forall_forall. apply H0.
          + apply IHHL2.
            * intros. apply HL1'. now right.
            * apply i'.
        } 
      intros. eapply HL1. intros y b' Hy. revert b'. pattern y. revert y Hy.
      eapply List.Forall_forall.
      eapply Forall2_Forall_l. eassumption.
      eapply List.Forall_forall. intros. eapply H2. 2: eauto.
      intros. apply H0.
      eapply in_concat. eauto. eauto.
    - specialize om.(oracle_continuous).
      intros [mono _]%cont_is_mon_and_comp x.
      assert (om (red (char_rel C)) x I <-> om (char_rel B) x I) as -> by (split; eapply mono, Hred).
      apply Hom.
  Qed.

  Lemma oracle_semi_decidable_complement_iff {X} (A : X -> Prop) {Y} (B : Y -> Prop) :
    stable B -> oracle_semi_decidable B A <-> oracle_semi_decidable (fun y => ~ B y) A.
  Proof.
    intros DN.
    split.
    - intros H. apply (semi_dec_turing_red_trans H), Turing_red_compl, DN.
    - intros H. apply (semi_dec_turing_red_trans H), compl_Turing_red, DN.
  Qed.

  Lemma semi_decidable_m_red {X} (Q : X -> Prop) {Y} (P : Y -> Prop) {Y'} (P' : Y' -> Prop):
    P ⪯ₘ P' -> oracle_semi_decidable Q P' -> oracle_semi_decidable Q P.
  Proof.
    intros [f Hf] [[r r' Hr Hc] Hom]. cbn in *.
    unfold reduction in Hf. unfold oracle_semi_decidable.
    setoid_rewrite Hf. setoid_rewrite Hom.
    eapply mk_semi_dec with
      (r := fun R x => r R (f x) I)
      (r' := fun R x => (r' R (f x))).
      - intros. now apply Hr.
      - intros. now apply Hc.
      - reflexivity.
  Qed.

  Definition V0 (f : nat -> bool) := forall n, f n = true.
  Definition Cof0 (f : nat -> bool) := exists k, forall n, n > k -> f n = true.

  Lemma Cof0_is_semi_decidable_in_V0: 
    oracle_semi_decidable V0 Cof0.
  Proof.
    eapply mk_semi_dec with 
      (r := fun O f =>(exists k, O (fun n => if Nat.leb n k then true else f n) true))
      (r' := (fun O f => mkpart (fun! ⟨k,m⟩ => 
        match seval (O (fun n => if Nat.leb n k then true else f n)) m with 
        | Some true => Some I
        | _ => None
        end))).
    - intros f R Hr f'. rewrite mkpart_hasvalue. 1: intros ? ? [] []; reflexivity.  
      split.
      + intros [em H]. destruct unembed as [k m]. exists k.
        destruct seval as [[]|] eqn:eq; try congruence.
        apply Hr. apply seval_hasvalue. eauto.
      + intros [k H].
        unfold pcomputes in Hr.
        specialize Hr as Hr'.
        specialize (Hr' (fun n : nat => if Nat.leb n k then true else f' n) true) as [_ Hr']. specialize (Hr' H).
        apply seval_hasvalue in Hr' as [m Hr'].
        exists (embed (k, m)).
        rewrite embedP.
        destruct seval as [[]|] eqn:eq.
        * reflexivity.
        * congruence.
        * congruence.
    - intros R x [k H].
      exists [(fun n : nat => if Nat.leb n k then true else x n)].
      split. { intros f [<-|[]]. now exists true. }
      intros R' Hl. exists k. now apply Hl; [now left|].
    - intros f.
      unfold Cof0. unfold V0. split.
      + intros [k H]. exists k. intros n. destruct Nat.leb eqn:leb.
        * reflexivity.
        * apply H. apply Compare_dec.leb_complete_conv in leb. lia.
      + intros [k H]. exists k. intros n ge. rewrite <- (H n). destruct Nat.leb eqn:leb.
        * apply Compare_dec.leb_complete in leb. lia.
        * reflexivity.
  Qed.

End OracleSemiDecidability.

(** ** Determinacy of Oracle Machines by Their Cores *)
Section CoreDeterminacy.

  Context {Part : partiality}.

  Variable vec_to_nat : forall k, vec nat k -> nat.
  Variable nat_to_vec : forall k, nat -> vec nat k.
  Variable vec_nat_inv : forall k v, nat_to_vec k (vec_to_nat v) = v.
  Variable nat_vec_inv : forall k n, vec_to_nat (nat_to_vec k n) = n.

  Definition oracle_from_lists {X} (dec : forall (x y : X), {x = y} + {x <> y}) (LT LF: list X) (x : X) :=
      if existsb (fun y => match dec x y with left _ => true | right _ => false end) LT then ret true
  else if existsb (fun y => match dec x y with left _ => true | right _ => false end) LF then ret false
  else undef.

  Lemma oracle_from_lists_spec {X} (dec : forall (x y : X), {x = y} + {x <> y}) LT LF  x:
    (forall y, ~(List.In y LT /\ List.In y LF)) ->
      (oracle_from_lists dec LT LF x =! true <-> List.In x LT)
    /\ (oracle_from_lists dec LT LF x =! false <-> List.In x LF).
  Proof.
    intros disj.
    unfold oracle_from_lists. destruct (existsb _ LT) eqn:eq; [|destruct (existsb _ LF) eqn:eq'].
    - repeat rewrite <- ret_hasvalue_iff. apply List.existsb_exists in eq as [y [i eq]].
      destruct (dec x y) as [<-|]; firstorder congruence.
    - repeat rewrite <- ret_hasvalue_iff. apply List.existsb_exists in eq' as [y [i eq']].
      destruct (dec x y) as [<-|]; firstorder congruence.
    - split; split.
      + intros []%undef_hasvalue.
      + intros H. enough (false = true) as [=]. rewrite <- eq. apply List.existsb_exists.
        exists x. now destruct dec.
      + intros []%undef_hasvalue.
      + intros H. enough (false = true) as [=]. rewrite <- eq'. apply List.existsb_exists.
        exists x. now destruct dec.
  Qed.

  Lemma split_L_LT_LF {X} (L: list X) (R: FunRel X bool):
    (forall x, In x L -> exists b, R x b) ->
    exists LT LF, 
      (forall y, List.In y LT -> R y true) /\
      (forall y, List.In y LF -> R y false) /\
      (forall x, List.In x L -> List.In x LT \/ List.In x LF ) /\
      (forall y, ~(In y LT /\ In y LF)).
  Proof.
    induction L as [|x L IH]; intros H.
    - now exists List.nil, List.nil.
    - destruct (IH ltac:(firstorder)) as [LT [LF [IH1 [IH2 [IH3 IH4]]]]].
      destruct (H x ltac:(now left)) as [[] Hb].
      + exists (List.cons x LT), LF. clear IH. repeat split. 1-3: firstorder congruence.
        intros y [[-> | i1] i2].
        * eapply R_func; eauto.
        * eapply R_func; [apply IH1|apply IH2]; eauto.
      + exists LT, (List.cons x LF). clear IH. repeat split. 1-3: firstorder congruence.
        intros y [i1 [-> | i2]].
        * eapply R_func; eauto.
        * eapply R_func; [apply IH1|apply IH2]; eauto.
  Qed. 

  Lemma oracle_iff_exists_LT_LF {A X Y} (dec : forall (x y : A), {x = y} + {x <> y}) (om : oracle_machine A bool X Y) :
    forall R x y, om R x y <-> (exists LT LF, (forall y, List.In y LT -> R y true) /\ (forall y, List.In y LF -> R y false) /\ om.(oracle_fun_part) (oracle_from_lists dec LT LF) x =! y).
  Proof.
    intros x. destruct om as [r r' Hr cont].
    unfold continuous, monotonic in *. cbn in *. intros ? z.
    split.
    - intros halt.
      destruct (cont _ _ _ halt) as [L [Hl' Hl]].
      destruct (split_L_LT_LF Hl') as [LT [LF [H1 [H2 [H3 disj]]]]].
      exists LT, LF. repeat split; try assumption.
      apply (Hr _ (@Build_FunRel _ _ (fun y b => (oracle_from_lists dec LT LF) y =! b) ltac:(intros ?; apply hasvalue_det))). 1: now intros ? ?.
      apply Hl.
      intros y b i H; cbn in *.
      destruct b.
      + apply (oracle_from_lists_spec dec _ disj). destruct (H3 y i) as [|H'%H2]; [easy|].
        destruct (R_func H H').
      + apply (oracle_from_lists_spec dec _ disj). destruct (H3 y i) as [H'%H1|]; [|easy].
        destruct (R_func H' H).
    - intros [LT [LF [HT [HF H]]]].
      apply (Hr _ (@Build_FunRel _ _ (fun y b => (oracle_from_lists dec LT LF) y =! b) ltac:(intros ?; apply hasvalue_det))) in H; [|now intros y b].
      apply cont_is_mon_and_comp in cont as [mono _].
      eapply mono. 2: apply H.
      intros y []; cbn.
      + intros H'%oracle_from_lists_spec. now apply HT.
        intros v [Rt%HT Rf%HF]. destruct (R_func Rt Rf).
      + intros H'%oracle_from_lists_spec. now apply HF.
        intros v [Rt%HT Rf%HF]. destruct (R_func Rt Rf).
  Qed.

  Lemma eq_core {A X Y} (dec : forall (x y : A), {x = y} + {x <> y}) :
  forall (om1 om2 : oracle_machine A bool X Y),
    (forall f x z, om1.(oracle_fun_part) f x =! z <-> om2.(oracle_fun_part) f x =! z) -> forall R x z, om1 R x z <-> om2 R x z.
  Proof.
    intros om1 om2 eq R x z.
    repeat rewrite (oracle_iff_exists_LT_LF dec). now setoid_rewrite eq.
  Qed.

  Lemma core_to_om {A X Y} (dec : forall (x y : A), {x = y} + {x <> y}):
    forall C, continuous_f C ->
    { M : oracle_machine A bool X Y | M.(oracle_fun_part) = C }.
  Proof.
    intros C cont.
    unshelve eexists. {
      unshelve econstructor.
      - intros R. eapply (@Build_FunRel X Y (fun x z => exists LT LF, (forall y, List.In y LT -> R y true) /\ (forall y, List.In y LF -> R y false) /\ C (oracle_from_lists dec LT LF) x =! z)).
        intros x z1 z2. intros [LT1 [LF1 [LH1 [LH1' LH1'']]]] [LT2 [LF2 [LH2 [LH2' LH2'']]]].
        apply (cont_is_mon_and_comp_f dec) in cont as [mono _]. unfold monotonic_f in mono.
        assert (forall y, ~(List.In y LT1 /\ List.In y LF1)) as disj1. {
          intros y [Rt%LH1 Rf%LH1']. eapply R_func; eauto.
        }
        assert (forall y, ~(List.In y LT2 /\ List.In y LF2)) as disj2. {
          intros y [Rt%LH2 Rf%LH2']. eapply R_func; eauto.
        }
        assert (forall y, ~(List.In y (LT1++LT2) /\ List.In y (LF1++LF2))) as disj12. {
          intros y [[Rt%LH1|Rt%LH2]%in_app_or [Rf%LH1'|Rf%LH2']%in_app_or]; eapply R_func; eauto.
        }
        assert (C (oracle_from_lists dec (LT1++LT2) (LF1++LF2)) x =! z1) as Hz1. {
          eapply mono. 2: apply LH1''. intros y []; intros H%(oracle_from_lists_spec dec y disj1).
          all: eapply (oracle_from_lists_spec dec y disj12), in_app_iff; auto.
        }
        assert (C (oracle_from_lists dec (LT1++LT2) (LF1++LF2)) x =! z2) as Hz2. {
          eapply mono. 2: apply LH2''. intros y []; intros H%(oracle_from_lists_spec dec y disj2).
          all: eapply (oracle_from_lists_spec dec y disj12), in_app_iff; auto.
        }
        eapply hasvalue_det.
        + apply Hz1.
        + apply Hz2.
      - apply C.
      - cbn. unfold pcomputes. intros f R HfR x y. {
        split.
          - intros halt.
            destruct (cont _ _ _ halt) as [L [Hl' Hl]].
            destruct (partfun_to_FunRel f) as [F HF].
            specialize Hl' as Hl''. setoid_rewrite HfR in Hl''.
            setoid_rewrite <- HF in Hl'.
            destruct (split_L_LT_LF Hl') as [LT [LF [H1 [H2 [H3 disj]]]]].
            setoid_rewrite HF in H1. setoid_rewrite HF in H2.
            setoid_rewrite HfR in H1. setoid_rewrite HfR in H2.
            exists LT, LF. repeat split; try assumption.
            apply (cont_is_mon_and_comp_f dec) in cont as [mono _]. unfold monotonic_f in mono.
            apply Hl. intros y' [] [i|i]%H3 h%HfR;
            eapply (oracle_from_lists_spec dec _ disj).
            all: try assumption.
            + destruct (R_func h (H2 _ i)).
            + destruct (R_func (H1 _ i) h).
          - apply (cont_is_mon_and_comp_f dec) in cont as [mono _]. unfold monotonic_f in mono.
            intros [LT [LF [HT [HF H]]]].
            eapply mono. 2: apply H.
            intros y' []; cbn.
            + intros H'%oracle_from_lists_spec. now apply HfR, HT.
              intros v [Rt%HT Rf%HF]. destruct (R_func Rt Rf).
            + intros H'%oracle_from_lists_spec. now apply HfR, HF.
              intros v [Rt%HT Rf%HF]. destruct (R_func Rt Rf).
      }
      - unfold continuous. cbn.
        intros R x z [LT [LF [H1 [H2 H3]]]].
        exists (LT ++ LF). split.
        + intros y [i%H1|i%H2]%in_app_iff; eexists; eauto.
        + intros R' HR'. exists LT, LF. repeat split.
          * intros y i. apply HR'. 2: now apply H1. apply in_app_iff. now left.
          * intros y i. apply HR'. 2: now apply H2. apply in_app_iff. now right.
          * apply H3.
    } reflexivity.
  Qed.

  Lemma core_to_om_True {A X}:
    forall C, continuous_f C ->
    { M : oracle_machine A bool X True | M.(oracle_fun_part) = C }.
  Proof.
    intros C cont.
    unshelve eexists. {
      eapply mk𝕄True with 
        (r := fun R x => exists L, (forall y, In y L -> exists b, R y b) /\ (forall f, (forall y b, In y L -> R y b -> f y =! b) -> C f x =! I))
        (r' := C).
      - intros r R H x. unfold pcomputes in H. split.
        + intros iT. destruct (cont r x I iT) as [L [Hl Hl']].
          exists L. setoid_rewrite <- H. split;[apply Hl|]. intros f l. eapply (Hl' f l).
        + intros [L [Hl Hl']]. specialize (Hl' r). setoid_rewrite <- H in Hl'. now apply Hl'.
      - intros R x [L [Hl Hl']].
        exists L. split;[apply Hl|]. intros R'. intros HR'.
        exists L. split.
        + intros y i.
          destruct (Hl y i) as [b Hb]. exists b. now apply HR'.
        + intros f H'. apply Hl'. intros y b i HR.
          apply (H' _ _ i). now apply HR'.
    } reflexivity.
  Qed.

End CoreDeterminacy.

(** ** Comparison to Forster-Kirst *)
Section compare_Forster_Kirst.

  Hypothesis Fext : forall X Y (f g : X -> Y), (forall x, f x = g x) -> f = g.
  Hypothesis Pext : forall P Q : Prop, P <-> Q -> P = Q.

  Fact PI : forall P : Prop, forall H1 H2 : P, H1 = H2.
  Proof.
    intros P H1 H2.
    assert (P <-> True) as -> % Pext by firstorder.
    now destruct H1, H2.
  Qed.

  Lemma FunRel_ext {X Y} (R1 R2 : FunRel X Y) :
    (forall x y, R1 x y <-> R2 x y) -> R1 = R2.
  Proof.
    destruct R1 as [R1 H1], R2 as [R2 H2].
    cbn. intros H.
    - assert (R1 = R2) as ->. {
        eapply Fext. intros x. eapply Fext. intros y.
        eapply Pext, H. }
      f_equal. eapply PI.
  Qed.

  Context {Part : partiality}.
  
  Record Turing_red X Y :=
  {
  red_fun_relT :> FunRel Y bool -> FunRel X bool ;
  red_fun_partT : (Y ↛ bool) -> (X ↛ bool) ;
  red_factorsT : (forall f R, pcomputes f (the_rel R) -> pcomputes (red_fun_partT f) (red_fun_relT R)) ;
  fun_rel_contT : forall (R : FunRel Y bool) x, ~~ exists L, forall R' : FunRel Y bool, (forall y b, In y L -> R y b -> R' y b) -> forall b, red_fun_relT R x b -> red_fun_relT R' x b ;
  fun_rel_monoT : forall (R R' : FunRel Y bool), (forall x b, R x b -> R' x b) -> forall x b, red_fun_relT R x b -> red_fun_relT R' x b ;
  }.

Definition red_Turing_FK {X Y} (p : X -> Prop) (q : Y -> Prop) :=
  exists r : Turing_red X Y, char_rel p = r (char_rel q). 

Notation "P ⪯ꜰᴋ Q" := (red_Turing_FK P Q) (at level 50).

  Fact cont_impl_ForsterKirst {W X Y Z : Type} (F : FunRel Y W -> FunRel X Z) :
    continuous F -> forall (R : FunRel Y W) x, ~~ exists L, forall R' : FunRel Y W, (forall y b, In y L -> R y b -> R' y b) -> forall b, F R x b -> F R' x b.
  Proof.
    unfold continuous. intros H R x.
    assert (~~((exists b, F R x b) \/ ~(exists b, F R x b))) as LEMb by firstorder.
    intros nnE. apply LEMb. intros [[b Fb] | nFb].
    - specialize (H R x b Fb) as [L Hl].
      apply nnE. exists L. intros R' HRR' b' Hb'.
      assert (b = b') as ->. { eapply (F R); eauto. }
      now apply Hl.
    - apply nnE. exists []. intros ? ? b' Hb'. contradict nFb. now exists b'.
  Qed.

  Definition LEM := forall p, p \/ ~p.

  Fact cont_ForsterKirst_impl {W X Y Z} (F : FunRel Y W -> FunRel X Z) :
    LEM -> (forall (R : FunRel Y W) x, ~~ exists L, forall R' : FunRel Y W, (forall y b, In y L -> R y b -> R' y b) -> forall b, F R x b -> F R' x b)
    -> continuous F.
  Proof.
    unfold continuous, LEM. intros LEM H R x b Hb.
    assert (forall p, ~~p -> p) as DN. { intros p nnp. now destruct (LEM p). }
    specialize (H R x). apply DN in H. destruct H as [L Hl].
    assert (exists L', (forall y, In y L' -> exists b, R y b) /\ (forall y, In y L -> In y L' \/ forall b, ~R y b)) as [L' [Hl'1 Hl'2]]. {
      clear Hl x b Hb. induction L as [|y L IHL].
      - now exists [].
      - destruct IHL as [L' [HL1 HL2]].
        destruct (LEM (exists b, R y b)) as [E | nE].
        + exists (y::L'). split; intros y'.
          * intros [->|]; [apply E|now apply HL1].
          * intros [->|i]; [now left;left|].
            destruct (HL2 y' i); [now left;right|now right].
        + exists L'. split;[apply HL1|].
          intros y' [->|i]; [right; firstorder|].
          destruct (HL2 y' i); [now left|now right].
    }
    exists L'. split.
    - apply Hl'1.
    - intros R' HRR'.
      apply Hl. 2: apply Hb.
      intros y b' i Hb'. destruct (Hl'2 y i); firstorder.
  Qed.

  Lemma redT_impl_ForsterKirst {X Y} (P : X -> Prop) (Q : Y -> Prop) :
    P ⪯ᴛ Q -> P ⪯ꜰᴋ Q.
  Proof.
    intros [om H].
    unshelve eexists. {
      unshelve econstructor.
      - apply om.
      - apply om.
      - apply om.
      - apply cont_impl_ForsterKirst, om.
      - apply cont_is_mon_and_comp, om.
    } apply FunRel_ext, H.
  Qed.

  Lemma ForsterKirst_impl_redT {X Y} (P : X -> Prop) (Q : Y -> Prop) :
    LEM -> P ⪯ꜰᴋ Q -> P ⪯ᴛ Q.
  Proof.
    intros LEM [om H].
    unshelve eexists. {
      unshelve econstructor.
      - apply om.
      - apply om.
      - apply om.
      - apply (cont_ForsterKirst_impl LEM), om.
    } now rewrite H.
  Qed.

  Lemma finite_agreeing_function (R : FunRel nat bool) :
    forall L, ~~exists f, forall y b, (In y L -> f y =! b <-> R y b) /\ (f y =! b -> R y b). 
  Proof.
    induction L as [|n ns].
    - intros nnE. apply nnE. exists (fun _ => undef). intros y b. split; [easy| intros []%undef_hasvalue].
    - enough (R n true \/ ~R n true -> R n false \/ ~R n false
    -> (exists f : nat ↛ bool, forall (y : nat) (b : bool), (In y ns -> f y =! b <-> R y b) /\ (f y =! b -> R y b))
    -> (exists f : nat ↛ bool, forall (y : nat) (b : bool), (In y (n :: ns) -> f y =! b <-> R y b) /\ (f y =! b -> R y b))) by firstorder.
    intros [T | nT] [F | nF] [f Hf].
    + specialize (@the_func_proof _ _ R _ _ _ T F) as [=].
    + exists (fun y => if PeanoNat.Nat.eqb y n then ret true else f y). intros y b.
      destruct (PeanoNat.Nat.eqb y n) eqn:eq.
      * rewrite (EqNat.beq_nat_true _ _ eq). split.
        -- intros _. rewrite <- ret_hasvalue_iff. now destruct b.
        -- rewrite <- ret_hasvalue_iff. now destruct b.
      * specialize (EqNat.beq_nat_false _ _ eq) as neq. split.
        -- intros [->|i]; [contradiction|]. now apply Hf.
        -- apply Hf.
    + exists (fun y => if PeanoNat.Nat.eqb y n then ret false else f y). intros y b.
      destruct (PeanoNat.Nat.eqb y n) eqn:eq.
      * rewrite (EqNat.beq_nat_true _ _ eq). split.
        -- intros _. rewrite <- ret_hasvalue_iff. now destruct b.
        -- rewrite <- ret_hasvalue_iff. now destruct b.
      * specialize (EqNat.beq_nat_false _ _ eq) as neq. split.
        -- intros [->|i]; [contradiction|]. now apply Hf.
        -- apply Hf.
    + exists (fun y => if PeanoNat.Nat.eqb y n then undef else f y). intros y b.
      destruct (PeanoNat.Nat.eqb y n) eqn:eq.
      * rewrite (EqNat.beq_nat_true _ _ eq). split.
        -- intros _. split; [intros []%undef_hasvalue|]. now destruct b.
        -- intros []%undef_hasvalue.
      * specialize (EqNat.beq_nat_false _ _ eq) as neq. split.
        -- intros [->|i]; [contradiction|]. now apply Hf.
        -- apply Hf.
  Qed.

  Lemma eq_core_ForsterKirst :
  forall (F1 F2 : Turing_red nat nat),
    (forall f x z, F1.(red_fun_partT) f x =! z <-> F2.(red_fun_partT) f x =! z) -> forall R x b, ~F1 R x b -> ~F2 R x b.
  Proof.
    intros [r1 r'1 Hr1 c1' m1] [r2 r'2 Hr2 c2 m2]. cbn in *.
    unfold continuous, monotonic in *.
    intros eq R x b nH1 H2.
    apply (c1' R x). intros [L1 c1].
    apply (c2 R x). clear c2. intros [L2 c2].
    apply (@finite_agreeing_function R L2). intros [f Hf].
    specialize (c2 (@Build_FunRel _ _ (fun y b => f y =! b) ltac:(intros ?; apply hasvalue_det)) ltac:(apply Hf) b H2) as H2'.
    
    unfold pcomputes in *.
    apply (Hr2 f) in H2'. 2: now intros.
    setoid_rewrite eq in Hr1.
    eapply (Hr1 f {|
    the_rel := fun (y : nat) (b : bool) => f y =! b;
    the_func_proof := fun x0 : nat => hasvalue_det (x:=f x0)|}) in H2'. 2: firstorder.
    apply nH1. eapply m1. 2: apply H2'.
    intros y b'. cbn.
    apply Hf.
  Qed.

End compare_Forster_Kirst.
