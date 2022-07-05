From stdpp Require Import list.

From SyntheticComputability Require Import reductions ReducibilityFacts EnumerabilityFacts Synthetic.Definitions DecidabilityFacts truthtables principles Dec.
Require Import SyntheticComputability.Shared.partial.
Require Import Setoid Morphisms.

From SyntheticComputability Require Import Pigeonhole.

Axiom FunExt : forall (X : Type) (Y : X -> Type) (f g : forall x : X, Y x), (forall x, f x = g x) -> f = g.
Axiom PropExt : forall P1 P2 : Prop, P1 <-> P2 -> P1 = P2.
Fact PropExt' : forall P1 P2 : Prop, P1 <-> P2 <-> P1 = P2.
Proof.
  split. eapply PropExt. now intros ->.
Qed. 
Fact PI : forall P : Prop, forall H1 H2 : P, H1 = H2.
Proof.
  intros P H1 H2.
  assert (P <-> True) as -> % PropExt by firstorder.
  now destruct H1, H2.
Qed.

Fact PredExt : forall X : Type, forall p q : X -> Prop, (forall x, p x <-> q x) -> p = q.
Proof.
  intros. eapply FunExt. intros. now eapply PropExt.
Qed.

(** * Propositional truth table reductions  *)

Definition truthtable {X} (r : X -> list Prop -> Prop) :=
  exists r' : X -> list bool -> bool, forall x, forall l : list bool, r x (map (eq true) l) <-> r' x l = true.

Definition red_tt' {X} {Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists qs : X -> list Y, exists r : X -> list Prop -> Prop,
      truthtable r /\ forall x, P x <-> r x (map Q (qs x)).
Notation "P ⪯ₜₜ' Q" := (red_tt' P Q) (at level 50).

Lemma red_tt_incl {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₜₜ' q -> p ⪯ₜₜ q.
Proof.
  intros (qus & tb & (tb' & H') & H).
  exists (fun x => existT (qus x) (mk_tt (tb' x) (length (qus x)))).
  intros x L HL; cbn in *.
  red. rewrite H.
  rewrite eval_tt_mk_tt'.
  2:{ eapply Forall2_length in HL. now rewrite HL, map_length. }
  rewrite <- H'. eapply PropExt'.
  f_equal. induction HL; cbn in *; f_equal;
  try eapply PropExt; firstorder.
Qed.

Lemma list_reflects L : ~~ exists l, Forall2 reflects l L.
Proof.
  induction L as [ | P L].
  - cprove exists nil. econstructor.
  - cunwrap. destruct IHL as (l & IH).
    ccase P as [H | H].
    + cprove exists (true :: l). econstructor; firstorder.
    + cprove exists (false :: l). econstructor; firstorder.
Qed.

Lemma red_tt_incl' {X Y} (p : X -> Prop) (q : Y -> Prop) :
  stable p -> p ⪯ₜₜ q -> p ⪯ₜₜ' q.
Proof.
  intros Hsp (f & Hf).
  exists (fun x => projT1 (f x)).
  exists (fun x l => ~~ ext_eval (projT2 (f x)) l).
  split.
  exists (fun x l => eval_tt (projT2 (f x)) l).
  - intros x l.
    rewrite truthtable_extension. clear. destruct (eval_tt); firstorder.
  - intros x. red in Hf.
    enough (~~ (p x <-> ext_eval (projT2 (f x)) (map q (projT1 (f x))))). {
      split.
      + intros. cunwrap. now cprove eapply H.
      + intros. eapply Hsp. firstorder.
    }
    intros HG.
    eapply (list_reflects (map q (projT1 (f x)))).
    intros (L & HL). apply HG.
    specialize (Hf _ _ HL).  red in Hf. rewrite Hf.
    rewrite <- truthtable_extension.
    eapply PropExt'. f_equal.
    clear - HL. revert HL.
    generalize (projT1 (f x)).
    induction 1; cbn; intros; f_equal.
    eapply PropExt. firstorder. firstorder.
Qed.

Instance red_tt_reflexive {X} : Reflexive (@red_tt' X X).
Proof.
  intros p.
  exists (fun x => [x]). exists (fun x L => match L with [P] => P | _ => True end).
  split. exists (fun x L => match L with [b] => b | _ => true end).
  - intros _ [ | ? []]; cbn; firstorder.
  - reflexivity.
Qed.

Lemma take_map:
  ∀ X Y (l : list X) (P : X → Y) (n : nat),
    take n (map P l) = map P (take n l).
Proof.
  intros.
  induction n in l |- *; destruct l; cbn; congruence.
Qed.

Lemma drop_map:
  ∀ X Y (l : list X) (P : X → Y) (n : nat),
    drop n (map P l) = map P (drop n l).
Proof.
  intros.
  induction n in l |- *; destruct l; cbn; congruence.
Qed.

Lemma red_tt_transitive' {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ₜₜ' q -> q ⪯ₜₜ' r -> p ⪯ₜₜ' r.
Proof.
  intros (qus1 & etb1 & (tb1 & Htb1) & H1) (qus2 & etb2 & (tb2 & Htb2) & H2).
  exists (fun x => flat_map qus2 (qus1 x)).
  exists (fun x L => etb1 x (((fix rec L1 L2 :=
                             match L1 with
                             | [] => []
                             | y :: L1  => let l := (length (qus2 y)) in (etb2 y) (take l L2) :: rec L1 (skipn l L2)
                           end) (qus1 x) L))). split.
  exists (fun x L => (tb1 x) (((fix rec L1 L2 :=
                         match L1 with
                         | [] => []
                         | y :: L1  => let l := (length (qus2 y)) in (tb2 y) (take l L2) :: rec L1 (skipn l L2)
                         end) (qus1 x) L))).
  - intros x l.
    rewrite <- Htb1. eapply PropExt'. f_equal.
    induction (qus1 x) in l |- *.
    + reflexivity.
    + cbn. f_equal.
      * eapply PropExt.
        assert (true = tb2 a (take (length (qus2 a)) l) <->
                tb2 a (take (length (qus2 a)) l) = true) as -> by firstorder.
        rewrite <- Htb2.
        eapply PropExt'. f_equal. clear.
        eapply take_map.
      * rewrite drop_map, IHl0. f_equal.
  - intros x. rewrite H1. eapply PropExt'. f_equal.
    generalize (qus1 x).
    induction l.
    + reflexivity.
    + cbn. f_equal.
      * eapply PropExt. rewrite H2. eapply PropExt'. f_equal.
        now rewrite map_app, <- (map_length r (qus2 a)), take_app.
      * rewrite IHl. f_equal.
        now rewrite map_app, <- (map_length r (qus2 a)), drop_app.
Qed.

Lemma red_tt_transports' {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₜₜ' q -> decidable q -> decidable p.
Proof.
  intros (qus & tb & (f & Hf) & Htb) [d Hd].
  exists (fun x => f x (map d (qus x))).
  intros x. red. rewrite Htb. rewrite <- Hf.
  rewrite map_map. erewrite map_ext. reflexivity.
  intros. cbn. eapply PropExt. firstorder.
Qed.

Lemma red_mo_tt' {X Y} (p : X -> Prop) (q : Y -> Prop) : p ⪯ₘ q -> p ⪯ₜₜ' q.
Proof.
  intros [f Hf].
  exists (fun x => [f x]).
  exists (fun x L => if L is [P] then P else True). split.
  exists (fun x L => if L is [b] then b else true).
  - intros _ [ | ? []]; cbn; clear; firstorder.
  - cbn. eapply Hf.
Qed.

Lemma red_tt_complement' {X} {p : X -> Prop} : compl p ⪯ₜₜ' p. 
Proof.
  exists (fun x => [x]).
  exists (fun x L => if L is [P] then ~ P else True). split.
  exists (fun x L => if L is [b] then negb b else true).
  - intros _ [ | [] []]; cbn; clear; firstorder.
  - cbn. reflexivity.
Qed.

Lemma red_tt_not_m' :
  (fun _ : unit => True) ⪯ₜₜ' (fun _ : unit => False) /\
  ~ (fun _ : unit => True) ⪯ₘ (fun _ : unit => False).
Proof.
  split.
  - exists (fun _ => []).
    exists (fun _ _ => True). split.
    exists (fun _ _ => true). firstorder. firstorder.
  - intros [f Hf]. now eapply (Hf tt). 
Qed.

Section upper_semi_lattice.

  Context {X Y : Prop}.
  Variables (p : X -> Prop) (q : Y -> Prop).

  Lemma red_tt_join_p' :
    p ⪯ₜₜ' join p q.
  Proof.
    exists (fun x => [inl x]).
    exists (fun x L => if L is [P] then P else True). split.
    exists (fun x L => if L is [P] then P else true).
    - intros ? [ | [] []]; cbn; clear; firstorder.
    - firstorder.
  Qed.

  Lemma red_tt_join_q' :
    q ⪯ₜₜ' join p q.
  Proof.
    exists (fun x => [inr x]).
    exists (fun x L => if L is [P] then P else True). split.
    exists (fun x L => if L is [P] then P else true).
    - intros ? [ | [] []]; cbn; clear; firstorder.
    - firstorder.
  Qed.

  Lemma red_tt_join_least' {Z} (r : Z -> Prop) :
    p ⪯ₜₜ' r -> q ⪯ₜₜ' r -> join p q ⪯ₜₜ' r.
  Proof.
    intros (qus & tb & (f & Hf) & Htb) (qus' & tb' & (f' & Hf') & Htb').
    exists (fun z => match z with inl x => qus x | inr y => qus' y end).
    exists (fun z L => match z with inl x => tb x L | inr y => tb' y L end). split.
    exists (fun z L => match z with inl x => f x L | inr y => f' y L end).
    - intros []; firstorder.
    - intros []; firstorder.
  Qed.

End upper_semi_lattice.

Lemma red_tt_decidable' {X Y} {p : X -> Prop} {q : Y -> Prop} :
  decidable p -> p ⪯ₜₜ' q.
Proof.
  intros [f H].
  exists (fun _ => []).
  exists (fun x _ => p x). split.
  exists (fun x _ => f x).
  - firstorder.
  - firstorder.
Qed.

Record TT X :=
  {
  the_qus : list X ;
  the_tb  : list bool -> bool ;
  the_ext : list Prop -> Prop ;
  the_cond : (∀ (x : X) (l : list bool), the_ext (map (eq true) l) ↔ the_tb l = true)
  }.

Definition tt_conds' {X} (p : X -> Prop) :=
  fun tt : TT X => the_ext _ tt (map p (the_qus _ tt)).
Notation "q 'ᵗᵗ''" := (tt_conds' q) (at level 10).

Lemma tt_char_1' {X} {p : X -> Prop} :
  p ⪯₁ p ᵗᵗ'.
Proof.
  unshelve eexists (fun x => Build_TT _ [x] (fun L => if L is [b] then b else false) (fun L => if L is [b] then b else False) _).
  2: split.
  - abstract (destruct l as [ | [] []]; firstorder).
  - firstorder congruence.
  - intros x. cbn. reflexivity.
Qed.

Lemma p_tt_conds' {X} {p : X -> Prop} :
  p ⪯₁ tt_conds' p.
Proof.
  unshelve eexists (fun x => Build_TT _ [x] (fun L => if L is [b] then b else true) (fun L => if L is [b] then b else True) _). 2:split.
  - abstract (destruct l as [ | [] []]; firstorder).
  - firstorder congruence.
  - intros x. cbn. reflexivity.
Qed.

Lemma conds_tt_p' {X} {p : X -> Prop} {x0 : X} :
  tt_conds' p ⪯ₜₜ' p.
Proof.
  exists (fun x => the_qus _ x).
  exists (fun x => the_ext _ x). split.
  exists (fun x => the_tb _ x).
  - intros []; cbn. eauto.
  - intros []; cbn. reflexivity.
Qed.

Lemma tt_make_inj' {X} {Y} (q : Y -> Prop) (p : X -> Prop) (g : X -> Y) :
  Inj (=) (=) g ->
  p ⪯ₜₜ' q -> p ⪯₁ tt_conds' q.
Proof.
  intros Hg (qus & tb & (f & Hf) & Htb).
  unshelve eexists (fun x => Build_TT _ (g x :: qus x) (fun l => if l is _ :: l then f x l else false) (fun l => if l is _ :: l then tb x l else False) _).
  - abstract (intros ? [ | [] []]; firstorder).
  - split.
    + intros x y. intros [=].
      now eapply Hg.
    + intros x. cbn. eapply Htb.
Qed.

Lemma tt_conds_1' {X} {p : X -> Prop} {Y} {q : Y -> Prop} {x0 : X} (g : Y -> X) :
  Inj (=) (=) g ->
  q ⪯ₜₜ' p -> q ⪯₁ tt_conds' p.
Proof.
  intros Hg H1. 
  eapply tt_make_inj' in H1. 2: exact Hg.
  eapply red_1_transitive. exact H1.
  exists (fun x => x). split. firstorder.
  intros [qus tb]; reflexivity.
Qed.

Lemma redtt_char_as_redo' {X} {p : X -> Prop} {Y} {q : Y -> Prop} {x0 : X} {y0 : Y} (g : TT X → Y) :
  Inj (=) (=) g ->
  p ⪯ₜₜ' q <-> tt_conds' p ⪯₁ tt_conds' q.
Proof.
  intros Hg.
  split.
  - intros H.
    eapply (tt_conds_1' (x0 := y0)). exact Hg.
    apply (red_tt_transitive' p); try eassumption.
    eapply (conds_tt_p' (x0 := x0)).
  - intros H.
    apply (red_tt_transitive' (tt_conds' p)).
    now eapply red_mo_tt', red_oo_mm, p_tt_conds'.
    apply (red_tt_transitive' (tt_conds' q)). now eapply red_mo_tt', red_oo_mm.
    eapply (conds_tt_p' (x0 := y0)).
Qed.

(** * Bounded Turing reductions *)

Context {Part : partiality}.

Notation "P ⇉ Q" := ((P -> Q) /\ (~ P -> ~ Q)) (at level 70).

Lemma double_impl {P Q} :
  Q <-> P -> P ⇉ Q.
Proof.
  firstorder.
Qed.

Record bTuring_red X Y :=
  {
  red_fun_rel :> FunRel Y bool -> FunRel X bool ;
  red_fun_part :> (Y ↛ bool) -> (X ↛ bool) ;
  part_cont : X -> list Y ;
  red_factors : (forall f R, pcomputes f (the_rel R) -> pcomputes (red_fun_part f) (red_fun_rel R)) ;
  fun_rel_cont : forall x, forall R R' : FunRel Y bool, (forall y, In y (part_cont x) -> forall b, R y b -> R' y b) -> forall b, red_fun_rel R x b -> red_fun_rel R' x b ;
  }.

Definition char_rel {X} (p : X -> Prop) : FunRel X bool.
  exists (fun x b => if (b : bool) then p x else ~ p x).
  abstract (intros ? [] [] ? ?; firstorder congruence).
Defined.

Definition red_bTuring {X Y} (p : X -> Prop) (q : Y -> Prop) :=
  exists r : bTuring_red X Y, char_rel p = r (char_rel q). 

Program Definition rel_of_pfun {X Y} (f : X ↛ Y) : FunRel X Y :=
  @Build_FunRel _ _ (fun x y => f x =! y) _.
Next Obligation.
  intros x y1 y2 H1 H2. eapply hasvalue_det; eauto.
Qed.

Lemma rel_of_pfun_pcomputes  {X Y} (f : X ↛ Y) :
  pcomputes f (rel_of_pfun f).
Proof.
  intros x y. firstorder.
Qed.

Lemma FunRel_ext {X Y} (R1 R2 : FunRel X Y) :
  (forall x y, R1 x y <-> R2 x y) -> R1 = R2.
Proof.
  destruct R1 as [R1 H1], R2 as [R2 H2].
  cbn. intros H.
  - assert (R1 = R2) as ->. {
      eapply FunExt. intros x. eapply FunExt. intros y.
      eapply PropExt, H. }
    f_equal. eapply PI.
Qed.

Lemma FunRel_ext' {X Y} (R1 R2 : FunRel X Y) :
  R1 = R2 -> (forall x y, R1 x y <-> R2 x y).
Proof.
  now intros ->.
Qed.

Lemma mkbTuring {X Y} {p : X -> Prop} {q : Y -> Prop} (r : FunRel Y bool -> FunRel X bool) (r' : (Y ↛ bool) -> (X ↛ bool)) (C : X -> list Y) :
  (forall f R, pcomputes f (the_rel R) -> pcomputes (r' f) (r R)) ->
  (forall x, forall R R' : FunRel Y bool, (forall y, In y (C x) -> forall b, R y b -> R' y b) -> forall b, r R x b -> r R' x b) ->
  char_rel p = r (char_rel q) ->
  red_bTuring p q.
Proof.
  intros Hr' Hcont Hpq.
  unshelve eexists.
  eapply Build_bTuring_red with (red_fun_rel := r) (red_fun_part := r') (part_cont := C); eauto.
  cbn; eauto.
Qed.

Definition red_totalbTuring {X Y} (p : X -> Prop) (q : Y -> Prop) :=
  exists r : bTuring_red X Y,   (forall R : FunRel Y bool, total R -> total (r R)) /\ char_rel p = r (char_rel q).

Lemma mktotalbTuring {X Y} {p : X -> Prop} {q : Y -> Prop} (r : FunRel Y bool -> FunRel X bool) (r' : (Y ↛ bool) -> (X ↛ bool)) (C : X -> list Y) :
  (forall f R, pcomputes f (the_rel R) -> pcomputes (r' f) (r R)) ->
  (forall x, forall R R' : FunRel Y bool, (forall y, In y (C x) -> forall b, R y b -> R' y b) -> forall b, r R x b -> r R' x b) ->
  char_rel p = r (char_rel q) ->
  (forall R : FunRel Y bool, total R -> total (r R)) ->
  red_totalbTuring p q.
Proof.
  intros Hr' Hcont Hpq Htot.
  unshelve eexists.
  eapply Build_bTuring_red with (red_fun_rel := r) (red_fun_part := r') (part_cont := C); eauto.
  split; cbn; eauto.
Qed.
Notation "P ⪯ᴛb Q" := (red_bTuring P Q) (at level 50).
Notation "P ⪯ₜᴛb Q" := (red_totalbTuring P Q) (at level 50).

Lemma total_bounded_Turing_bounded_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₜᴛb q ->  p ⪯ᴛb q.
Proof.
  intros []. exists x. firstorder.
Qed.

Lemma bTuring_refl {X} (p : X -> Prop) :
  p ⪯ᴛb p.
Proof.
  eapply (mkbTuring (fun R => R) (fun f => f) (fun x => [x])); cbn; eauto.
Qed.

Lemma bTuring_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ᴛb q -> q ⪯ᴛb r -> p ⪯ᴛb r.
Proof.
  intros ([r1 r1' C1 Hr1' HC1] & H1) ([r2 r2' C2 Hr2' HC2] & H2).
  eapply (mkbTuring (fun R => r1 (r2 R)) (fun f x => r1' (r2' f) x) (fun x => flat_map C2 (C1 x))) ; eauto.
  - intros. eapply HC1. intros. eapply HC2. intros. eapply H. eapply in_flat_map. all: eauto. 
  - cbn in *. congruence.
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
  destruct (partial_total _ _ _ Hter) as [g Hg].
  exists g. intros x. red. rewrite <- He. specialize (Hg x).
  destruct (g x); firstorder. eapply hasvalue_det; eauto.
Qed.

Lemma red_bTuring_decidable : forall X Y (p : X -> Prop) (q : Y -> Prop),
    MP ->
    p ⪯ᴛb q -> decidable q -> decidable p. (* The converse direction is proved below as decidable_bounded_Turing_MP *)
Proof.
  intros X Y p q mp ([r r' C Hr' HC] & H) [f Hf].
  pose proof (Hq := Hr' (fun x => ret (f x)) (char_rel q)).
  - cbn in *.
    eapply (@Proper_decidable X) with (y := fun x => r (char_rel q) x true).
    intros x. now rewrite (FunRel_ext' _ _ H x true).
    unshelve epose proof (Hq _); clear Hq; try rename H0 into Hq.
    + intros x b. rewrite <- ret_hasvalue_iff.
      specialize (Hf x). clear - Hf. destruct b, (f x); firstorder.
    + eapply partial_decidable. 2: intros; eapply Hq.
      intros. eapply (MP_to_MP_partial mp). intros Hx.
      ccase (p x) as [Hp | Hp].
      -- eapply (FunRel_ext' _ _ H x true) in Hp. eapply Hx. eapply Hq in Hp. eexists; eauto.
      -- eapply (FunRel_ext' _ _ H x false) in Hp. eapply Hx. eapply Hq in Hp. eexists; eauto.
Qed.

Lemma reflects_iff (b : bool) P :
  (if b then P else ~ P) <-> reflects b P.
Proof.
  destruct b; firstorder.
Qed.

Lemma total_bounded_Turing_transport {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₜᴛb q -> decidable q -> decidable p.
Proof.
  intros ([r r' C Hr' HC] & [Htot H]) [f Hf].
  pose proof (Hq := Hr' (fun x => ret (f x)) (char_rel q)).
  - cbn in *.
    eapply (@Proper_decidable X) with (y := fun x => r (char_rel q) x true).
    intros x. now rewrite (FunRel_ext' _ _ H x true).
    unshelve epose proof (Hq _); clear Hq; try rename H0 into Hq.
    + intros x b. rewrite <- ret_hasvalue_iff.
      specialize (Hf x). clear - Hf. destruct b, (f x); firstorder.
    + eapply partial_decidable. 2: intros; eapply Hq.
      intros.
      edestruct (Htot (char_rel q)).
      -- intros x0. cbv. setoid_rewrite reflects_iff.
         exists (f x0). eapply Hf.
      -- eapply Hr' in H0.  eexists. eassumption.
         unfold pcomputes. intros.
         rewrite <- ret_hasvalue_iff. cbn.
         rewrite reflects_iff. red in Hf. unfold reflects in *.
         rewrite Hf.
         clear.
         destruct (f x1), y; firstorder congruence.
Qed.

Goal forall X Y (p : X -> Prop) (q : Y -> Prop),
    p ⪯ₘ q -> p ⪯ᴛb q.
Proof.
  intros X Y p q [f H].
  red in H.
  unshelve eapply (mkbTuring (fun R => @Build_FunRel _ _ (fun x b => the_rel R (f x) b) _) (fun g x => g (f x)) (fun x => [f x])).
  - intros ? ? ?; eapply R.
  - intros f_R R HR.
    cbn. firstorder.
  - cbn. eauto.
  - eapply FunRel_ext; cbn. intros x []; firstorder.
Qed.

Lemma Forall2_functional_ext {X Y} (R : X -> Y -> Prop) L L1 L2 :
  functional R ->
  Forall2 R L L1 ->
  Forall2 R L L2 -> L1 = L2.
Proof.
  intros Rfun H0 H1. induction H0 in L2, H1 |- *; inv H1.
  - reflexivity.
  - f_equal; firstorder. 
Qed.

Fixpoint part_map {X Y} (f : X ↛ Y) (l : list X) : part (list Y) :=
  match l with
  | nil => ret nil
  | x :: l => bind (f x) (fun y => bind (part_map f l) (fun l' => ret (y :: l')))
  end.

Lemma pcomputes_part_map:
  ∀ (Y : Type) (g : Y → part bool) (R : FunRel Y bool) (L : list bool) (l : list Y),
    pcomputes g R → part_map g l =! L <-> Forall2 R l L.
Proof.
  intros Y g R L l Hg. induction L in l |- *; cbn; split.
  - destruct l; cbn. econstructor.
    intros (? & ? & (? & ? & ? % ret_hasvalue_inv) % bind_hasvalue) % bind_hasvalue.
    congruence.
  - intros H0. inv H0.  eapply ret_hasvalue.
  - destruct l; cbn. intros ? % ret_hasvalue_inv. congruence.
    intros (? & ? & (? & ? & ? % ret_hasvalue_inv) % bind_hasvalue) % bind_hasvalue.
    inv H1. econstructor. 2: firstorder. now eapply Hg.
  - intros HL. inv HL. cbn. eapply Hg in H2; eauto.
    eapply bind_hasvalue. 
    eexists; split; eauto.
    eapply bind_hasvalue. eexists; split; eauto.
    eapply IHL. eauto. 
    eapply ret_hasvalue.
Qed.

Lemma part_map_total:
  ∀ (Y : Type) (g : Y → part bool) (g' : Y → bool),
    (∀ x : Y, g x =! g' x) → ∀ l : list Y, part_map g l =! map g' l.
Proof.
  intros Y g g' Hg'.
  induction l; cbn.
  - eapply ret_hasvalue.
  - eapply bind_hasvalue. eexists. split. eapply Hg'.
    eapply bind_hasvalue. eexists. split. eassumption. eapply ret_hasvalue.
Qed.

Lemma Forall2_total {X} {Y} (R : X -> Y -> Prop) :
  total R -> total (Forall2 R).
Proof.
  intros HP L2. induction L2.
  - exists nil. econstructor.
  - destruct (HP a) as [b H].
    destruct IHL2 as [L2' IH].
    exists (b :: L2'). econstructor. eauto. eauto.
Qed.


Lemma MP_hasvalue_stable {X} (x : part X) a :
  eq_dec X ->
  MP -> ~~ x =! a -> x =! a.
Proof.
  intros HX mp Hx.
  assert (x =! a <-> exists n, (if seval x n is Some a' then if Dec (a = a') then true else false else false) = true). {
    rewrite seval_hasvalue. split; intros (n & H); exists n. rewrite H. clear. destruct Dec; firstorder.
    destruct seval. destruct Dec. congruence. firstorder. firstorder. congruence.
  }
  rewrite H in *. now apply mp. 
Qed.

Lemma red_tt_to_red_totalbTuring : forall X Y (p : X -> Prop) (q : Y -> Prop),
    MP -> stable p ->
    red_tt' p q -> p ⪯ₜᴛb q.
Proof.
  intros X Y p q mp' Hsp (qus & tb & (f & Hf) & Htb).
  pose proof (mp := MP_to_MP_partial mp').
  unshelve eapply (mktotalbTuring 
    (fun R : FunRel Y bool =>
       @Build_FunRel _ _ (fun x b => 
                           exists L : list Prop, List.Forall2 (fun x (p : Prop) =>
                                                         (p -> the_rel R x true) /\ ( ~p -> the_rel R x false)) (qus x) L /\
                                         (tb x L <-> b = true)) _)
    (fun g x => bind (part_map g (qus x)) (fun L => ret (f x L)))
    (fun x => qus x)).
  - intros x b1 b2 [L1 [H1 H1']] [L2 [H2 H2']].
    cstart.
    enough (~~ (b1 = true <-> b2 = true)). { cunwrap. now cprove eapply Bool.eq_true_iff_eq. }
    rewrite <- H1', <- H2'. clear H1' H2'. 
    enough (~~ L1 = L2). { cunwrap. subst. firstorder. }
    revert L1 L2 H1 H2.
    induction (qus x); intros L1 L2 H1 H2; inv H1; inv H2.
    + firstorder.
    + assert (~~ (y = y0)). {
        ccase y as [Hy | Hy]; ccase y0 as [Hy0 | Hy0].
        + now cprove eapply PropExt.
        + eapply H3 in Hy. eapply H1 in Hy0. enough (true = false) by congruence. eapply R; eauto.
        + eapply H3 in Hy. eapply H1 in Hy0. enough (true = false) by congruence. eapply R; eauto.
        + now cprove eapply PropExt.
      }
      assert (~~ (l' = l'0)) by (eapply IHl; eauto).
      cunwrap. now subst.
  - intros g R Hg x. intros b. split; cbn.
    + intros (L & ? % (pcomputes_part_map _ _ _ _ _ Hg) & <- % ret_hasvalue_inv) % bind_hasvalue.
      exists (map (eq true) L). split.
      * eapply Forall2_fmap_r, Forall2_impl; eauto.
        cbn. clear - H. intros ? [] ?; firstorder. (* enough (true = false) by congruence. all: eapply R; eauto. *)
      * eapply Hf.
    + intros (L & HL1 & HL2).
      apply MP_hasvalue_stable; eauto. intros G.
      apply (list_reflects L). intros (l & Hl).
      ccase (part_map g (qus x) =! l) as [Hgl | Hgl].
      * eapply G. eapply bind_hasvalue. eexists; split; eauto.
        eapply ret_hasvalue'.
        eapply Bool.eq_true_iff_eq.
        rewrite <- Hf, <- HL2.
        eapply PropExt'. f_equal.
        clear - Hl.
        induction Hl; cbn; f_equal; firstorder.
        eapply PropExt. firstorder. 
      * rewrite pcomputes_part_map in Hgl; eauto.
        apply Hgl. clear - HL1 Hl.
        eapply Forall2_flip in Hl.
        eapply Forall2_transitive; eauto.
        cbn. unfold reflects. intros.
        destruct z; try now firstorder.
  - cbn. intros x R R' Hcont b (L & H1 & H2). exists L; split; eauto.
    revert Hcont. clear H2.
    induction H1.
    * econstructor.
    * intros. econstructor; eauto. destruct H as [HH1 HH2]. split; intros; eapply Hcont; eauto.
  - cbn. eapply FunRel_ext. intros x. cbn.
    intros b. split.
    + rewrite reflects_iff. unfold reflects. rewrite Htb.
      intros H. exists (map q (qus x)).
      split. 2: firstorder.
      eapply Forall2_fmap_r, Forall_Forall2_diag, Forall_forall.
      intros y. cbn. intros. firstorder.
    + intros (L & IL & HL).
      enough (~~ if b then p x else ¬ p x). { destruct b; firstorder. }
      rewrite reflects_iff. unfold reflects. rewrite Htb, <- HL.
      enough (~~ L = map q (qus x)). { cunwrap. subst. firstorder. }
      revert IL. generalize (qus x). clear. intros.
      induction IL; cbn. firstorder.
      cunwrap. subst.
      assert (~~ (y <-> q x)) by firstorder. cunwrap.
      cprove f_equal. eapply PropExt. firstorder.
  - intros R Htot x. cbn.
    eapply Forall2_total in Htot. specialize (Htot (qus x)) as [L HL].
    exists (f x L).
    exists (map (eq true) L). split.
    2:eapply Hf.
    revert HL. generalize (qus x). clear.
    intros l. induction 1; cbn; econstructor; eauto.
    destruct y.
    + split. firstorder. firstorder.
    + split. 2: firstorder congruence. firstorder congruence.
Qed.

Lemma pcomputes_ter {X Y} (R : X -> Y -> Prop) f x :
  pcomputes f R -> ~ ter (f x) -> ~ exists y, R x y.
Proof.
  intros Hf H [y Hy].
  apply Hf in Hy. eauto.
  firstorder.
Qed.

Definition char_rel_fun {X Y} (f : X -> Y) :=
  (@Build_FunRel _ _(fun x b => f x = b) ltac:(firstorder congruence)).

Lemma pcomputes_char_rel_fun:
  ∀ (Y : Type) (f : Y → bool), pcomputes (λ y : Y, ret (f y)) (char_rel_fun f).
Proof.
  intros Y f x y.
  rewrite <- ret_hasvalue_iff. reflexivity.
Qed.

Lemma totalbTuring_function {X Y} (r : bTuring_red X Y) :
  (forall R : FunRel Y bool, total R -> total (r R)) ->
  ∑ F : (Y -> bool) -> (X -> bool),
        (forall x, forall f f', (forall y, In y (part_cont _ _ r x) -> f y = f' y) -> F f x = F f' x) /\
        (forall f x b, r (char_rel_fun f) x b <-> F f x = b).
Proof.
  intros Htot. destruct r as [r r' C Hr' HC]. cbn in *.
  unshelve eexists. 2:split.
  - intros f. destruct (partial_total _ _ (r' (fun y => ret (f y)))) as [g Hg].
    + intros. unshelve edestruct (Htot (char_rel_fun f)) as [b Hb].
      1: exact x.
      1: intros ?; cbn; eauto.
      exists b. eapply Hr'; eauto.
      eapply pcomputes_char_rel_fun.
    + exact g.
  - cbn. intros x f f' Hcont.  destruct (partial_total) as [g Hg].
    destruct partial_total as [g' Hg']. eapply hasvalue_det; eauto.
    eapply Hr'. eapply pcomputes_char_rel_fun.
    eapply HC. 2: eapply Hr'. 3: eapply Hg'.
    2: eapply pcomputes_char_rel_fun. intros.
    eapply Hcont in H. cbn in *. congruence.
  - intros f x b. cbn. destruct (partial_total) as [g Hg].
    specialize (Hg x).
    split.
    + intros H. eapply Hr' in H. eapply hasvalue_det; eauto.
      eapply pcomputes_char_rel_fun.
    + intros <-. eapply Hr'. eapply pcomputes_char_rel_fun. eauto.
Qed.

Lemma totalbTuring_truthtable {X Y} (p : X -> Prop) (q : Y -> Prop) :
  eq_dec Y ->
  p ⪯ₜᴛb q -> p ⪯ₜₜ' q.
Proof.
  intros HY (r & Htot & H).
  destruct (totalbTuring_function r) as [r'' Hr'']; eauto.
  destruct r as [r r' C Hr' HC]; cbn in *.
  eexists C.
  assert (∀ (x : X) (R R' : FunRel Y bool), (∀ y : Y, In y (C x) → R y = R' y) → r R x = r R' x). {
      intros. eapply FunExt. intros b. eapply PropExt. split; eapply HC; intros. now rewrite <- H0. now rewrite H0.
  } clear HC. rename H0 into HC.
  unshelve eexists (fun x L => r (@Build_FunRel _ _ (fun y b => exists i, pos y (C x) = Some i /\ reflects b (nth i L (true = false)))  _ ) x true); eauto.
  2:split.
  + intros y b1 b2 (i1 & H1 & H1') (i2 & H2 & H2').
    eapply Bool.eq_true_iff_eq. red in H1', H2'. rewrite <- H1', <- H2'.
    rewrite H1 in H2; inv H2. rewrite H1' in H2'. inv H2'. reflexivity.
  + cbn. eexists (fun x l => r'' (fun y => if pos y (C x) is Some i then nth i l false else false) x). 
    destruct Hr'' as [H1 H2].
    intros x l.
    rewrite <- H2.
    erewrite HC. reflexivity.
    intros y Hy. cbn. eapply FunExt. intros b. eapply PropExt.
    split.
    * intros (i & -> & H4). red in H4.
      assert (b = true <-> true = b) as E % PropExt. {
        clear. firstorder congruence.
      } rewrite E in H4. clear E.
      rewrite map_nth in H4.
      eapply Bool.eq_true_iff_eq. clear - H4. firstorder. rewrite H. reflexivity. congruence. 
      rewrite <- H0. eauto. congruence. 
    * intros <-. cbn.
      epose proof (el_pos _ _ _ _ Hy) as [n Hn]. rewrite Hn.
      eapply pos_nthe in Hn.
      eapply map_nth_error in Hn.
      eapply nth_error_nth in Hn.
      eexists. split. reflexivity.
      rewrite <- nth_default_eq.
      unfold nth_default.
      destruct nth_error as [b | ] eqn:E.
      -- eapply map_nth_error in E. eapply nth_error_nth in E.
         rewrite E. firstorder.
      -- rewrite map_nth. rewrite <- nth_default_eq.
         unfold nth_default. rewrite E. firstorder.
  + intros x. cbn. specialize (FunRel_ext' _ _ H x true) as ->.
    erewrite HC. reflexivity.
    intros y Hy. cbn.
    eapply FunExt. intros b. eapply PropExt.
    rewrite reflects_iff. split.
    * intros Hr. eapply el_pos in Hy as [i Hi]. exists i. split.
      eauto.
      rewrite <- nth_default_eq. unfold nth_default.
      erewrite map_nth_error. eauto. eapply pos_nthe; eauto. 
    * intros (i & H1 & H2).
      red. red in H2. rewrite <- H2.
      rewrite <- nth_default_eq. unfold nth_default. erewrite map_nth_error. reflexivity.
      eapply pos_nthe; eauto.
      Unshelve. exact bool. exact (fun _ => true). exact true.
Qed.


(** * Turing reductions *)

Record Turing_red X Y :=
  {
  red_fun_relT :> FunRel Y bool -> FunRel X bool ;
  red_fun_partT :> (Y ↛ bool) -> (X ↛ bool) ;
  red_factorsT : (forall f R, pcomputes f (the_rel R) -> pcomputes (red_fun_partT f) (red_fun_relT R)) ;
  fun_rel_contT : forall (R : FunRel Y bool) x, ~~ exists L, forall R' : FunRel Y bool, (forall y b, In y L -> R y b -> R' y b) -> forall b, red_fun_relT R x b -> red_fun_relT R' x b ;
  fun_rel_monoT : forall (R R' : FunRel Y bool), (forall x b, R x b -> R' x b) -> forall x b, red_fun_relT R x b -> red_fun_relT R' x b ;
  }.

Definition continuous {X Y Z1 Z2} (r : FunRel Y Z1 -> FunRel X Z2) :=
  forall (R : FunRel Y Z1) (x : X), ~~ exists L, forall R' : FunRel Y Z1, (forall y b, In y L -> R y b -> R' y b) -> forall b : Z2, r R x b -> r R' x b.

Definition monotonic {X Y Z1 Z2} (r : FunRel Y Z1 -> FunRel X Z2) :=
  forall (R R' : FunRel Y Z1), (forall x b, R x b -> R' x b) -> forall x b, r R x b -> r R' x b.

Program Definition fin_to_rel {X Y} {Heq : eq_dec X} (l : list (X * Y)) :=
  @Build_FunRel _ _ (fun x y => exists i, @pos X Heq x (map fst l) = Some i /\
                                  nth_error (map snd l) i = Some y) _.
Next Obligation.
  intros ? ? ? (i1 & H1 & H2) (i2 & H3 & H4). congruence.
Qed.

Lemma weakly_total_Forall2 {X Y} {R : X -> Y -> Prop} (L : list X) :
  (forall x, In x L -> ~~ exists y, R x y) -> ~~ exists L', Forall2 R L L'.
Proof.
  intros Htot. induction L.
  - cprove exists []. econstructor.
  - unshelve epose proof (IHL _) as IH.
    + intros. eapply Htot. firstorder.
    + specialize (Htot a ltac:(firstorder)).
      cunwrap. destruct IH as [L' IH].
      destruct Htot as [y Hy].
      cprove exists (y :: L'). now econstructor.
Qed.

Lemma pos_map {X Y} (f : X -> Y) x l {d1 : eq_dec X} {d2 : eq_dec Y} :
  Inj (=) (=) f -> @pos _ d2 (f x) (map f l) = @pos _ d1 x l.
Proof.
  intros Hf.
  induction l; cbn.
  - reflexivity.
  - destruct d2 as [-> % Hf | E].
    + destruct d1; try congruence.
    + destruct d1; try congruence.
      now rewrite IHl.
Qed.

Lemma Forall2_Forall {A B} P (l1 : list A) (l2 : list B) :
  Forall2 P l1 l2 → Forall (uncurry P) (zip l1 l2).
Proof. induction 1; constructor; auto. Qed.

Lemma bla {X Y Z1 Z2} (r : FunRel Y Z1 -> FunRel X Z2) {Heq : eq_dec Y} :
  continuous r /\ monotonic r <->
  (forall (R : FunRel Y Z1) (x : X) b, r R x b -> ~~ exists Rfin, (exists L, forall x b, the_rel Rfin x b -> In x L /\ R x b) /\ r Rfin x b) /\
  (forall (R : FunRel Y Z1) (x : X) b, r R x b -> forall R' : FunRel Y Z1, (forall x b, R x b -> R' x b) -> r R' x b).
Proof.
  split.
  intros [Hc Hm].
  - split. 2:{ intros. eapply Hm; eauto. }
    intros R x b H G.
    eapply (Hc R x). intros (L & HL).
    eapply IsFilter_nnex with (l := L) (p := fun x => exists y, R x y).
    intros (L1 & HL1).
    eapply (@weakly_total_Forall2 _ _ R L1).
    + eapply IsFilter_spec in HL1. intros ? ? % HL1. firstorder.
    + intros (L2 & HL2). eapply G.
      unshelve eexists.
      { unshelve econstructor. exact (fun y z => In y L1 /\ R y z). intros ? ? ? [] []. eapply R; eauto. }
      split.
      * exists L1. cbn. firstorder.
      * eapply HL; eauto.
        cbn. firstorder.
        eapply IsFilter_spec in HL1. eapply HL1. firstorder.
  - intros [Hc Hm]. split. 2:{ intros ? ? ? ? ? ?. eapply Hm; eauto. }
    intros R x G. cstart. ccase (exists b, r R x b) as [[b Hx % Hc] | Hx].
    + cunwrap. destruct Hx as (Rfin & (L & H1) & H2). cprove apply G.
      exists L. intros.
      assert (b0 = b) as ->. {
        eapply r. eapply H0. eapply Hm. eauto. firstorder. }
      eapply Hm. exact H2. firstorder.
    + cprove eapply G. exists []. intros. destruct Hx. firstorder.
Qed.

Definition red_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :=
  exists r : Turing_red X Y, char_rel p = r (char_rel q). 

Lemma mkTuring' {X Y} {p : X -> Prop} {q : Y -> Prop} (r : FunRel Y bool -> FunRel X bool) (r' : (Y ↛ bool) -> (X ↛ bool)) (C : X -> list Y) :
  (forall f R, pcomputes f (the_rel R) -> pcomputes (r' f) (r R)) ->
  (forall (R : FunRel Y bool) x, forall R' : FunRel Y bool, (forall y b, In y (C x) -> R y b -> R' y b) -> forall b, r R x b -> r R' x b) ->
  char_rel p = r (char_rel q) ->
  red_Turing p q.
Proof.
  intros Hr' Hcont Hpq.
  unshelve eexists.
  eapply Build_Turing_red with (red_fun_relT := r) (red_fun_partT := r'); eauto.
  cbn; eauto.
Qed.

Lemma mkTuring {X Y} {p : X -> Prop} {q : Y -> Prop} (r : FunRel Y bool -> FunRel X bool) (r' : (Y ↛ bool) -> (X ↛ bool)) :
  (forall f R, pcomputes f (the_rel R) -> pcomputes (r' f) (r R)) ->
  (forall (R : FunRel Y bool) x, ~~ exists L, forall R' : FunRel Y bool, (forall y b, In y L -> R y b -> R' y b) -> forall b, r R x b -> r R' x b) ->
  (forall (R R' : FunRel Y bool), (forall x b, R x b -> R' x b) -> forall x b, r R x b -> r R' x b) ->
  char_rel p = r (char_rel q) ->
  red_Turing p q.
Proof.
  intros Hr' Hcont Hpq.
  unshelve eexists.
  eapply Build_Turing_red with (red_fun_relT := r) (red_fun_partT := r'); eauto.
  cbn; eauto.
Qed.

Definition red_totalTuring {X Y} (p : X -> Prop) (q : Y -> Prop) :=
  exists r : Turing_red X Y,   (forall R : FunRel Y bool, total R -> total (r R)) /\ char_rel p = r (char_rel q).

Lemma mktotalTuring {X Y} {p : X -> Prop} {q : Y -> Prop} (r : FunRel Y bool -> FunRel X bool) (r' : (Y ↛ bool) -> (X ↛ bool)) (C : X -> list Y) :
  (forall f R, pcomputes f (the_rel R) -> pcomputes (r' f) (r R)) ->
  (forall x, forall R R' : FunRel Y bool, (forall y b, In y (C x) -> R y b -> R' y b) -> forall b, r R x b -> r R' x b) ->
  char_rel p = r (char_rel q) ->
  (forall R : FunRel Y bool, total R -> total (r R)) ->
  red_totalTuring p q.
Proof.
  intros Hr' Hcont Hpq Htot.
  unshelve eexists.
  eapply Build_Turing_red with (red_fun_relT := r) (red_fun_partT := r'); eauto.
  split; cbn; eauto.
Qed.

Notation "P ⪯ᴛ Q" := (red_Turing P Q) (at level 50).
Notation "P ⪯ₜᴛ Q" := (red_totalTuring P Q) (at level 50).

Lemma Turing_refl {X} (p : X -> Prop) :
  p ⪯ᴛ p.
Proof.
  eapply (mkTuring' (fun R => R) (fun f => f) (fun x => [x])); cbn; eauto.
Qed.

Lemma weakly_total_Forall2' {X Y} {R : X -> Y -> Prop} (L : list X) :
  (forall x, ~~ exists y, R x y) -> ~~ exists L', Forall2 R L L'.
Proof.
  intros Htot. induction L.
  - cprove exists []. econstructor.
  - specialize (Htot a).
    cunwrap. destruct IHL as [L' IH].
    destruct Htot as [y Hy].
    cprove exists (y :: L'). now econstructor.
Qed.

Lemma Turing_transitive' {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ᴛ q -> q ⪯ᴛ r -> p ⪯ᴛ r.
Proof.
  intros ([r1 r1' Hr1' HC1] & H1) ([r2 r2' Hr2' HC2] & H2).
  eapply (mkTuring (fun R => r1 (r2 R)) (fun f x => r1' (r2' f) x)) ; eauto.
  (* (fun x => flat_map C2 (C1 x)) *)
  - intros R x G. apply (HC1 (r2 R) x). intros [L1 HL1]. cbn in *.
    eapply (@weakly_total_Forall2' _ _ _ L1) in HC2. apply HC2.
    intros [L2 HL2]. apply G. exists (concat L2).
    intros. eapply HL1. 2:eauto. intros y b' Hy. revert b'. pattern y. revert y Hy.
    eapply Forall_forall.
    eapply Forall2_Forall_l. eassumption.
    eapply Forall_forall. intros. eapply H4. 2: eauto.
    intros. eapply H.
    eapply in_concat. eauto. eauto.
  - cbn in *. congruence.
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

Goal forall X Y (p : X -> Prop) (q : Y -> Prop),
    MP ->
    p ⪯ᴛ q -> decidable q -> decidable p.
Proof.
  intros X Y p q mp ([r r' Hr' HC] & H) [f Hf].
  pose proof (Hq := Hr' (fun x => ret (f x)) (char_rel q)).
  - cbn in *.
    eapply (@Proper_decidable X) with (y := fun x => r (char_rel q) x true).
    intros x. now rewrite (FunRel_ext' _ _ H x true).
    unshelve epose proof (Hq _); clear Hq; try rename H0 into Hq.
    + intros x b. rewrite <- ret_hasvalue_iff.
      specialize (Hf x). clear - Hf. destruct b, (f x); firstorder.
    +  eapply pcomputes_decider; eauto.
       intros. eapply (MP_to_MP_partial mp). intros Hx.
       ccase (p x) as [Hp | Hp].
       -- eapply (FunRel_ext' _ _ H x true) in Hp. eapply Hx. eapply Hq in Hp. eexists; eauto.
       -- eapply (FunRel_ext' _ _ H x false) in Hp. eapply Hx. eapply Hq in Hp. eexists; eauto.
Qed.

Lemma red_bTuring_to_red_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ᴛb q -> p ⪯ᴛ q.
Proof.
  intros ([r1 r1' C1 Hr1' HC1] & H1).
  eapply mkTuring'; eauto.
Qed.

Print Assumptions red_bTuring_to_red_Turing.

(** * Bauer's Turing reductions *)

Record oracle (X : Type) : Type :=
  {
  S0 : X -> Prop;
  S1 : X -> Prop;
  H_oracle : forall x, S0 x -> S1 x -> False
  }.
Arguments S0 {_} _.
Arguments S1 {_} _.

Definition maximal {X} (p1 p2 : X -> Prop) :=
  forall x, ~ p1 x -> ~ p2 x -> False.

Program Definition char_oracle {X} (p : X -> Prop) :=
  {| S0 := p ; S1 := compl p ; H_oracle := ltac:(abstract firstorder) |}.

Definition Turing_reduction {X Y} (f : oracle Y -> oracle X) :=
  exists e0' e1',
  (forall e0 e1 o, enumerator e0 (S0 o) -> enumerator e1 (S1 o) ->
             enumerator (e0' e0 e1) (S0 (f o)) /\
             enumerator (e1' e0 e1) (S1 (f o))).

Definition red_TuringBauer {X Y} (p : X -> Prop) (q : Y -> Prop) :=
  exists r, Turing_reduction r /\ char_oracle p = r (char_oracle q).

Notation "P ⪯ʙ Q" := (red_TuringBauer P Q) (at level 50).

Definition bienumerable {X} (p : X -> Prop) :=  enumerable p /\ enumerable (fun x => ~ p x).

Lemma Bauer_refl {X} (p : X -> Prop) :
  p ⪯ʙ p.
Proof.
  exists (fun o => o). firstorder.
  exists (fun e0 e1 => e0). exists (fun e0 e1 => e1).
  firstorder.
Qed.

Lemma Bauer_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ʙ q -> q ⪯ʙ r -> p ⪯ʙ r.
Proof.
  intros [r1 [Hr1 H1]] [r2 [Hr2 H2]].
  exists (fun o => r1 (r2 o)). split. 
  - destruct Hr1 as (e0' & e1' & He1).
    destruct Hr2 as (e0_' & e1_' & He1_).
    eexists. eexists. split.
    + intros. eapply He1; eapply He1_; eauto.
    + intros. eapply He1; eapply He1_; eauto.
  - congruence.
Qed.

Goal forall X Y (p : X -> Prop) (q : Y -> Prop),
    p ⪯ʙ q -> bienumerable q -> bienumerable p.
Proof.
  intros X Y p q (r & (e0' & e1' & T_red) & H) [(e0 & E0) (e1 & E1)].
  destruct (T_red e0 e1 (char_oracle q) ltac:(firstorder) ltac:(firstorder)) as [H1' H2'].
  split.
  - eapply Proper_enumerable with (y := (S0 (r (char_oracle q)))); eauto.
    intros x. now rewrite <- H.
  - eapply Proper_enumerable with (y := (S1 (r (char_oracle q)))); eauto.
    intros x. now rewrite <- H.
Qed.
 
Fact oracle_ext {X} (o2 o1 : oracle X) :
  (forall x, S0 o1 x <-> S0 o2 x) -> (forall x, S1 o1 x <-> S1 o2 x) -> o1 = o2.
Proof.
  intros. destruct o1, o2; cbn in *.
  setoid_rewrite PropExt' in H.
  eapply FunExt in H as ->.
  setoid_rewrite PropExt' in H0.
  eapply FunExt in H0 as ->.
  f_equal. eapply PI.
Qed.

Goal forall X Y (p : X -> Prop) (q : Y -> Prop),
    enumerableᵗ X -> discrete Y ->
    p ⪯ₘ q -> p ⪯ʙ q.
Proof.
  intros X Y p q EX DY [f H].
  red in H.
  unshelve eexists.
  - intros o.
    unshelve eexists. 
    + exact (fun x => (S0 o (f x))).
    + exact (fun x => (S1 o (f x))).
    + destruct o as [S0 S1 ?]; cbn in *. firstorder.
  - split.
    + cbn. destruct EX as [eX EX].
      destruct DY as [dY DY].
      eexists. eexists. intros. split.
      * unshelve eapply enumerator_red with (r := f) (q := S0 o).
        5:firstorder.
        4,5,6: eauto. 2: eauto.
      * unshelve eapply enumerator_red with (r := f) (q := S1 o). 5: firstorder.
        3, 5, 6: eauto.
    + cbn. eapply oracle_ext; firstorder.
Qed.


Section equivalence.

  Variable X : Type.
  Variable eX : eq_dec X.
  Implicit Type o : oracle X.
  Implicit Type R : FunRel X bool.

  Program Definition of_o (o : oracle X) :=
    @Build_FunRel _ _ (fun x b => if (b : bool) then S0 o x else S1 o x) _.
  Next Obligation.
    destruct o; intros ? [] [] ? ?; cbn in *; firstorder. 
  Qed.

  Program Definition to_o (R : FunRel X bool) : oracle X :=
    @Build_oracle _ (fun x => R x true) (fun x => R x false) _.
  Next Obligation.
    enough (true = false) by congruence; eapply R; eauto.
  Qed.

  Lemma of_o_enumerator o f0 f1 :
    enumerator f0 (S0 o) -> enumerator f1 (S1 o) ->
    pcomputes (fun x => bind (mu_tot (fun n => Dec (f0 n = Some x) || Dec (f1 n = Some x)))
                          (fun n => if Dec (f0 n = Some x) then ret true else ret false)) (of_o o).
  Proof.
    intros H0 H1 x b. split.
    - intros (? & [] % mu_tot_hasvalue & ?) % bind_hasvalue.
      unfold Dec in *.
      do 2 destruct Dec.option_eq_dec; cbn in *; eapply ret_hasvalue_inv in H3 as <-.
      + cbn. eapply H0. eauto.
      + cbn. eapply H0. eauto.
      + cbn. eapply H1. eauto.
      + congruence.
    - intros Ho. destruct b; cbn in *.
      + eapply H0 in Ho as [n Ho].
        assert ((λ n : nat, Dec (f0 n = Some x) || Dec (f1 n = Some x) : bool) n = true) as [n' Hn] % mu_tot_ter by (destruct Dec; firstorder).
        pose proof Hn as [Hn' _] % mu_tot_hasvalue.
        eapply bind_hasvalue.
        eexists; split; eauto.
        destruct (Dec (f0 n' = Some x)). eapply ret_hasvalue.
        cbn in Hn'. destruct Dec; cbn in *; try congruence.
        edestruct H_oracle.
        eapply H0. eauto. eapply H1; eauto.
      + eapply H1 in Ho as [n Ho].
        assert ((λ n : nat, Dec (f0 n = Some x) || Dec (f1 n = Some x) : bool) n = true) as [n' Hn] % mu_tot_ter. {
          do 2 destruct Dec; cbn; firstorder. }
        pose proof Hn as [Hn' _] % mu_tot_hasvalue.
        eapply bind_hasvalue.
        eexists; split; eauto.
        destruct (Dec (f0 n' = Some x)). 2:eapply ret_hasvalue.
        cbn in Hn'.  edestruct H_oracle.
        eapply H0. eauto. eapply H1; eauto.
  Qed.

  Lemma to_o_char (q : X -> Prop) :
    to_o (char_rel q) = char_oracle q.
  Proof.
    eapply oracle_ext; reflexivity.
  Qed.

  Lemma of_o_char (q : X -> Prop) :
    of_o (char_oracle q) = char_rel q.
  Proof.
    eapply FunRel_ext; firstorder.
  Qed.

  Lemma pcomputes_enum {Y} f fX (R : Y -> X -> Prop) b :
    enumeratorᵗ fX Y -> eq_dec X ->
    pcomputes f R -> enumerator (fun! ⟨m,n⟩ => if fX m is Some x then
                                  if seval (f x) n is Some b' then
                                             if Dec (b = b') then Some x else None else None else None) (fun x => R x b).
  Proof.
    intros HY HX Hf.
    split.
    - intros [n Hn] % Hf % seval_hasvalue.
      destruct (HY x) as [m Hm].
      exists ⟨m, n⟩. rewrite embedP, Hm, Hn.
      destruct Dec; firstorder.
    - intros (mn & H). destruct (unembed mn) as [m n].
      eapply Hf. eapply seval_hasvalue. exists n.
      edestruct fX eqn:E1, seval eqn:E2, Dec ; try congruence.
    Unshelve. all:exact False.
  Qed.
  
End equivalence.

Lemma bienumerable_bounded_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :
  eq_dec X ->
  enumerable p -> enumerable (compl p) ->
  p ⪯ᴛb q.
Proof.
  intros HX [f Hf] [g Hg].
  eapply (mkbTuring (fun R => char_rel p)) with (r' := fun _ => _) (C := fun _ => []).
  - intros. rewrite <- of_o_char. eapply of_o_enumerator; cbn; eauto. eauto.
  - intros. eauto.
  - reflexivity.
Qed.

Lemma bounded_Turing_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ᴛb q -> p ⪯ᴛ q.
Proof.
  intros ([x1 x2 x3 x4 x5] & ?).
  cbn in H.
  unshelve eexists.
  econstructor; cbn in *.
  all: eauto.
  intros. cprove eexists. intros. eapply x5; eauto.
Qed.

Lemma bienumerable_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :
  eq_dec X ->
  enumerable p -> enumerable (compl p) ->
  p ⪯ᴛ q.
Proof.
  intros HX Hp Hq.
  eapply bounded_Turing_Turing, bienumerable_bounded_Turing; eauto.
Qed.

Lemma decidable_Turing {X Y} (p : X -> Prop) (q : Y -> Prop) :
  eq_dec X ->  enumerableᵗ X ->
  decidable p ->
  p ⪯ᴛ q.
Proof.
  intros.
  eapply bienumerable_Turing.
  - eauto.
  - eapply decidable_enumerable. eauto. eauto.
  - eapply decidable_enumerable. eapply decidable_complement. eauto. eauto.
Qed.

Lemma decidable_bounded_Turing_MP :
  (forall  (p : nat -> Prop) (q : nat -> Prop), p ⪯ᴛb q -> decidable q -> decidable p) ->
  MP.
Proof.
  intros H. eapply (Post_nempty_to_MP 0).
  intros p ? % halting.semi_decidable_enumerable_iff_nat ? % halting.semi_decidable_enumerable_iff_nat. 
  eapply H with (q := fun x => True).
  eapply bienumerable_bounded_Turing; eauto.
  exists (fun _ => true). cbv. firstorder.
Qed.

Lemma decidable_Turing_MP :
  (forall  (p : nat -> Prop) (q : nat -> Prop), p ⪯ᴛ q -> decidable q -> decidable p) ->
  MP.
Proof.
  intros H. eapply (Post_nempty_to_MP 0).
  intros p ? % halting.semi_decidable_enumerable_iff_nat ? % halting.semi_decidable_enumerable_iff_nat. 
  eapply H with (q := fun x => True).
  eapply bienumerable_Turing; eauto.
  exists (fun _ => true). cbv. firstorder.
Qed.

Lemma Turing_to_Bauer {X Y} (q : Y -> Prop) (p : X -> Prop) :
  enumerableᵗ X -> discrete Y ->
  p ⪯ᴛ q -> p ⪯ʙ q.
Proof.
  intros [fX HX] [HY] % discrete_iff ([r r' Hr' HC] & H).
  exists (fun o => @to_o _ (r (@of_o _ o))).
  split.
  - intros. eexists (fun e0 e1 => _). eexists (fun e0 e1 => _). cbn.
    intros. split.
    + eapply pcomputes_enum; eauto.  eapply Hr'.
      eapply of_o_enumerator; eauto.
    + eapply pcomputes_enum; eauto. eapply Hr'.
      eapply of_o_enumerator; eauto.
  - cbn in H. now rewrite of_o_char, <- H, to_o_char.
Qed.

From SyntheticComputability Require Import hypersimple_construction.

Lemma non_finite_to {p : nat -> Prop} (f : nat -> nat) :
  Inj (=) (=) f ->
  ~ exhaustible p ->
  forall z, ~~ exists x, p x /\ f x >= z.
Proof.
  intros Hf Hp. intros z. 
  assert (~~ exists L, forall x, In x L <-> f x < z). {
    clear - Hf.
    induction z.
    - cprove exists []. firstorder lia.
    - cunwrap. destruct IHz as (L & HL).
      ccase (exists x, f x = z) as [[x H] | H].
      + cprove exists (x :: L). cbn. intros y. rewrite HL.
        firstorder subst. lia. lia. 
        ccase (f y < f x) as [H | H].
        eauto. left. eapply Hf. lia.
      + cprove exists L. intros y. rewrite HL.
        split. intros. lia.
        intros. assert (f y = z \/ f y < z) as [ | ] by lia.
        firstorder. lia.
  }
  cunwrap. destruct H as (L & HL).
  intros H. apply Hp. exists L.
  intros x Hx. eapply HL.
  cstart. intros Hfx.
  apply H. exists x. split. eauto. lia.
Qed.

Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
Proof.
  intros H x. apply H.
  induction (f x).
  - intros y. lia.
  - intros y. intros [] % le_lt_or_eq.
    + apply IHn; lia.
    + apply H. injection H0. now intros ->.
Qed.

Lemma neg_neg_least {X} p (f : X -> nat) :
  (~~ exists x, p x (f x)) -> ~~ exists x, p x (f x) /\ forall y, p y (f y) -> f x <= f y.
Proof.
  intros H. cunwrap. destruct H as (x & Hx).
  revert Hx. pattern x. eapply size_ind with (f := f). clear. intros x IH H.
  destruct (f x) eqn:E.
  - cprove exists x. split. congruence. intros. rewrite E. lia.
  - ccase (exists y, f y <= n /\ p y (f y)) as [Hf | Hf].
    + destruct Hf as (y & H1 & H2).
      eapply IH in H2. 2: lia. cunwrap.
      destruct H2 as (x' & Hx' & Hx'').
      cprove exists x'. split. eauto. firstorder.
    + cprove exists x. split. rewrite E. eauto. intros.
      cstart. intros Hx. apply Hf. exists y. split; eauto. lia.
      Unshelve. eapply nat_le_dec.
Qed.

Lemma non_finite_to_least {p : nat -> Prop} (f : nat -> nat) :
  Inj (=) (=) f ->
  ~ exhaustible p ->
  forall z, ~~ exists x, p x /\ f x >= z /\ forall y, p y /\ f y >= z -> f x <= f y.
Proof.
  intros Hf Hp. intros z.
  assert (~~ exists L, forall x, In x L <-> f x < z). {
    clear - Hf.
    induction z.
    - cprove exists []. firstorder lia.
    - cunwrap. destruct IHz as (L & HL).
      ccase (exists x, f x = z) as [[x H] | H].
      + cprove exists (x :: L). cbn. intros y. rewrite HL.
        firstorder subst. lia. lia.
        ccase (f y < f x) as [H | H].
        eauto. left. eapply Hf. lia.
      + cprove exists L. intros y. rewrite HL.
        split. intros. lia.
        intros. assert (f y = z \/ f y < z) as [ | ] by lia.
        firstorder. lia.
  }
  cunwrap. destruct H as (L & HL).
  intros H. apply Hp. exists L.
  intros x Hx. eapply HL.
  cstart. intros Hfx. eapply neg_neg_least with (p := fun x fx => p x /\ f x >= z). cprove exists x. split. eauto. lia.
  intros (x' & [] & Hx''). apply H. exists x'. split. eauto. split. eauto.
  intros ? []. eapply Hx''. firstorder.
Qed.

Section HS. 
  Import  Coq.Init.Nat.

  Context {Part : partiality}.

  Variable I : nat -> Prop. 

  Variable E_I: nat -> nat.

  Variable E_I_injective: injective E_I.
  
  Variable E_I_enum: strong_enumerator E_I I.

  Variable I_undec: ~ decidable I.

  Lemma I_iff:
    ∀ z x : nat, ¬ HS E_I x → E_I x > z → I z ↔ In z (map E_I (seq 0 (x + 1))).
  Proof.
    intros z x Hcx Hxz.
    
    split.
    * intros [n Hn] % E_I_enum. eapply in_map_iff. eexists. split. eauto.
      eapply in_seq. split. lia. cstart. intros HH. apply Hcx. exists n. split.
      lia. lia.
    * intros (? & ? & ?) % in_map_iff. subst. eapply E_I_enum. eauto.
  Qed.

  From SyntheticComputability Require Import ListAutomation.

  Lemma red : MP -> I ⪯ᴛ HS E_I.
  Proof.
    intros mp.
    unshelve eapply mkTuring.
    - intros R. unshelve eexists.
      + intros z b. exact (~~ exists x, R x false /\ E_I x > z /\ (forall x', x' < x -> ~~ (R x' true \/ R x' false /\ E_I x' <= z)) /\ reflects b (In z (map E_I (seq 0 (x + 1))))).
      + intros z [] []; repeat setoid_rewrite <- reflects_iff; try congruence.
        * intros H1 H2. cstart. cunwrap. decompose [ex and] H1. decompose [ex and] H2.
          assert (~~ x = x0). {
            assert (x < x0 \/ x = x0 \/ x0 < x) as [ | [ | ]] by lia.
            -- eapply H7 in H8. cunwrap. destruct H8 as [| []]. enough (true = false) by congruence. eapply R; eauto. lia.
            -- eauto.
            -- eapply H3 in H8. cunwrap. destruct H8 as [| []]. enough (true = false) by congruence. eapply R; eauto. lia.
          } cunwrap. subst.
          contradiction H5.
        * intros H1 H2. cstart. cunwrap. decompose [ex and] H1. decompose [ex and] H2.
          assert (~~ x = x0). {
            assert (x < x0 \/ x = x0 \/ x0 < x) as [ | [ | ]] by lia.
            -- eapply H7 in H8. cunwrap. destruct H8 as [| []]. enough (true = false) by congruence. eapply R; eauto. lia.
            -- eauto.
            -- eapply H3 in H8. cunwrap. destruct H8 as [| []]. enough (true = false) by congruence. eapply R; eauto. lia.
          } cunwrap. subst.
          contradiction H5.
    -exact (fun f z => bind (mu (fun x => bind (f x) (fun b => if negb b then if Dec (E_I x > z) then ret true else ret false else ret false))) (fun x => ret (if Dec (In z (map E_I (seq 0 (x + 1)))) then true else false))).
    - intros f R Hf z b. cbn.
      pose proof (non_finite_to E_I_injective (@HS_co_infinite I E_I I_undec) (z := S z)).
      split.
      + intros (x & ((b' & ? & ?) % bind_hasvalue & ?) % mu_hasvalue & ?) % bind_hasvalue.
        destruct b'; cbn in H1.
        * eapply ret_hasvalue_inv in H1. congruence.
        * destruct Dec; eapply ret_hasvalue_inv in H1; try congruence.
          eapply ret_hasvalue_inv in H3. subst.
          cprove exists x. split.
          -- eapply Hf. eauto. 
          -- rewrite <- reflects_iff. split.  eauto.  split.
             2:destruct Dec; eauto.
             intros m ([] & ? & ?) % H2 % bind_hasvalue; cbn in H4.
             ++ cprove left. eapply Hf. eauto.
             ++ destruct Dec. eapply ret_hasvalue_inv in H4. congruence.
                cprove right. split. now eapply Hf. lia.
      + intros Hb.
        eapply (MP_hasvalue_stable); eauto.
        cunwrap. destruct Hb as (x & H1 & H2 & H3 & H4).
        cprove eapply bind_hasvalue.
        exists x. split. eapply mu_hasvalue. split.
        eapply bind_hasvalue.  exists false. split.
        * now eapply Hf.
        * cbn. destruct Dec. eapply ret_hasvalue. lia.
        * intros. eapply MP_hasvalue_stable; eauto.
          eapply H3 in H0. cunwrap.  destruct H0 as [ | []]. cprove eapply bind_hasvalue.
          exists true. split. eapply Hf. eauto. cbn. eapply ret_hasvalue.
          cprove eapply bind_hasvalue. exists false. split. now eapply Hf.
          cbn. destruct Dec; try lia. eapply ret_hasvalue.
        * intros. eapply ret_hasvalue'. rewrite <- reflects_iff in H4.
          destruct b; destruct Dec; try congruence.
    - cbn. intros R z. ccase (∃ x : nat, R x false ∧ E_I x > z ∧ (∀ x' : nat, x' < x → ¬ ¬ (R x' true ∨ R x' false ∧ E_I x' ≤ z))) as [(x & Hx1 & Hx2 & Hx3) | H].
      2:{ cprove exists []. intros. exfalso. firstorder. }
      cprove exists (seq 0 (S x)). intros R' Heq. intros b H.
      cunwrap. destruct H as (x' & Hx'1 & Hx'2 & Hx'3 & Hx'4).
      enough (x' = x) as ->.
      clear Hx'1 Hx'2 Hx'3.
      cprove exists x. split. 2:split. 3:split.
      + eapply Heq. eauto. eapply in_seq. lia. eauto.
      + eauto.
      + intros x' H. specialize (Hx3 _ H). cunwrap. destruct Hx3 as [H' | H'].
        * cprove left. eapply Heq. eapply in_seq. lia. eauto.
        * cprove right. split. eapply Heq. eapply in_seq. lia. firstorder. firstorder.
      + eauto.
      + assert (x' < x \/ x = x' \/ x < x') as [ | []] by lia; eauto.
        * pose proof (H' := H). eapply Hx3 in H. cstart. cunwrap. destruct H.
          -- enough (false = true) by congruence. eapply R; eauto.
          -- lia.
        * pose proof (H' := H). eapply Hx'3 in H. cstart. cunwrap. destruct H.
          -- enough (true = false) by congruence. eapply R; eauto.
          -- lia.
    - intros R R' H z b Hz Hx. apply Hz. intros (x & H1 & H2 & H3 & H4).
      eapply Hx. exists x. split. eauto. split. eauto. split.
      intros ? ? ?. eapply H3; eauto. intros []; apply H5. left. eauto. right. firstorder. eauto.
    - eapply FunRel_ext. intros z b. cbn.
      split.
      + intros Hz.
        pose proof (non_finite_to_least E_I_injective (@HS_co_infinite I E_I I_undec) (z := S z)).
        cunwrap. destruct H as (x & Hcx & Hzx & Hleast). cprove exists x.
        split. eauto. split. lia. split. 
        { intros. ccase (HS E_I x') as [Hx' | Hx']. eauto. cprove right.
          split. eauto. assert (E_I x' >= S z \/ E_I x' <= z) as [] by lia; try lia.
          exfalso. unshelve epose proof (Hleast x' _). eauto.
          assert (E_I x < E_I x' \/ E_I x = E_I x') as [] by lia.
          2: eapply E_I_injective in H2; lia. 
          eapply Hx'. exists x. eauto.
        }
        rewrite reflects_iff in Hz. unfold reflects in *.
        rewrite <- I_iff; eauto.
      + intros. 
        enough (~~ if b then I z else ¬ I z). {
          destruct b; [ eapply (MP_to_MP_semidecidable mp) | ]; eauto.
          eapply EA.enum_iff.
          enough (strongly_enumerable I) as [? _] % enumerable_strongly_enumerable_iff; eauto.
          now exists E_I.
        }
        cunwrap. destruct H as (x & Hcx & Hxz & Hle & Hb).
        setoid_rewrite reflects_iff. unfold reflects in *.
        cprove rewrite I_iff; eauto.
  Qed.

End HS.

