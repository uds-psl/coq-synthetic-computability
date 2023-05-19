From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From SyntheticComputability Require Import LMuRecursion.
From Undecidability.L Require Import Computability.Computability Functions.Eval.
From Undecidability.L.Datatypes Require Import LNat LOptions LProd Lists.

Require Import Datatypes.

Inductive is_computable {A} {t : TT A} (a : A) : Prop :=
  C : computable a -> is_computable a.

Notation enumerates f p := (forall x, p x <-> exists n : nat, f n = Some x).

Definition L_decidable {X} `{encodable X} (P : X -> Prop) :=
  exists f : X -> bool, is_computable f /\ forall x, P x <-> f x = true.

Definition L_enumerable {X} `{encodable X} (p : X -> Prop) := 
  exists f : nat -> option X, is_computable f /\ (enumerates f p).

Definition L_recognisable {X} `{encodable X} (p : X -> Prop) :=
  exists f : X -> nat -> bool, is_computable f /\ forall x, p x <-> exists n, f x n = true.

Definition L_recognisable' {X} `{encodable X} (p : X -> Prop) :=
  exists s : term, forall x, p x <-> converges (L.app s (enc x)).

Notation "s ▹ t" := (eval s t) (at level 50).
Import L_Notations.

Lemma modesty_func {X} {HX : encodable X} {Y} {HY : encodable Y} s unenc :
  (forall t (y:Y), enc y = t -> y = unenc t) ->
  proc s -> (forall x : X, exists y : Y, s (enc x) ▹ (enc y)) -> {f : X -> Y | forall x, s (enc x) ▹ enc (f x)}.
Proof.
  intros Hunenc Hp Hs. 
  unshelve eexists.
  - intros x. edestruct lcomp_comp with (u := s (enc x)) as [y Hy].
    + eapply Hunenc.
    + destruct (Hs x) as [y Hy]. exists y. Lsimpl. reflexivity.
    + exact y.
  - intros x. cbn. destruct lcomp_comp as [y Hy].
    rewrite Hy. eapply eval_refl. Lproc.
Qed.  

Lemma step_beta s t u :
  t = subst s 0 u ->
  lambda u ->
  L.app (lam s) u ≻ t.
Proof.
  intros -> [? ->]. econstructor.
Qed.

Lemma L_decidable_iff {X} `{HR : encodable X} (p : X -> Prop) :
  L_decidable p <-> exists s, closed s /\ forall x, (s (enc x) ▹ enc true /\ p x) \/ (s (enc x) ▹ enc false /\ ~ p x).
Proof.
  split.
  - intros (f & [Hf] & H). exists (ext f). split. 1:Lproc. 
    intros x. destruct (f x) eqn:E.
    + left. split. 2: now eapply H.
      Lsimpl. rewrite E. eapply eval_refl. Lproc.
    + right. split. 2: rewrite H; congruence.
      Lsimpl. rewrite E. eapply eval_refl. Lproc.
  - intros (s & Hp & Hs).
    edestruct (@modesty_func X HR) with (unenc := bool_enc_inv) (s := lam (s 0)) as [f Hf].
    + eapply bool_enc_inv_correct.
    + Lproc.
    + intros x. destruct (Hs x) as [[? _] | [? _]].
      * exists true. split. 2: Lproc. econstructor 2.
        eapply step_beta. cbn. red in Hp. rewrite Hp. reflexivity. Lproc.
        eapply H.
      * exists false. split. 2: Lproc. econstructor 2.
        eapply step_beta. cbn. red in Hp. rewrite Hp. reflexivity. Lproc.
        eapply H.
    + exists f. split. econstructor. exists (lam (s 0)).
      * cbn. split. Lproc. intros x ? ->. exists (enc (f x)). split; try reflexivity. Lsimpl. reflexivity.
      * intros x. split.
        -- intros Hx. destruct (Hs x) as [[] | []]; try tauto. specialize (Hf x).
           eapply enc_extinj. destruct Hf. rewrite <- H1. destruct H. rewrite <- H. clear H H1.
           etransitivity. econstructor 1. eapply step_beta. cbn.
           cbn. red in Hp. now rewrite Hp. Lproc. reflexivity.
        -- intros Hx. destruct (Hs x) as [[] | []]; try tauto. specialize (Hf x).
           enough (true = false) by congruence.
           eapply enc_extinj. destruct Hf. rewrite Hx in H1. destruct H. rewrite <- H, <- H1. clear H H1.
           etransitivity. econstructor 1. eapply step_beta. cbn.
           cbn. red in Hp. now rewrite Hp. Lproc. reflexivity.
Qed.

Lemma L_recognisable_iff {X} `{HR : encodable X} (p : X -> Prop) :
  computable (enc (X := X)) ->
  L_recognisable p <-> L_recognisable' p.
Proof.
  split.
  - intros (f & [Hc] & H).
    exists (lam (mu (lam ((ext f 1 0))))). intros x.
    rewrite H. split.
    + intros [n Hn]. edestruct (mu_complete) as [n' Hn']. 4:{ exists (ext n'). split. 2:Lproc. Lsimpl. exact Hn'. }
      * Lproc.
      * intros n'. exists (f x n'). now Lsimpl.
      * instantiate (1 := n). Lsimpl. now rewrite Hn.
    + intros (v & H1 & H2).
      assert (Eq : lam (mu (lam (ext f # 1 # 0))) (enc x) == mu (lam (ext f (enc x) # 0))) by now Lsimpl.
      rewrite Eq in H1; clear Eq.
      eapply mu_sound in H1 as (n & -> & H3 & H4).
      * exists n. eapply enc_extinj. rewrite <- H3. now Lsimpl.
      * Lproc.
      * intros n. exists (f x n). now Lsimpl.
      * eauto.
  - intros [s Hs].
    exists (fun x n => if eva n (s (enc x)) is Some s then true else false).
    split.
    + econstructor. extract.
    + intros x. rewrite Hs. split.
      * intros (t & H1 & H2). eapply equiv_eva in H1 as [n Hn]. exists n. now rewrite Hn. assumption.
      * intros (n & Hn). destruct eva eqn:E; try congruence.
        exists t. split. eapply eva_equiv. eauto. eapply eva_lam. eauto.
Qed.

Definition unembed' := (fix F (k : nat) := 
  match k with 0 => (0,0) | S n => match fst (F n) with 0 => (S (snd (F n)), 0) | S x => (x, S (snd (F n))) end end).

Global Instance unembed_computable : computable unembed.
Proof.
  eapply computableExt with (x := unembed'). 2:extract.
  intros n. cbn. induction n; cbn.
  - reflexivity.
  - fold (unembed n). rewrite IHn. now destruct (unembed n).
Qed.

Lemma L_enumerable_iff {X} {HR : encodable X} {HI : encInj HR} (p : X -> Prop) unenc :
   (forall (t : term) (y : X), enc y = t <-> Some y = unenc t) ->
   computable unenc ->
   L_enumerable p <-> exists t, proc t /\ forall x, p x <-> exists n : nat, t (enc n) ▹ enc x.
Proof.
  intros Hunenc Hcunenc.
  split.
  - intros (f & [Hc] & H).
    exists (lam (ext f 0 (lam (lam 1)) (lam Omega) (lam 0))). split. Lproc.
    intros x. 
    assert (Heq : forall n, lam (ext f # 0 (lam (lam # 1)) (lam Omega) (lam # 0)) (enc n) >*
      (if f n is (Some H0) then lam (lam # 1) (enc H0) else lam (omega omega))
      (lam # 0)). { intros. unfold Omega. now Lsimpl. }
    split.
    + intros [n Hn] % H. exists n.  split. 2:Lproc. unfold Omega.
      rewrite Heq, Hn. now Lsimpl.
    + intros [n Hn]. eapply H. exists n.
      rewrite Heq in Hn. destruct (f n) as [x' | ] eqn:E.
      * f_equal. eapply enc_extinj.
        destruct Hn as [Hn _]. rewrite <- Hn. symmetry.
        now Lsimpl.
      * destruct (proc_enc x) as [H1 [t Ht]].
        edestruct Omega_diverges with (s := t).
        enough (lam (omega omega) (lam # 0) == Omega) as <-. rewrite <- Ht.
        destruct Hn. rewrite H0. reflexivity.
        unfold Omega. clear Hn. now Lsimpl.
  - intros (t & Ht & H).
    exists (fun nm => match unembed nm with (n,m) => match eva n (t (enc m)) with Some v =>
      unenc v | None => None
    end end).
    split.
    + econstructor. extract.
    + intros x. rewrite H. clear H. split.
      * intros (n & H1 & H2). eapply star_equiv_subrelation in H1.
        eapply equiv_eva in H1 as [m H]; [ | auto].
        exists ⟨m,n⟩. rewrite embedP, H. symmetry. now eapply Hunenc.
      * intros [nm H]. destruct (unembed nm) as [n m].
        destruct eva eqn:E; try congruence.
        symmetry in H. eapply Hunenc in H. subst.
        exists m. eapply eva_equiv in E. rewrite E. eapply eval_refl. Lproc.
Qed.

Section L_enum_rec.

  Variable X : Type.
  Context `{encodable X}.
  Variable (p : X -> Prop).

  Hypotheses (f : nat -> option X) (c_f : computable f) (H_f : enumerates f p).
  Hypotheses (d : X -> X -> bool) (c_d : computable d) (H_d : forall x y, reflect (x = y) (d x y)).

  Definition test := (fun x n => match f n with Some y => d x y | None => false end).

  Instance term_test : computable test.
  Proof using c_f c_d.
    extract.
  Qed.

  Import HOAS_Notations.

  Lemma proc_test (x : X) :
    proc [L_HOAS λ y, !!(ext test) !!(enc x) y].
  Proof.
    cbn. Lproc.
  Qed.
    
  Lemma L_enumerable_recognisable :
    L_recognisable' p.
  Proof using c_f c_d H_f H_d.
    exists [L_HOAS λ x, !!mu (λ y, !!(ext test) x y)].
    intros. split; intros.
    - eapply H_f in H0 as [n H0].
      edestruct (mu_complete (proc_test x)) with (n := n).
      + intros. exists (test x n0). cbn. now Lsimpl.
      + cbn. Lsimpl. unfold test. rewrite H0. destruct (H_d x x); intuition.
      + exists (ext x0). split; try Lproc.
        cbn. Lsimpl. now rewrite H1.
    - destruct H0 as (v & ? & ?).
      edestruct (mu_sound (proc_test x)) with (v := v) as (n & ? & ? & _).
      + intros. exists (test x n). cbn. now Lsimpl.
      + Lproc.
      + rewrite <- H0. symmetry. cbn. now Lsimpl.
      + subst. eapply H_f. exists n.
        assert ([L_HOAS (λ y, !! (ext test) !! (enc x) y) !!(ext n)] == ext (test x n)).
        cbn. now Lsimpl. cbn in *. rewrite H2 in *.
        eapply unique_normal_forms in H3;[|Lproc..].
        eapply inj_enc in H3.
        unfold test in H3. destruct (f n); inv H3.
        destruct (H_d x x0); firstorder congruence.
  Qed.

End L_enum_rec.

Definition opt_to_list n := match nat_enum n with Some x => [x] | None => [] end.

Global Instance term_opt_to_list : computable opt_to_list.
Proof.
  extract.
Qed.
  
Definition L_nat := cumul (opt_to_list).

Global Instance term_L_nat : computable L_nat.
Proof.
  unfold L_nat. unfold cumul.
  extract.
Qed.

(* Definition T_nat_nat := Eval cbn in L_T (X := nat * nat). *)

(* Definition pair' : nat * nat -> nat * nat := fun '(x,y) => (x,y). *)

(* Instance term_pair' : computable pair'. *)
(* Proof. *)
(*   extract. *)
(* Qed. *)

Require Import SyntheticComputability.Shared.embed_nat Nat.

(* Instance term_nat_rec {X : Set} `{encodable X} : computable (@nat_rec (fun _ => X)). *)
(* Proof. *)
(*   unfold nat_rec, nat_rect. extract. *)
(* Qed. *)

Definition F' := (fix F (n : nat) : nat := match n with
                                                           | 0 => 0
                                                           | S n0 => S n0 + F n0
                                                           end).

Global Instance term_F' : computable F'.
Proof.
  extract.
Qed.

Definition F'' := (fix F (n0 : nat) : nat * nat := match n0 with
                                                     | 0 => (0, 0)
                                                     | S n1 => match F n1 with
                                                               | (0, y) => (S y, 0)
                                                               | (S x0, y) => (x0, S y)
                                                               end
                                             end).

Global Instance term_F'' : computable F''.
Proof.
  extract.
Qed.

Global Instance term_embed_nat : computable embed.
Proof.
  change (computable (fun '(x, y) => y + F' (y + x))).
  extract.
Qed.

Global Instance term_unembed_nat : computable unembed.
Proof.
  unfold unembed.
  change (computable F'').
  exact term_F''.
Qed.

(* Definition F''' := (prod_enum nat_enum nat_enum). *)

(* Instance term_prod_enum : computable F'''. *)
(* Proof. *)
(*   unfold F'''. *)
(*   extract. *)
(* Qed. *)

(* Instance term_nat_enum : computable nat_enum. *)
(* Proof. *)
(*   extract. *)
(* Qed. *)

(* Instance term_T_nat_nat : computable T_nat_nat. *)
(* Proof. *)
(*   change (computable *)
(*     (fix f (n : nat) : list (nat * nat) := match n with *)
(*                                            | 0 => [] *)
(*                                            | S n0 => f n0 ++ opt_to_list (F''' n0) *)
(*                                            end)). *)
(*   extract. *)
(* Qed. *)

(* Instance term_R_nat_nat : computable R_nat_nat. *)
(* Proof. *)
(*   change (computable (fun n : nat => nthe n (T_nat_nat n))). *)
(*   extract. *)
(* Qed. *)

(* Instance term_ofNat X `{encodable X} : *)
(*   computable (@ofNat X). *)
(* Proof. *)
(*   extract. *)
(* Qed. *)

Definition lenumerates {X} L (p : X -> Prop) :=
  cumulative L /\ (forall x : X, p x <-> (exists m : nat, x el L m)).

Definition L_enum {X} `{encodable X} (p : X -> Prop) :=
  exists L, is_computable L /\ lenumerates L p.

Lemma projection X Y {HX : encodable X} {HY : encodable Y} (p : X * Y -> Prop) :
  L_enumerable p -> L_enumerable (fun x => exists y, p (x,y)).
Proof.
  intros (f & [cf] & ?).
  exists (fun n => match f n with Some (x, y) => Some x | None => None end).
  split.
  - econstructor. extract.
  - intros; split.
    + intros [y ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
    + intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inv H0.
      exists y. eapply H. eauto.
Qed.

Lemma L_enumerable_ext X `{encodable X} p q : L_enumerable p -> (forall x : X, p x <-> q x) -> L_enumerable q.
Proof.
  intros (f & cf & Hf) He. exists f; split; eauto.
  intros ?. rewrite <- He. eapply Hf.
Qed.

Definition F1 {X} (T : nat -> list X) :=  (fun n => let (n, m) := unembed n in nth_error (T n) m).

Global Instance term_F1 {X} {H : encodable X} :  @computable ((nat -> list X) -> nat -> option X) ((! nat ~> ! list X) ~> ! nat ~> ! option X) (@F1 X).
Proof.
  extract.  
Qed.

Lemma L_enumerable_enum {X} `{encodable X} (p : X -> Prop) :
  L_enum p -> L_enumerable p.
Proof.
  intros (f & [cf] & Hf).
  exists (F1 f). split.
  - econstructor. extract.
  - destruct Hf as [CX HX].
    intros x. unfold F1.
    now rewrite list_enumerator_to_enumerator.
Qed.

Lemma L_enumerable_halt {X} `{encodable X} (p : X -> Prop) :
  L_decidable (X := X * X) (fun '(x,y) => x = y) ->
  L_enumerable p -> p ⪯ converges.
Proof.
  intros (d & [c_d] & H_d) (f & [c_f] & H_f).
  edestruct L_enumerable_recognisable with (p := p) (d := fun x y => d (x,y)) (f := f); eauto.
  - extract.
  - intros. specialize (H_d (x,y)). destruct (d (x,y)); intuition.
  - now exists (fun x0 => L.app x (enc x0)). 
Qed.  

Import L_Notations.

Lemma L_recognisable'_recognisable {X} `{encodable X} (p : X -> Prop) :
  L_recognisable p -> L_recognisable' p.
Proof.
  intros (f & [c_f] & H_f).
  exists (lam (mu (lam (ext f 1 0)))).
  intros. 
  assert (((lam (mu (lam ((ext f 1) 0)))) (enc x)) >* mu (lam (ext f (enc x) 0))) by now Lsimpl.
  rewrite H0. rewrite mu_spec.
  - rewrite H_f. split; intros [n]; exists n.
    Lsimpl. now rewrite H1.
    eapply enc_extinj.
    now assert ((lam (((ext f) (enc x)) 0)) (ext n) == enc (f x n)) as <- by now Lsimpl.
  - Lproc.
  - intros. exists (f x n). now Lsimpl.
Qed.    

Lemma L_recognisable_halt {X} `{encodable X} (p : X -> Prop) :
  L_recognisable p -> p ⪯ converges.
Proof.
  intros. eapply L_recognisable'_recognisable in H0 as  (f & H_f). now exists (fun x0 => f (enc x0)). 
Qed.

Lemma L_recognisable_HaltL {X} `{encodable X} (p : X -> Prop) :
  L_recognisable p -> p ⪯ HaltL.
Proof.
  intros. eapply L_recognisable'_recognisable in H0 as  (f & H_f). exists (fun x0 => f (enc x0)). 
  intros x. rewrite H_f. unfold converges, HaltL. setoid_rewrite eval_iff. firstorder.
  subst. eapply eproc_equiv in H0. eauto.
Qed.
