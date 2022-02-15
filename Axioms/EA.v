From Undecidability Require Import Synthetic.DecidabilityFacts Synthetic.SemiDecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.ListEnumerabilityFacts reductions partial embed_nat ReducibilityFacts truthtables bestaxioms.
Require Import Setoid Program Lia List.

Axiom EA : EA.

Notation φ := (proj1_sig EA).
Notation EAP := (proj2_sig EA).

Lemma EAS : forall p : nat -> nat -> Prop, enumerable (uncurry p) -> exists γ, forall x, enumerator (φ (γ x)) (p x).
Proof.
  intros p [γ H] % penumerable_iff % EAP; firstorder; eauto.
  eapply discrete_nat.
Qed.

Definition W c x := exists n, φ c n = Some x.

Lemma W_spec : forall p, enumerable p <-> exists c, forall x, p x <-> W c x.
Proof.
  intros p.
  split.
  - intros [f Hf].
    destruct (EAP (fun _ => p)) as [γ H].
    + exists (fun _ => f). firstorder.
    + exists (γ 0). firstorder.
  - intros [c H]. exists (φ c). firstorder.
Qed.

Lemma do_EA p : enumerable p -> exists c, forall x, p x <-> W c x.
Proof.
  eapply W_spec.
Qed.

Hint Resolve discrete_nat : core.

Lemma EAS' :
  forall p : nat -> nat -> Prop, enumerable (fun! ⟨x,y⟩ => p x y) ->
                                        exists c : nat -> nat, forall x y, p x y <-> W (c x) y.
Proof.
  intros p Hp.
  eapply EAS, enumerable_red; eauto.
  exists embed. red. intros [x y]. now rewrite embedP.
Qed.

Lemma EAS_datatype X (p : X -> nat -> Prop) (x0 : X) :
  datatype X ->
  enumerable (uncurry p) ->
  exists c : X -> nat, forall x y, p x y <-> W (c x) y.
Proof.
  intros (I & R & HIR) Ep.
  destruct (EAS (fun x y => if R x is Some l then p l y else p x0 y)) as [c Hc].
  - eapply enumerable_red.
    4: eapply Ep.
    + exists (fun '(x, y) => if R x is Some l then (l,y) else (x0, y)).
      intros [x y]. cbn.
      destruct (R x); reflexivity.
    + eauto.
    + eapply discrete_prod. eapply datatype_discrete. now exists I, R.
      eapply discrete_nat.
  - exists (fun l => c (I l)). intros. 
    now rewrite <- (Hc (I x) y), HIR.
Qed.

Lemma EAS_list (p : list nat -> nat -> Prop) : enumerable (uncurry p) ->
                                      exists c : list nat -> nat, forall x y, W (c x) y <-> p x y.
Proof.
  intros.
  edestruct EAS_datatype with (p := p) as [c Hc]; eauto.
  - exact nil.
  - eapply enumerable_discrete_datatype.
    eapply discrete_list, discrete_nat.
    eauto.
  - exists c. firstorder.
Qed.

Lemma List_id : exists c_l, forall (l : list nat), forall x, W (c_l l) x <-> List.In x l.
Proof.
  eapply EAS_list. 
  eapply decidable_enumerable. 2:eauto.
  eapply decidable_iff. econstructor.
  intros [x y]. cbn. exact _. 
Qed.

Notation π1 := (fun! ⟨x, y⟩ => x).
Notation π2 := (fun! ⟨x, y⟩ => y).

Lemma enumerable_W : enumerable (fun '(x, y) => W x y).
Proof.
  exists (fun p => let (n,m) := unembed p in if φ n m is Some m then Some (n, m) else None).
  intros [n m].
  split.
  - intros H. destruct H as [n' H].
    exists (embed (n, n')). rewrite embedP. cbn. now rewrite H.
  - unfold W.
    intros [p H].
    destruct (unembed p) as [n' m'].
    exists m'.
    destruct (φ n' m') eqn:E; inversion H; now subst.
Qed.

Lemma W_maximal (p : nat -> Prop) :
  enumerable p -> p ⪯ₘ uncurry W.
Proof.
  intros Hp.
  destruct (do_EA p Hp) as [c Hc].
  exists (fun x => (c, x)). exact Hc.
Qed.

Lemma SMN' : forall f, exists k, forall c x, W c (f x) <-> W (k c) x.
Proof.
  intros f.
  eapply EAS.
  eapply enumerable_red with (q := uncurry W).
  - exists (fun '(x,y) => (x, f y)). now intros [x y].
  - eauto.
  - eapply discrete_prod; now eapply discrete_nat.
  - eapply enumerable_W.
Qed.

Lemma TT : 
  forall f : nat -> { Q : list nat & truthtable}, 
    exists c : list nat -> nat, forall l x, W (c l) x <-> eval_tt (projT2 (f x)) (List.map (fun x => negb (inb (uncurry Nat.eqb) x l)) (projT1 (f x))) = false.
Proof.
  intros f.
  eapply EAS_list.
  eapply decidable_enumerable. 2:eauto.
  eapply decidable_iff. econstructor.
  intros [x y]. cbn. exact _. 
Qed.

Tactic Notation "intros" "⟨" ident(n) "," ident(m) "⟩" :=
  let nm := fresh "nm" in
  let E := fresh "E" in
  intros nm; destruct (unembed nm) as [n m] eqn:E.

Definition K0 c := W c c.

Lemma K0_not_enumerable : ~ enumerable (compl K0).
Proof.
  intros [c Hc] % do_EA. specialize (Hc c).
  unfold K0, compl in Hc. tauto.
Qed.

Lemma K0_undecidable : ~ decidable (compl K0).
Proof.
  intros Hf % decidable_enumerable; eauto.
  now eapply K0_not_enumerable.
Qed.

Lemma W_uncurry_red:
  (fun! ⟨ n, m ⟩ => W n m) ⪯ₘ uncurry W.
Proof.
  exists (fun! ⟨n,m⟩ => (n,m)). intros nm. destruct (unembed nm) as [n m]. reflexivity.
Qed.

Lemma K0_red:
  K0 ⪯ₘ uncurry W.
Proof.
  exists (fun n => (n,n)). intros n. reflexivity.
Qed.

Lemma W_uncurry_red':
  uncurry W ⪯ₘ (fun! ⟨ n, m ⟩ => W n m).
Proof.
  exists (fun '(n,m) => ⟨n,m⟩). intros [n m]. now rewrite embedP.
Qed.

Global Hint Resolve discrete_prod discrete_nat : core.

Lemma W_not_enumerable : ~ enumerable (compl (uncurry W)).
Proof.
  eapply not_coenumerable; eauto.
  - eapply K0_red.
  - eapply K0_not_enumerable. 
Qed.

Lemma K0_enum : enumerable K0.
Proof.
  eapply enumerable_red with (q := uncurry W).
  eapply K0_red. all:eauto.
  eapply enumerable_W.
Qed.

Lemma red_tt_not_red_m :
  compl K0 ⪯ₜₜ K0 /\ ~ compl K0 ⪯ₘ K0.
Proof.
  split.
  - eapply red_tt_complement.
  - intros H % enumerable_red.
    + now eapply K0_not_enumerable.
    + eauto.
    + eapply discrete_nat.
    + eapply K0_enum.
Qed.

Notation "m-complete p" := (forall q : nat -> Prop, enumerable q -> q ⪯ₘ p) (at level 10).

Lemma m_complete_W :
  m-complete (fun! ⟨n,m⟩ =>  W n m).
Proof.
  intros q [c Hc] % do_EA.
  exists (fun x => ⟨c,x⟩). intros x.
  now rewrite embedP.
Qed.

Lemma W_red_K0 : (fun! ⟨n,m⟩ =>  W n m) ⪯ₘ K0.
Proof.
  edestruct EAS with (p := fun! ⟨x,y⟩ => fun (z : nat) => W x y) as [c Hc].
  - eapply ReducibilityFacts.enumerable_red with (q := uncurry W); eauto.
    2: eapply enumerable_W. all:eauto.
    exists (fun '(xy,z) => (fun! ⟨x,y⟩ => (x,y)) xy). intros [xy z].
    cbn. now destruct (unembed xy) as [x y]. 
  - exists c. intros xy. unfold K0. rewrite <- (Hc xy (c xy)).
    now destruct (unembed xy) as [x y].
Qed.

Lemma m_complete_K0 : m-complete K0.
Proof.
  intros q Hq % m_complete_W.
  eapply red_m_transitive. exact Hq. exact W_red_K0.
Qed.

Lemma enum_iff (p : nat -> Prop) : enumerable p <-> semi_decidable p.
Proof.
  split.
  - intros H. eapply enumerable_semi_decidable. eapply discrete_nat. eassumption.
  - intros H. eapply semi_decidable_enumerable. eauto. eauto.
Qed.

Lemma generative_W :   generative (fun! ⟨ n, m ⟩ => W n m).
Proof.
  eapply unbounded_generative. 
  intros x y; destruct (numbers.nat_eq_dec x y); eauto.
  destruct (do_EA (fun _ => True)) as [c_top H_top]. {
    eapply decidable_enumerable. 2:eauto. exists (fun _ => true). firstorder.
  }
  intros n. exists (map (fun m => ⟨c_top,m⟩) (seq 0 n)). split.
  now rewrite map_length, seq_length. split.
  eapply NoDup_map. intros ? ? E % (f_equal unembed). rewrite !embedP in E. congruence. eapply seq_NoDup.
  intros ? (? & <- & ?) % in_map_iff. rewrite embedP. firstorder.
Qed.