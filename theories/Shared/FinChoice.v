From SyntheticComputability.Shared Require Import FinitenessFacts.
Require Import List.

Definition total {X Y} (R : X -> Y -> Prop) :=
  forall x, exists y, R x y.

Lemma Forall2_total {X} {Y} (R : X -> Y -> Prop) L :
  (forall x, In x L -> exists y, R x y) -> exists L', Forall2 R L L'.
Proof.
  intros HP. induction L.
  - exists nil. econstructor.
  - destruct (HP a) as [b H]. 1:firstorder.
    destruct IHL as [L2' IH].
    + firstorder.
    + exists (b :: L2'). econstructor; eauto.
Qed.

Lemma finite_choice_list {X Y} (R : X -> Y -> Prop) L (y0 : Y) :
  (forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) ->
  (forall x, In x L -> exists y, R x y) -> 
  exists f, forall x, In x L -> R x (f x).
Proof.
  intros D Htot.
  induction L as [ | x L].
  - exists (fun _ => y0). firstorder.
  - destruct IHL as [f Hf].
    + firstorder.
    + destruct (Htot x) as [y Hy]; [ firstorder | ].
      exists (fun x' => if D x x' then y else f x').
      intros x0 [-> | H].
      * destruct (D x0 x0); tauto.
      * destruct (D x x0) as [-> | Hx]; auto.
Qed.     

Lemma finite_choice_precond {X Y} (R : X -> Y -> Prop) (p : X -> Prop) (y0 : Y) :
  listable p ->
  (forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) ->
  (forall x, p x -> exists y, R x y) -> 
  exists f, forall x, p x -> R x (f x).
Proof.
  intros [L HL]. red in HL. setoid_rewrite HL.
  eapply finite_choice_list. exact y0.
Qed.

Lemma finite_choice {X Y} (R : X -> Y -> Prop) :
  finiteᵗ X ->
  (forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) ->
  (forall x, exists y, R x y) -> 
  exists f, forall x, R x (f x).
Proof.
  intros [L HL] D Htot.
  destruct L as [ | x0].
  - unshelve eexists; intros; exfalso; firstorder.
  - destruct (Htot x0) as [y0 _]. revert HL. generalize (x0 :: L). clear L x0. intros L HL.
    destruct (@finite_choice_list _ _ R L y0) as [f Hf].
    + exact D.
    + firstorder.
    + exists f. intros. now apply Hf.
Qed.
