Set Implicit Arguments.

Require Import GUnionInter.

Inductive RS : Mode -> typ -> typ -> Prop :=
| RSInt : forall m, RS m typ_int typ_int
| RSTB1 : forall A m, RS m A (mode_to_sub m)
| RSFun : forall A B C D m, RS (flip m) A C -> RS m B D -> RS m (typ_arrow A B) (typ_arrow C D)
| RLeft  : forall A B C m, RS m A C -> RS m (choose m A B) C
| RRight : forall A B C m, RS m B C -> RS m (choose m A B) C
| RBoth  : forall A B C m, RS m A B -> RS m A C -> RS m A (choose m B C)
| RSSym : forall m A B, RS (flip m) B A -> RS m A B.

Lemma flip_flip : forall m, flip (flip m) = m.
Proof. intros m; destruct m; reflexivity. Qed.

(* The declarative relation is invariant under flipping the mode and
   swapping the two types. *)
Lemma R_flip : forall m A B, R m A B -> R (flip m) B A.
Proof.
  intros m A B H. induction H.
  - apply SInt.
  - destruct m; simpl; apply STB2.
  - apply STB1.
  - apply SFun; assumption.
  - destruct m; simpl in *; apply SLeft2; assumption.
  - apply SLeft1; assumption.
  - destruct m; simpl in *; apply SRight2; assumption.
  - apply SRight1; assumption.
  - destruct m; simpl in *; apply SBoth2; assumption.
  - apply SBoth1; assumption.
Qed.

Theorem sound : forall m A B, R m A B -> RS m A B.
Proof.
  intros m A B H. induction H.
  - apply RSInt.
  - apply RSTB1.
  - apply RSSym; apply RSTB1.
  - apply RSFun; assumption.
  - apply RLeft; assumption.
  - destruct m; simpl in *; apply RSSym; apply RLeft; apply RSSym; assumption.
  - apply RRight; assumption.
  - destruct m; simpl in *; apply RSSym; apply RRight; apply RSSym; assumption.
  - apply RBoth; assumption.
  - destruct m; simpl in *; apply RSSym; apply RBoth; apply RSSym; assumption.
Qed.

Theorem complete : forall m A B, RS m A B -> R m A B.
Proof.
  intros m A B H. induction H.
  - apply SInt.
  - apply STB1.
  - apply SFun; assumption.
  - apply SLeft1; assumption.
  - apply SRight1; assumption.
  - apply SBoth1; assumption.
  - apply R_flip in IHRS. rewrite flip_flip in IHRS. exact IHRS.
Qed.
