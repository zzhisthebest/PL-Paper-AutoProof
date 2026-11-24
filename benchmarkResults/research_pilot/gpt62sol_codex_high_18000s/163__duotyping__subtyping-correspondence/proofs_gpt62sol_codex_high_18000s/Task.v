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

Lemma flip_involutive : forall m, flip (flip m) = m.
Proof.
  destruct m; reflexivity.
Qed.

Theorem sound : forall m A B, R m A B -> RS m A B.
Proof.
  intros m A B H.
  induction H.
  - apply RSInt.
  - apply RSTB1.
  - apply RSSym, RSTB1.
  - now apply RSFun.
  - now apply RLeft.
  - apply RSSym, RLeft, RSSym.
    now rewrite flip_involutive.
  - now apply RRight.
  - apply RSSym, RRight, RSSym.
    now rewrite flip_involutive.
  - now apply RBoth.
  - apply RSSym, RBoth; apply RSSym; now rewrite flip_involutive.
Qed.

Lemma R_flip : forall m A B, R m A B -> R (flip m) B A.
Proof.
  intros m A B H.
  induction H.
  - apply SInt.
  - destruct m; apply STB2.
  - apply STB1.
  - now apply SFun.
  - destruct m; now apply SLeft2.
  - now apply SLeft1.
  - destruct m; now apply SRight2.
  - now apply SRight1.
  - destruct m; now apply SBoth2.
  - now apply SBoth1.
Qed.

Theorem complete : forall m A B, RS m A B -> R m A B.
Proof.
  intros m A B H.
  induction H.
  - apply SInt.
  - apply STB1.
  - now apply SFun.
  - now apply SLeft1.
  - now apply SRight1.
  - now apply SBoth1.
  - rewrite <- (flip_involutive m).
    now apply R_flip.
Qed.
