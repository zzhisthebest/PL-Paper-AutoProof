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

Theorem sound : forall m A B, R m A B -> RS m A B.

Theorem complete : forall m A B, RS m A B -> R m A B.
