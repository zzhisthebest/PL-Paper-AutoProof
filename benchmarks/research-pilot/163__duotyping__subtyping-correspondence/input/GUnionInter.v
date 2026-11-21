Set Implicit Arguments.

Inductive typ : Set :=
  | typ_btm   : typ
  | typ_top   : typ
  | typ_int   : typ
  | typ_arrow : typ -> typ -> typ
  | typ_and   : typ -> typ -> typ
  | typ_or    : typ -> typ -> typ.

Inductive Mode := Sub | Sup.

Definition flip (m : Mode) : Mode :=
  match m with
  | Sub => Sup
  | Sup => Sub
  end.

Definition mode_to_sub m := match m with
  | Sub => typ_top
  | Sup => typ_btm end.

Definition choose (m : Mode) : typ -> typ -> typ :=
  match m with
  | Sub => typ_and
  | Sup => typ_or
  end.

Inductive R : Mode -> typ -> typ -> Prop :=
  | SInt : forall m, R m typ_int typ_int
  | STB1 : forall A m, R m A (mode_to_sub m)
  | STB2 : forall A m, R m (mode_to_sub (flip m)) A
  | SFun : forall A B C D m, R (flip m) A C -> R m B D -> R m (typ_arrow A B) (typ_arrow C D)
  | SLeft1  : forall A B C m, R m A C -> R m (choose m A B) C
  | SLeft2  : forall A B C m, R m A B -> R m A (choose (flip m) B C)
  | SRight1 : forall A B C m, R m B C -> R m (choose m A B) C
  | SRight2 : forall A B C m, R m A C -> R m A (choose (flip m) B C)
  | SBoth1  : forall A B C m, R m A B -> R m A C -> R m A (choose m B C)
  | SBoth2  : forall A B C m, R m A C -> R m B C -> R m (choose (flip m) A B) C.
