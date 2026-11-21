Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Lia.

Require Import Language.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | int => 1
    | top => 1
    | arr A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | rcd l1 A2 => 1 + (size_typ A2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | unit => 1
    | lit i1 => 1
    | ctx => 1
    | merge e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | ann e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | rec l1 e2 => 1 + (size_exp e2)
    | proj e2 l1 => 1 + (size_exp e2)
    | lam fm e2 => 1 + (size_exp e2)
    | app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | box e2 e3 => 1 + (size_exp e2) + (size_exp e3)
  end.

Definition relation (X:Type) := X -> X -> Prop.

Section Star.

Variable A : Type.

Variable R : relation A.

Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Definition irred a : Prop := forall b, ~(R a b).

End Star.
