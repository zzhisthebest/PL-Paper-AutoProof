Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Language Infra SubDis.

Fixpoint principal_type (v:exp) : typ :=
  match v with
  | unit => top
  | lit i5 => int
  | box e1 (ann (lam bl e) (arr A B)) => arr A B
  | box e1 (ann (lam wh e) (arr (rcd l A) B)) => arr A B
  | merge v1 v2 => and (principal_type v1) (principal_type v2)
  | rec l v1 => rcd l (principal_type v1)
  | _ => top
  end.

Definition old_dis A B :=
  forall C, sub A C -> sub B C -> toplike C.
