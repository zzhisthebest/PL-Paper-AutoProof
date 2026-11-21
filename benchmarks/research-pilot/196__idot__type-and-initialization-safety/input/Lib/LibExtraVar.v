Set Implicit Arguments.

From TLC Require Import LibTactics LibLogic LibVar.

Require Import LibExtraList.

Fixpoint vars_zip_map {A} f (xs : list var) (ys : list var) (X : A) :=
  match xs, ys with
  | nil, _ => X
  | _, nil => X
  | cons x xs, cons y ys => f x y (vars_zip_map f xs ys X)
  end.
