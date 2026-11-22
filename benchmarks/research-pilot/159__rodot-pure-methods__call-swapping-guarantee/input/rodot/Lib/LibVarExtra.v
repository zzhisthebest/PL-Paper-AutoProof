Set Implicit Arguments.

From TLC Require Import LibVar LibLN.

Fixpoint vars_zip_map {A} f (xs : list var) (ys : list var) (X : A) :=
  match xs, ys with
  | nil, _ => X
  | _, nil => X
  | cons x xs, cons y ys => f x y (vars_zip_map f xs ys X)
  end.

Notation "z '\[' x '->' y ']'" := (If z = x then y else z) (x at level 69, at level 7, left associativity).

Definition subst_fvar (x y z: var): var := If z = x then y else z.
