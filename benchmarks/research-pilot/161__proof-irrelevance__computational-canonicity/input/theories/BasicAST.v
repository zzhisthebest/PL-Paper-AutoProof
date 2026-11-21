From Stdlib Require Import Utf8 String.

Inductive level :=
| ty (n : nat) | prop.

Definition ax (l : level) :=
  match l with
  | prop => 0
  | ty i => S i
  end.

Definition ru l j :=
    match l with
    | prop => j
    | ty i => max i j
    end.

Definition Ax (l : level) : level :=
  ty (ax l).

Definition Ru (l1 l2 : level) : level :=
  match l2 with
  | prop => prop
  | ty j => ty (ru l1 j)
  end.

Definition aref := nat.
