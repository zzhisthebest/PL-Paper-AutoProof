Require Import List.

Require Import ZArith.

Fixpoint replace {A : Type} (l : list A)  (i : nat) (v : A) :=
  match l with
  | nil => nil
  | a :: l1 => match i with
               |    0 => v :: l1
               | S i1 => a :: replace l1 i1 v
               end
  end.
