Require Import List.

Fixpoint snoc {A: Type} (x: A) (xx: list A) : list A :=
 match xx with
 | nil       => x :: nil
 | y :: xs'  => y :: snoc x xs'
 end.

Notation "xs :> x" := (snoc x xs) (at level 62, right associativity).
