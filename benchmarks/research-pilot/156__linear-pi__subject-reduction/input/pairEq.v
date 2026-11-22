Require Import Bool List Lia PeanoNat header operations.

Section PairEq.

Definition pair_eq (p1 p2 : name * name) :=
    (fst p1 =? fst p2) && (snd p1 =? snd p2).

Fixpoint In2 a l :=
    match l with
    | nil => false
    | b :: m =>
      if pair_eq a b then true else In2 a m
    end.

End PairEq.
