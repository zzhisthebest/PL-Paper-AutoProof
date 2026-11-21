Require Import List.

Require Import Lists.

Require Import Nat.

Require Import ZArith.

Import ListNotations.

Definition var := nat.

Fixpoint find_w (n: nat) (key: var) (l: list var) :=
  match l with
    | [] => None
    | (x :: xs) => if key =? x then Some n else find_w (S n) key xs
  end.

Definition find_where := (find_w 0).

Section Ref.

Class Referable (A: Type) :={
                               ref : A -> var;
                               find: var -> list A -> option A :=
                                 let fix f (key: var) (l: list A) :=
                                     match l with
                                     | [] => None
                                     | (x :: xs) => if key =? (ref x)
                                                   then Some x
                                                   else f key xs
                                     end in f;
                             }.

End Ref.

Module Refs.

Definition refs {A: Type} {R: Referable A} (x: list A) := (map ref x).

End Refs.

Export Refs.
