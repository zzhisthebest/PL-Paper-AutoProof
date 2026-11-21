Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import LibExtraEnv.

Notation "z '\[' x '->' y ']'" := (If z = x then y else z) (x at level 69, at level 70).

Definition subst_fvar (x y z: var): var := If z = x then y else z.
