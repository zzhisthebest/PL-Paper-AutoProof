Require Import String Arith Lia Bool List Nat Datatypes.

Require Import terms types subtypes derive.

Set Default Proof Using "Type".

Theorem reduction_preserves_typing:
  forall gamma M ty, derive gamma M ty -> forall N, t_red1 M N -> derive gamma N ty.
