From TLC Require Import LibLN.

Set Implicit Arguments.

Require Import LamI_Full_ott.

Implicit Types x : var.

Definition decidable (P : Prop) := (P \/ ~ P).

Theorem typing_decidable : forall E e,
  lc_trm e -> wf E -> decidable (exists T, typing E e T).
