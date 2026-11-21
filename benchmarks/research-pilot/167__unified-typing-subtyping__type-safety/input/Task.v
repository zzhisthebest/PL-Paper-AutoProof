Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import Full_ott Full_Infra.

Implicit Types x : var.

Theorem subject_reduction_wh : forall E t t' T,
  sub E t t T -> t --> t' -> sub E t' t' T.

Theorem progress_empty_wh : forall t T,
  sub empty t t T ->
  value t \/ exists t', t --> t'.
