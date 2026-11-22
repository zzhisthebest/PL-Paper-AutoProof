From Fsub.ExtendedBase Require Import Fsub_LetSum_Definitions.

Theorem preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.

Theorem progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
