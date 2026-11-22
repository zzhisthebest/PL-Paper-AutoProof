Require Import Metalib.Metatheory.

Require Import Rules.

Theorem preservation : forall e e' T,
    typing nil e T ->
    step e e' ->
    typing nil e' T.

Theorem progress : forall e T,
  typing empty e T ->
  value e \/ exists e', step e e'.
