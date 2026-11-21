Require Import Metalib.Metatheory.
Require Import syntax_ott.

Theorem preservation : forall e e' A,
    Etyping nil e A ->
    step e e' ->
    Etyping nil e' A.

Theorem progress : forall e A,
    Etyping nil e A ->
    value e \/ exists e', step e e'.
